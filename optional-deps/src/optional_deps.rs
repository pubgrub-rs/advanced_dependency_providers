// SPDX-License-Identifier: MPL-2.0

use crate::index::{Dep, Index};
use core::borrow::Borrow;
use core::fmt::Display;
use pubgrub::range::Range;
use pubgrub::solver::{Dependencies, DependencyConstraints, DependencyProvider};
use pubgrub::type_aliases::Map;
use pubgrub::version::NumberVersion as Version;
use std::str::FromStr;

/// A package is either a base package like "a",
/// or a feature package, corresponding to a feature associated to a base package.
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum Package {
    Base(String),
    Feature { base: String, feature: String },
}

impl Package {
    fn base_pkg(&self) -> &String {
        match self {
            Package::Base(pkg) => pkg,
            Package::Feature { base, .. } => base,
        }
    }
}

impl FromStr for Package {
    type Err = String;
    fn from_str(pkg: &str) -> Result<Self, Self::Err> {
        let mut pkg_parts = pkg.split('/');
        match (pkg_parts.next(), pkg_parts.next()) {
            (Some(base), None) => Ok(Package::Base(base.to_string())),
            (Some(base), Some(feat)) => Ok(Package::Feature {
                base: base.to_string(),
                feature: feat.to_string(),
            }),
            _ => Err(format!("{} is not a valid package name", pkg)),
        }
    }
}

impl Display for Package {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Package::Base(pkg) => write!(f, "{}", pkg),
            Package::Feature { base, feature } => write!(f, "{}/{}", base, feature),
        }
    }
}

impl Index {
    /// List existing versions for a given package with newest versions first.
    pub fn list_versions(&self, package: &Package) -> impl Iterator<Item = &Version> {
        self.available_versions(package.base_pkg())
    }
}

impl DependencyProvider<Package, Version> for Index {
    fn choose_package_version<T: Borrow<Package>, U: Borrow<Range<Version>>>(
        &self,
        potential_packages: impl Iterator<Item = (T, U)>,
    ) -> Result<(T, Option<Version>), Box<dyn std::error::Error>> {
        Ok(pubgrub::solver::choose_package_with_fewest_versions(
            |p| self.list_versions(p).cloned(),
            potential_packages,
        ))
    }

    fn get_dependencies(
        &self,
        package: &Package,
        version: &Version,
    ) -> Result<Dependencies<Package, Version>, Box<dyn std::error::Error>> {
        let all_versions = match self.packages.get(package.base_pkg()) {
            None => return Ok(Dependencies::Unknown),
            Some(all_versions) => all_versions,
        };
        let deps = match all_versions.get(version) {
            None => return Ok(Dependencies::Unknown),
            Some(deps) => deps,
        };

        match package {
            // If we asked for a base package, we simply return the mandatory dependencies.
            Package::Base(_) => Ok(Dependencies::Known(from_deps(&deps.mandatory))),
            // Otherwise, we concatenate the feature deps with a dependency to the base package.
            Package::Feature { base, feature } => match deps.optional.get(feature) {
                None => Ok(Dependencies::Unknown),
                Some(feature_deps) => {
                    let mut all_deps = from_deps(feature_deps);
                    all_deps.insert(
                        Package::Base(base.to_string()),
                        Range::exact(version.clone()),
                    );
                    Ok(Dependencies::Known(all_deps))
                }
            },
        }
    }
}

/// Helper function to convert Index deps into what is expected by the dependency provider.
fn from_deps(deps: &Map<String, Dep>) -> DependencyConstraints<Package, Version> {
    deps.iter()
        .map(|(base_pkg, dep)| {
            let feature_count = dep.features.len();
            dep.features
                .iter()
                .map(move |feat| {
                    (
                        Package::Feature {
                            base: base_pkg.clone(),
                            feature: feat.clone(),
                        },
                        dep.range.clone(),
                    )
                })
                .chain(std::iter::once((
                    Package::Base(base_pkg.clone()),
                    dep.range.clone(),
                )))
                // If there was no feature, we take the base package, otherwise, we don't.
                .take(feature_count.max(1))
        })
        .flatten()
        .collect()
}

// TESTS #######################################################################

#[cfg(test)]
pub mod tests {
    use super::*;
    use core::fmt::Debug;
    use pubgrub::error::PubGrubError;
    use pubgrub::type_aliases::{Map, SelectedDependencies};
    type R = core::ops::RangeFull;

    /// Helper function to simplify the tests code.
    fn resolve(
        provider: &impl DependencyProvider<Package, Version>,
        pkg: &str,
        version: u32,
    ) -> Result<SelectedDependencies<Package, Version>, PubGrubError<Package, Version>> {
        let pkg = Package::from_str(pkg).unwrap();
        pubgrub::solver::resolve(provider, pkg, version)
    }

    /// Helper function to build a solution selection.
    fn select(packages: &[(&str, u32)]) -> SelectedDependencies<Package, Version> {
        packages
            .iter()
            .map(|(p, v)| (Package::from_str(p).unwrap(), Version::from(*v)))
            .collect()
    }

    /// Helper function to compare a solution to an exact selection of package versions.
    fn assert_map_eq<K: Eq + std::hash::Hash, V: PartialEq + Debug>(
        h1: &Map<K, V>,
        h2: &Map<K, V>,
    ) {
        assert_eq!(h1.len(), h2.len());
        for (k, v) in h1.iter() {
            assert_eq!(h2.get(k), Some(v));
        }
    }

    #[test]
    fn success_when_no_feature() {
        let mut index = Index::new();
        index.add_deps::<R>("a", 0, &[]);
        assert_map_eq(&resolve(&index, "a", 0).unwrap(), &select(&[("a", 0)]));
    }

    #[test]
    fn failure_when_missing_feature() {
        let mut index = Index::new();
        index.add_deps::<R>("a", 0, &[]);
        assert!(resolve(&index, "a/missing_feat", 0).is_err());
    }

    #[test]
    fn success_when_feature_with_no_dep() {
        let mut index = Index::new();
        index.add_feature::<R>("a", 0, "feat", &[]);
        assert_map_eq(
            &resolve(&index, "a/feat", 0).unwrap(),
            &select(&[("a", 0), ("a/feat", 0)]),
        );
    }

    #[test]
    fn success_when_feature_with_one_dep() {
        let mut index = Index::new();
        index.add_feature("a", 0, "feat", &[("f", .., &[])]);
        index.add_deps::<R>("f", 0, &[]);
        assert_map_eq(
            &resolve(&index, "a/feat", 0).unwrap(),
            &select(&[("a", 0), ("a/feat", 0), ("f", 0)]),
        );
    }

    #[test]
    fn success_when_feature_with_two_deps() {
        let mut index = Index::new();
        index.add_feature("a", 0, "feat", &[("f1", .., &[]), ("f2", .., &[])]);
        index.add_deps::<R>("f1", 0, &[]);
        index.add_deps::<R>("f2", 0, &[]);
        assert_map_eq(
            &resolve(&index, "a/feat", 0).unwrap(),
            &select(&[("a", 0), ("a/feat", 0), ("f1", 0), ("f2", 0)]),
        );
    }

    #[test]
    fn success_when_transitive_feature() {
        let mut index = Index::new();
        index.add_deps("a", 0, &[("b", .., &["feat"])]);
        index.add_feature("b", 0, "feat", &[("f", .., &[])]);
        index.add_deps::<R>("f", 0, &[]);
        assert_map_eq(
            &resolve(&index, "a", 0).unwrap(),
            &select(&[("a", 0), ("b", 0), ("b/feat", 0), ("f", 0)]),
        );
    }

    #[test]
    fn success_when_recursive_feature() {
        let mut index = Index::new();
        index.add_deps("a", 0, &[("b", .., &["feat"])]);
        index.add_feature("b", 0, "feat", &[("f", .., &["rec_feat"])]);
        index.add_feature::<R>("f", 0, "rec_feat", &[]);
        assert_map_eq(
            &resolve(&index, "a", 0).unwrap(),
            &select(&[
                ("a", 0),
                ("b", 0),
                ("b/feat", 0),
                ("f", 0),
                ("f/rec_feat", 0),
            ]),
        );
    }

    #[test]
    fn success_when_multiple_features() {
        let mut index = Index::new();
        index.add_deps("a", 0, &[("b", .., &["feat1", "feat2"])]);
        index.add_feature("b", 0, "feat1", &[("f1", .., &[])]);
        index.add_feature("b", 0, "feat2", &[("f2", .., &[])]);
        index.add_deps::<R>("f1", 0, &[]);
        index.add_deps::<R>("f2", 0, &[]);
        assert_map_eq(
            &resolve(&index, "a", 0).unwrap(),
            &select(&[
                ("a", 0),
                ("b", 0),
                ("b/feat1", 0),
                ("b/feat2", 0),
                ("f1", 0),
                ("f2", 0),
            ]),
        );
    }

    #[test]
    /// b/feat1 and b/feat2 are not available with the same version of b.
    fn failure_when_different_feature_versions() {
        let mut index = Index::new();
        index.add_deps("a", 0, &[("b", .., &["feat1", "feat2"])]);
        index.add_feature("b", 0, "feat1", &[("f1", .., &[])]);
        // feat2 is only available for version 1 of b
        index.add_feature("b", 1, "feat2", &[("f2", .., &[])]);
        index.add_deps::<R>("f1", 0, &[]);
        index.add_deps::<R>("f2", 0, &[]);
        assert!(resolve(&index, "a", 0).is_err());
    }
}
