// SPDX-License-Identifier: MPL-2.0

use crate::index::{Index, Privacy};
use core::borrow::Borrow;
use core::fmt::Display;
use pubgrub::range::Range;
use pubgrub::solver::{Dependencies, DependencyProvider};
use pubgrub::version::SemanticVersion as SemVer;
use std::str::FromStr;

/// A package is identified by its name, and has a private seed.
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct Package {
    /// Package identifier
    pub name: String,
    /// Seed, the identifier of the current public subgraph
    pub seed: Seed,
}

/// A seed is the identifier associated with the private package at the origin of a public subgraph
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct Seed {
    /// Seed package identifier
    pub name: String,
    /// Seed version identifier
    pub version: SemVer,
}

impl Display for Package {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}${}", self.name, self.seed)
    }
}

impl Display for Seed {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}@{}", self.name, self.version)
    }
}

impl FromStr for Package {
    type Err = String;
    /// "a$root@1.0.0" -> Package "a" with seed "root" at version 1.0.0
    fn from_str(pkg: &str) -> Result<Self, Self::Err> {
        let mut pkg_parts = pkg.split('$');
        match (pkg_parts.next(), pkg_parts.next()) {
            (Some(name), Some(seed)) => Ok(Package {
                name: name.to_string(),
                seed: seed.parse().unwrap(),
            }),
            _ => Err(format!("{} is not a valid package name", pkg)),
        }
    }
}

impl FromStr for Seed {
    type Err = String;
    /// "root@1.0.0" -> Seed "root" at version 1.0.0
    fn from_str(seed: &str) -> Result<Self, Self::Err> {
        let mut seed_parts = seed.split('@');
        match (seed_parts.next(), seed_parts.next()) {
            (Some(name), Some(version)) => Ok(Seed {
                name: name.to_string(),
                version: version.parse().unwrap(),
            }),
            _ => Err(format!("{} is not a valid seed name", seed)),
        }
    }
}

impl Index {
    /// List existing versions for a given package with newest versions first.
    pub fn list_versions(&self, package: &Package) -> impl Iterator<Item = SemVer> + '_ {
        self.available_versions(&package.name).cloned()
    }
}

impl DependencyProvider<Package, SemVer> for Index {
    fn choose_package_version<T: Borrow<Package>, U: Borrow<Range<SemVer>>>(
        &self,
        potential_packages: impl Iterator<Item = (T, U)>,
    ) -> Result<(T, Option<SemVer>), Box<dyn std::error::Error>> {
        Ok(pubgrub::solver::choose_package_with_fewest_versions(
            |p| self.list_versions(p),
            potential_packages,
        ))
    }

    fn get_dependencies(
        &self,
        package: &Package,
        version: &SemVer,
    ) -> Result<Dependencies<Package, SemVer>, Box<dyn std::error::Error>> {
        let index_deps = match self
            .packages
            .get(&package.name)
            .and_then(|vs| vs.get(version))
        {
            None => return Ok(Dependencies::Unknown),
            Some(deps) => deps,
        };
        Ok(Dependencies::Known(
            index_deps
                .iter()
                .map(|(pkg, (prv, r))| {
                    match prv {
                        // For a public dependency, use the parent seed.
                        Privacy::Public => {
                            let dep_pkg = Package {
                                name: pkg.clone(),
                                seed: package.seed.clone(),
                            };
                            (dep_pkg, r.clone())
                        }
                        // For a private dependency, use current package as seed.
                        Privacy::Private => {
                            let seed = Seed {
                                name: package.name.clone(),
                                version: version.clone(),
                            };
                            let dep_pkg = Package {
                                name: pkg.clone(),
                                seed,
                            };
                            (dep_pkg, r.clone())
                        }
                    }
                })
                .collect(),
        ))
    }
}

// TESTS #######################################################################

#[cfg(test)]
pub mod tests {
    use super::*;
    use crate::index::Privacy::{Private, Public};
    use core::fmt::Debug;
    use pubgrub::error::PubGrubError;
    use pubgrub::type_aliases::{Map, SelectedDependencies};
    type R = core::ops::RangeFull;

    /// Helper function to simplify the tests code.
    fn resolve(
        provider: &impl DependencyProvider<Package, SemVer>,
        pkg: &str,
        version: (u32, u32, u32),
    ) -> Result<SelectedDependencies<Package, SemVer>, PubGrubError<Package, SemVer>> {
        let pkg = Package::from_str(pkg).unwrap();
        pubgrub::solver::resolve(provider, pkg, version)
    }

    /// Helper function to build a solution selection.
    fn select(packages: &[(&str, (u32, u32, u32))]) -> SelectedDependencies<Package, SemVer> {
        packages
            .iter()
            .map(|(p, v)| (Package::from_str(p).unwrap(), SemVer::from(*v)))
            .collect()
    }

    /// Helper function to compare a solution to an exact selection of package versions.
    fn assert_map_eq<K: Eq + std::hash::Hash + Debug, V: PartialEq + Debug>(
        h1: &Map<K, V>,
        h2: &Map<K, V>,
    ) {
        assert_eq!(
            h1.len(),
            h2.len(),
            "Different length:\n\n{:?}\n\n{:?}",
            h1,
            h2
        );
        for (k, v) in h1.iter() {
            assert_eq!(h2.get(k), Some(v));
        }
    }

    #[test]
    /// Example in guide.
    fn success_when_all_is_private() {
        let mut index = Index::new();
        index.add_deps("root", (1, 0, 0), &[("a", Private, ..)]);
        index.add_deps("root", (1, 0, 0), &[("b", Private, (2, 0, 0)..(2, 0, 1))]);
        index.add_deps("a", (1, 0, 0), &[("b", Private, (1, 0, 0)..(1, 0, 1))]);
        index.add_deps::<R>("b", (1, 0, 0), &[]);
        index.add_deps("b", (2, 0, 0), &[("c", Private, ..)]);
        index.add_deps::<R>("c", (1, 0, 0), &[]);
        assert_map_eq(
            &resolve(&index, "root$root@1.0.0", (1, 0, 0)).unwrap(),
            &select(&[
                ("root$root@1.0.0", (1, 0, 0)),
                ("a$root@1.0.0", (1, 0, 0)),
                ("b$root@1.0.0", (2, 0, 0)),
                ("b$a@1.0.0", (1, 0, 0)),
                ("c$b@2.0.0", (1, 0, 0)),
            ]),
        );
    }

    #[test]
    /// Package "b" is required at two different versions through public dependency of "a"
    fn failure_when_public_dependency_clash() {
        let mut index = Index::new();
        index.add_deps("root", (1, 0, 0), &[("a", Private, ..)]);
        index.add_deps("root", (1, 0, 0), &[("b", Private, (2, 0, 0)..(2, 0, 1))]);
        // "a" depends on "b" publicly.
        index.add_deps("a", (1, 0, 0), &[("b", Public, (1, 0, 0)..(1, 0, 1))]);
        index.add_deps::<R>("b", (1, 0, 0), &[]);
        index.add_deps("b", (2, 0, 0), &[("c", Private, ..)]);
        index.add_deps::<R>("c", (1, 0, 0), &[]);
        assert!(resolve(&index, "root$root@1.0.0", (1, 0, 0)).is_err());
    }
}
