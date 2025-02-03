// SPDX-License-Identifier: MPL-2.0

use crate::index::Index;
use core::fmt::Display;
use itertools::Either;
use pubgrub::Map;
use pubgrub::Range;
use pubgrub::SemanticVersion as SemVer;
use pubgrub::{Dependencies, DependencyProvider};
use std::convert::Infallible;
use std::ops::Bound;
use std::str::FromStr;

/// A package is either a bucket, or a proxy between two packages.
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum Package {
    /// "a#1"
    Bucket(Bucket),
    /// source -> target
    Proxy {
        source: (Bucket, SemVer),
        target: String,
    },
}

/// A bucket corresponds to a given package, and match versions in a range identified by their
/// major component.
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct Bucket {
    pub name: String,
    pub bucket: u32, // 1 maps to the range 1.0.0 <= v < 2.0.0
}

impl Package {
    fn pkg_name(&self) -> &String {
        match self {
            Package::Bucket(b) => &b.name,
            Package::Proxy { source, .. } => &source.0.name,
        }
    }
}

impl FromStr for Package {
    type Err = String;
    /// "a#1" -> Package::Bucket
    fn from_str(pkg: &str) -> Result<Self, Self::Err> {
        let mut pkg_parts = pkg.split('#');
        match (pkg_parts.next(), pkg_parts.next()) {
            (Some(name), Some(bucket)) => Ok(Package::Bucket(Bucket {
                name: name.to_string(),
                bucket: bucket.parse().unwrap(),
            })),
            _ => Err(format!("{} is not a valid package name", pkg)),
        }
    }
}

impl Display for Package {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Package::Bucket(pkg) => write!(f, "{}", pkg),
            Package::Proxy { source, target } => write!(f, "{}@{}->{}", source.0, source.1, target),
        }
    }
}

impl Display for Bucket {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}#{}", self.name, self.bucket)
    }
}

impl Index {
    /// List existing versions for a given package with newest versions first.
    pub fn list_versions(&self, package: &Package) -> impl Iterator<Item = SemVer> + '_ {
        match package {
            // If we are on a bucket, we need to filter versions
            // to only keep those within the bucket.
            Package::Bucket(p) => {
                let bucket_range = Range::between((p.bucket, 0, 0), (p.bucket + 1, 0, 0));
                Either::Left(
                    self.available_versions(&p.name)
                        .filter(move |v| bucket_range.contains(*v))
                        .cloned(),
                )
            }
            // If we are on a proxy, there is one version per bucket in the target package.
            // We can additionally filter versions to only those inside the dependency range.
            Package::Proxy { target, source } => {
                let dep_range = self
                    .packages
                    .get(&source.0.name)
                    .unwrap()
                    .get(&source.1)
                    .unwrap()
                    .get(target)
                    .unwrap();
                Either::Right(bucket_versions(
                    self.available_versions(&target)
                        .filter(move |v| dep_range.contains(v))
                        .cloned(),
                ))
            }
        }
    }
}

/// Take a list of versions, and output a list of the corresponding bucket versions.
/// So [1.1, 1.2, 2.3] -> [1.0, 2.0]
fn bucket_versions(versions: impl Iterator<Item = SemVer>) -> impl Iterator<Item = SemVer> {
    let mut current_bucket = None;
    // This filter_map makes the hypothesis that versions are sorted in a normal or reverse order.
    // Would need a bit more work if they are not ordered due to prioritizations, etc.
    versions.filter_map(move |v| {
        let v_bucket = Some(bucket_version(v));
        if v_bucket != current_bucket {
            current_bucket = v_bucket;
            v_bucket
        } else {
            None
        }
    })
}

fn bucket_version(v: SemVer) -> SemVer {
    let (major, _, _) = v.into();
    (major, 0, 0).into()
}

impl DependencyProvider for Index {
    type P = Package;

    type V = SemVer;

    type VS = Range<SemVer>;

    type M = String;

    fn prioritize(
        &self,
        _package: &Self::P,
        _range: &Self::VS,
        _package_conflicts_counts: &pubgrub::PackageResolutionStatistics,
    ) -> Self::Priority {
        1
    }

    type Priority = u8;

    type Err = Infallible;

    fn choose_version(
        &self,
        package: &Self::P,
        range: &Self::VS,
    ) -> Result<Option<Self::V>, Self::Err> {
        Ok(self
            .list_versions(package)
            .filter(|v| range.contains(v))
            .next())
    }

    fn get_dependencies(
        &self,
        package: &Package,
        version: &SemVer,
    ) -> Result<Dependencies<Package, Self::VS, Self::M>, Self::Err> {
        let all_versions = match self.packages.get(package.pkg_name()) {
            None => return Ok(Dependencies::Unavailable("".into())),
            Some(all_versions) => all_versions,
        };

        match package {
            Package::Bucket(pkg) => {
                // If this is a bucket, we convert each original dependency into
                // either a dependency to a bucket package if the range is fully contained within one bucket,
                // or a dependency to a proxy package at any version otherwise.
                let deps = match all_versions.get(version) {
                    None => return Ok(Dependencies::Unavailable("".into())),
                    Some(deps) => deps,
                };
                let pkg_deps = deps
                    .iter()
                    .map(|(name, range)| {
                        if let Some(bucket) = single_bucket_spanned(range) {
                            let name = name.clone();
                            let bucket_dep = Bucket { name, bucket };
                            (Package::Bucket(bucket_dep), range.clone())
                        } else {
                            let proxy = Package::Proxy {
                                source: (pkg.clone(), version.clone()),
                                target: name.clone(),
                            };
                            (proxy, Range::full())
                        }
                    })
                    .collect();
                Ok(Dependencies::Available(pkg_deps))
            }
            Package::Proxy { source, target } => {
                // If this is a proxy package, it depends on a single bucket package, the target,
                // at a range of versions corresponding to the bucket range of the version asked,
                // intersected with the original dependency range.
                let deps = match all_versions.get(&source.1) {
                    None => return Ok(Dependencies::Unavailable("".into())),
                    Some(deps) => deps,
                };
                let (target_bucket, _, _) = version.clone().into();
                let bucket_range = Range::between((target_bucket, 0, 0), (target_bucket + 1, 0, 0));
                let target_range = deps.get(target).unwrap();
                let mut bucket_dep = Map::default();
                bucket_dep.insert(
                    Package::Bucket(Bucket {
                        name: target.clone(),
                        bucket: target_bucket,
                    }),
                    bucket_range.intersection(target_range),
                );
                Ok(Dependencies::Available(bucket_dep))
            }
        }
    }
}

/// If the range is fully contained within one bucket,
/// this returns that bucket identifier.
/// Otherwise, it returns None.
fn single_bucket_spanned(range: &Range<SemVer>) -> Option<u32> {
    let (Bound::Included(low) | Bound::Excluded(low)) = range.bounding_range()?.0 else {
        return None;
    };
    let bucket_range = Range::between(low, low.bump_major());
    range.subset_of(&bucket_range).then(|| {
        let (major, _, _) = low.clone().into();
        major
    })
}
// TESTS #######################################################################

#[cfg(test)]
pub mod tests {
    use super::*;
    use core::fmt::Debug;
    use pubgrub::PubGrubError;
    use pubgrub::{Map, SelectedDependencies};
    type R = core::ops::RangeFull;

    /// Helper function to simplify the tests code.
    fn resolve(
        provider: &Index,
        pkg: &str,
        version: (u32, u32, u32),
    ) -> Result<SelectedDependencies<Index>, PubGrubError<Index>> {
        let pkg = Package::from_str(pkg).unwrap();
        pubgrub::resolve(provider, pkg, version).map(|solution| {
            // remove proxy packages from the solution
            solution
                .into_iter()
                .filter(|(pkg, _)| match pkg {
                    Package::Bucket(_) => true,
                    _ => false,
                })
                .collect()
        })
    }

    /// Helper function to build a solution selection.
    fn select(packages: &[(&str, (u32, u32, u32))]) -> SelectedDependencies<Index> {
        packages
            .iter()
            .map(|(p, v)| (Package::from_str(p).unwrap(), SemVer::from(*v)))
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
    /// Example in guide.
    fn success_when_simple_version() {
        let mut index = Index::new();
        index.add_deps("a", (1, 4, 0), &[("b", (1, 1, 0)..(2, 9, 0))]);
        index.add_deps("b", (1, 3, 0), &[("c", (1, 1, 0)..(1, 1, 1))]);
        index.add_deps("b", (2, 7, 0), &[("d", (3, 1, 0)..(3, 1, 1))]);
        index.add_deps::<R>("c", (1, 1, 0), &[]);
        index.add_deps::<R>("d", (3, 1, 0), &[]);
        assert_map_eq(
            &resolve(&index, "a#1", (1, 4, 0)).unwrap(),
            &select(&[("a#1", (1, 4, 0)), ("b#2", (2, 7, 0)), ("d#3", (3, 1, 0))]),
        );
    }

    #[test]
    /// "a" depends on "d"@1 and "d"@2 via "b" and "c".
    fn success_when_double_version() {
        let mut index = Index::new();
        index.add_deps("a", (1, 0, 0), &[("b", (1, 0, 0)..(2, 0, 0))]);
        index.add_deps("a", (1, 0, 0), &[("c", (1, 0, 0)..(2, 0, 0))]);
        index.add_deps("b", (1, 0, 0), &[("d", (1, 0, 0)..(2, 0, 0))]);
        index.add_deps("c", (1, 0, 0), &[("d", (2, 0, 0)..(3, 0, 0))]);
        index.add_deps::<R>("d", (1, 0, 0), &[]);
        index.add_deps::<R>("d", (2, 0, 0), &[]);
        assert_map_eq(
            &resolve(&index, "a#1", (1, 0, 0)).unwrap(),
            &select(&[
                ("a#1", (1, 0, 0)),
                ("b#1", (1, 0, 0)),
                ("c#1", (1, 0, 0)),
                ("d#1", (1, 0, 0)),
                ("d#2", (2, 0, 0)),
            ]),
        );
    }

    #[test]
    /// "a" depends on "d"@1.0 and "d"@1.5 via "b" and "c" which is forbidden
    fn fail_when_same_bucket() {
        let mut index = Index::new();
        index.add_deps("a", (1, 0, 0), &[("b", (1, 0, 0)..(2, 0, 0))]);
        index.add_deps("a", (1, 0, 0), &[("c", (1, 0, 0)..(2, 0, 0))]);
        index.add_deps("b", (1, 0, 0), &[("d", (1, 0, 0)..(1, 5, 0))]);
        index.add_deps("c", (1, 0, 0), &[("d", (1, 5, 0)..(2, 0, 0))]);
        index.add_deps::<R>("d", (1, 0, 0), &[]);
        index.add_deps::<R>("d", (1, 5, 0), &[]);
        assert!(resolve(&index, "a#1", (1, 0, 0)).is_err());
    }
}
