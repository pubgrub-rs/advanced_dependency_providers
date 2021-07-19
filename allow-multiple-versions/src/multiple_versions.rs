// SPDX-License-Identifier: MPL-2.0

use crate::index::Index;
use core::borrow::Borrow;
use core::fmt::Display;
use itertools::Either;
use pubgrub::range::Range;
use pubgrub::solver::{Dependencies, DependencyProvider};
use pubgrub::type_aliases::Map;
use pubgrub::version::SemanticVersion as SemVer;
use std::str::FromStr;

/// A package is either a bucket, or a proxi between two packages.
#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum Package {
    /// "a#1"
    Bucket(Bucket),
    /// source -> target
    Proxi {
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
            Package::Proxi { source, .. } => &source.0.name,
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
            Package::Proxi { source, target } => write!(f, "{}@{}->{}", source.0, source.1, target),
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
                    self.available_versions(package.pkg_name())
                        .filter(move |v| bucket_range.contains(*v))
                        .cloned(),
                )
            }
            // If we are on a proxi, there is one version per bucket in the target package.
            Package::Proxi { target, .. } => {
                Either::Right(bucket_versions(self.available_versions(&target).cloned()))
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
        let all_versions = match self.packages.get(package.pkg_name()) {
            None => return Ok(Dependencies::Unknown),
            Some(all_versions) => all_versions,
        };
        let deps = match all_versions.get(version) {
            None => return Ok(Dependencies::Unknown),
            Some(deps) => deps,
        };

        match package {
            Package::Bucket(pkg) => {
                // If this is a bucket, we convert each original dependency into
                // either a dependency to a bucket package if the range is fully contained within one bucket,
                // or a dependency to a proxi package at any version otherwise.
                let pkg_deps = deps
                    .iter()
                    .map(|(name, range)| {
                        if let Some(bucket) = single_bucket_spanned(range) {
                            let name = name.clone();
                            let bucket_dep = Bucket { name, bucket };
                            (Package::Bucket(bucket_dep), range.clone())
                        } else {
                            let proxi = Package::Proxi {
                                source: (pkg.clone(), version.clone()),
                                target: name.clone(),
                            };
                            (proxi, Range::any())
                        }
                    })
                    .collect();
                Ok(Dependencies::Known(pkg_deps))
            }
            Package::Proxi { target, .. } => {
                // If this is a proxi package, it depends on a single bucket package, the target,
                // at a range of versions corresponding to the bucket range of the version asked.
                let (target_bucket, _, _) = version.clone().into();
                let bucket_range = Range::between((target_bucket, 0, 0), (target_bucket + 1, 0, 0));
                let mut bucket_dep = Map::default();
                bucket_dep.insert(
                    Package::Bucket(Bucket {
                        name: target.clone(),
                        bucket: target_bucket,
                    }),
                    bucket_range,
                );
                Ok(Dependencies::Known(bucket_dep))
            }
        }
    }
}

/// If the range is fully contained within one bucket,
/// this returns that bucket identifier.
/// Otherwise, it returns None.
fn single_bucket_spanned(range: &Range<SemVer>) -> Option<u32> {
    // TODO: problem here since I need to extract somehow the lower and higher bounds
    // of the range, but the Range API does not allow that.
    todo!()
}

// TESTS #######################################################################
