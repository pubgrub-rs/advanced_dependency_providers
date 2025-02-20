// SPDX-License-Identifier: MPL-2.0

use core::ops::RangeBounds;
use pubgrub::Map;
use pubgrub::Range;
use std::collections::{BTreeMap, BTreeSet as Set};
use u32 as Version;

/// Each package is identified by its name.
pub type PackageName = String;
/// Features are identified by their name.
pub type Feature = String;

/// Global registry of known packages.
pub struct Index {
    /// Specify dependencies of each package version.
    pub packages: Map<PackageName, BTreeMap<Version, Deps>>,
}

/// Dependencies include mandatory dependencies and optional dependencies.
/// Optional dependencies are identified by an option called a "feature".
pub struct Deps {
    /// The regular, mandatory dependencies.
    pub mandatory: Map<PackageName, Dep>,
    /// The optional, feature-gated dependencies.
    pub optional: Map<Feature, Map<PackageName, Dep>>,
}

/// A dependency is specified with a range, and with a set of activated features.
pub struct Dep {
    /// The range dependended upon.
    pub range: Range<Version>,
    /// The activated features for that dependency.
    pub features: Set<Feature>,
}

impl Default for Deps {
    fn default() -> Self {
        Self {
            mandatory: Map::default(),
            optional: Map::default(),
        }
    }
}

impl Index {
    /// Empty new index.
    pub fn new() -> Self {
        Self {
            packages: Map::default(),
        }
    }

    /// List existing versions for a given package with newest versions first.
    pub fn available_versions(&self, package: &PackageName) -> impl Iterator<Item = &Version> {
        self.packages
            .get(package)
            .into_iter()
            .flat_map(|k| k.keys())
            .rev()
    }

    /// Register a package and its mandatory dependencies in the index.
    pub fn add_deps<R: RangeBounds<u32> + Clone>(
        &mut self,
        package: &str,
        version: u32,
        mandatory_deps: &[(&str, R, &[&str])],
    ) {
        let deps = self
            .packages
            .entry(package.to_string())
            .or_default()
            .entry(version.into())
            .or_default();
        for (p, r, features) in mandatory_deps {
            let dep = Dep {
                range: Range::from_range_bounds(r.clone()),
                features: features.iter().map(|s| s.to_string()).collect(),
            };
            deps.mandatory.insert(String::from(*p), dep);
        }
    }

    /// Register a feature and its associated dependencies for a given package in the index.
    pub fn add_feature<R: RangeBounds<u32> + Clone>(
        &mut self,
        package: &str,
        version: u32,
        feature: &str,
        optional_deps: &[(&str, R, &[&str])],
    ) {
        let deps = self
            .packages
            .entry(package.to_string())
            .or_default()
            .entry(version.into())
            .or_default()
            .optional
            .entry(feature.to_string())
            .or_default();
        for (p, r, features) in optional_deps {
            let dep = Dep {
                range: Range::from_range_bounds(r.clone()),
                features: features.iter().map(|s| s.to_string()).collect(),
            };
            deps.insert(String::from(*p), dep);
        }
    }
}

// TESTS #######################################################################

#[cfg(test)]
pub mod tests {
    use super::*;
    type R = core::ops::RangeFull;

    #[test]
    fn index_creation() {
        let mut index = Index::new();
        index.add_deps::<R>("a", 0, &[]);
        index.add_deps("a", 1, &[("b", 1.., &[])]);
        index.add_deps("a", 2, &[("c", .., &[])]);
        index.add_deps("b", 1, &[("d", ..4, &[])]);
        index.add_deps("c", 1, &[("d", ..4, &["feat"])]);
        index.add_feature("d", 1, "feat", &[("f", 1.., &[])]);
        index.add_deps::<R>("f", 1, &[]);
    }
}
