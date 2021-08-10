// SPDX-License-Identifier: MPL-2.0

use crate::index::{Index, Privacy};
use core::borrow::Borrow;
use core::fmt::Display;
use pubgrub::range::Range;
use pubgrub::solver::{Dependencies, DependencyProvider};
use pubgrub::type_aliases::Map;
use pubgrub::version::SemanticVersion as SemVer;
use std::collections::BTreeSet as Set;
use std::str::FromStr;

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub struct Package {
    name: String,
    seeds: SeededPkg,
}

#[derive(Debug, Clone, Eq, PartialEq, Hash)]
pub enum SeededPkg {
    Final(Seed),
    Multi(Set<Seed>),
}

/// A seed is the identifier associated with the private package at the origin of a public subgraph
#[derive(Debug, Clone, Eq, PartialEq, Hash, PartialOrd, Ord)]
pub struct Seed {
    /// Seed package identifier
    pub name: String,
    /// Seed version identifier
    pub version: SemVer,
}

impl SeededPkg {
    pub fn is_final(&self) -> bool {
        match self {
            Self::Final(_) => true,
            _ => false,
        }
    }
}

impl Display for Package {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}${}", self.name, self.seeds)
    }
}

impl Display for SeededPkg {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Final(seed) => write!(f, "{} final", seed),
            Self::Multi(seeds) => {
                let all_seeds: Vec<_> = seeds.iter().map(|s| s.to_string()).collect();
                write!(f, "{} seeded", all_seeds.join("$"))
            }
        }
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
            (Some(name), Some(seeds)) => Ok(Package {
                name: name.to_string(),
                seeds: seeds.parse().unwrap(),
            }),
            _ => Err(format!("{} is not a valid package name", pkg)),
        }
    }
}

impl FromStr for SeededPkg {
    type Err = String;
    /// "root@1.0.0 final" -> Final package "a" with seed "root" at version 1.0.0
    fn from_str(pkg: &str) -> Result<Self, Self::Err> {
        let mut pkg_parts = pkg.split(' ');
        match (pkg_parts.next(), pkg_parts.next()) {
            (Some(seed), Some("final")) => Ok(Self::Final(seed.parse().unwrap())),
            (Some(seed), Some("seeded")) => {
                let mut seeds = Set::default();
                seeds.insert(seed.parse().unwrap());
                Ok(Self::Multi(seeds))
            }
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
        match &package.seeds {
            SeededPkg::Final(_) => Ok(Dependencies::Known(Map::default())),
            SeededPkg::Multi(seeds) => {
                let index_deps = match self
                    .packages
                    .get(&package.name)
                    .and_then(|vs| vs.get(version))
                {
                    None => return Ok(Dependencies::Unknown),
                    Some(deps) => deps,
                };
                // Start an iterator with final seeds
                let seeded_pkg = |seed: &Seed| Package {
                    name: package.name.clone(),
                    seeds: SeededPkg::Final(seed.clone()),
                };
                let final_seeded = seeds
                    .iter()
                    .map(|s| (seeded_pkg(s), Range::exact(version.clone())));
                // Figure out if there are both private and public deps.
                let has_private = index_deps
                    .values()
                    .any(|(privacy, _)| privacy == &Privacy::Private);
                let has_public = index_deps
                    .values()
                    .any(|(privacy, _)| privacy == &Privacy::Public);
                // Compute the new set of seeds if there is a need.
                let new_seeds = if has_private && has_public {
                    let mut seeds_copy = seeds.clone();
                    seeds_copy.insert(Seed {
                        name: package.name.clone(),
                        version: version.clone(),
                    });
                    seeds_copy
                } else {
                    seeds.clone()
                };
                // Chain the final_seeded iterator with actual dependencies.
                let singleton = |s| {
                    let mut s_set = Set::default();
                    s_set.insert(s);
                    s_set
                };
                Ok(Dependencies::Known(
                    final_seeded
                        .chain(index_deps.iter().map(|(p, (privacy, r))| {
                            let p_seeds = if privacy == &Privacy::Private {
                                SeededPkg::Multi(singleton(Seed {
                                    name: package.name.clone(),
                                    version: version.clone(),
                                }))
                            } else {
                                SeededPkg::Multi(new_seeds.clone())
                            };
                            let dep_p = Package {
                                name: p.clone(),
                                seeds: p_seeds,
                            };
                            (dep_p, r.clone())
                        }))
                        .collect(),
                ))
            }
        }
    }
}

// TESTS #######################################################################

#[cfg(test)]
pub mod tests {
    use super::*;
    use crate::index::Privacy::{Private, Public};
    use core::fmt::Debug;
    use pubgrub::error::PubGrubError;
    // use pubgrub::report::{DefaultStringReporter, Reporter};
    use pubgrub::type_aliases::{Map, SelectedDependencies};
    type R = core::ops::RangeFull;

    /// Helper function to simplify the tests code.
    fn resolve(
        provider: &impl DependencyProvider<Package, SemVer>,
        pkg: &str,
        version: (u32, u32, u32),
    ) -> Result<SelectedDependencies<Package, SemVer>, PubGrubError<Package, SemVer>> {
        let pkg = Package::from_str(pkg).unwrap();
        pubgrub::solver::resolve(provider, pkg, version).map(|solution| {
            solution
                .into_iter()
                .filter(|(p, _)| p.seeds.is_final())
                .collect()
        })
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
        index.add_deps("root", (1, 0, 0), &[("a", Private, (1, 0, 0)..(1, 0, 1))]);
        index.add_deps("root", (1, 0, 0), &[("b", Private, (1, 0, 0)..(1, 0, 1))]);
        // "a" depends on "b" privately.
        index.add_deps("a", (1, 0, 0), &[("b", Private, (2, 0, 0)..(2, 0, 1))]);
        index.add_deps::<R>("b", (1, 0, 0), &[]);
        index.add_deps::<R>("b", (2, 0, 0), &[]);
        let solution = resolve(&index, "root$root@1.0.0 seeded", (1, 0, 0));
        assert_map_eq(
            &solution.unwrap(),
            &select(&[
                ("root$root@1.0.0 final", (1, 0, 0)),
                ("a$root@1.0.0 final", (1, 0, 0)),
                ("b$root@1.0.0 final", (1, 0, 0)),
                ("b$a@1.0.0 final", (2, 0, 0)),
            ]),
        );
    }

    #[test]
    /// Package "b" is required at two different versions through public dependency of "a"
    fn failure_when_public_dependency_clash() {
        let mut index = Index::new();
        index.add_deps("root", (1, 0, 0), &[("a", Private, (1, 0, 0)..(1, 0, 1))]);
        index.add_deps("root", (1, 0, 0), &[("b", Private, (1, 0, 0)..(1, 0, 1))]);
        // "a" depends on "b" publicly.
        index.add_deps("a", (1, 0, 0), &[("b", Public, (2, 0, 0)..(2, 0, 1))]);
        index.add_deps::<R>("b", (1, 0, 0), &[]);
        index.add_deps::<R>("b", (2, 0, 0), &[]);
        let solution = resolve(&index, "root$root@1.0.0 seeded", (1, 0, 0));
        assert!(solution.is_err());
    }

    #[test]
    fn success_when_after_double_private_fork() {
        let mut index = Index::new();
        index.add_deps("root", (1, 0, 0), &[("a", Public, (1, 0, 0)..(1, 0, 1))]);
        // "a" depends on "b" and "c" privately.
        index.add_deps("a", (1, 0, 0), &[("b", Private, (1, 0, 0)..(1, 0, 1))]);
        index.add_deps("a", (1, 0, 0), &[("c", Private, (1, 0, 0)..(1, 0, 1))]);
        // "b" and "c" depend on two different versions of d.
        index.add_deps("b", (1, 0, 0), &[("d", Private, (1, 0, 0)..(1, 0, 1))]);
        index.add_deps("c", (1, 0, 0), &[("d", Private, (2, 0, 0)..(2, 0, 1))]);
        index.add_deps::<R>("d", (1, 0, 0), &[]);
        index.add_deps::<R>("d", (2, 0, 0), &[]);
        let solution = resolve(&index, "root$root@1.0.0 seeded", (1, 0, 0));
        assert_map_eq(
            &solution.unwrap(),
            &select(&[
                ("root$root@1.0.0 final", (1, 0, 0)),
                ("a$root@1.0.0 final", (1, 0, 0)),
                ("b$a@1.0.0 final", (1, 0, 0)),
                ("c$a@1.0.0 final", (1, 0, 0)),
                ("d$b@1.0.0 final", (1, 0, 0)),
                ("d$c@1.0.0 final", (2, 0, 0)),
            ]),
        );
    }

    #[test]
    fn failure_when_after_single_private_fork() {
        let mut index = Index::new();
        index.add_deps("root", (1, 0, 0), &[("a", Public, (1, 0, 0)..(1, 0, 1))]);
        // "a" depends on "b" and "c" privately.
        index.add_deps("a", (1, 0, 0), &[("b", Private, (1, 0, 0)..(1, 0, 1))]);
        index.add_deps("a", (1, 0, 0), &[("c", Private, (1, 0, 0)..(1, 0, 1))]);
        // "b" and "c" depend on two different versions of d.
        index.add_deps("b", (1, 0, 0), &[("d", Public, (1, 0, 0)..(1, 0, 1))]);
        index.add_deps("c", (1, 0, 0), &[("d", Public, (2, 0, 0)..(2, 0, 1))]);
        index.add_deps::<R>("d", (1, 0, 0), &[]);
        index.add_deps::<R>("d", (2, 0, 0), &[]);
        let solution = resolve(&index, "root$root@1.0.0 seeded", (1, 0, 0));
        assert!(solution.is_err());
    }

    #[test]
    fn success_when_after_single_private_fork_if_same_version() {
        let mut index = Index::new();
        index.add_deps("root", (1, 0, 0), &[("a", Public, (1, 0, 0)..(1, 0, 1))]);
        // "a" depends on "b" and "c" privately.
        index.add_deps("a", (1, 0, 0), &[("b", Private, (1, 0, 0)..(1, 0, 1))]);
        index.add_deps("a", (1, 0, 0), &[("c", Private, (1, 0, 0)..(1, 0, 1))]);
        // "b" and "c" depend on two different versions of d.
        index.add_deps("b", (1, 0, 0), &[("d", Public, ..)]);
        index.add_deps("c", (1, 0, 0), &[("d", Public, (1, 0, 0)..(1, 0, 1))]);
        index.add_deps::<R>("d", (1, 0, 0), &[]);
        index.add_deps::<R>("d", (2, 0, 0), &[]);
        let solution = resolve(&index, "root$root@1.0.0 seeded", (1, 0, 0));
        assert_map_eq(
            &solution.unwrap(),
            &select(&[
                ("root$root@1.0.0 final", (1, 0, 0)),
                ("a$root@1.0.0 final", (1, 0, 0)),
                ("b$a@1.0.0 final", (1, 0, 0)),
                ("c$a@1.0.0 final", (1, 0, 0)),
                ("d$a@1.0.0 final", (1, 0, 0)),
            ]),
        );
    }

    #[test]
    fn failure_after_long_chain() {
        let mut index = Index::new();
        // long public chain root-a-b-c-d
        index.add_deps("root", (1, 0, 0), &[("a", Public, (1, 0, 0)..(1, 0, 1))]);
        index.add_deps("a", (1, 0, 0), &[("b", Public, (1, 0, 0)..(1, 0, 1))]);
        index.add_deps("b", (1, 0, 0), &[("c", Public, (1, 0, 0)..(1, 0, 1))]);
        index.add_deps("c", (1, 0, 0), &[("d", Public, (1, 0, 0)..(1, 0, 1))]);
        index.add_deps::<R>("d", (1, 0, 0), &[]);
        // private branches at a, b, and c
        index.add_deps("a", (1, 0, 0), &[("e", Private, (1, 0, 0)..(1, 0, 1))]);
        index.add_deps("b", (1, 0, 0), &[("f", Private, (1, 0, 0)..(1, 0, 1))]);
        index.add_deps("c", (1, 0, 0), &[("g", Private, (1, 0, 0)..(1, 0, 1))]);
        index.add_deps::<R>("f", (1, 0, 0), &[]);
        index.add_deps::<R>("g", (1, 0, 0), &[]);
        // long public chain from a-e to another version of d
        index.add_deps("e", (1, 0, 0), &[("h", Public, (1, 0, 0)..(1, 0, 1))]);
        index.add_deps("h", (1, 0, 0), &[("i", Public, (1, 0, 0)..(1, 0, 1))]);
        index.add_deps("i", (1, 0, 0), &[("d", Public, (2, 0, 0)..(2, 0, 1))]);
        index.add_deps::<R>("h", (1, 0, 0), &[]);
        index.add_deps::<R>("i", (1, 0, 0), &[]);
        index.add_deps::<R>("d", (2, 0, 0), &[]);
        let solution = resolve(&index, "root$root@1.0.0 seeded", (1, 0, 0));
        assert!(solution.is_err());
    }

    #[test]
    fn success_after_long_chain_with_one_private_on_main() {
        let mut index = Index::new();
        // long public chain root-a-b-c-d
        index.add_deps("root", (1, 0, 0), &[("a", Public, (1, 0, 0)..(1, 0, 1))]);
        index.add_deps("a", (1, 0, 0), &[("b", Public, (1, 0, 0)..(1, 0, 1))]);
        index.add_deps("b", (1, 0, 0), &[("c", Public, (1, 0, 0)..(1, 0, 1))]);
        index.add_deps("c", (1, 0, 0), &[("d", Private, (1, 0, 0)..(1, 0, 1))]);
        index.add_deps::<R>("d", (1, 0, 0), &[]);
        // private branches at a, b, and c
        index.add_deps("a", (1, 0, 0), &[("e", Private, (1, 0, 0)..(1, 0, 1))]);
        index.add_deps("b", (1, 0, 0), &[("f", Private, (1, 0, 0)..(1, 0, 1))]);
        index.add_deps("c", (1, 0, 0), &[("g", Private, (1, 0, 0)..(1, 0, 1))]);
        index.add_deps::<R>("f", (1, 0, 0), &[]);
        index.add_deps::<R>("g", (1, 0, 0), &[]);
        // long public chain from a-e to another version of d
        index.add_deps("e", (1, 0, 0), &[("h", Public, (1, 0, 0)..(1, 0, 1))]);
        index.add_deps("h", (1, 0, 0), &[("i", Public, (1, 0, 0)..(1, 0, 1))]);
        index.add_deps("i", (1, 0, 0), &[("d", Public, (2, 0, 0)..(2, 0, 1))]);
        index.add_deps::<R>("h", (1, 0, 0), &[]);
        index.add_deps::<R>("i", (1, 0, 0), &[]);
        index.add_deps::<R>("d", (2, 0, 0), &[]);
        let solution = resolve(&index, "root$root@1.0.0 seeded", (1, 0, 0));
        assert_map_eq(
            &solution.unwrap(),
            &select(&[
                ("root$root@1.0.0 final", (1, 0, 0)),
                ("a$root@1.0.0 final", (1, 0, 0)),
                ("b$root@1.0.0 final", (1, 0, 0)),
                ("b$a@1.0.0 final", (1, 0, 0)), // hum ...
                ("c$root@1.0.0 final", (1, 0, 0)),
                ("c$a@1.0.0 final", (1, 0, 0)), // hum ...
                ("c$b@1.0.0 final", (1, 0, 0)), // hum ...
                ("d$c@1.0.0 final", (1, 0, 0)),
                ("e$a@1.0.0 final", (1, 0, 0)),
                ("f$b@1.0.0 final", (1, 0, 0)),
                ("g$c@1.0.0 final", (1, 0, 0)),
                ("h$a@1.0.0 final", (1, 0, 0)),
                ("i$a@1.0.0 final", (1, 0, 0)),
                // d @ 2 coming from a @ 1
                ("d$a@1.0.0 final", (2, 0, 0)),
            ]),
        );
    }

    #[test]
    fn success_after_long_chain_with_one_private_on_other() {
        let mut index = Index::new();
        // long public chain root-a-b-c-d
        index.add_deps("root", (1, 0, 0), &[("a", Public, (1, 0, 0)..(1, 0, 1))]);
        index.add_deps("a", (1, 0, 0), &[("b", Public, (1, 0, 0)..(1, 0, 1))]);
        index.add_deps("b", (1, 0, 0), &[("c", Public, (1, 0, 0)..(1, 0, 1))]);
        index.add_deps("c", (1, 0, 0), &[("d", Public, (1, 0, 0)..(1, 0, 1))]);
        index.add_deps::<R>("d", (1, 0, 0), &[]);
        // private branches at a, b, and c
        index.add_deps("a", (1, 0, 0), &[("e", Private, (1, 0, 0)..(1, 0, 1))]);
        index.add_deps("b", (1, 0, 0), &[("f", Private, (1, 0, 0)..(1, 0, 1))]);
        index.add_deps("c", (1, 0, 0), &[("g", Private, (1, 0, 0)..(1, 0, 1))]);
        index.add_deps::<R>("f", (1, 0, 0), &[]);
        index.add_deps::<R>("g", (1, 0, 0), &[]);
        // long public chain from a-e to another version of d
        index.add_deps("e", (1, 0, 0), &[("h", Public, (1, 0, 0)..(1, 0, 1))]);
        index.add_deps("h", (1, 0, 0), &[("i", Public, (1, 0, 0)..(1, 0, 1))]);
        index.add_deps("i", (1, 0, 0), &[("d", Private, (2, 0, 0)..(2, 0, 1))]);
        index.add_deps::<R>("h", (1, 0, 0), &[]);
        index.add_deps::<R>("i", (1, 0, 0), &[]);
        index.add_deps::<R>("d", (2, 0, 0), &[]);
        let solution = resolve(&index, "root$root@1.0.0 seeded", (1, 0, 0));
        assert_map_eq(
            &solution.unwrap(),
            &select(&[
                ("root$root@1.0.0 final", (1, 0, 0)),
                ("a$root@1.0.0 final", (1, 0, 0)),
                ("b$root@1.0.0 final", (1, 0, 0)),
                ("b$a@1.0.0 final", (1, 0, 0)), // hum ...
                ("c$root@1.0.0 final", (1, 0, 0)),
                ("c$a@1.0.0 final", (1, 0, 0)), // hum ...
                ("c$b@1.0.0 final", (1, 0, 0)), // hum ...
                ("d$root@1.0.0 final", (1, 0, 0)),
                ("d$a@1.0.0 final", (1, 0, 0)), // hum ...
                ("d$b@1.0.0 final", (1, 0, 0)), // hum ...
                ("d$c@1.0.0 final", (1, 0, 0)), // hum ...
                ("e$a@1.0.0 final", (1, 0, 0)),
                ("f$b@1.0.0 final", (1, 0, 0)),
                ("g$c@1.0.0 final", (1, 0, 0)),
                ("h$a@1.0.0 final", (1, 0, 0)),
                ("i$a@1.0.0 final", (1, 0, 0)),
                // d @ 2 coming from i @ 1
                ("d$i@1.0.0 final", (2, 0, 0)),
            ]),
        );
    }

    #[test]
    fn success_when_all_private_except_c_x() {
        let mut index = Index::new();
        index.add_deps("root", (1, 0, 0), &[("a", Private, ..)]);
        index.add_deps("root", (1, 0, 0), &[("b", Private, ..)]);
        index.add_deps("a", (1, 0, 0), &[("x", Private, (1, 0, 0)..(1, 0, 1))]);
        index.add_deps("a", (1, 0, 0), &[("c", Private, ..)]);
        index.add_deps("b", (1, 0, 0), &[("x", Private, (2, 0, 0)..(2, 0, 1))]);
        index.add_deps("b", (1, 0, 0), &[("c", Private, ..)]);
        // Only c-x is public
        index.add_deps("c", (1, 0, 0), &[("x", Public, ..)]);
        index.add_deps::<R>("x", (1, 0, 0), &[]);
        index.add_deps::<R>("x", (2, 0, 0), &[]);
        let solution = resolve(&index, "root$root@1.0.0 seeded", (1, 0, 0));
        assert_map_eq(
            &solution.unwrap(),
            &select(&[
                ("root$root@1.0.0 final", (1, 0, 0)),
                ("a$root@1.0.0 final", (1, 0, 0)),
                ("b$root@1.0.0 final", (1, 0, 0)),
                ("c$a@1.0.0 final", (1, 0, 0)),
                ("c$b@1.0.0 final", (1, 0, 0)),
                ("x$a@1.0.0 final", (1, 0, 0)),
                ("x$b@1.0.0 final", (2, 0, 0)),
            ]),
        );
        // match solution {
        //     Ok(sol) => {
        //         println!("{:?}", sol);
        //         panic!("Should not have found a solution");
        //     }
        //     Err(PubGrubError::NoSolution(mut derivation_tree)) => {
        //         derivation_tree.collapse_no_versions();
        //         eprintln!("{}", DefaultStringReporter::report(&derivation_tree));
        //         panic!("Panic just to see the failure report");
        //     }
        //     Err(err) => panic!("{:?}", err),
        // };
    }
}
