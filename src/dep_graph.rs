// Alex Ozdemir <aozdemir@hmc.edu>
//
// Holds a keyed dependency graph which supports 3 operations:
// insert(key,dependent,dependency)
// get_dependents(dependency)
// remove(key,dependent)

use std::collections::{self, HashSet, HashMap};
use std::hash::Hash;

pub struct KeyedDepGraph<K,N> {
    map: HashMap<N,HashMap<N,HashSet<K>>>,
}

impl<K,N> KeyedDepGraph<K,N> where K: Eq + Hash , N: Hash + Eq {
    /// Create a graph with no registered dependencies
    pub fn new() -> KeyedDepGraph<K,N> {
        KeyedDepGraph {
            map: HashMap::new(),
        }
    }

    /// Register a dependency with a key
    pub fn insert(&mut self, key: K, dependent: N, dependency: N) {
        self.map.entry(dependency).or_insert_with(HashMap::new)
                .entry(dependent).or_insert_with(HashSet::new).insert(key);
    }

    /// Remove the dependency of `dependent` on _ with key `key`
    pub fn remove(&mut self, key: &K, dependent: &N) {
        self.map.iter_mut().map(|(_,m)| {
            if m.get(dependent).map(|m| m.contains(key)).unwrap_or(false) {
                m.get_mut(dependent).unwrap().remove(key);
                if m.get(dependent).unwrap().len() == 0 {
                    m.remove(dependent);
                }
            }
        }).count();
    }

    /// Produce an iterator of the dependents of `dependency`
    pub fn get_dependents<'a>(&'a mut self, dependency: N) -> collections::hash_map::Keys<'a, N, collections::HashSet<K>> {
        self.map.entry(dependency).or_insert_with(HashMap::new).keys()
    }
}
