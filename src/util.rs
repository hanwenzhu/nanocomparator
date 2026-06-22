use rustc_hash::FxHasher;
use std::collections::HashSet;
use std::hash::BuildHasherDefault;

pub(crate) type FxHashSet<K> = HashSet<K, BuildHasherDefault<FxHasher>>;
pub(crate) fn new_fx_hash_set<K>() -> FxHashSet<K> {
    FxHashSet::with_hasher(Default::default())
}
