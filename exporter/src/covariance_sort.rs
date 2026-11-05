//! Cache only ordering keys, never compiler relation answers or demand sets.
use std::collections::HashMap;
use std::hash::Hash;
use std::sync::Arc;

pub(super) struct Cache<T> {
    keys: HashMap<T, Arc<str>>,
    ranks: HashMap<(T, T), usize>,
}
impl<T> Default for Cache<T> {
    fn default() -> Self {
        Self {
            keys: HashMap::new(),
            ranks: HashMap::new(),
        }
    }
}
impl<T: Copy + Eq + Hash> Cache<T> {
    /// With render keys fixed for this cache lifetime, exactly the stable order
    /// of sorting by `(render(source), render(target))`.
    /// Equal textual keys share a rank: distinct types with identical debug text
    /// must retain input order, including the old adjacent-dedup behavior.
    /// Returns true when the previous key order suffices for the current domain.
    pub(super) fn sort(
        &mut self,
        pairs: &mut [(T, T)],
        mut render: impl FnMut(T) -> String,
    ) -> bool {
        if pairs.iter().all(|pair| self.ranks.contains_key(pair)) {
            pairs.sort_by_cached_key(|pair| self.ranks[pair]);
            return true;
        }
        for &(source, target) in pairs.iter() {
            for ty in [source, target] {
                self.keys.entry(ty).or_insert_with(|| render(ty).into());
            }
        }
        let key =
            |(source, target): &(T, T)| (self.keys[source].clone(), self.keys[target].clone());
        pairs.sort_by_cached_key(key);
        // A newly inserted key changes ranks. Replace the whole rank domain;
        // do not retain stale ranks for pairs absent from this round.
        self.ranks.clear();
        let mut previous = None;
        let mut rank = 0;
        for &pair in pairs.iter() {
            let current = key(&pair);
            if previous.as_ref().is_some_and(|old| old != &current) {
                rank += 1;
            }
            self.ranks.insert(pair, rank);
            previous = Some(current);
        }
        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn stable_ties_duplicates_and_changing_domains_match_legacy_order() {
        let render = |ty: u32| format!("key-{}", ty % 5);
        let mut cache = Cache::default();
        let mut seed = 7u64;
        for wave in 0..100 {
            let mut pairs = Vec::new();
            for _ in 0..80 {
                seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1);
                let pair = (
                    ((seed >> 32) as u32) % (wave % 17 + 1),
                    ((seed >> 16) as u32) % 13,
                );
                pairs.extend([pair, pair]);
            }
            let mut expected = pairs.clone();
            expected.sort_by_key(|&(a, b)| (render(a), render(b)));
            cache.sort(&mut pairs, render);
            assert_eq!(pairs, expected);
            pairs.dedup();
            expected.dedup();
            assert_eq!(pairs, expected);
        }
    }

    #[test]
    fn keys_are_rendered_once_and_rank_reuse_handles_subsets_and_insertions() {
        let mut cache = Cache::default();
        let mut calls = 0;
        let mut render = |ty| {
            calls += 1;
            format!("{ty:04}")
        };
        assert!(!cache.sort(&mut [(9, 3), (3, 9)], &mut render));
        assert!(cache.sort(&mut [(3, 9)], &mut render));
        assert!(!cache.sort(&mut [(3, 9), (1, 3)], &mut render));
        assert!(cache.sort(&mut [(3, 9), (1, 3)], &mut render));
        // The pair omitted during the last rebuild has no stale rank.
        let mut pairs = [(9, 3), (1, 3), (3, 9)];
        assert!(!cache.sort(&mut pairs, &mut render));
        assert_eq!(pairs, [(1, 3), (3, 9), (9, 3)]);
        assert_eq!(calls, 3);
    }
}
