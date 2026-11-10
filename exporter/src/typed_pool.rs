//! Compiler keys prevent equal payloads from collapsing distinct identities.
//! Definitions retain their semantic Rust type until the document is serialized.
//! Slots are reserved before traversal because definitions can reference themselves.
use std::collections::HashMap;
use std::hash::Hash;

pub(super) struct Pool<K, D> {
    ids: HashMap<K, u64>,
    definitions: Vec<Option<D>>,
    keys: Vec<K>,
    defined_count: usize,
}

impl<K, D> Default for Pool<K, D> {
    fn default() -> Self {
        Self {
            ids: HashMap::new(),
            definitions: Vec::new(),
            keys: Vec::new(),
            defined_count: 0,
        }
    }
}

impl<K: Clone + Eq + Hash, D> Pool<K, D> {
    pub(super) fn get(&self, key: &K) -> Option<&u64> {
        self.ids.get(key)
    }
    pub(super) fn keys(&self) -> impl Iterator<Item = &K> {
        self.keys.iter()
    }
    pub(super) fn values(&self) -> impl Iterator<Item = &u64> {
        self.ids.values()
    }
    pub(super) fn iter(&self) -> impl Iterator<Item = (&K, &u64)> {
        self.keys.iter().map(|key| (key, &self.ids[key]))
    }
    pub(super) fn len(&self) -> usize {
        self.keys.len()
    }
    pub(super) fn defined_len(&self) -> usize {
        self.defined_count
    }
    pub(super) fn definition(&self, id: u64) -> Option<&D> {
        self.definitions.get(id as usize)?.as_ref()
    }
    pub(super) fn reserve(&mut self, key: K) -> (usize, bool) {
        if let Some(&id) = self.ids.get(&key) {
            return (id as usize, false);
        }
        let id = self.definitions.len();
        self.ids.insert(key.clone(), id as u64);
        self.keys.push(key);
        self.definitions.push(None);
        (id, true)
    }

    pub(super) fn key(&self, id: usize) -> Option<&K> {
        self.keys.get(id)
    }

    pub(super) fn define(&mut self, id: usize, definition: D) {
        let slot = self
            .definitions
            .get_mut(id)
            .expect("definition must have a reserved ID");
        assert!(slot.is_none(), "pool definition must be unique");
        *slot = Some(definition);
        self.defined_count += 1;
    }

    pub(super) fn finish(self, id_field: &str) -> Result<Vec<D>, String> {
        self.definitions
            .into_iter()
            .enumerate()
            .map(|(id, slot)| {
                let definition =
                    slot.ok_or_else(|| format!("{id_field} {id}: unfinished pool definition"))?;
                Ok(definition)
            })
            .collect()
    }
}

impl<K: Eq + Hash, D> std::ops::Index<&K> for Pool<K, D> {
    type Output = u64;
    fn index(&self, key: &K) -> &u64 {
        &self.ids[key]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn reserved_identity_is_available_before_definition() {
        let mut pool = Pool::default();
        let (id, fresh) = pool.reserve("recursive");
        assert!(fresh);
        assert_eq!(pool.definition(id as u64), None);
        assert_eq!(pool.defined_len(), 0);
        assert_eq!(pool.reserve("recursive"), (id, false));
        assert_eq!(pool.get(&"recursive"), Some(&(id as u64)));
        assert_eq!(pool.key(id), Some(&"recursive"));
        pool.define(id, id);
        assert_eq!(pool.defined_len(), 1);
        assert_eq!(pool.finish("test_id").unwrap(), vec![0]);
    }

    #[test]
    fn equal_payload_does_not_merge_distinct_semantic_keys() {
        let mut pool = Pool::default();
        let (first, _) = pool.reserve(1);
        let (second, _) = pool.reserve(2);
        pool.define(first, Vec::<u8>::new());
        pool.define(second, Vec::<u8>::new());
        assert_ne!(first, second);
        assert_eq!(pool.finish("allocation_id").unwrap().len(), 2);
    }

    #[test]
    fn enumeration_preserves_first_discovery_order() {
        let mut pool: Pool<_, ()> = Pool::default();
        for key in [9, 2, 7, 2] {
            pool.reserve(key);
        }
        assert_eq!(pool.keys().copied().collect::<Vec<_>>(), vec![9, 2, 7]);
        assert_eq!(
            pool.iter().map(|(key, id)| (*key, *id)).collect::<Vec<_>>(),
            vec![(9, 0), (2, 1), (7, 2)]
        );
        let mut requests = super::OrderedSet::default();
        requests.extend([9, 2, 7, 2]);
        assert!(!requests.insert(9));
        assert_eq!(requests.get_index(1), Some(&2));
        assert_eq!(requests.suffix(2), &[7]);
        assert!(requests.contains(&9));
        assert_eq!(requests.into_iter().collect::<Vec<_>>(), vec![9, 2, 7]);
    }

    #[test]
    fn unfinished_definitions_fail_export() {
        let mut pool: Pool<_, ()> = Pool::default();
        pool.reserve("missing");
        assert!(pool.finish("test_id").unwrap_err().contains("unfinished"));
    }
    #[test]
    fn completion_preserves_reservation_order_and_typed_fields() {
        #[derive(Debug, PartialEq)]
        struct Definition {
            bytes: Vec<u8>,
            next: Option<usize>,
        }
        let mut pool = Pool::default();
        let (first, _) = pool.reserve("first");
        let (second, _) = pool.reserve("second");
        pool.define(
            second,
            Definition {
                bytes: vec![2],
                next: Some(first),
            },
        );
        pool.define(
            first,
            Definition {
                bytes: vec![1],
                next: Some(second),
            },
        );
        assert_eq!(pool.key(first), Some(&"first"));
        assert_eq!(pool.definition(second as u64).unwrap().next, Some(first));
        assert_eq!(
            pool.finish("node").unwrap(),
            vec![
                Definition {
                    bytes: vec![1],
                    next: Some(second)
                },
                Definition {
                    bytes: vec![2],
                    next: Some(first)
                },
            ]
        );
    }

    #[test]
    #[should_panic(expected = "pool definition must be unique")]
    fn duplicate_definitions_fail() {
        let mut pool = Pool::default();
        let (id, _) = pool.reserve("duplicate");
        pool.define(id, ());
        pool.define(id, ());
    }

    #[test]
    #[should_panic(expected = "definition must have a reserved ID")]
    fn unreserved_definitions_fail() {
        let mut pool: Pool<&str, ()> = Pool::default();
        pool.define(0, ());
    }
}

/// Deduplicated requests in deterministic first-discovery order. Unlike pool
/// reservation, insertion here assigns no serialized identity.
#[derive(Clone)]
pub(super) struct OrderedSet<K> {
    seen: std::collections::HashMap<K, usize>,
    order: Vec<K>,
}
impl<K> Default for OrderedSet<K> {
    fn default() -> Self {
        Self {
            seen: Default::default(),
            order: Vec::new(),
        }
    }
}
impl<K: Clone + Eq + Hash> OrderedSet<K> {
    pub(super) fn insert(&mut self, key: K) -> bool {
        if self.seen.contains_key(&key) {
            return false;
        }
        self.seen.insert(key.clone(), self.order.len());
        self.order.push(key);
        true
    }
    pub(super) fn contains(&self, key: &K) -> bool { self.seen.contains_key(key) }
    pub(super) fn get_index(&self, index: usize) -> Option<&K> { self.order.get(index) }
    pub(super) fn suffix(&self, cursor: usize) -> &[K] { &self.order[cursor..] }
    pub(super) fn iter(&self) -> std::slice::Iter<'_, K> {
        self.order.iter()
    }
    pub(super) fn len(&self) -> usize {
        self.order.len()
    }
    pub(super) fn extend(&mut self, keys: impl IntoIterator<Item = K>) {
        for key in keys {
            self.insert(key);
        }
    }
}
impl<K> IntoIterator for OrderedSet<K> {
    type Item = K;
    type IntoIter = std::vec::IntoIter<K>;
    fn into_iter(self) -> Self::IntoIter {
        self.order.into_iter()
    }
}
