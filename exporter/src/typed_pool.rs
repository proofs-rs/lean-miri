//! Compiler keys prevent equal JSON payloads from collapsing distinct identities.
//! Slots are reserved before traversal because definitions can reference themselves.
use serde_json::Value;
use std::collections::HashMap;
use std::hash::Hash;

pub(super) struct Pool<K> {
    ids: HashMap<K, usize>,
    definitions: Vec<Option<Value>>,
    keys: Vec<K>,
}

impl<K> Default for Pool<K> {
    fn default() -> Self {
        Self {
            ids: HashMap::new(),
            definitions: Vec::new(),
            keys: Vec::new(),
        }
    }
}

impl<K: Clone + Eq + Hash> Pool<K> {
    pub(super) fn reserve(&mut self, key: K) -> (usize, bool) {
        if let Some(&id) = self.ids.get(&key) {
            return (id, false);
        }
        let id = self.definitions.len();
        self.ids.insert(key.clone(), id);
        self.keys.push(key);
        self.definitions.push(None);
        (id, true)
    }

    pub(super) fn key(&self, id: usize) -> Option<&K> {
        self.keys.get(id)
    }

    pub(super) fn define(&mut self, id: usize, definition: Value) {
        let slot = self
            .definitions
            .get_mut(id)
            .expect("definition must have a reserved ID");
        assert!(slot.is_none(), "pool definition must be unique");
        *slot = Some(definition);
    }

    pub(super) fn finish(self, id_field: &str) -> Result<Vec<Value>, String> {
        self.definitions
            .into_iter()
            .enumerate()
            .map(|(id, slot)| {
                let definition =
                    slot.ok_or_else(|| format!("{id_field} {id}: unfinished pool definition"))?;
                if !definition.is_object() {
                    return Err(format!("{id_field} {id}: definition is not an object"));
                }
                Ok(definition)
            })
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;

    #[test]
    fn reserved_identity_is_available_before_definition() {
        let mut pool = Pool::default();
        let (id, fresh) = pool.reserve("recursive");
        assert!(fresh);
        assert_eq!(pool.reserve("recursive"), (id, false));
        pool.define(id, json!({"next": id}));
        assert_eq!(pool.finish("test_id").unwrap(), vec![json!({"next": 0})]);
    }

    #[test]
    fn equal_payload_does_not_merge_distinct_semantic_keys() {
        let mut pool = Pool::default();
        let (first, _) = pool.reserve(1);
        let (second, _) = pool.reserve(2);
        pool.define(first, json!({"bytes": []}));
        pool.define(second, json!({"bytes": []}));
        assert_ne!(first, second);
        assert_eq!(pool.finish("allocation_id").unwrap().len(), 2);
    }

    #[test]
    fn unfinished_definitions_fail_export() {
        let mut pool = Pool::default();
        pool.reserve("missing");
        assert!(pool.finish("test_id").unwrap_err().contains("unfinished"));
    }
}
