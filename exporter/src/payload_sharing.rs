//! Online hash-consing of exporter values. Constructors retain immutable
//! semantic DAG handles; wire nodes contain only scalar data and child IDs.
//! Serialization never rebuilds or shares a completed expanded document.

use crate::payload_value::{Plain, Value};
use serde::{Serialize, Serializer};
use serde_json::{json as raw_json, Value as Raw};
use std::cell::RefCell;
use std::collections::{HashMap, HashSet};

const REF: &str = "$lean_miri_shared_ref";
const CATALOG: &str = "shared_payloads";

#[derive(Default)]
pub(crate) struct Pool {
    nodes: Vec<Value>,
    edges: Vec<Vec<usize>>,
    keys: HashMap<String, usize>,
    identities: HashMap<(u8, usize), usize>,
    inline: HashMap<String, Value>,
    invalid: Option<String>,
}
thread_local! { static POOL: RefCell<Pool> = RefCell::new(Pool::default()); }

pub(crate) fn take_pool() -> Pool {
    POOL.with(|pool| std::mem::take(&mut *pool.borrow_mut()))
}
pub(crate) fn install_pool(value: Pool) {
    POOL.with(|pool| *pool.borrow_mut() = value);
}

pub(crate) fn begin_export() {
    POOL.with(|pool| *pool.borrow_mut() = Pool::default());
}

fn fixed_string(field: Option<&str>) -> bool {
    matches!(
        field,
        Some(
            "kind"
                | "status"
                | "variant"
                | "operator"
                | "mode"
                | "abi"
                | "category"
                | "schema"
                | "rustc_commit"
                | "miri_commit"
                | "rustc_version"
                | "compiler_version"
        )
    )
}
fn eligible(value: &Value, field: Option<&str>) -> bool {
    match value {
        Value::String(_) => !fixed_string(field),
        Value::Array(values) => !values.is_empty(),
        Value::Object(fields) => {
            if fields.len() == 2
                && fields.get("line").and_then(Value::as_u64).is_some()
                && fields.get("column").and_then(Value::as_u64).is_some()
            {
                return false;
            }
            fields.len() >= 4
                || fields.iter().any(|(key, child)| match child {
                    Value::Array(values) => !values.is_empty(),
                    Value::String(_) => !fixed_string(Some(key)),
                    Value::Object(_) => eligible(child, None),
                    _ => false,
                })
        }
        _ => false,
    }
}
fn reference(id: usize) -> Raw {
    raw_json!({REF: id})
}

fn collect_refs(value: &Raw, result: &mut Vec<usize>) {
    match value {
        Raw::Object(fields) => {
            if fields.len() == 1 {
                if let Some(id) = fields.get(REF).and_then(Raw::as_u64) {
                    result.push(id as usize);
                    return;
                }
            }
            for value in fields.values() {
                collect_refs(value, result);
            }
        }
        Raw::Array(values) => {
            for value in values {
                collect_refs(value, result);
            }
        }
        _ => (),
    }
}

// No RefCell borrow is held while constructing a node's child references.
fn payload(value: &Value) -> Raw {
    match value {
        Value::Null => Raw::Null,
        Value::Bool(value) => Raw::Bool(*value),
        Value::Number(value) => Raw::Number(value.clone()),
        Value::String(value) => Raw::String(value.to_string()),
        Value::Array(values) => Raw::Array(values.iter().map(|v| wire(v, None)).collect()),
        Value::Object(fields) => Raw::Object(
            fields
                .iter()
                .map(|(key, value)| (key.clone(), wire(value, Some(key))))
                .collect(),
        ),
    }
}
fn intern(value: &Value) -> usize {
    let identity = value
        .identity()
        .expect("only containers/strings are interned");
    if let Some(id) = POOL.with(|pool| pool.borrow().identities.get(&identity).copied()) {
        return id;
    }
    let encoded = payload(value);
    let key = encoded.to_string();
    let mut edges = Vec::new();
    collect_refs(&encoded, &mut edges);
    POOL.with(|pool| {
        let mut pool = pool.borrow_mut();
        if let Some(id) = pool.keys.get(&key) {
            return *id;
        }
        let id = pool.nodes.len();
        assert!(edges.iter().all(|child| *child < id));
        pool.nodes.push(value.clone());
        pool.edges.push(edges);
        pool.keys.insert(key, id);
        // Only canonical nodes are memoized by address. The pool owns them,
        // so these addresses cannot be freed/reused while the map is live.
        pool.identities.insert(identity, id);
        id
    })
}
fn wire(value: &Value, field: Option<&str>) -> Raw {
    if eligible(value, field) {
        reference(intern(value))
    } else {
        payload(value)
    }
}

pub(crate) fn canonicalize(value: Value) -> Value {
    if let Some(fields) = value.as_object() {
        if fields.contains_key(REF) || fields.contains_key(CATALOG) {
            POOL.with(|pool| {
                pool.borrow_mut().invalid =
                    Some("export payload contains reserved shared-graph fields".into())
            });
            return value;
        }
    }
    if eligible(&value, None) {
        return lookup_node(intern(&value)).expect("newly interned node exists");
    }
    if value.identity().is_none() {
        return value;
    }
    // Tiny inline records (e.g. type_id and source positions) share semantic
    // storage too, without increasing the wire representation size.
    let key = payload(&value).to_string();
    POOL.with(|pool| pool.borrow_mut().inline.entry(key).or_insert(value).clone())
}
pub(crate) fn lookup_node(id: usize) -> Option<Value> {
    POOL.with(|pool| pool.borrow().nodes.get(id).cloned())
}
pub(crate) fn serialize_value<S: Serializer>(
    value: &Value,
    serializer: S,
) -> Result<S::Ok, S::Error> {
    wire(value, None).serialize(serializer)
}

/// A frozen wire snapshot. Reachability works on the already-interned ID
/// graph, never on an expanded JSON tree; dead temporary snapshots become
/// null slots, keeping all construction-time IDs stable and backward-only.
pub(crate) struct Document {
    root: Raw,
}
impl Document {
    pub(crate) fn new(value: &Value) -> Result<Self, String> {
        if let Some(error) = POOL.with(|pool| pool.borrow().invalid.clone()) {
            return Err(error);
        }
        let fields = value
            .as_object()
            .ok_or("export document must be an object")?;
        if fields.contains_key(CATALOG) {
            return Err("document already contains shared_payloads".into());
        }
        let mut root = serde_json::Map::new();
        for (key, value) in fields {
            // Candidate IDs are an independent, directly indexed kind table.
            // Its slots stay opaque to the general graph decoder.
            let value = if key == "compiler_virtual_candidates" {
                serde_json::to_value(Plain(value)).map_err(|e| e.to_string())?
            } else {
                wire(value, Some(key))
            };
            root.insert(key.clone(), value);
        }
        let (nodes, edges) = POOL.with(|pool| {
            let pool = pool.borrow();
            (pool.nodes.clone(), pool.edges.clone())
        });
        let mut pending = Vec::new();
        for value in root.values() {
            collect_refs(value, &mut pending);
        }
        let mut alive = HashSet::new();
        while let Some(id) = pending.pop() {
            if id >= nodes.len() {
                return Err("exporter generated an invalid payload reference".into());
            }
            if alive.insert(id) {
                pending.extend(edges[id].iter().copied());
            }
        }
        let length = alive.iter().copied().max().map_or(0, |id| id + 1);
        let encoded = (0..length)
            .map(|id| {
                if alive.contains(&id) {
                    payload(&nodes[id])
                } else {
                    Raw::Null
                }
            })
            .collect::<Vec<_>>();
        root.insert(
            CATALOG.into(),
            raw_json!({"schema_version":2,"nodes":encoded}),
        );
        Ok(Self {
            root: Raw::Object(root),
        })
    }
}
impl Serialize for Document {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        self.root.serialize(serializer)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::payload_value::json;
    fn resolve(value: &Raw, nodes: &[Raw]) -> Raw {
        if let Some(id) = value
            .as_object()
            .filter(|m| m.len() == 1)
            .and_then(|m| m.get(REF))
            .and_then(Raw::as_u64)
        {
            return resolve(&nodes[id as usize], nodes);
        }
        match value {
            Raw::Array(values) => Raw::Array(values.iter().map(|v| resolve(v, nodes)).collect()),
            Raw::Object(fields) => Raw::Object(
                fields
                    .iter()
                    .map(|(k, v)| (k.clone(), resolve(v, nodes)))
                    .collect(),
            ),
            _ => value.clone(),
        }
    }
    #[test]
    fn collection_deduplicates_before_document_exists() {
        begin_export();
        let first = json!({"payload":[1,2,3],"name":"shared"});
        let second = json!({"payload":[1,2,3],"name":"shared"});
        assert_eq!(first.identity(), second.identity());
        let root = json!({"first":first,"second":second});
        let document = Document::new(&root).unwrap();
        let mut raw = serde_json::to_value(document).unwrap();
        let nodes = raw.as_object_mut().unwrap().remove(CATALOG).unwrap()["nodes"]
            .as_array()
            .unwrap()
            .clone();
        assert_eq!(
            resolve(&raw, &nodes),
            serde_json::to_value(Plain(&root)).unwrap()
        );
        for (id, node) in nodes.iter().enumerate() {
            let mut refs = Vec::new();
            collect_refs(node, &mut refs);
            assert!(refs.iter().all(|child| *child < id));
        }
    }
    #[test]
    fn cow_changes_one_occurrence_and_does_not_serialize_dead_snapshots() {
        begin_export();
        let original = json!({"payload":[1,2,3],"name":"original"});
        let mut changed = original.clone();
        changed["name"] = json!("changed");
        let root = json!({"left":original,"right":changed});
        let first = serde_json::to_vec(&Document::new(&root).unwrap()).unwrap();
        let _unrelated = json!({"unused":["a","b"]});
        assert_eq!(
            first,
            serde_json::to_vec(&Document::new(&root).unwrap()).unwrap()
        );
        assert_eq!(root["left"]["name"].as_str(), Some("original"));
        assert_eq!(root["right"]["name"].as_str(), Some("changed"));
    }
    #[test]
    fn semantic_scalar_records_share_storage_while_remaining_inline() {
        begin_export();
        let first = json!({"type_id":7});
        let second = json!({"type_id":7});
        assert_eq!(first.identity(), second.identity());
        assert_eq!(wire(&first, None), raw_json!({"type_id":7}));
    }

    #[test]
    fn pool_transfer_preserves_ids_and_frozen_documents_survive_release() {
        begin_export();
        let child = json!({"payload": [1, 2, 3], "name": "transferred"});
        let root = json!({"left": child.clone(), "right": child.clone()});
        let id = wire(&child, None)[REF].as_u64().unwrap() as usize;
        let identity = child.identity();
        let expected = serde_json::to_value(Plain(&root)).unwrap();
        let frozen = Document::new(&root).unwrap();
        let before = serde_json::to_vec(&frozen).unwrap();
        let pool = take_pool();
        assert!(lookup_node(id).is_none());
        std::thread::spawn(move || {
            install_pool(pool);
            assert_eq!(lookup_node(id).unwrap().identity(), identity);
            assert_eq!(wire(&child, None)[REF], raw_json!(id));
            assert_eq!(
                serde_json::to_vec(&Document::new(&root).unwrap()).unwrap(),
                before
            );
            // The Miri-reference path releases the semantic pool after freezing
            // the source snapshot; serialized snapshots remain self-contained.
            begin_export();
            assert_eq!(serde_json::to_vec(&frozen).unwrap(), before);
            // A live sidecar/semantic value can be serialized in a fresh pool.
            let mut rebuilt = serde_json::to_value(Document::new(&root).unwrap()).unwrap();
            let catalog = rebuilt.as_object_mut().unwrap().remove(CATALOG).unwrap();
            let nodes = catalog["nodes"].as_array().unwrap();
            assert_eq!(resolve(&rebuilt, nodes), expected);
        })
        .join()
        .unwrap();
    }

    #[test]
    fn reserved_payload_fields_cannot_become_a_successful_export() {
        for key in [REF, CATALOG] {
            begin_export();
            let malformed = Value::from_raw(raw_json!({key: 7}));
            let error = match Document::new(&malformed) {
                Ok(_) => panic!("reserved source payload field was accepted"),
                Err(error) => error,
            };
            assert!(error.contains("reserved"));
        }
    }
}
