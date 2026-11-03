//! Generic bottom-up JSON DAG encoding for large repeated exporter payloads.
//!
//! This is a final wire transform. It does not change compiler query demand
//! or ordering. Eligible values are represented by numeric
//! references into `shared_payloads.nodes`; nodes are emitted after their
//! children, so every reference in a node points to a lower numbered node.

use crate::{JsonMap as Map, Value, json};
use std::collections::HashMap;

const SHARED_CATALOG_FIELD: &str = "shared_payloads";
const SHARED_REF_FIELD: &str = "$lean_miri_shared_ref";
const SCHEMA_VERSION: u64 = 2;

fn contains_reference_marker(value: &Value) -> bool {
    value
        .as_object()
        .is_some_and(|object| object.contains_key(SHARED_REF_FIELD))
}

fn is_position_container(object: &Map<String, Value>) -> bool {
    object.len() == 2
        && object.get("line").and_then(Value::as_u64).is_some()
        && object.get("column").and_then(Value::as_u64).is_some()
}

fn is_fixed_leaf_string_field(field: Option<&str>) -> bool {
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

/// Encode payload strings by their field role, regardless of today's length.
/// Only fixed enum/tag fields and root schema/pin metadata stay inline.
fn eligible(value: &Value, field: Option<&str>) -> bool {
    match value {
        Value::String(_) => !is_fixed_leaf_string_field(field),
        Value::Array(values) => !values.is_empty(),
        Value::Object(object) => {
            !is_position_container(object)
                && (object.len() >= 4
                    || object
                        .values()
                        .any(|child| matches!(child, Value::Array(values) if !values.is_empty()))
                    || object.iter().any(|(key, child)| match child {
                        Value::String(_) => !is_fixed_leaf_string_field(Some(key)),
                        Value::Object(_) => eligible(child, None),
                        _ => false,
                    }))
        }
        _ => false,
    }
}

fn reference(index: usize) -> Value {
    json!({SHARED_REF_FIELD: index})
}

#[derive(Default)]
struct Encoder {
    nodes: Vec<Value>,
    #[cfg(feature = "legacy-json")]
    indices: HashMap<String, usize>,
    #[cfg(not(feature = "legacy-json"))]
    indices: HashMap<WireKey, usize>,
    #[cfg(not(feature = "legacy-json"))]
    source_nodes: HashMap<(u8, usize, bool), (Value, Value, u8)>,
    scan_flags: Vec<u8>,
}

/// Exact canonical wire equality, including numeric spelling (notably -0.0).
/// Hash collisions always fall through to full equality; hashes are not IDs.
#[cfg(not(feature = "legacy-json"))]
#[derive(Clone)]
struct WireKey(Value);
#[cfg(not(feature = "legacy-json"))]
impl PartialEq for WireKey {
    fn eq(&self, other: &Self) -> bool {
        fn eq(a: &Value, b: &Value) -> bool {
            match (a, b) {
                (Value::Null, Value::Null) => true,
                (Value::Bool(a), Value::Bool(b)) => a == b,
                (Value::Number(a), Value::Number(b)) => a.to_string() == b.to_string(),
                (Value::String(a), Value::String(b)) => a == b,
                (Value::Array(a), Value::Array(b)) => {
                    a.len() == b.len() && a.iter().zip(b.iter()).all(|(a, b)| eq(a, b))
                }
                (Value::Object(a), Value::Object(b)) => {
                    a.len() == b.len()
                        && a.iter()
                            .zip(b.iter())
                            .all(|((ka, a), (kb, b))| ka == kb && eq(a, b))
                }
                _ => false,
            }
        }
        eq(&self.0, &other.0)
    }
}
#[cfg(not(feature = "legacy-json"))]
impl Eq for WireKey {}
#[cfg(not(feature = "legacy-json"))]
impl std::hash::Hash for WireKey {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        fn walk<H: std::hash::Hasher>(value: &Value, state: &mut H) {
            std::mem::discriminant(value).hash(state);
            match value {
                Value::Null => (),
                Value::Bool(v) => v.hash(state),
                Value::Number(v) => v.to_string().hash(state),
                Value::String(v) => v.as_str().hash(state),
                Value::Array(v) => {
                    v.len().hash(state);
                    for child in v.iter() {
                        walk(child, state);
                    }
                }
                Value::Object(v) => {
                    v.len().hash(state);
                    for (key, child) in v.iter() {
                        key.hash(state);
                        walk(child, state);
                    }
                }
            }
        }
        walk(&self.0, state);
    }
}

fn field_interest(name: &str) -> u8 {
    match name {
        "type_id" | "allocation_id" | "instance_id" => 1,
        "locals" | "basic_blocks" => 2,
        "fn_abi" | "calling_convention" => 4,
        "vtable_allocation" => 8,
        _ => 0,
    }
}

impl Encoder {
    fn encode_value(&mut self, value: &mut Value, field: Option<&str>) -> Result<u8, String> {
        if contains_reference_marker(value) {
            return Err(format!(
                "input contains reserved `{SHARED_REF_FIELD}` reference shape"
            ));
        }

        // Eligibility must be based on the source shape. Replacing a child
        // array with a reference can otherwise make its containing record look
        // small by the time its own post-order visit finishes.
        let should_intern = eligible(value, field);
        #[cfg(not(feature = "legacy-json"))]
        {
            let identity = value
                .identity()
                .filter(|_| value.is_shared())
                .map(|(tag, ptr)| (tag, ptr, should_intern));
            if let Some(identity) = identity {
                if let Some((_, encoded, interests)) = self.source_nodes.get(&identity) {
                    *value = encoded.clone();
                    return Ok(*interests);
                }
            }
            // Retaining the immutable source prevents address reuse and makes
            // subsequent mutations COW. This is a per-document traversal memo.
            let original = identity.map(|_| value.clone());
            let interests = self.encode_unique(value, field, should_intern)?;
            if let Some(identity) = identity {
                self.source_nodes
                    .insert(identity, (original.unwrap(), value.clone(), interests));
            }
            return Ok(interests);
        }
        #[cfg(feature = "legacy-json")]
        self.encode_unique(value, field, should_intern)
    }

    fn encode_unique(
        &mut self,
        value: &mut Value,
        _field: Option<&str>,
        should_intern: bool,
    ) -> Result<u8, String> {
        let mut interests = 0;

        match value {
            Value::Array(values) => {
                for child in values {
                    interests |= self.encode_value(child, None)?;
                }
            }
            Value::Object(object) => {
                for (key, child) in object.iter_mut() {
                    interests |= field_interest(key) | self.encode_value(child, Some(key))?;
                }
            }
            _ => {}
        }

        if !should_intern {
            return Ok(interests);
        }

        // Both representations have ordered object keys. Exact wire equality,
        // including numeric spelling, resolves all structural hash collisions.
        #[cfg(feature = "legacy-json")]
        let key = value.to_string();
        #[cfg(not(feature = "legacy-json"))]
        let key = WireKey(value.clone());
        if let Some(index) = self.indices.get(&key) {
            *value = reference(*index);
            return Ok(self.scan_flags[*index]);
        }

        let index = self.nodes.len();
        self.nodes.push(std::mem::replace(value, Value::Null));
        self.indices.insert(key, index);
        self.scan_flags.push(interests);
        *value = reference(index);
        Ok(interests)
    }
}

/// Encode eligible values as a bottom-up DAG while preserving root fields.
///
/// The transform is deterministic and exact: ordered structural wire values
/// are the interning keys, and references point to nodes with lower ids.
pub(crate) fn share_payloads(document: &mut Value) -> Result<(), String> {
    share_payloads_with_scan_flags(document, false)
}

/// Optional checked traversal summaries, using the same node IDs and payloads.
pub(crate) fn share_payloads_with_scan_flags(
    document: &mut Value,
    prepared: bool,
) -> Result<(), String> {
    let Some(root) = document.as_object() else {
        return Err("shared payload exporter expected a JSON object root".into());
    };
    if root.contains_key(SHARED_CATALOG_FIELD) {
        return Err(format!(
            "input already contains reserved `{SHARED_CATALOG_FIELD}` field"
        ));
    }

    let mut encoder = Encoder::default();
    let root = document.as_object_mut().expect("root was checked above");
    for (key, child) in root.iter_mut() {
        encoder.encode_value(child, Some(key))?;
    }

    let nodes = std::mem::take(&mut encoder.nodes);
    let scan_flags = std::mem::take(&mut encoder.scan_flags);
    // Release raw construction nodes and intern keys before writing. The final
    // graph owns its rows; inserting them does not serialize or clone them.
    drop(encoder);
    let mut catalog_fields = Map::new();
    catalog_fields.insert("schema_version".into(), json!(SCHEMA_VERSION));
    catalog_fields.insert("nodes".into(), Value::Array(nodes.into()));
    let mut catalog = Value::Object(catalog_fields.into());
    if prepared {
        catalog["scan_flags"] = json!(scan_flags);
    }
    root.insert(SHARED_CATALOG_FIELD.into(), catalog);
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[cfg(not(feature = "legacy-json"))]
    fn old_wire(mut document: serde_json::Value) -> serde_json::Value {
        use serde_json::Value as V;
        fn eligible(v: &V, field: Option<&str>) -> bool {
            match v {
                V::String(_) => !is_fixed_leaf_string_field(field),
                V::Array(v) => !v.is_empty(),
                V::Object(v) => {
                    !(v.len() == 2
                        && v.get("line").and_then(V::as_u64).is_some()
                        && v.get("column").and_then(V::as_u64).is_some())
                        && (v.len() >= 4
                            || v.values().any(|x| matches!(x,V::Array(a) if !a.is_empty()))
                            || v.iter().any(|(k, x)| match x {
                                V::String(_) => !is_fixed_leaf_string_field(Some(k)),
                                V::Object(_) => eligible(x, None),
                                _ => false,
                            }))
                }
                _ => false,
            }
        }
        fn encode(
            v: &mut V,
            field: Option<&str>,
            nodes: &mut Vec<V>,
            keys: &mut HashMap<String, usize>,
        ) {
            let share = eligible(v, field);
            match v {
                V::Array(a) => {
                    for x in a {
                        encode(x, None, nodes, keys)
                    }
                }
                V::Object(o) => {
                    for (k, x) in o {
                        encode(x, Some(k), nodes, keys)
                    }
                }
                _ => (),
            }
            if share {
                let key = v.to_string();
                let id = if let Some(id) = keys.get(&key) {
                    *id
                } else {
                    let id = nodes.len();
                    nodes.push(std::mem::take(v));
                    keys.insert(key, id);
                    id
                };
                *v = serde_json::json!({SHARED_REF_FIELD:id});
            }
        }
        let mut nodes = Vec::new();
        let mut keys = HashMap::new();
        for (k, v) in document.as_object_mut().unwrap() {
            encode(v, Some(k), &mut nodes, &mut keys);
        }
        document[SHARED_CATALOG_FIELD] = serde_json::json!({"schema_version":2,"nodes":nodes});
        document
    }

    #[cfg(not(feature = "legacy-json"))]
    #[test]
    fn shared_builder_and_encoder_preserve_exact_legacy_wire() {
        fn sample(seed: u64, depth: usize) -> serde_json::Value {
            if depth == 0 {
                return match seed % 5 {
                    0 => serde_json::Value::Null,
                    1 => serde_json::json!(seed % 2 == 0),
                    2 => serde_json::json!(seed),
                    3 => serde_json::json!(format!("unicode-λ-\\-\"-{seed}")),
                    _ => serde_json::json!(-0.0),
                };
            }
            let a = sample(seed.wrapping_mul(17).wrapping_add(1), depth - 1);
            let b = sample(seed.wrapping_mul(31).wrapping_add(2), depth - 1);
            if seed % 2 == 0 {
                serde_json::json!([a, b, a])
            } else {
                serde_json::json!({"kind":"tag","left":a,"right":b,"again":a})
            }
        }
        for seed in 0..64 {
            let original =
                serde_json::json!({"root":sample(seed,4),"position":{"line":1,"column":2}});
            let expected = old_wire(original.clone());
            let mut graph = Value::from(original);
            share_payloads(&mut graph).unwrap();
            assert_eq!(
                serde_json::to_vec(&graph).unwrap(),
                serde_json::to_vec(&expected).unwrap()
            );
        }
        let scalar = json!("shared-role");
        let mut graph = json!({"kind":scalar,"payload":scalar,"again":scalar,
            "zeros":[[0.0],[-0.0]],"identities":[{"kind":"function","id":17,"name":"a","salt":1},
            {"kind":"function","id":18,"name":"a","salt":1}]});
        let expected = old_wire(serde_json::to_value(&graph).unwrap());
        share_payloads(&mut graph).unwrap();
        assert_eq!(
            serde_json::to_vec(&graph).unwrap(),
            serde_json::to_vec(&expected).unwrap()
        );
    }

    #[cfg(not(feature = "legacy-json"))]
    #[test]
    fn wire_key_hash_collisions_do_not_merge_distinct_payloads() {
        #[derive(Default)]
        struct Zero;
        impl std::hash::Hasher for Zero {
            fn finish(&self) -> u64 {
                0
            }
            fn write(&mut self, _: &[u8]) {}
        }
        let mut map: HashMap<WireKey, usize, std::hash::BuildHasherDefault<Zero>> =
            HashMap::default();
        for (id, value) in [json!([0.0]), json!([-0.0]), json!([1]), json!([1.0])]
            .into_iter()
            .enumerate()
        {
            assert!(map.insert(WireKey(value), id).is_none());
        }
        assert_eq!(map.len(), 4);
    }

    fn is_reference(value: &Value) -> bool {
        value
            .as_object()
            .is_some_and(|object| object.len() == 1 && object.contains_key(SHARED_REF_FIELD))
    }

    fn dereference(value: &Value, nodes: &[Value], current_node: Option<usize>) -> Value {
        if let Some(index) = value
            .as_object()
            .filter(|object| object.len() == 1)
            .and_then(|object| object.get(SHARED_REF_FIELD))
            .and_then(Value::as_u64)
        {
            let index = index as usize;
            if let Some(parent) = current_node {
                assert!(index < parent, "node references must point backward");
            }
            return dereference(&nodes[index], nodes, Some(index));
        }

        match value {
            Value::Array(values) => Value::Array(
                (values
                    .iter()
                    .map(|child| dereference(child, nodes, current_node))
                    .collect::<Vec<_>>())
                .into(),
            ),
            Value::Object(object) => Value::Object(
                (object
                    .iter()
                    .map(|(key, child)| (key.clone(), dereference(child, nodes, current_node)))
                    .collect::<Map<_, _>>())
                .into(),
            ),
            _ => value.clone(),
        }
    }

    #[test]
    fn generic_dag_round_trips_and_interns_repeated_nested_payloads() {
        let long = "a long compiler type name that should receive a graph id";
        let original = json!({
            "items": [
                {"name": long, "values": [1, 2, 3]},
                {"name": long, "values": [1, 2, 3]},
            ],
            "position": {"line": 7, "column": 12},
            "small": "enum_tag"
        });
        let mut encoded = original.clone();
        share_payloads(&mut encoded).unwrap();

        let catalog = encoded.get(SHARED_CATALOG_FIELD).unwrap();
        assert_eq!(catalog["schema_version"], 2);
        let nodes = catalog["nodes"].as_array().unwrap();
        assert!(nodes.len() >= 4, "nested eligible payloads should be nodes");
        let decoded = dereference(&encoded, nodes, None);
        let mut decoded = decoded.as_object().unwrap().clone();
        decoded.remove(SHARED_CATALOG_FIELD);
        assert_eq!(Value::Object(decoded.into()), original);
    }

    #[test]
    fn root_fields_remain_and_catalog_is_emitted_for_small_documents() {
        let mut document = json!({"kind": "mir", "position": {"line": 1, "column": 2}});
        share_payloads(&mut document).unwrap();
        assert_eq!(document["kind"], "mir");
        assert_eq!(document["position"]["line"], 1);
        assert_eq!(document[SHARED_CATALOG_FIELD]["nodes"], json!([]));
    }

    #[test]
    fn short_payloads_and_singleton_arrays_are_shared_but_enum_tags_stay_inline() {
        let original = json!({
            "def_path": "crate::f",
            "kind": "Call",
            "arguments": [7],
            "layout": {
                "status": "unsupported",
                "kind": "layout",
                "reason": "type still has a generic parameter"
            }
        });
        let mut encoded = original.clone();
        share_payloads(&mut encoded).unwrap();

        assert!(is_reference(&encoded["def_path"]));
        assert_eq!(encoded["kind"], "Call");
        assert!(is_reference(&encoded["arguments"]));
        assert!(is_reference(&encoded["layout"]));

        let nodes = encoded[SHARED_CATALOG_FIELD]["nodes"].as_array().unwrap();
        let decoded = dereference(&encoded, nodes, None);
        let mut decoded = decoded.as_object().unwrap().clone();
        decoded.remove(SHARED_CATALOG_FIELD);
        assert_eq!(Value::Object(decoded.into()), original);
    }

    #[test]
    fn distinct_runtime_identity_fields_remain_distinct_after_encoding() {
        let original = json!({
            "instances": [
                {"kind": "function", "instance_id": 17, "def_path": "crate::left", "generation": 1},
                {"kind": "function", "instance_id": 18, "def_path": "crate::right", "generation": 1},
            ]
        });
        let mut encoded = original.clone();
        share_payloads(&mut encoded).unwrap();
        let nodes = encoded[SHARED_CATALOG_FIELD]["nodes"].as_array().unwrap();
        let decoded = dereference(&encoded, nodes, None);
        let mut decoded = decoded.as_object().unwrap().clone();
        decoded.remove(SHARED_CATALOG_FIELD);
        assert_eq!(Value::Object(decoded.into()), original);
        assert_ne!(nodes[0], nodes[1]);
    }

    #[test]
    fn reserved_catalog_and_reference_shapes_are_rejected() {
        let mut with_catalog = json!({"shared_payloads": {}});
        assert!(share_payloads(&mut with_catalog).is_err());

        let mut with_ref = json!({"payload": {SHARED_REF_FIELD: 0}});
        assert!(share_payloads(&mut with_ref).is_err());
    }

    #[test]
    fn prepared_scan_flags_follow_shared_edges_and_preserve_transport() {
        let original = json!({"items": [
            {"locals": [], "basic_blocks": [{"type_id": 7}]},
            {"fn_abi": {"calling_convention": "Rust"}},
            {"vtable_allocation": {"kind": "dynamic_vtable_upcast"}},
            {"plain": [1, 2, 3]}
        ]});
        let mut ordinary = original.clone();
        share_payloads(&mut ordinary).unwrap();
        let mut prepared = original;
        share_payloads_with_scan_flags(&mut prepared, true).unwrap();
        let catalog = prepared[SHARED_CATALOG_FIELD].as_object_mut().unwrap();
        let flags = catalog.remove("scan_flags").unwrap();
        assert_eq!(
            flags.as_array().unwrap().len(),
            catalog["nodes"].as_array().unwrap().len()
        );
        assert!(
            flags
                .as_array()
                .unwrap()
                .iter()
                .any(|flag| flag == &json!(15))
        );
        assert!(
            flags
                .as_array()
                .unwrap()
                .iter()
                .any(|flag| flag == &json!(0))
        );
        assert_eq!(ordinary, prepared, "only the checked summaries may differ");
    }
}
