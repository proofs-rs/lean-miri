//! Generic bottom-up JSON DAG encoding for large repeated exporter payloads.
//!
//! This is a final wire transform. It does not change compiler query demand
//! or ordering. Eligible values are represented by numeric
//! references into `shared_payloads.nodes`; nodes are emitted after their
//! children, so every reference in a node points to a lower numbered node.

use serde_json::{Map, Value, json};
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
    indices: HashMap<String, usize>,
}

impl Encoder {
    fn encode_value(&mut self, value: &mut Value, field: Option<&str>) -> Result<(), String> {
        if contains_reference_marker(value) {
            return Err(format!(
                "input contains reserved `{SHARED_REF_FIELD}` reference shape"
            ));
        }

        // Eligibility must be based on the source shape. Replacing a child
        // array with a reference can otherwise make its containing record look
        // small by the time its own post-order visit finishes.
        let should_intern = eligible(value, field);

        match value {
            Value::Array(values) => {
                for child in values {
                    self.encode_value(child, None)?;
                }
            }
            Value::Object(object) => {
                for (key, child) in object.iter_mut() {
                    self.encode_value(child, Some(key))?;
                }
            }
            _ => {}
        }

        if !should_intern {
            return Ok(());
        }

        // serde_json's default Map is key ordered, making this a stable,
        // collision-free structural key (rather than a hash-only identity).
        let key = value.to_string();
        if let Some(index) = self.indices.get(&key) {
            *value = reference(*index);
            return Ok(());
        }

        let index = self.nodes.len();
        self.nodes.push(std::mem::replace(value, Value::Null));
        self.indices.insert(key, index);
        *value = reference(index);
        Ok(())
    }
}

/// Encode eligible values as a bottom-up DAG while preserving root fields.
///
/// The transform is deterministic and exact: structural JSON serialization
/// is used as the interning key, and references point to nodes with lower ids.
pub(crate) fn share_payloads(document: &mut Value) -> Result<(), String> {
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

    root.insert(
        SHARED_CATALOG_FIELD.into(),
        json!({
            "schema_version": SCHEMA_VERSION,
            "nodes": encoder.nodes,
        }),
    );
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

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
                values
                    .iter()
                    .map(|child| dereference(child, nodes, current_node))
                    .collect(),
            ),
            Value::Object(object) => Value::Object(
                object
                    .iter()
                    .map(|(key, child)| (key.clone(), dereference(child, nodes, current_node)))
                    .collect(),
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
        assert_eq!(Value::Object(decoded), original);
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
        assert_eq!(Value::Object(decoded), original);
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
        assert_eq!(Value::Object(decoded), original);
        assert_ne!(nodes[0], nodes[1]);
    }

    #[test]
    fn reserved_catalog_and_reference_shapes_are_rejected() {
        let mut with_catalog = json!({"shared_payloads": {}});
        assert!(share_payloads(&mut with_catalog).is_err());

        let mut with_ref = json!({"payload": {SHARED_REF_FIELD: 0}});
        assert!(share_payloads(&mut with_ref).is_err());
    }
}
