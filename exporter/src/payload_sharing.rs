//! Numeric references in independent semantic ID spaces.
//!
//! This final wire transform runs after compiler demand closure and diagnostics.
//! Compiler identities (types, instances, allocations, predicates) are retained;
//! immutable metadata is structurally interned within its own kind only. MIR
//! locals, blocks, scopes, binder indices and allocation provenance stay local.

use serde_json::{Map, Value, json};
use std::collections::{BTreeMap, HashMap};

pub(crate) const KINDS: &[&str] = &[
    "spans", "layouts", "function_abis", "generic_args", "regions",
    "constants", "signatures", "binders", "predicates",
    "definitions", "instance_kinds", "argument_abis", "abi_attributes",
    "abi_registers", "cast_targets", "patterns",
];

/// Field roles are schema, not a size or shape based compression heuristic.
/// Keep this inventory synchronized with SemanticTables.lean and mir_json.py.
fn field_kind(field: &str, parent: &Map<String, Value>) -> Option<&'static str> {
    let tag = parent.get("kind").and_then(Value::as_str).unwrap_or("");
    match field {
        "span" | "preamble_def_span" | "callsite_span" | "function_span" |
        "root_span" => Some("spans"),
        "layout" => Some("layouts"),
        "fn_abi" | "abi_query" => Some("function_abis"),
        "generic_args" | "rebased_args" => Some("generic_args"),
        "arguments" if tag == "expression" => Some("generic_args"),
        "region" => Some("regions"),
        "instance_kind" | "source_instance_kind" => Some("instance_kinds"),
        "def_id" | "instance_def_id" | "trait_def_id" | "scope_def_id" | "method_definition" | "parent_trait" | "definition" |
        "owner_def_id" | "source_def_id" | "call_once_def_id" | "closure_def_id" |
        "coroutine_closure_def_id" | "start_lang_item" | "compiler_entry" | "hoisted_from" => Some("definitions"),
        "signature" => Some("signatures"),
        "signature_query" if parent.contains_key("function_kind") ||
            parent.get("query").and_then(Value::as_str) == Some("instantiate_bound_regions_with_erased(fn_sig(instance.def_id()).instantiate(instance.args))") => Some("signatures"),
        "pattern" => Some("patterns"),
        "bound_variables" | "signature_bound_variables" => Some("binders"),
        "const" | "constant" => Some("constants"),
        "length" if tag == "array" => Some("constants"),
        "count" if tag == "Repeat" => Some("constants"),
        "start" | "end" if tag == "range" => Some("constants"),
        "value" if tag == "lifetime" => Some("regions"),
        "value" if tag == "const" || tag == "sym_fn" => Some("constants"),
        "normalized_operand" => Some("constants"),
        _ => None,
    }
}

#[derive(Default)]
struct Table {
    nodes: Vec<Value>,
    indices: HashMap<String, usize>,
}

#[derive(Default)]
struct Encoder {
    tables: BTreeMap<&'static str, Table>,
    predicates: BTreeMap<u64, Value>,
    instance_identities: HashMap<u64, (Value, Value)>,
}

impl Encoder {
    fn intern(&mut self, kind: &'static str, value: &mut Value) {
        if value.is_null() { return; }
        let table = self.tables.entry(kind).or_default();
        let key = value.to_string();
        let id = if let Some(id) = table.indices.get(&key) { *id } else {
            let id = table.nodes.len();
            table.nodes.push(std::mem::replace(value, Value::Null));
            table.indices.insert(key, id);
            id
        };
        *value = json!(id);
    }

    fn visit(&mut self, value: &mut Value, role: Option<&'static str>) -> Result<(), String> {
        self.visit_node(value, role, false)
    }

    fn visit_node(&mut self, value: &mut Value, role: Option<&'static str>, preserve_identity: bool) -> Result<(), String> {
        // Type-shape definition identities historically used a `crate:index`
        // spelling, while other serializers emitted the same pair as a record.
        // Canonicalize both encodings before assigning definition IDs.
        if role == Some("definitions") {
            if let Some(text) = value.as_str() {
                if let Some((krate, index)) = text.split_once(':') {
                    if let (Ok(krate), Ok(index)) = (krate.parse::<u32>(), index.parse::<u32>()) {
                        *value = json!({"crate":krate,"index":index});
                    }
                }
            }
        }
        // Pure instance identities carry no query- or position-specific
        // evidence. Their authoritative kind/arguments live in instances.
        if let Some(object) = value.as_object() {
            if !preserve_identity && object.contains_key("instance_kind") && object.contains_key("generic_args")
                && object.keys().all(|key| ["instance_id", "instance_kind", "generic_args"].contains(&key.as_str()))
            {
                if let Some(id) = object.get("instance_id").and_then(Value::as_u64) {
                    let identity = (object["instance_kind"].clone(), object["generic_args"].clone());
                    if self.instance_identities.get(&id) != Some(&identity) {
                        return Err(format!("instance reference {id} differs from canonical identity"));
                    }
                    *value = json!(id);
                    return Ok(());
                }
            }
        }
        // Only singleton references are replaced. Catalog records retain their
        // identity field and full payload, including allocation provenance.
        if let Some(object) = value.as_object() {
            if object.len() == 1 {
                for field in ["type_id", "instance_id", "allocation_id", "predicate_id"] {
                    if let Some(id) = object.get(field) {
                        if id.as_u64().is_none() { return Err(format!("invalid {field}")); }
                        *value = id.clone();
                        return Ok(());
                    }
                }
            }
        }
        // Exact serializer shapes identify metadata in direct query-result
        // slots; scalar result numbers are never guessed to be references.
        let role = role.or_else(|| value.as_object().and_then(|o| {
            if o.len() == 2 && o.contains_key("crate") && o.contains_key("index") { Some("definitions") }
            else if o.contains_key("calling_convention") && o.contains_key("fixed_count") { Some("function_abis") }
            else if o.contains_key("inputs") && o.contains_key("output") && o.contains_key("c_variadic") { Some("signatures") }
            else if o.contains_key("abi_align_bytes") && o.contains_key("size_bytes") { Some("layouts") }
            else if o.contains_key("lo") && o.contains_key("hi") && o.contains_key("ctxt") && o.contains_key("start") { Some("spans") }
            else if o.len() == 3 && o.contains_key("type") && o.contains_key("layout") && o.contains_key("mode") { Some("argument_abis") }
            else if o.contains_key("constant") && o.contains_key("type") && o.contains_key("span") && o.contains_key("user_type_annotation") { Some("constants") }
            else if o.contains_key("regular_bits") && o.contains_key("arg_extension") { Some("abi_attributes") }
            else if o.len() == 2 && o.contains_key("size_bits") && o.contains_key("kind") { Some("abi_registers") }
            else if o.contains_key("prefix_registers") && o.contains_key("rest_register") { Some("cast_targets") }
            else { None }
        }));
        match value {
            Value::Object(object) => {
                if object.contains_key("$lean_miri_shared_ref") {
                    return Err("obsolete generic shared reference in exporter input".into());
                }
                // Compute roles before mutating fields: parent discriminants
                // must remain available even when a child becomes an ID.
                let roles: Vec<_> = object.keys().map(|key| (key.clone(), field_kind(key, object))).collect();
                let tag = object.get("kind").and_then(Value::as_str).unwrap_or("").to_owned();
                for (key, child_role) in roles {
                    let child = object.get_mut(&key).unwrap();
                    if (key == "line_spans" || (key == "elements" && tag == "branch") || (key == "patterns" && tag == "or")) && child.is_array() {
                        let element_role = if key == "line_spans" { "spans" } else if key == "patterns" { "patterns" } else { "constants" };
                        for element in child.as_array_mut().unwrap() { self.visit(element, Some(element_role))?; }
                    } else {
                        self.visit(child, child_role)?;
                    }
                }
                if let Some(id) = object.get("predicate_id").and_then(Value::as_u64)
                    .filter(|_| matches!(tag.as_str(), "trait" | "auto_trait" | "projection")) {
                    let node = Value::Object(object.clone());
                    if let Some(previous) = self.predicates.insert(id, node.clone()) {
                        if previous != node { return Err(format!("conflicting predicate identity {id}")); }
                    }
                    *value = json!(id);
                    return Ok(());
                }
            }
            Value::Array(values) => for child in values { self.visit(child, None)?; },
            _ => {},
        }
        if let Some(kind) = role { self.intern(kind, value); }
        Ok(())
    }
}

pub(crate) fn encode_numeric_references(document: &mut Value) -> Result<(), String> {
    let root = document.as_object_mut().ok_or("numeric exporter expected object root")?;
    if root.contains_key("semantic_tables") || root.contains_key("shared_payloads") {
        return Err("exporter input already contains a wire catalog".into());
    }
    let mut encoder = Encoder::default();
    if let Some(instances) = root.get("instances").and_then(Value::as_array) {
        for row in instances {
            if let (Some(id), Some(kind), Some(args)) = (row.get("instance_id").and_then(Value::as_u64), row.get("instance_kind"), row.get("generic_args")) {
                if encoder.instance_identities.insert(id, (kind.clone(), args.clone())).is_some() {
                    return Err(format!("duplicate canonical instance {id}"));
                }
            }
        }
    }
    for (key, child) in root.iter_mut() {
        if key == "instances" {
            for row in child.as_array_mut().ok_or("instances must be an array")? {
                encoder.visit_node(row, None, true)?;
            }
        } else { encoder.visit(child, None)?; }
    }
    let mut catalog = Map::new();
    catalog.insert("schema_version".into(), json!(1));
    for kind in KINDS {
        if *kind == "predicates" {
            // Predicate IDs are compiler identities and may be sparse: retain
            // explicit predicate_id rather than renumbering query references.
            catalog.insert((*kind).into(), Value::Array(encoder.predicates.values().cloned().collect()));
        } else {
            catalog.insert((*kind).into(), Value::Array(encoder.tables.remove(kind).unwrap_or_default().nodes));
        }
    }
    root.insert("semantic_tables".into(), Value::Object(catalog));
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    #[test]
    fn kinds_have_independent_ids_and_all_type_occurrences_are_numeric() {
        let mut document = json!({"types":[{"type_id":0,"shape":{"kind":"tuple","elements":[{"type_id":0}]},"layout":{"size_bytes":0}}],
            "instances":[{"instance_id":0,"generic_args":[]}],
            "bodies":[{"entry_instance":{"instance_id":0},"locals":[{"type":{"type_id":0},"layout":{"size_bytes":0}}]}]});
        encode_numeric_references(&mut document).unwrap();
        assert_eq!(document["types"][0]["shape"]["elements"][0], 0);
        assert_eq!(document["bodies"][0]["entry_instance"], 0);
        assert_eq!(document["bodies"][0]["locals"][0]["type"], 0);
        assert_eq!(document["types"][0]["layout"], 0);
        assert_eq!(document["semantic_tables"]["layouts"].as_array().unwrap().len(), 1);
        assert_eq!(document["instances"][0]["generic_args"], 0);
    }
    #[test]
    fn local_indices_and_allocation_identity_are_preserved() {
        let mut document = json!({"allocations":[{"allocation_id":7,"bytes":[0],"provenance":[{"allocation_id":8}]},{"allocation_id":8,"bytes":[0]}],
            "bodies":[{"local":2,"scope":2,"target":2,"region":{"kind":"erased"},"span":{"lo":2,"hi":2}}]});
        encode_numeric_references(&mut document).unwrap();
        assert_eq!(document["allocations"].as_array().unwrap().len(), 2);
        assert_eq!(document["allocations"][0]["allocation_id"], 7);
        assert_eq!(document["allocations"][0]["provenance"][0], 8);
        for field in ["local", "scope", "target"] { assert_eq!(document["bodies"][0][field], 2); }
        assert_eq!(document["bodies"][0]["region"], 0);
        assert_eq!(document["bodies"][0]["span"], 0);
    }
    #[test]
    fn predicates_keep_identity_and_bound_variables_are_interned() {
        let predicate = json!({"predicate_id":3,"kind":"trait","bound_variables":[]});
        let mut document = json!({"left":predicate,"right":predicate});
        encode_numeric_references(&mut document).unwrap();
        assert_eq!(document["left"], 3);
        assert_eq!(document["right"], 3);
        assert_eq!(document["semantic_tables"]["predicates"][0]["predicate_id"], 3);
        assert_eq!(document["semantic_tables"]["binders"], json!([[]]));
    }
    #[test]
    fn type_patterns_and_hoisted_definitions_have_explicit_kinds() {
        let pattern = json!({"kind":"range","start":{"kind":"value","type":{"type_id":2},"value":{"kind":"leaf","bits_unsigned":"1","size_bytes":4}},"end":{"kind":"value","type":{"type_id":2},"value":{"kind":"leaf","bits_unsigned":"9","size_bytes":4}}});
        let mut document = json!({"left":{"pattern":pattern,"hoisted_from":{"crate":2,"index":7}},"right":{"pattern":pattern},"third":{"pattern":{"kind":"or","patterns":[pattern,pattern]}}});
        encode_numeric_references(&mut document).unwrap();
        assert_eq!(document["left"]["pattern"], 0);
        assert_eq!(document["right"]["pattern"], 0);
        assert_eq!(document["semantic_tables"]["patterns"].as_array().unwrap().len(), 2);
        assert!(document["semantic_tables"]["patterns"][0]["start"].is_u64());
        assert_eq!(document["third"]["pattern"], 1);
        assert_eq!(document["semantic_tables"]["patterns"][1]["patterns"], json!([0,0]));
        assert_eq!(document["left"]["hoisted_from"], 0);
    }
    #[test]
    fn definitions_and_abi_query_payloads_use_dedicated_tables() {
        let abi = json!({"calling_convention":{"kind":"Rust"},"fixed_count":0,"return":{"type":{"type_id":2},"layout":{"size_bytes":0,"abi_align_bytes":1},"mode":{"kind":"Ignore"}},"arguments":[]});
        let mut document = json!({"left":{"def_id":"3:7"},"right":{"def_id":{"crate":3,"index":7}},"query":{"abi_query":abi}});
        encode_numeric_references(&mut document).unwrap();
        assert_eq!(document["left"]["def_id"], document["right"]["def_id"]);
        assert_eq!(document["semantic_tables"]["definitions"], json!([{"crate":3,"index":7}]));
        assert_eq!(document["query"]["abi_query"], 0);
        assert_eq!(document["semantic_tables"]["function_abis"][0]["return"], 0);
        assert_eq!(document["semantic_tables"]["argument_abis"][0]["type"], 2);
    }
    #[test]
    fn direct_signature_queries_keep_main_entry_and_scalar_results_separate() {
        let signature = json!({"inputs":[],"output":{"type_id":2},"c_variadic":false});
        let entry = json!({"compiler_selected_entry":false,"return_type":{"type_id":2},"start_resolution":null});
        let mut document = json!({"function":{"function_kind":"function_definition","signature_query":signature},
            "entry":{"signature_query":entry},"cast":{"query_kind":"supertrait_slot","value":999}});
        encode_numeric_references(&mut document).unwrap();
        assert_eq!(document["function"]["signature_query"], 0);
        assert!(document["entry"]["signature_query"].is_object());
        assert_eq!(document["entry"]["signature_query"]["return_type"], 2);
        assert_eq!(document["cast"]["value"], 999);
        assert_eq!(document["semantic_tables"]["signatures"].as_array().unwrap().len(), 1);
    }
    #[test]
    fn predicate_query_rows_are_not_predicate_payloads() {
        let mut document = json!({"queries":[{"predicate_id":2,"typing_env":"fully_monomorphized","original":{"predicate_id":2,"kind":"trait","bound_variables":[]},"normalization":2}]});
        encode_numeric_references(&mut document).unwrap();
        assert_eq!(document["queries"][0]["predicate_id"], 2);
        assert_eq!(document["queries"][0]["original"], 2);
        assert_eq!(document["semantic_tables"]["predicates"][0]["kind"], "trait");
    }
    #[test]
    fn conflicting_identities_and_obsolete_wire_documents_are_rejected() {
        let mut conflicting = json!({"a":{"predicate_id":0,"kind":"trait"},"b":{"predicate_id":0,"kind":"auto_trait"}});
        assert!(encode_numeric_references(&mut conflicting).is_err());
        assert!(encode_numeric_references(&mut json!({"semantic_tables":{}})).is_err());
        assert!(encode_numeric_references(&mut json!({"shared_payloads":{}})).is_err());
        assert!(encode_numeric_references(&mut json!({"x":{"$lean_miri_shared_ref":0}})).is_err());
    }

    #[test]
    fn plain_instance_references_use_the_canonical_identity_only() {
        let identity = json!({"instance_kind":{"kind":"item","def_id":{"crate":0,"index":1}},"generic_args":[]});
        let mut canonical = identity.clone();
        canonical["instance_id"] = json!(2);
        let reference = canonical.clone();
        let mut query = reference.clone();
        query["requires_caller_location"] = json!(false);
        let mut document = json!({"instances":[canonical],"entry_instance":reference,"query":query});
        encode_numeric_references(&mut document).unwrap();
        assert_eq!(document["entry_instance"], 2);
        assert_eq!(document["instances"][0]["instance_id"], 2);
        assert_eq!(document["query"]["instance_id"], 2);
        assert_eq!(document["query"]["requires_caller_location"], false);
        assert!(document["query"]["instance_kind"].is_u64());
        let mut inconsistent = json!({"instances":[],"entry_instance":{"instance_id":2,"instance_kind":{},"generic_args":[]}});
        assert!(encode_numeric_references(&mut inconsistent).is_err());
    }

}
