//! Versioned positional FnAbi transport. This transforms only exact producer
//! records after DAG interning; node IDs and all ordinary payloads are retained.
use serde_json::{Value, json};
use std::collections::HashSet;

const ARG: &str = "$lean_miri_abi_arg";
const ABI: &str = "$lean_miri_fn_abi";
const REF: &str = "$lean_miri_shared_ref";

fn reference(value: &Value) -> Option<usize> {
    let object = value.as_object()?;
    if object.len() != 1 { return None; }
    usize::try_from(object.get(REF)?.as_u64()?).ok()
}

fn exact(value: &Value, keys: &[&str]) -> bool {
    value.as_object().is_some_and(|object| {
        object.len() == keys.len() && keys.iter().all(|key| object.contains_key(*key))
    })
}

/// No interpretation or safety result is exported. Layouts, modes and calling
/// conventions still carry the original compiler evidence and are checked in Lean.
pub(crate) fn pack(document: &mut Value) -> Result<(usize, usize), String> {
    let catalog = document.get_mut("shared_payloads").and_then(Value::as_object_mut)
        .ok_or("typed ABI transport requires a shared-payload catalog")?;
    if catalog.contains_key("typed_abi_version") {
        return Err("typed ABI catalog is already encoded".into());
    }
    let nodes = catalog.get_mut("nodes").and_then(Value::as_array_mut)
        .ok_or("typed ABI transport requires a node array")?;
    let mut arguments = HashSet::new();
    let mut vectors = HashSet::new();
    let mut functions = 0;
    for index in 0..nodes.len() {
        let value = &nodes[index];
        if value.get(ARG).is_some() || value.get(ABI).is_some() {
            return Err("input contains reserved typed ABI marker".into());
        }
        if exact(value, &["type", "layout", "mode"])
            && exact(&value["type"], &["type_id"])
            && value["type"]["type_id"].as_u64().is_some()
        {
            let record = json!({ARG: [value["type"]["type_id"], value["layout"], value["mode"]]});
            nodes[index] = record;
            arguments.insert(index);
        } else if value.as_array().is_some_and(|values| values.iter().all(|child| {
            reference(child).is_some_and(|id| id < index && arguments.contains(&id))
        })) {
            vectors.insert(index);
        } else if exact(value, &["arguments", "return", "calling_convention", "can_unwind", "c_variadic", "fixed_count"])
            && value["can_unwind"].is_boolean() && value["c_variadic"].is_boolean()
            && value["fixed_count"].as_u64().is_some()
        {
            let empty = value["arguments"].as_array().is_some_and(Vec::is_empty);
            let vector = reference(&value["arguments"]).filter(|id| vectors.contains(id));
            let returned = reference(&value["return"]).filter(|id| arguments.contains(id));
            if let Some(returned) = returned {
                if empty || vector.is_some() {
                    let record = json!({ABI: [vector, returned, value["calling_convention"],
                        value["can_unwind"], value["c_variadic"], value["fixed_count"]]});
                    nodes[index] = record;
                    functions += 1;
                }
            }
        }
    }
    catalog.insert("typed_abi_version".into(), json!(1));
    Ok((arguments.len(), functions))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn preserves_ids_and_packs_only_exact_records() {
        let arg = json!({"type":{"type_id":7},"layout":{"status":"unsupported"},"mode":{"kind":"Ignore"}});
        let abi = json!({"arguments":{REF:1},"return":{REF:0},"calling_convention":{"kind":"Rust"},
            "can_unwind":false,"c_variadic":false,"fixed_count":1});
        let extra = json!({"type":{"type_id":7},"layout":{},"mode":{},"extra":"retained"});
        let mut document = json!({"shared_payloads":{"schema_version":2,"nodes":[arg,[{REF:0}],abi,extra.clone()]}});
        assert_eq!(pack(&mut document).unwrap(), (1,1));
        let catalog = &document["shared_payloads"];
        assert_eq!(catalog["typed_abi_version"],1);
        assert_eq!(catalog["nodes"][0][ARG][0],7);
        assert_eq!(catalog["nodes"][2][ABI][0],1);
        assert_eq!(catalog["nodes"][2][ABI][1],0);
        assert_eq!(catalog["nodes"][3],extra);
        assert!(pack(&mut document).is_err());
    }
}
