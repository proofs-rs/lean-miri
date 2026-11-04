//! The same fixtures run against both persistent and legacy tree patch passes.
use super::*;

#[test]
fn runtime_type_operation_promotion_keeps_prior_fields_and_one_row() {
    let mut rows = Vec::new();
    let mut positions = HashMap::new();
    merge_runtime_type_queries(&mut rows, &mut positions, vec![
        json!({"input_type_id":9,"mut_pointer_type":{"status":"supported","value":{"type_id":10}}}),
        json!({"input_type_id":2,"drop_glue":{"status":"unsupported"}}),
    ]);
    merge_runtime_type_queries(&mut rows, &mut positions, vec![
        json!({"input_type_id":9,"mut_reference_type":{"status":"supported","value":{"type_id":11}}}),
    ]);
    assert_eq!(rows.len(), 2);
    assert_eq!(positions[&9], 0);
    assert_eq!(rows[0]["mut_pointer_type"]["value"]["type_id"], 10);
    assert_eq!(rows[0]["mut_reference_type"]["value"]["type_id"], 11);
    assert!(rows[0].get("drop_glue").is_none());
    assert_eq!(rows[1]["drop_glue"]["status"], "unsupported");
}

#[test]
fn exact_vtable_links_keep_unknown_queries_unknown() {
    let hit = json!({"status":"supported","vtable_query":{
        "status":"supported","_query_key":{"input_type_id":7,"input_predicate_ids":[2,3]}}});
    let miss = json!({"status":"supported","vtable_query":{
        "status":"supported","_query_key":{"input_type_id":8,"input_predicate_ids":[2,3]}}});
    let mut document = json!([hit, hit, miss, {"vtable_query":null}, {"vtable_query":false}]);
    patch_vtable_query_ids(&mut document, &HashMap::from([((7, vec![2, 3]), 19)]));
    assert_eq!(
        document[0]["vtable_query"],
        json!({"status":"supported","query_id":19})
    );
    assert_eq!(document[0], document[1]);
    assert_eq!(document[2]["status"], "unknown");
    assert_eq!(document[2]["vtable_query"]["status"], "unknown");
    assert!(document[2]["vtable_query"].get("_query_key").is_none());
    assert!(document[2]["vtable_query"].get("query_id").is_none());
    assert_eq!(document[3], json!({"vtable_query":null}));
    assert_eq!(
        document[4],
        json!({"status":"unknown","vtable_query":false})
    );
}

#[test]
fn virtual_candidates_use_exact_instance_and_sorted_unique_queries() {
    let call = json!({"virtual_resolution":{"instance_id":5}});
    let mut document = json!({
        "compiler_runtime_queries":{"virtual":[
            {"original_instance_id":5,"vtable_query":{"query_id":9}},
            {"original_instance_id":5,"vtable_query":{"query_id":2}},
            {"original_instance_id":5,"vtable_query":{"query_id":9}},
            {"original_instance_id":6,"vtable_query":{"query_id":8}},
            {"original_instance_id":5,"vtable_query":{"status":"unknown"}}]},
        "calls":[call,call,{"virtual_resolution":{"instance_id":7}},
            {"virtual_resolution":null},{"virtual_resolution":{"instance_id":"5"}}]});
    patch_virtual_resolution_candidates(&mut document);
    assert_eq!(
        document["calls"][0]["virtual_resolution"]["candidate_query_ids"],
        json!([2, 9])
    );
    assert_eq!(document["calls"][0], document["calls"][1]);
    assert_eq!(
        document["calls"][2]["virtual_resolution"]["candidate_query_ids"],
        json!([])
    );
    assert_eq!(document["calls"][3], json!({"virtual_resolution":null}));
    assert_eq!(
        document["calls"][4],
        json!({"virtual_resolution":{"instance_id":"5"}})
    );
}
