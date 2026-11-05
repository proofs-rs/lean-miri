//! The same fixtures run against both persistent and legacy tree patch passes.
use super::*;

#[cfg(not(feature = "legacy-json"))]
#[test]
fn fused_vtable_pass_matches_ordered_reference_with_aliases_and_malformed_rows() {
    let ids = HashMap::from([((7, vec![2, 3]), 19)]);
    let hit = json!({"status":"supported","vtable_query":{
        "status":"supported","_query_key":{"input_type_id":7,"input_predicate_ids":[2,3]}},
        "virtual_resolution":{"instance_id":5}});
    let malformed = json!({"original_instance_id":5,"vtable_query":{
        "query_id":2,"_query_key":{"input_type_id":"bad"},
        "virtual_resolution":{"instance_id":5}}});
    let mut cases = vec![Value::Null, json!(false), json!([]), hit.clone(), malformed.clone()];
    for rows in [Value::Null, json!(false), json!([hit, hit, malformed]),
        json!([{"original_instance_id":5,"vtable_query":{"query_id":9}},
            {"original_instance_id":5,"vtable_query":{"query_id":9}}])] {
        let call = json!({"virtual_resolution":{"instance_id":5}});
        cases.push(json!({"compiler_runtime_queries":{"virtual":rows},
            "calls":[call,call,{"virtual_resolution":false},{"vtable_query":false}]}));
    }
    for mut actual in cases {
        let mut expected = actual.clone();
        patch_vtable_query_ids(&mut expected, &ids);
        patch_virtual_resolution_candidates(&mut expected);
        patch_compiler_vtable_metadata(&mut actual, &ids);
        assert_eq!(actual.to_string(), expected.to_string());
    }
}

#[test]
fn finished_snapshot_crosses_threads_without_construction_nodes() {
    fn require_send<T: Send>() {}
    require_send::<Snapshot>();
    let snapshot = finish_snapshot(json!({"values":["text",1,-0.0,true,null]})).unwrap();
    let expected = serde_json::to_string(&snapshot).unwrap();
    let actual = std::thread::spawn(move || serde_json::to_string(&snapshot).unwrap()).join().unwrap();
    assert_eq!(actual,expected);
}

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

#[test]
fn diagnostic_graph_scan_preserves_every_occurrence_and_order() {
    let probe = json!({"vtable_probe":{"status":"incomplete",
        "kind":"symbolic_vtable_allocation","salt_policy":"kept"}});
    let unresolved = json!({"status":"unsupported","kind":"query","reason":"kept"});
    let debug = json!({"status":"debug_payload","nested":[unresolved, probe]});
    let mut shared = json!({"a.b%[": [probe, unresolved, debug], "supported":{"status":"supported"}});
    for depth in 0..9 {
        let document = json!({"types":[shared, shared],
            "compiler_runtime_queries":{"later":shared},
            "bodies":[shared, shared],"instances":{"later":shared}});
        assert_eq!(catalog_evidence_obligations(&document),
            catalog_evidence_obligations_reference(&document), "catalog depth {depth}");
        assert_eq!(retained_vtable_probe_diagnostics(&document),
            retained_vtable_probe_diagnostics_reference(&document), "probe depth {depth}");
        shared = json!({"a":[shared, shared],"z":probe});
    }
}

#[test]
fn binary_format_flag_is_consumed_before_rustc_arguments() {
    let binary = parse_args(["--output","test.lmir","--binary-image","--","test.rs"]
        .map(str::to_owned)).unwrap();
    assert!(binary.binary_image);
    assert!(!binary.rustc_args.iter().any(|arg|arg=="--binary-image"));
    let json = parse_args(["--output","test.json","--","test.rs"].map(str::to_owned)).unwrap();
    assert!(!json.binary_image);
}
