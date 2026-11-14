#!/usr/bin/env python3
"""Check a complete abstract virtual identity without inventing concrete targets."""
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "tools"))
from mir_json import load_mir_inspection_document as load_mir_document, pool_entry

doc = load_mir_document(sys.argv[1])
scope = doc["selected_scope"]
assert "completeness" not in doc
assert scope["kind"] == "rooted_structural_closure"
assert scope["semantics"] == "structural_export_closure_only"
assert scope["roots"][0]["def_path"] == "call_trait_object"

virtual_targets = {item["instance_id"]: item for item in doc["instances"]
                   if item["instance_kind"]["kind"] == "virtual"}
assert virtual_targets, "the source Virtual identity was dropped"
for target in virtual_targets.values():
    assert target["kind"] == "identity_only"
    assert "body" not in target and "virtual_identity" not in target and "status" not in target
    kind = target["instance_kind"]
    assert kind["def_id"] == target["def_id"] and kind["dispatch_slot"] == 3
    declaration = pool_entry(doc, "definitions", kind["def_id"])
    assert declaration["callable_source"]["definition_kind"] == "associated_function"
    assert declaration["callable_source"]["container"] == "trait" and declaration["callable_source"]["has_self"]
    assert declaration["body_track_caller"] is False
    assert len(target["generic_args"]) == 1 and target["generic_args"][0]["kind"] == "type"
    self_type = pool_entry(doc, "types", target["generic_args"][0]["value"])["shape"]
    assert self_type["kind"] == "dynamic_trait_object"
    principal = pool_entry(doc, "predicates", self_type["principal_predicate"])
    assert principal["kind"] == "trait" and principal["generic_args"] == []
    owner = pool_entry(doc, "definitions", principal["def_id"])
    assert declaration["source_environment"]["generic_parent"] == {
        "definition": {"crate": owner["crate"], "index": owner["index"]}, "parameter_count": 1}
    assert not any(row["instance_id"] == target["instance_id"] for row in doc["compiler_instance_abis"])

def walk(value):
    if isinstance(value, dict):
        yield value
        for child in value.values():
            yield from walk(child)
    elif isinstance(value, list):
        for child in value:
            yield from walk(child)

calls = [node for node in walk(doc["bodies"])
         if node.get("kind") == "source_instance" and node.get("instance_id") in virtual_targets]
assert calls, "the MIR callsite lost its exact source Virtual operation"
assert {call["instance_id"] for call in calls} == set(virtual_targets)
for call in calls:
    assert set(call) == {"kind", "function_type", "instance_id"}
    target = virtual_targets[call["instance_id"]]
    function = pool_entry(doc, "types", call["function_type"])["shape"]
    assert function["kind"] == "function_definition" and function["def_id"] == target["def_id"]
    assert function["generic_args"] == target["generic_args"]
# An opaque input has no compiler-created concrete vtable target. The source
# Virtual identity/slot drives runtime selection; its absence remains Unsupported.
assert not any(row.get("resolved") is not None and row.get("original_instance_id") in virtual_targets
               for row in doc["compiler_runtime_queries"]["virtual"])

assert "status" not in scope
assert "unresolved_obligations" not in scope
print("validated exact abstract virtual dispatch identity with runtime target demand left open")
