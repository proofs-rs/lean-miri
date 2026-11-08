#!/usr/bin/env python3
"""Check a complete abstract virtual identity without inventing concrete targets."""
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "tools"))
from mir_json import load_mir_document

doc = load_mir_document(sys.argv[1])
scope = doc["selected_scope"]
assert "completeness" not in doc
assert scope["kind"] == "rooted_structural_closure"
assert scope["semantics"] == "structural_export_closure_only"
assert scope["roots"][0]["def_path"] == "call_trait_object"

virtual_targets = [
    item for item in doc["instances"]
    if item.get("kind") == "virtual_dispatch_target"
]
assert virtual_targets, "the source virtual instance identity was dropped"
for target in virtual_targets:
    assert "status" not in target
    assert target["body_status"] == "not_applicable"
    assert "status" not in target["virtual_identity"]
    assert "status" not in target["virtual_identity"]["fn_abi"]

def walk(value):
    if isinstance(value, dict):
        yield value
        for child in value.values():
            yield from walk(child)
    elif isinstance(value, list):
        for child in value:
            yield from walk(child)

calls = [
    node for node in walk(doc["bodies"])
    if node.get("virtual_resolution", {}).get("instance_id") is not None
]
assert calls, "the MIR callsite lost its virtual operation"
for call in calls:
    assert call["kind"] == "virtual_dispatch"
    assert isinstance(call.get("dispatch_slot"), int)
    assert isinstance(call["virtual_resolution"].get("generic_args"), list)
    # An opaque input has no compiler-created concrete vtable candidate.
    # Runtime selection remains demand-local and returns Unsupported when the
    # actual receiver's table or matching method entry is absent.
    resolution = call["virtual_resolution"]
    assert "candidate_query_ids" not in resolution
    index = doc["compiler_virtual_candidates"]
    assert index["schema_version"] == 1
    assert len(index["by_instance"]) == len(doc["instances"])
    assert index["by_instance"][resolution["instance_id"]] == []

assert "status" not in scope
assert "unresolved_obligations" not in scope
print("validated exact abstract virtual dispatch identity with runtime target demand left open")
