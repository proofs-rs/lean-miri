#!/usr/bin/env python3
"""Check that opaque virtual dispatch is represented structurally and fails on demand."""
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "tools"))
from mir_json import load_mir_document

doc = load_mir_document(sys.argv[1])
scope = doc["selected_scope"]
assert doc["completeness"]["status"] == "incomplete"
assert scope["kind"] == "rooted_structural_closure"
assert scope["semantics"] == "structural_export_closure_only"
assert scope["roots"][0]["def_path"] == "call_trait_object"

virtual_targets = [
    item for item in doc["instances"]
    if item.get("kind") == "virtual_dispatch_target"
]
assert virtual_targets, "the source virtual instance identity was dropped"
for target in virtual_targets:
    assert target["status"] == "supported"
    assert target["body_status"] == "not_applicable"
    assert target["virtual_identity"]["status"] == "supported"
    assert target["virtual_identity"]["fn_abi"]["status"] == "supported"

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
    if node.get("virtual_resolution", {}).get("status") == "supported"
]
assert calls, "the MIR callsite lost its virtual operation"
for call in calls:
    assert call["kind"] == "virtual_dispatch"
    assert isinstance(call.get("dispatch_slot"), int)
    assert isinstance(call["virtual_resolution"].get("generic_args"), list)
    # An opaque input has no compiler-created concrete vtable candidate.
    # Runtime selection remains demand-local and returns Unsupported when the
    # actual receiver's table or matching method entry is absent.
    assert call["virtual_resolution"].get("candidate_query_ids") == []

assert not any(
    item.get("status") == "unknown" and item.get("kind") == "virtual_dispatch_target"
    for item in scope["unresolved_obligations"]
), "abstract virtual identity must not poison structural closure"
print("validated exact abstract virtual dispatch identity with runtime target demand left open")
