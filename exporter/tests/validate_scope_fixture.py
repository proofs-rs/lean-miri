#!/usr/bin/env python3
"""Validate that rooted export admits only a closed structural graph."""
import json
import sys
from copy import deepcopy
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "tools"))
from mir_json import load_mir_document

doc = load_mir_document(sys.argv[1])
scope = doc["selected_scope"]
assert doc["completeness"]["status"] == "incomplete"
assert scope["kind"] == "rooted_structural_closure"
assert scope["semantics"] == "structural_export_closure_only"
assert scope["status"] == "complete", scope["unresolved_obligations"]
assert scope["unresolved_obligations"] == []
assert scope["roots"] == [{"def_path": "add_one", "def_id": doc["bodies"][0]["def_id"]}]
assert len(doc["bodies"]) == 1 and doc["bodies"][0]["def_path"] == "add_one"

# The document also carries compiler-query catalogs whose instances are not
# reachable from this selected root. Check only the executable structural
# closure, rather than rejecting unrelated, demand-local catalog records.
tables = {
    "type_id": "types",
    "allocation_id": "allocations",
    "instance_id": "instances",
}
def reachable_obligations(document):
    pending = []
    seen = set()
    obligations = []

    def visit(value):
        if isinstance(value, dict):
            if value.get("status") == "debug_payload":
                return
            status = value.get("status")
            if status is not None and status != "supported":
                obligations.append((status, value.get("kind")))
            for key, child in value.items():
                if key in {"normalization_template", "compiler_facts", "constructor_identity"}:
                    continue
                if key in tables and isinstance(child, int):
                    pending.append((key, child))
                visit(child)
        elif isinstance(value, list):
            for child in value:
                visit(child)

    visit(document["bodies"][0]["entry_instance"])
    while pending:
        kind, identifier = pending.pop()
        reference = (kind, identifier)
        if reference in seen:
            continue
        seen.add(reference)
        table = document[tables[kind]]
        entry = next(
            (node for node in table if node.get(kind) == identifier),
            None,
        )
        assert entry is not None, f"missing reachable {kind} {identifier}"
        visit(entry)
    return obligations, seen


obligations, reachable = reachable_obligations(doc)
assert obligations == [], obligations

# Prove that reachable failures remain structural while an unrelated catalog
# record does not poison this selected closure.
reachable_negative = deepcopy(doc)
instance_refs = {identifier for kind, identifier in reachable if kind == "instance_id"}
target = next(node for node in reachable_negative["instances"] if node["instance_id"] in instance_refs)
target["status"] = "unsupported"
assert reachable_obligations(reachable_negative)[0], "reachable failure was ignored"
catalog_negative = deepcopy(doc)
catalog_negative["instances"].append({"instance_id": 2**31, "status": "unknown"})
assert reachable_obligations(catalog_negative)[0] == [], "unreferenced catalog row poisoned closure"
assert all(node.get("shape", {}).get("status") == "supported" for node in doc["types"])
assert any(
    statement["kind"].get("rvalue", {}).get("kind") == "BinaryOp"
    for block in doc["bodies"][0]["basic_blocks"]
    for statement in block["statements"]
)
print("validated rooted structural closure for add_one")
