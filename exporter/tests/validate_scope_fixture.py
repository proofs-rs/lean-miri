#!/usr/bin/env python3
"""Every semantic payload in a successful rooted export must be complete."""
from copy import deepcopy
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "tools"))
from mir_json import load_mir_document

doc = load_mir_document(sys.argv[1])
scope = doc["selected_scope"]
assert doc["completeness"] == {"status": "complete"}
assert scope["kind"] == "rooted_structural_closure"
assert scope["semantics"] == "structural_export_closure_only"
assert scope["status"] == "complete"
assert "unresolved_obligations" not in scope
assert "retained_catalog_obligations" not in scope
assert scope["roots"] == [{"def_path": "add_one", "def_id": doc["bodies"][0]["def_id"]}]
assert len(doc["bodies"]) == 1 and doc["bodies"][0]["def_path"] == "add_one"


def validate(document):
    catalogs = {
        key: {node[key] for node in document[table]}
        for key, table in [("type_id", "types"), ("allocation_id", "allocations"),
                           ("instance_id", "instances")]
    }
    seen = set()

    def visit(value):
        if not isinstance(value, (dict, list)) or id(value) in seen:
            return
        seen.add(id(value))
        if isinstance(value, dict):
            if value.get("status") == "debug_payload":
                return
            if "status" in value:
                assert value["status"] in {"supported", "complete"}, value
            for key, child in value.items():
                if key in catalogs and isinstance(child, int):
                    assert child in catalogs[key], f"missing {key} {child}"
                visit(child)
        else:
            for child in value:
                visit(child)

    visit(document)


validate(doc)
# Unused failures are failures of the complete export contract too.
for failure in ("unsupported", "unknown", "incomplete"):
    invalid = deepcopy(doc)
    invalid["unused_catalog"] = {"status": failure}
    try:
        validate(invalid)
    except AssertionError:
        pass
    else:
        raise AssertionError(f"unreferenced {failure} payload was accepted")
print("validated a complete rooted export and all emitted semantic catalogs")
