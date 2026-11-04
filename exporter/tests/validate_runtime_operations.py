#!/usr/bin/env python3
"""Check source operation requirements, independently of a successful trace."""
import pathlib
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[2] / "tools"))
from mir_json import load_mir_document

document = load_mir_document(sys.argv[1])
queries = document["compiler_runtime_queries"]
rows = queries["types"]
by_id = {row["input_type_id"]: row for row in rows}
assert len(by_id) == len(rows), "operation promotion duplicated a type row"

def type_id(name):
    types = [ty for ty in document["types"]
             if ty.get("shape", {}).get("def_path", "").split("::")[-1] == name]
    assert len(types) == 1, (name, len(types))
    return types[0]["type_id"]

full = queries.get("type_query_schema") is None
if not full:
    assert queries["type_query_schema"] == "source_operations_v1"
    assert type_id("BorrowOnly") not in by_id, "borrow-only type expanded runtime constructors"
for name, operations in [
    ("OwnedDrop", ["mut_pointer_type", "mut_reference_type", "drop_glue"]),
    ("EmptyDyn", ["mut_pointer_type", "mut_reference_type", "drop_glue"]),
]:
    row = by_id[type_id(name)]
    for operation in operations:
        assert row[operation]["status"] == "supported", (name, operation)
print("PASS: borrow-only pruning, Box pointer, drop reference/glue, empty dyn drop, unique rows")
