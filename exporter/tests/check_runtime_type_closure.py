#!/usr/bin/env python3
"""Check exact runtime constructor coverage for the vtable-reached fixture."""

import json
import pathlib
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[2] / "tools"))
from mir_json import load_mir_document

document = load_mir_document(sys.argv[1])
late = [
    node for node in document["types"]
    if node.get("shape", {}).get("def_path", "").split("::")[-1] == "LateOnly"
]
assert len(late) == 1, f"expected one LateOnly type node, got {len(late)}"
late_id = late[0]["type_id"]
rows = document["compiler_runtime_queries"]["types"]
matches = [row for row in rows if row["input_type_id"] == late_id]
assert len(matches) == 1, f"type {late_id} has {len(matches)} runtime query rows"
virtual_instances = [
    row for row in document["instances"]
    if row.get("kind") == "virtual_dispatch_target"
]
assert len(virtual_instances) == 2, f"expected two reached virtual methods, got {len(virtual_instances)}"
virtual_rows = document["compiler_runtime_queries"]["virtual"]
for instance in virtual_instances:
    associated = [
        row for row in virtual_rows
        if row["original_instance_id"] == instance["instance_id"]
        and row["method_definition"] == instance["def_id"]
    ]
    assert associated, f"virtual instance {instance['instance_id']} lacks exact method rows"
    assert all(row["vtable_query"].get("query_id") is not None for row in associated)
print(f"PASS: LateOnly type {late_id} has a query row; {len(virtual_instances)} reached virtual methods have exact rows")
