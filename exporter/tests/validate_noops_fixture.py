#!/usr/bin/env python3
"""Check pinned MIR no-op tags and their exact invocation provenance."""

import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "tools"))
from mir_json import load_mir_document

doc = load_mir_document(sys.argv[1])
assert doc["producer"]["rustc_commit"] == "8144389c895da997dbdecaa635e41d6a50be6ffd"
assert doc["completeness"]["status"] == "incomplete"
assert doc["selected_scope"]["semantics"] == "structural_export_closure_only"
assert doc["selected_scope"]["status"] == "complete"
assert doc["invocation"]["kind"] == "direct_rustc_driver"
assert "-Cinstrument-coverage" in doc["invocation"]["rustc_args"]
assert doc["invocation"]["rustc_args_fingerprint_fnv1a64"]
body = next(body for body in doc["bodies"] if body["def_path"] == "covered")
coverage = [
    statement["kind"]
    for block in body["basic_blocks"]
    for statement in block["statements"]
    if statement["kind"].get("variant") == "Coverage"
]
assert coverage, "-Cinstrument-coverage did not produce a Coverage statement"
assert all(
    item["status"] == "supported"
    and item["execution"] == "no_op"
    and item["coverage"]["status"] == "supported"
    and item["coverage"]["kind"] in ("point", "block_marker", "virtual_counter")
    for item in coverage
)
print("validated typed coverage no-op and complete rooted structural scope")
