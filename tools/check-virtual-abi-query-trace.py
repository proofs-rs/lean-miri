#!/usr/bin/env python3
"""Audit explicit Virtual ABI calls, including identity serialization."""
import argparse
from pathlib import Path
import re

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("oracle", type=Path)
parser.add_argument("candidate", type=Path)
parser.add_argument("--keys", type=int, default=7)
parser.add_argument("--unsupported-name", default="tracked")
args = parser.parse_args()
pattern = re.compile(r"^lean_miri_instance_abi_call route=(\S+) queried=(true|false) instance=(.*)$")


def load(path):
    rows = []
    for line in path.read_text().splitlines():
        if not line.startswith("lean_miri_instance_abi_call "):
            continue
        match = pattern.fullmatch(line)
        assert match, "malformed explicit ABI trace: " + line
        if "def: Virtual(" in match[3]:
            rows.append((match[1], match[2] == "true", match[3]))
    assert rows, "missing Virtual query instrumentation"
    return rows


oracle, candidate = load(args.oracle), load(args.candidate)
keys = {key for _, queried, key in oracle if queried}
residual = {key for key in keys if f"::{args.unsupported_name})" in key}
covered = keys - residual
assert len(covered) == args.keys and len(residual) == 1, (len(covered), len(residual))
for key in sorted(covered):
    before = sum(queried and actual == key for _, queried, actual in oracle)
    after = sum(queried and actual == key for _, queried, actual in candidate)
    identity = sum(route == "identity-source" and not queried and actual == key
                   for route, queried, actual in candidate)
    assert before > 0 and after == 0 and identity > 0, (key, before, after, identity)
    print(f"PASS Virtual complete key explicit calls {before}->0; source identity requests {identity}: {key}")
for key in residual:
    assert any(queried and actual == key for _, queried, actual in candidate)
    assert not any(not queried and actual == key for _, queried, actual in candidate)
print("PASS tracked caller-location residual retains explicit ABI query")
print("Scope: explicit exporter calls, including identity route; rustc-internal query execution is separate")
