#!/usr/bin/env python3
"""Produce malformed source identity controls, then run the production decoder."""
import argparse
import copy
import json
from pathlib import Path
import subprocess

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("input", type=Path)
parser.add_argument("--output", required=True, type=Path)
parser.add_argument("--lake", default="lake")
args = parser.parse_args()
root = Path(__file__).resolve().parents[1]
source = json.loads(args.input.read_text())
virtuals = [row for row in source["instances"]
            if row["instance_kind"]["kind"] == "virtual" and row["kind"] == "identity_only"]
assert len(virtuals) >= 2, "control needs actual covered Virtual identities"
selected = virtuals[0]
other = next(row for row in virtuals if row["def_id"] != selected["def_id"])
args.output.mkdir(parents=True, exist_ok=True)
paths = []
for label in ("bodyless-item", "wrong-virtual-definition", "bodyless-shim"):
    changed = copy.deepcopy(source)
    node = changed["instances"][selected["instance_id"]]
    if label == "bodyless-item":
        node["instance_kind"] = {"kind": "item", "def_id": node["def_id"]}
    elif label == "bodyless-shim":
        node["instance_kind"] = {"kind": "shim", "shim_kind": "vtable", "def_id": node["def_id"]}
    else:
        node["instance_kind"]["def_id"] = node["def_id"] = other["def_id"]
    path = args.output / (label + ".json")
    path.write_text(json.dumps(changed))
    paths.append(str(path.resolve()))
subprocess.run([args.lake, "env", "lean", "--run", "tests/compiler_queries/VirtualSourceDecodeControls.lean",
                str(args.input.resolve()), *paths], cwd=root, check=True)
