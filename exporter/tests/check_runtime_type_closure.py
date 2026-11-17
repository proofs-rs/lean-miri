#!/usr/bin/env python3
"""Check runtime type and vtable coverage for the nested vtable fixture."""

import os
import pathlib
import subprocess
import sys

root = pathlib.Path(__file__).resolve().parents[2]
sys.path.insert(0, str(root / "tools"))
from mir_json import load_mir_inspection_document as load_mir_document

document = load_mir_document(sys.argv[1])
late = [node for node in document["types"]
        if node.get("shape", {}).get("def_path", "").split("::")[-1] == "LateOnly"]
assert len(late) == 1, f"expected one LateOnly type node, got {len(late)}"
virtual_instances = [row for row in document["instances"]
                     if row.get("kind") == "virtual_dispatch_target"]
assert len(virtual_instances) == 2 and {row["def_path"] for row in virtual_instances} == {"LateTrait::call", "InnerTrait::inner"}
instances = {row["instance_id"]: row for row in document["instances"]}
arguments = [str(late[0]["type_id"])]
for virtual in virtual_instances:
    matches = [(binding, method) for binding in document["source_vtables"]["bindings"]
               for method in binding["methods"]
               if method["definition"] == virtual["def_id"] and method["instance_id"] is not None]
    assert len(matches) == 1, f"virtual instance {virtual['instance_id']} has {len(matches)} bindings"
    binding, method = matches[0]
    target = instances[method["instance_id"]]
    expected = {"LateTrait::call": "<Concrete as LateTrait>::call",
                "InnerTrait::inner": "<Inner as InnerTrait>::inner"}[virtual["def_path"]]
    assert target["kind"] == "instance_mir" and target["def_path"] == expected and isinstance(target.get("body"), int), target
    arguments.extend(str(value) for value in (binding["type_id"], binding["principal"],
                                              virtual["dispatch_slot"], method["instance_id"]))
subprocess.run([str(pathlib.Path(os.environ.get("ELAN_HOME", root / ".elan")) / "bin/lake"), "env", "lean", "--run",
                "exporter/tests/RuntimeTypeClosure.lean", sys.argv[1], *arguments],
               cwd=root, check=True)
