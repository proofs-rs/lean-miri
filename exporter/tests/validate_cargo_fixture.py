#!/usr/bin/env python3
"""Check Cargo wrapper output, encoded dependency MIR, and concrete instance MIR."""
import glob
import json
import os
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "tools"))
from mir_json import load_mir_document

root = Path(sys.argv[1])
documents = {}
for path in glob.glob(str(root / "**/lean-miri-mir/*.json"), recursive=True):
    doc = load_mir_document(path)
    crate = doc.get("invocation", {}).get("crate_name")
    if crate:
        documents[crate] = doc

assert "exporter_helper" in documents, f"dependency crate MIR JSON absent: {list(documents)}"
assert "exporter_cargo_app" in documents, f"application crate MIR JSON absent: {list(documents)}"
app = documents["exporter_cargo_app"]
instances = [
    item for item in app["instances"]
    if item.get("kind") == "instance_mir" and item.get("status") == "supported"
]
# A DefId/path can have several distinct generic instantiations. Discovery
# retains symbolic instances too; choose the concrete full argument key.
types = {item["type_id"]: item for item in app["types"]}
def u32_argument(instance):
    args = instance.get("generic_args", [])
    return len(args) == 1 and args[0].get("kind") == "type" and types[args[0]["value"]["type_id"]]["display"] == "u32"
wrap = next(item for item in instances if item["def_path"].endswith("::wrap") and u32_argument(item))
identity = next(item for item in instances if item["def_path"].endswith("::identity") and item["generic_args"] == wrap["generic_args"])
assert identity["instance_id"] != wrap["instance_id"]
assert wrap["body_instantiation"] == {"kind": "substituted_and_normalized", "status": "supported"}
assert identity["body_instantiation"]["status"] == "supported"

types = {item["type_id"]: item for item in app["types"]}

def local_displays(instance):
    return {
        types[local["type"]["type_id"]]["display"]
        for local in instance["body"]["locals"]
    }

assert "u32" in local_displays(wrap), "external generic wrapper MIR was not monomorphized"
assert "u32" in local_displays(identity), "transitive generic callee MIR was not monomorphized"
assert app["invocation"]["target_crate"] is True
assert app["producer"]["rustc_commit"] == "8144389c895da997dbdecaa635e41d6a50be6ffd"
assert list(root.rglob("*.rmeta")), "Cargo metadata output missing; wrapper must continue codegen/metadata emission"
assert list(root.rglob("*.rlib")), "Cargo codegen artifact missing; wrapper must continue beyond analysis"
if os.environ.get("MIRI_SYSROOT"):
    vector_len = next(
        item for item in instances
        if "Vec" in item.get("def_path", "") and item.get("def_path", "").endswith("::len")
    )
    assert vector_len["body_instantiation"]["status"] == "supported"
    assert any("Vec<u32>" in ty for ty in local_displays(vector_len)), "Miri sysroot std MIR was not monomorphized"
print(f"validated Cargo MIR for {len(documents)} crates and concrete external generic closure")
