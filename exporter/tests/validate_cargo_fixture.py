#!/usr/bin/env python3
"""Check Cargo output and external material/raw-source instance ownership."""
import glob
import json
import os
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "tools"))
from mir_json import load_mir_inspection_document as load_mir_document, pool_entry

root = Path(sys.argv[1])
documents = {}
for path in glob.glob(str(root / "**/lean-miri-mir/*.json"), recursive=True):
    doc = load_mir_document(path)
    crate = doc.get("invocation", {}).get("crate_name")
    if crate:
        documents[crate] = doc

assert "exporter_helper" in documents, f"dependency crate MIR JSON absent: {list(documents)}"
assert "exporter_cargo_app" in documents, f"application crate MIR JSON absent: {list(documents)}"
assert "build_script_build" not in documents, "host build scripts are not guest input"
app = documents["exporter_cargo_app"]
instances = [
    item for item in app["instances"]
    if item.get("kind") == "instance_mir" and "status" not in item
]
# A DefId/path can have several distinct generic instantiations. Discovery
# chooses the concrete full argument key.
types = {item["type_id"]: item for item in app["types"]}
def u32_argument(instance):
    args = instance.get("generic_args", [])
    return len(args) == 1 and args[0].get("kind") == "type" and types[args[0]["value"]]["shape"] == {"kind": "uint", "unsigned_kind": "u32"}
wrap = next(item for item in instances if item["def_path"].endswith("::wrap") and u32_argument(item))
identity = next(item for item in instances if item["def_path"].endswith("::identity") and item["generic_args"] == wrap["generic_args"])
assert identity["instance_id"] != wrap["instance_id"]
assert pool_entry(app, "bodies", wrap["body"])["instance_id"] == wrap["instance_id"]
assert pool_entry(app, "bodies", identity["body"])["instance_id"] == identity["instance_id"]

types = {item["type_id"]: item for item in app["types"]}

def material_local_displays(instance):
    body = pool_entry(app, "bodies", instance["body"])
    assert body["body_kind"] == "material", "this fixture role requires material MIR"
    return {types[local["type"]]["display"] for local in body["locals"]}


assert "u32" in material_local_displays(wrap), "external generic wrapper MIR lost its u32 substitution"
wrap_body = pool_entry(app, "bodies", wrap["body"])
wrap_calls = [block["terminator"]["kind"] for block in wrap_body["basic_blocks"]
              if block["terminator"]["kind"]["variant"] == "Call"]
assert len(wrap_calls) == 1 and wrap_calls[0]["resolution"]["kind"] == "source_instance"
assert "fn_abi" not in wrap_calls[0]["resolution"]
assert wrap_calls[0]["resolution"]["instance_id"] == identity["instance_id"], "wrapper must call the exact identity::<u32> instance"

# The transitive identity callee is compiler-owned source syntax. Validate its
# complete source operation and actual type binding without instantiating MIR
# in this Python inspection adapter.
seed = pool_entry(app, "bodies", identity["body"])
assert seed["body_kind"] == "copy_template"
assert set(seed) == {"body_kind", "template_id", "instance_id", "generic_args", "promoted_bodies"}
assert seed["generic_args"] == identity["generic_args"] == wrap["generic_args"]
assert seed["promoted_bodies"] == [] and u32_argument(identity)
assert type(seed["template_id"]) is int and 0 <= seed["template_id"] < len(app["mir_templates"])
source = app["mir_templates"][seed["template_id"]]
assert source["source_promoted"] is None
assert source["source_def_id"] == identity["def_id"] and source["def_path"] == "exporter_helper::identity"
assert identity["instance_kind"] == {"kind": "item", "def_id": identity["def_id"]}
declaration = pool_entry(app, "definitions", source["source_def_id"])
assert declaration["raw_path"]["components"] == [
    {"kind": "crate_root", "name": "exporter_helper", "disambiguator": 0},
    {"kind": "value", "name": "identity", "disambiguator": 0}
], "source declaration must be the external helper identity function"
assert isinstance(source["template"], str)
template = json.loads(source["template"])
assert template["parameters"] == ["type"]
assert template["types"] == [{"kind": "parameter", "sort": "type", "index": 0}]
skeleton = template["skeleton"]
assert skeleton["phase"] == "runtime_optimized"
assert skeleton["argument_count"] == 1 and skeleton["spread_argument"] is None
assert skeleton["locals"] == [0, 0], "identity return/argument locals must bind to the same raw type parameter"
assert len(source["local_sources"]) == 2
assert len(skeleton["blocks"]) == 1
block = skeleton["blocks"][0]
assert block["cleanup"] is False and len(block["statements"]) == 1
assert block["statements"][0]["kind"] == {
    "kind": "assign", "destination": 0,
    "value": {"kind": "use", "operand": {"kind": "move", "local": 1}, "retag": "yes"}
}, "raw identity source must move argument 1 into return local 0 with its exact retag"
assert block["terminator"]["kind"] == {"kind": "return"}
assert source["source_scopes"] == [{
    "scope": 0, "parent": None, "span": source["span"], "inlined": None, "inlined_parent_scope": None
}]
for info in [*source["local_sources"], block["statements"][0]["source"], block["terminator"]["source"]]:
    assert info["scope"] == 0
    pool_entry(app, "spans", info["span"])
for span in source["backtrace_spans"]:
    pool_entry(app, "spans", span["span"])
    filename = span["source_position"]["filename"]
    assert type(filename) is int and 0 <= filename < len(app["files"])
assert app["invocation"]["target_crate"] is True
assert app["producer"]["rustc_commit"] == "8144389c895da997dbdecaa635e41d6a50be6ffd"
assert list(root.rglob("*.rmeta")), "Cargo metadata output missing; wrapper must continue codegen/metadata emission"
assert list(root.rglob("*.rlib")), "Cargo codegen artifact missing; wrapper must continue beyond analysis"
if os.environ.get("MIRI_SYSROOT"):
    vector_len = next(
        item for item in instances
        if "Vec" in item.get("def_path", "") and item.get("def_path", "").endswith("::len")
    )
    assert pool_entry(app, "bodies", vector_len["body"])["instance_id"] == vector_len["instance_id"]
    assert any("Vec<u32>" in ty for ty in material_local_displays(vector_len)), "Miri sysroot std MIR was not monomorphized"
print(f"validated Cargo MIR for {len(documents)} crates and external generic wrapper and exact raw identity source binding")
