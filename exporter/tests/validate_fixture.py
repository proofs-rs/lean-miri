#!/usr/bin/env python3
"""Validate the structural evidence that the MIR fixture must export."""
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "tools"))
from mir_json import load_mir_document, pool_entry

doc = load_mir_document(sys.argv[1])
assert doc["schema"] == "lean-miri-rustc-mir"
assert doc["schema_version"] == 5
assert doc["producer"]["rustc_commit"] == "8144389c895da997dbdecaa635e41d6a50be6ffd"
assert doc["producer"]["miri_commit"] == "7fa591d7d4dd9af8154becbc8332f8096f8323b1"
assert "completeness" not in doc
assert all(isinstance(name, str) for name in doc["files"])
assert len(doc["files"]) == len(set(doc["files"])), "duplicate filename spellings"
for span in doc["spans"]:
    assert type(span["file"]) is int and 0 <= span["file"] < len(doc["files"])
for body in doc["bodies"]:
    for span in body["backtrace_spans"]:
        filename = span["source_position"]["filename"]
        assert type(filename) is int and 0 <= filename < len(doc["files"])
type_nodes = {node["type_id"]: node for node in doc["types"]}
assert type_nodes, "compilation-scoped type graph missing"
assert sorted(type_nodes) == list(range(len(type_nodes))), "type IDs must be session-local monotonic IDs"
assert all("shape" in node and "layout" in node for node in type_nodes.values())
assert {node["shape"].get("adt_kind") for node in type_nodes.values() if node["shape"].get("kind") == "adt"} == {
    "struct", "union", "enum"
}
assert any(node["shape"].get("unsigned_kind") == "u32" for node in type_nodes.values())
assert any(node["shape"].get("signed_kind") == "isize" for node in type_nodes.values())
tag_encodings = [
    pool_entry(doc, "layouts", node["layout"])["variants"]["tag_encoding"]
    for node in type_nodes.values()
    if node["layout"] is not None
    and pool_entry(doc, "layouts", node["layout"]).get("variants", {}).get("kind") == "multiple"
]
assert tag_encodings and all("status" not in tag for tag in tag_encodings)
assert any(tag["kind"] == "direct" for tag in tag_encodings), "direct enum tag encoding missing"
niche_tags = [tag for tag in tag_encodings if tag["kind"] == "niche"]
assert niche_tags, "niche enum tag encoding missing"
assert all(
    isinstance(tag["untagged_variant"], int)
    and set(tag["niche_variants"]) == {"start", "end"}
    and isinstance(tag["niche_variants"]["start"], int)
    and isinstance(tag["niche_variants"]["end"], int)
    and isinstance(tag["niche_start"], str)
    and tag["niche_start"].isdecimal()
    for tag in niche_tags
), "niche tag payload must preserve exact range indices and u128 value"

TYPE_REF_FIELDS = {"type", "element", "pointee", "base", "self_type", "source_type",
                   "target_type", "input_type", "output_type", "return_type", "function_type"}
TYPE_REF_ARRAYS = {"elements", "inputs", "argument_types", "extra_argument_types"}

def _walk_type_refs(value):
    if isinstance(value, dict):
        for key, child in value.items():
            if key in TYPE_REF_FIELDS and isinstance(child, int):
                yield child
            elif key in TYPE_REF_ARRAYS and isinstance(child, list):
                yield from (entry for entry in child if isinstance(entry, int))
            yield from _walk_type_refs(child)
    elif isinstance(value, list):
        for child in value:
            yield from _walk_type_refs(child)

def check_type_refs(value):
    for type_id in _walk_type_refs(value):
        assert type_id in type_nodes, f"dangling type reference {type_id}"

check_type_refs([doc["bodies"], doc["instances"], doc["allocations"]])
check_type_refs(doc["types"])
bodies = {root["def_path"]: root for root in doc["body_roots"]}
assert {
    "exercise", "make_link", "direct_tag_value", "promoted_ref", "byte_string", "pointer_slice",
    "as_trait_object", "as_drop_trait_object", "call_trait_object",
    "STATIC_DATA", "TLS_WORD", "read_tls",
}.issubset(bodies)
assert bodies["promoted_ref"]["promoted_bodies"], "promoted MIR body missing"
assert bodies["STATIC_DATA"]["is_static"] and not bodies["STATIC_DATA"]["thread_local_static"]
assert bodies["TLS_WORD"]["is_static"] and bodies["TLS_WORD"]["thread_local_static"]

exercise = pool_entry(doc, "bodies", bodies["exercise"]["body"])
assert exercise["locals"] and all("type" in local and "layout" in local for local in exercise["locals"])
assert "status" not in exercise["phase"]
assert exercise["phase"]["kind"] in ("built", "analysis", "runtime")
terminators = [bb["terminator"]["kind"] for bb in exercise["basic_blocks"] if bb["terminator"]]
assert any(term["variant"] == "SwitchInt" for term in terminators), "loop branch missing"
assert any(term["variant"] == "Goto" for term in terminators), "loop backedge missing"
calls = [term for term in terminators if term["variant"] == "Call"]
assert calls
assert all(
    "status" not in call["call_source"]
    and call["call_source"]["kind"] in (
        "overloaded_operator", "match_comparison", "miscellaneous_desugaring", "clone_or_use", "normal_call"
    )
    for call in calls
)
resolutions = [term["resolution"] for term in calls]
assert any(r.get("kind") == "resolved_instance" and pool_entry(doc, "instances", r["instance_id"]).get("def_path") == "id" for r in resolutions), "generic id::<u32> instance missing"
atomic = [r for r in resolutions if r.get("kind") == "resolved_instance" and "fetch_add" in pool_entry(doc, "instances", r["instance_id"]).get("def_path", "")]
assert atomic and pool_entry(doc, "fn_abis", atomic[0]["fn_abi"])["arguments"], "atomic call and FnAbi missing"
assert pool_entry(doc, "fn_abis", atomic[0]["fn_abi"])["calling_convention"] == {"kind": "rust"}
for argument in [pool_entry(doc, "fn_abis", atomic[0]["fn_abi"])["return"], *pool_entry(doc, "fn_abis", atomic[0]["fn_abi"])["arguments"]]:
    mode = argument["mode"]
    if mode["kind"] == "Direct":
        assert "status" not in mode["attributes"]["arg_extension"]
instances = {instance["instance_id"]: instance for instance in doc["instances"]}
assert len(instances) == len(doc["instances"]), "instance IDs must be unique"
assert all(r.get("instance_id") in instances for r in resolutions if r.get("kind") == "resolved_instance")
id_instance = next(
    instance
    for instance in instances.values()
    if instance.get("def_path") == "id"
    and instance.get("kind") == "instance_mir"
)
assert pool_entry(doc, "bodies", id_instance["body"])["instance_id"] == id_instance["instance_id"]
assert id_instance["instance_kind"] == {"kind": "item", "def_id": id_instance["def_id"]}
assert any(type_nodes[local["type"]]["display"] == "u32" for local in pool_entry(doc, "bodies", id_instance["body"])["locals"])
assert not any(
    (pool_entry(doc, "type_constants", node["shape"]["length"]).get("kind") if "length" in node["shape"] else None) == "parameter"
    for node in type_nodes.values()
), "uninstantiated generic constants must not enter a successful export"
array_instance = next(
    instance
    for instance in instances.values()
    if instance.get("def_path") == "array_len"
    and instance.get("kind") == "instance_mir"
)
assert pool_entry(doc, "bodies", array_instance["body"])["instance_id"] == array_instance["instance_id"]
const_arg = pool_entry(doc, "type_constants", next(arg["value"] for arg in array_instance["generic_args"] if arg["kind"] == "const"))
assert const_arg["kind"] == "value" and const_arg["value"] == {
    "bits_unsigned": "3", "kind": "leaf", "size_bytes": 8
}, "monomorphized generic const argument must be structurally exported"
assert any(
    instance.get("kind") == "intrinsic_dispatch"
    and "status" not in instance
    and instance.get("instance_kind", {}).get("kind") == "intrinsic"
    and instance.get("fallback_instance") is None
    and instance.get("reason") == "Miri executes intrinsic semantics outside a MIR body"
    for instance in instances.values()
), "intrinsic source identity and non-MIR dispatch boundary must be explicit"
assert any(
    instance.get("kind") == "virtual_dispatch_target"
    and "status" not in instance
    and instance.get("body_status") == "not_applicable"
    and "status" not in pool_entry(doc, "fn_abis", instance["virtual_identity"]["fn_abi"])
    for instance in instances.values()
), "virtual dispatch must retain exact non-body identity and ABI evidence"

serialized = json.dumps(exercise)
binary_ops = [
    statement["kind"]["rvalue"]
    for block in exercise["basic_blocks"]
    for statement in block["statements"]
    if statement["kind"].get("rvalue", {}).get("kind") == "BinaryOp"
]
assert binary_ops and all(
    "status" not in item["operator"] and isinstance(item["operator"]["kind"], str)
    for item in binary_ops
)
unary_ops = [
    statement["kind"]["rvalue"]
    for block in exercise["basic_blocks"]
    for statement in block["statements"]
    if statement["kind"].get("rvalue", {}).get("kind") == "UnaryOp"
]
assert unary_ops and all("status" not in item["operator"] for item in unary_ops)
retags = [
    statement["kind"]["rvalue"]["retag"]
    for block in exercise["basic_blocks"]
    for statement in block["statements"]
    if statement["kind"].get("rvalue", {}).get("kind") == "Use"
]
assert retags and all(
    "status" not in retag
    and retag["kind"] in ("yes", "no")
    and retag["performs_retag"] == (retag["kind"] == "yes")
    for retag in retags
)
reference_regions = [
    statement["kind"]["rvalue"]["region"]
    for body in doc["bodies"]
    for block in body["basic_blocks"]
    for statement in block["statements"]
    if statement["kind"].get("rvalue", {}).get("kind") == "Ref"
]
assert reference_regions and all(
    "status" not in region and region["kind"] in ("erased", "static", "bound", "early_parameter", "late_parameter", "placeholder")
    for region in reference_regions
)
assert '"kind": "Deref"' in serialized, "unsafe raw-pointer dereference projection missing"
assert '"active_union_field": 0' in serialized, "union active-field index missing"
assert "PointerExposeProvenance" in serialized, "pointer-to-integer cast kind missing"
assert "Copy" in serialized and "Move" in serialized


def has_cycle(type_id, active, visited):
    if type_id in active:
        return True
    if type_id in visited:
        return False
    active.add(type_id)
    for ref in _walk_type_refs(type_nodes[type_id]["shape"]):
        if has_cycle(ref, active, visited):
            return True
    active.remove(type_id)
    visited.add(type_id)
    return False

assert any(has_cycle(type_id, set(), set()) for type_id in type_nodes), "recursive ADT type graph cycle missing"
assert "type_display" not in serialized, "ADT fields must carry structured type nodes"
assert '"field_shuffle_seed":' in json.dumps(type_nodes), "repr/layout randomization input missing"
assert '"regular_bits":' in json.dumps(doc["fn_abis"]), "FnAbi attributes must be structurally represented"
assert '"attributes_debug":' not in serialized, "FnAbi attributes must not rely on debug-only strings"
assert '"source_instance_kind"' in serialized, "body source instance kind must be structured"
fn_signatures = [node["shape"]["signature"] for node in type_nodes.values() if "signature" in node["shape"]]
assert fn_signatures and all(
    isinstance(signature["safety"], dict)
    and signature["safety"]["kind"] in ("safe", "unsafe")
    and isinstance(signature["abi"], dict)
    and "status" not in signature["abi"]
    for signature in fn_signatures
), "function signatures must carry typed safety and ExternAbi tags"

allocations = {allocation["allocation_id"]: allocation for allocation in doc["allocations"]}
assert len(allocations) == len(doc["allocations"]), "allocation IDs must be unique"
assert all("status" not in allocation for allocation in allocations.values()), "fixture allocation unexpectedly incomplete"
memory_allocations = [allocation for allocation in allocations.values() if allocation.get("kind") == "memory"]
assert any(allocation["bytes_hex"] == "6c65616e2d6d697269" for allocation in memory_allocations), "byte-string allocation contents missing"
assert any(
    relocation.get("immutable") is True and relocation.get("shared_ref") is True
    for allocation in memory_allocations
    for relocation in allocation["relocations"]
), "CtfeProvenance flags missing from allocation relocation"
static = next(allocation for allocation in allocations.values() if allocation.get("kind") == "static")
assert static["thread_local"] is False
assert static["initializer"]["bytes_hex"] == "0b0000000d000000"
vtable_queries = [
    query["vtable_metadata"]
    for query in doc["compiler_vtable_queries"]
    if query.get("vtable_metadata", {}).get("entries") is not None
]
assert any(
    entry.get("kind") == "method" and pool_entry(doc, "instances", entry["instance_id"]).get("def_path") == "<ValueCell as ValueSource>::get"
    for vtable in vtable_queries for entry in vtable["entries"]
)
drop_entry = next(
    entry
    for vtable in vtable_queries for entry in vtable["entries"]
    if entry.get("kind") == "drop_in_place"
)
drop_glue = instances[drop_entry["instance_id"]]
assert drop_glue["instance_kind"]["kind"] == "shim"
assert drop_glue["instance_kind"]["shim_kind"] == "drop_glue"
assert "status" not in drop_glue and drop_glue["kind"] == "instance_mir"

# A TLS `ThreadLocalRef` contains exact compiler metadata. Runtime allocation
# and destruction are interpreter semantics, not synthetic exporter payload.
tls_refs = []
for block in pool_entry(doc, "bodies", bodies["read_tls"]["body"])["basic_blocks"]:
    for statement in block["statements"]:
        value = statement["kind"].get("rvalue")
        if value and value.get("kind") == "ThreadLocalRef":
            tls_refs.append(value)
assert len(tls_refs) == 1
tls = tls_refs[0]
assert "status" not in tls
assert tls["global_info"]["is_static"] is True
assert tls["global_info"]["thread_local"] is True
assert pool_entry(doc, "definitions", tls["def_id"])["crate"] >= 0 and pool_entry(doc, "definitions", tls["def_id"])["index"] >= 0
assert tls["initializer"]["allocation"]["bytes_hex"] == "11000000"
assert "runtime_allocation" not in tls

def check_allocation_refs(value):
    if isinstance(value, dict):
        if set(value) == {"allocation_id"}:
            assert value["allocation_id"] in allocations, f"dangling allocation reference {value}"
        for child in value.values():
            check_allocation_refs(child)
    elif isinstance(value, list):
        for child in value:
            check_allocation_refs(child)

check_allocation_refs([doc["bodies"], doc["instances"], doc["allocations"]])

# Every encountered operation in a successful document has typed semantics.
for body in doc["bodies"]:
    for block in body["basic_blocks"]:
        for statement in block["statements"]:
            assert statement["kind"].get("variant") and "status" not in statement["kind"]
        if block["terminator"]:
            assert block["terminator"]["kind"].get("variant") and "status" not in block["terminator"]["kind"]

print(f"validated {len(bodies)} local MIR bodies, {len(instances)} reachable instances, {len(allocations)} allocations, exact rustc pin")
