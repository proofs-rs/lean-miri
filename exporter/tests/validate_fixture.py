#!/usr/bin/env python3
"""Validate the structural evidence that the MIR fixture must export."""
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "tools"))
from mir_json import load_mir_inspection_document as load_mir_document, pool_entry

doc = load_mir_document(sys.argv[1])
assert doc["schema"] == "lean-miri-rustc-mir"
assert doc["schema_version"] == 17
assert doc["compiler_coroutine_coverage"]["body_coroutines"] == [False] * len(doc["bodies"])
assert doc["compiler_coroutine_coverage"]["coroutines"] == []
assert doc["compiler_coroutine_coverage"]["auxiliary_bodies"] == []
assert doc["producer"]["rustc_commit"] == "8eb778d04094d3af4b26580cab327e0413eb1e02"
assert doc["producer"]["miri_commit"] == "93c45edea8b148a6b6f05ec9384449a04217143f"
assert "completeness" not in doc
assert all(isinstance(name, str) for name in doc["files"])
assert len(doc["files"]) == len(set(doc["files"])), "duplicate filename spellings"
for span in doc["spans"]:
    assert type(span["file"]) is int and 0 <= span["file"] < len(doc["files"])
assert doc["syntax_contexts"][0]["outer_expansion"] is None
for span in doc["spans"]:
    assert 0 <= span["runtime_file"] < len(doc["files"])
    assert 0 <= span["ctxt"] < len(doc["syntax_contexts"])
assert all("backtrace_spans" not in body for body in doc["bodies"])
type_nodes = {node["type_id"]: node for node in doc["types"]}
assert type_nodes, "compilation-scoped type graph missing"
assert sorted(type_nodes) == list(range(len(type_nodes))), "type IDs must be session-local monotonic IDs"
assert all("shape" in node and "source_layout" in node and "layout" not in node for node in type_nodes.values())
for node in type_nodes.values():
    assert node["source_layout"]["normalized_type"] in type_nodes
    if node["shape"].get("kind") == "adt":
        representation = node["shape"]["representation"]
        assert type(representation["flags_bits"]) is int
        assert not {"simd", "c", "rust", "packed", "transparent", "linear", "scalable",
                    "can_randomize_type_layout", "inhibit_enum_layout_optimization",
                    "inhibit_struct_field_reordering", "inhibit_newtype_abi_optimization"} & representation.keys()
assert {node["shape"].get("adt_kind") for node in type_nodes.values() if node["shape"].get("kind") == "adt"} == {
    "struct", "union", "enum"
}
assert any(node["shape"].get("unsigned_kind") == "u32" for node in type_nodes.values())
assert any(node["shape"].get("signed_kind") == "isize" for node in type_nodes.values())
enum_sources = [node for node in type_nodes.values() if node["shape"].get("adt_kind") == "enum"]
assert enum_sources and all(node["source_layout"]["variant_discriminants"] for node in enum_sources)
assert not {"layouts", "fn_abis", "compiler_vtable_queries"} & doc.keys()

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

def check_scalar_widths(value):
    if isinstance(value, dict):
        if value.get("kind") == "scalar" and "bits_unsigned" in value:
            size = value["size_bytes"]
            assert type(size) is int and size > 0, "scalar byte width must be positive"
            assert 0 <= int(value["bits_unsigned"]) < 2 ** (8 * size), "scalar bits exceed byte width"
        for child in value.values():
            check_scalar_widths(child)
    elif isinstance(value, list):
        for child in value:
            check_scalar_widths(child)

check_scalar_widths(doc)

check_type_refs([doc["bodies"], doc["instances"], doc["allocations"]])
check_type_refs(doc["types"])
bodies = {root["def_path"]: root for root in doc["body_roots"]}
assert {
    "exercise", "make_link", "direct_tag_value", "promoted_ref", "byte_string", "pointer_slice",
    "as_trait_object", "as_drop_trait_object", "call_trait_object",
    "read_tls",
}.issubset(bodies)
assert bodies["promoted_ref"]["promoted_bodies"], "promoted MIR body missing"
exercise = pool_entry(doc, "bodies", bodies["exercise"]["body"])
assert exercise["locals"]
for local in exercise["locals"]:
    assert set(local) == {"local", "type", "source_info"}
    assert local["type"] in type_nodes
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
assert atomic, "atomic call missing"
for call in atomic:
    source = doc["source_abi"]["definitions"][call["instance_id"]]
    assert source and source["signature"]["abi"]["kind"] == "rust"
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
    and instance["virtual_identity"]["function_type"] in type_nodes
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
assert doc["source_abi"]["definitions"], "ABI source signatures must be present"
assert '"attributes_debug":' not in serialized, "FnAbi attributes must not rely on debug-only strings"
def check_attribute_fields(value):
    if isinstance(value, dict):
        if "regular_bits" in value:
            assert set(value) == {"regular_bits", "arg_extension", "pointee_size_bytes", "pointee_align_bytes"}
        if "source_spelling" in value:
            raise AssertionError("canonical ExternAbi spelling must be derived from kind/unwind")
        for child in value.values():
            check_attribute_fields(child)
    elif isinstance(value, list):
        for child in value:
            check_attribute_fields(child)

check_attribute_fields(doc)
assert '"source_instance_kind"' not in serialized, "unused body source instance kind must be omitted"
fn_signatures = [node["shape"]["signature"] for node in type_nodes.values() if "signature" in node["shape"]]
assert fn_signatures and all(
    isinstance(signature["safety"], dict)
    and signature["safety"]["kind"] in ("safe", "unsafe")
    and isinstance(signature["abi"], dict)
    and "status" not in signature["abi"]
    for signature in fn_signatures
), "function signatures must carry typed safety and ExternAbi tags"

graph_count = sum(len(row["identities"]) if row["kind"] == "function" else 1
                  for row in doc["allocations"])
allocations = {graph: pool_entry(doc, "allocations", graph) for graph in range(graph_count)}
assert all("status" not in allocation for allocation in allocations.values()), "fixture allocation unexpectedly incomplete"
memory_allocations = [allocation for allocation in allocations.values() if allocation.get("kind") == "memory"]
assert any(doc["byte_images"][allocation["byte_image_id"]] == "6c65616e2d6d697269" for allocation in memory_allocations), "byte-string allocation contents missing"
assert any(
    relocation.get("immutable") is True and relocation.get("shared_ref") is True
    for allocation in memory_allocations
    for relocation in allocation["relocations"]
), "CtfeProvenance flags missing from allocation relocation"
static = next(allocation for allocation in allocations.values() if allocation.get("kind") == "static" and allocation["def_path"] == "VTABLE_ROOT")
assert static["thread_local"] is False
assert static["initializer"]["size_bytes"] == 16
assert static["initializer"]["relocations"], "reachable static trait-object provenance missing"
assert not any(a.get("def_path") == "STATIC_DATA" for a in allocations.values()), "unreferenced static was exported"
bindings = doc["source_vtables"]["bindings"]
assert any(method["instance_id"] is not None and instances[method["instance_id"]]["def_path"] == "<ValueCell as ValueSource>::get"
           for binding in bindings for method in binding["methods"])
assert any(instances[binding["drop_instance"]]["instance_kind"].get("shim_kind") == "drop_glue"
           and instances[binding["drop_instance"]]["kind"] == "instance_mir" for binding in bindings)

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
assert doc["byte_images"][tls["initializer"]["allocation"]["byte_image_id"]] == "11000000"
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
