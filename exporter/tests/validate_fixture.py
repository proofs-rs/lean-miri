#!/usr/bin/env python3
"""Validate the structural evidence that the MIR fixture must export."""
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "tools"))
from mir_json import load_mir_inspection_document as load_mir_document, pool_entry

doc = load_mir_document(sys.argv[1])
assert doc["schema"] == "lean-miri-rustc-mir"
assert doc["schema_version"] == 13
assert doc["compiler_coroutine_coverage"]["body_coroutines"] == [False] * len(doc["bodies"])
assert doc["compiler_coroutine_coverage"]["coroutines"] == []
assert doc["compiler_coroutine_coverage"]["auxiliary_bodies"] == []
assert doc["producer"]["rustc_commit"] == "8144389c895da997dbdecaa635e41d6a50be6ffd"
assert doc["producer"]["miri_commit"] == "7fa591d7d4dd9af8154becbc8332f8096f8323b1"
assert "completeness" not in doc
assert all(isinstance(name, str) for name in doc["files"])
assert len(doc["files"]) == len(set(doc["files"])), "duplicate filename spellings"
for span in doc["spans"]:
    assert type(span["file"]) is int and 0 <= span["file"] < len(doc["files"])
def check_source_position(span):
    assert "collapsed_lo" not in span
    assert type(span["span"]) is int and 0 <= span["span"] < len(doc["spans"])
    assert type(span["source_position"]["byte_position"]) is int
    filename = span["source_position"]["filename"]
    assert type(filename) is int and 0 <= filename < len(doc["files"])


# Source seeds are checked in their own roles. No Python adapter constructs
# monomorphic MIR or invents locals/blocks for a raw template or shim seed.
material_bodies = []
copy_templates = {}
noop_drops = []
for body_index, body in enumerate(doc["bodies"]):
    instance = pool_entry(doc, "instances", body["instance_id"])
    owned_bodies = [instance["body"], *[promoted["body"] for promoted in instance["promoted_bodies"]]]
    assert owned_bodies.count(body_index) == 1, "body seed must have one ordinary/promoted role in its complete instance"
    role = body["body_kind"]
    if role == "material":
        material_bodies.append(body)
        source_spans = body["backtrace_spans"]
    elif role == "copy_template":
        assert set(body) == {"body_kind", "template_id", "instance_id", "generic_args", "promoted_bodies"}
        template_id = body["template_id"]
        assert type(template_id) is int and 0 <= template_id < len(doc["mir_templates"])
        source = doc["mir_templates"][template_id]
        assert source["source_def_id"] == instance["def_id"]
        assert source["def_path"] == instance["def_path"]
        assert instance["instance_kind"] == {"kind": "item", "def_id": instance["def_id"]}
        assert body["generic_args"] == instance["generic_args"], "raw MIR argument binding mismatch"
        assert source["source_promoted"] is None and body["promoted_bodies"] == []
        assert isinstance(source["template"], str), "raw MIR syntax must retain its explicit source encoding"
        template = json.loads(source["template"])
        arguments = body["generic_args"]
        assert template["parameters"] == [
            {"type": "type", "const": "constant", "lifetime": "region"}[argument["kind"]]
            for argument in arguments
        ], "raw MIR parameter/argument sorts differ"
        skeleton = template["skeleton"]
        assert skeleton["phase"] == "runtime_optimized"
        assert len(source["local_sources"]) == len(skeleton["locals"])
        assert all(type(slot) is int and 0 <= slot < len(template["types"])
                   for slot in skeleton["locals"]), "raw local type slot is absent"
        assert all(scope["scope"] == index and scope["inlined"] is None
                   for index, scope in enumerate(source["source_scopes"]))
        copy_templates[body_index] = (source, template)
        source_spans = source["backtrace_spans"]
    elif role == "noop_drop":
        assert set(body) == {"body_kind", "instance_id", "source_span"}
        assert instance["instance_kind"] == {
            "kind": "shim", "shim_kind": "drop_glue", "def_id": instance["def_id"], "drop_type": None
        }, "signature-only shim must be exact DropGlue(_, None)"
        definition = pool_entry(doc, "definitions", instance["def_id"])
        declaration = definition["generic_template"]
        assert declaration["parameters"] == ["type"]
        assert len(instance["generic_args"]) == 1 and instance["generic_args"][0]["kind"] == "type"
        pool_entry(doc, "types", instance["generic_args"][0]["value"])
        signature = declaration["signature_expression"]
        assert signature["kind"] == "binder" and len(signature["variables"]) == 1
        region = signature["variables"][0]
        assert region["kind"] == "region"
        signature = signature["value"]
        assert signature["kind"] == "node" and signature["sort"] == "aggregate" and signature["tag"] == "signature"
        assert json.loads(signature["payload"]) == {
            "abi_packed": 2, "safe": False, "c_variadic": False, "splatted": None
        }, "raw drop signature must retain the pinned unsafe Rust header"
        input_type, output_type = signature["children"]
        assert input_type["kind"] == "node" and input_type["sort"] == "type"
        assert input_type["tag"] == "reference" and input_type["payload"] == "mutable"
        assert len(input_type["children"]) == 2
        assert input_type["children"][0] == {
            "kind": "bound", "sort": "region", "index": 0, "variable": 0, "identity": region["identity"]
        }, "raw drop input region must refer to its own signature binder"
        assert input_type["children"][1] == {"kind": "parameter", "sort": "type", "index": 0}
        assert output_type == {"kind": "node", "sort": "type", "tag": "tuple", "payload": "", "children": []}
        noop_drops.append(body)
        source_spans = [body["source_span"]]
    else:
        raise AssertionError(f"unknown body seed role {role}")
    for span in source_spans:
        check_source_position(span)
assert copy_templates and noop_drops, "fixture must exercise raw generic MIR and signature-only no-op drop seeds"

type_nodes = {node["type_id"]: node for node in doc["types"]}
assert type_nodes, "compilation-scoped type graph missing"
assert sorted(type_nodes) == list(range(len(type_nodes))), "type IDs must be session-local monotonic IDs"
assert all("shape" in node and "layout" in node for node in type_nodes.values())
for node in type_nodes.values():
    assert "input_type" not in node["compiler_facts"]
    assert "query_input_type" not in node["compiler_facts"]
    query_input = node.get("layout_query_input_type")
    assert query_input is None or (type(query_input) is int and query_input in type_nodes)
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

def check_scalar_widths(value):
    if isinstance(value, dict):
        if value.get("kind") == "scalar" and "bits_unsigned" in value:
            size = value["size_bytes"]
            assert type(size) is int and size > 0, "scalar byte width must be positive"
            assert 0 <= int(value["bits_unsigned"]) < 2 ** (8 * size), "scalar bits exceed byte width"
            node = type_nodes[value["type"]]
            layout = pool_entry(doc, "layouts", node["layout"])
            if "primitive_recipe" in layout:
                # These widths follow the raw primitive kind and actual target,
                # independently of the MIR scalar's exported width.
                primitive = layout["primitive_recipe"]
                shape = node["shape"]
                fixed = {"bool": 1, "char": 4, "u8": 1, "i8": 1, "u16": 2, "i16": 2,
                         "u32": 4, "i32": 4, "u64": 8, "i64": 8, "u128": 16, "i128": 16,
                         "f16": 2, "f32": 4, "f64": 8, "f128": 16}
                if primitive in ("usize", "isize"):
                    bits = doc["runtime_target_data_layout"]["pointer_width_bits"]
                    assert type(bits) is int and bits > 0 and bits % 8 == 0
                    expected_size = bits // 8
                else:
                    assert primitive in fixed, f"unexpected scalar primitive recipe {primitive}"
                    expected_size = fixed[primitive]
                if primitive.startswith("u"):
                    assert shape == {"kind": "uint", "unsigned_kind": primitive}
                elif primitive.startswith("i"):
                    assert shape == {"kind": "int", "signed_kind": primitive}
                elif primitive.startswith("f"):
                    assert shape == {"kind": "float", "float_kind": primitive}
                else:
                    assert shape == {"kind": primitive}
            else:
                expected_size = layout["size_bytes"]
            assert size == expected_size, "scalar byte width differs from its raw type/target or physical layout"
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
    "STATIC_DATA", "TLS_WORD", "read_tls",
}.issubset(bodies)
assert bodies["promoted_ref"]["promoted_bodies"], "promoted MIR body missing"
assert bodies["STATIC_DATA"]["is_static"] and not bodies["STATIC_DATA"]["thread_local_static"]
assert bodies["TLS_WORD"]["is_static"] and bodies["TLS_WORD"]["thread_local_static"]

exercise = pool_entry(doc, "bodies", bodies["exercise"]["body"])
assert exercise["locals"]
for local in exercise["locals"]:
    # Schema 11 pool_body::Local retains the type ID, not a redundant layout.
    assert set(local) == {"local", "type", "source_info"}
    layout_id = type_nodes[local["type"]]["layout"]
    assert type(layout_id) is int
    assert isinstance(pool_entry(doc, "layouts", layout_id), dict)
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
# `id::<u32>` retains its raw parameter-local relation, not a fabricated
# monomorphic body. Check both the binding and the entire source operation.
id_source, id_template = copy_templates[id_instance["body"]]
assert id_source["def_path"] == "id"
assert id_template["parameters"] == ["type"]
assert id_template["types"] == [{"kind": "parameter", "sort": "type", "index": 0}]
assert len(id_instance["generic_args"]) == 1
id_argument = id_instance["generic_args"][0]
assert id_argument["kind"] == "type" and type_nodes[id_argument["value"]]["shape"] == {
    "kind": "uint", "unsigned_kind": "u32"
}
id_skeleton = id_template["skeleton"]
assert id_skeleton["argument_count"] == 1 and id_skeleton["spread_argument"] is None
assert id_skeleton["locals"] == [0, 0], "return/argument locals must refer to the same raw type parameter"
assert len(id_skeleton["blocks"]) == 1
id_block = id_skeleton["blocks"][0]
assert id_block["cleanup"] is False and len(id_block["statements"]) == 1
assert id_block["statements"][0]["kind"] == {
    "kind": "assign", "destination": 0,
    "value": {"kind": "use", "operand": {"kind": "move", "local": 1}, "retag": "yes"}
}, "raw id MIR must move its argument to its return local with the exact retag"
assert id_block["terminator"]["kind"] == {"kind": "return"}
assert {source["def_path"] for source, _ in copy_templates.values()} == {"id"}, "unexpected raw source fixture role"
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
    for body in material_bodies
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
static = next(allocation for allocation in allocations.values() if allocation.get("kind") == "static")
assert static["thread_local"] is False
assert doc["byte_images"][static["initializer"]["byte_image_id"]] == "0b0000000d000000"
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
for body in material_bodies:
    for block in body["basic_blocks"]:
        for statement in block["statements"]:
            assert statement["kind"].get("variant") and "status" not in statement["kind"]
        if block["terminator"]:
            assert block["terminator"]["kind"].get("variant") and "status" not in block["terminator"]["kind"]

print(f"validated {len(bodies)} local MIR bodies, {len(instances)} reachable instances, {len(allocations)} allocations, exact rustc pin; raw id parameter bindings and no-op drop signature checked")
