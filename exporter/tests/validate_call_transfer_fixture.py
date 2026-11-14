#!/usr/bin/env python3
"""Validate exact compiler transfer facts from the small call-transfer fixture.

The checks establish that these source edges caused relevant metadata to be
emitted. They make no claim that the finite function-pointer candidate pool is
an exhaustive runtime points-to set.
"""
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "tools"))
from mir_json import load_mir_inspection_document as load_mir_document, pool_entry


def require(condition, message):
    if not condition:
        raise SystemExit(message)


document = load_mir_document(sys.argv[1])
types = {item["type_id"]: item for item in document["types"]}
queries = document["compiler_runtime_queries"]
virtual_rows = queries["virtual"]
covariance = document["compiler_covariance_queries"]

# The catalog is a projection of the final pool. Each exact ordered pair must
# occur once, retain both boolean answers, and reference fully emitted types.
pair_keys = [(row["source_type"], row["target_type"]) for row in covariance]
require(pair_keys == sorted(set(pair_keys)),
        "covariance pairs are duplicated or not in numeric type-ID order")
for row in covariance:
    require(row["source_type"] in types and row["target_type"] in types,
            "covariance pair references a missing type definition")
    require(row["source_type"] != row["target_type"],
            "covariance catalog contains a redundant reflexive pair")
    require(type(row["value"]) is bool,
            "covariance answer is not a compiler boolean")



def display(type_ref):
    if not isinstance(type_ref, int):
        return ""
    node = types.get(type_ref, {})
    return node.get("display", "")


def type_id(type_ref):
    return type_ref if isinstance(type_ref, int) else None


def relation_ids(source_ref, target_ref):
    source_id = type_id(source_ref)
    target_id = type_id(target_ref)
    return any(
        type_id(row.get("source_type")) == source_id
        and type_id(row.get("target_type")) == target_id
        for row in covariance
    )


def require_false_relation(source_ref, target_ref, label):
    rows = [row for row in covariance
            if row["source_type"] == source_ref and row["target_type"] == target_ref]
    require(len(rows) == 1 and rows[0]["value"] is False,
            f"{label}: exact negative covariance answer was lost")


def require_transfer(source_ref, target_ref, label):
    require(source_ref is not None and target_ref is not None,
            f"{label}: source/destination type ID is missing")
    if type_id(source_ref) != type_id(target_ref):
        source_shape = types[source_ref]["shape"]
        target_shape = types[target_ref]["shape"]
        if (source_shape.get("kind") == target_shape.get("kind") == "raw_pointer"
                and source_shape.get("mutability") != target_shape.get("mutability")):
            # Pinned structurally_relate_tys rejects unequal pointer mutability
            # before inspecting pointees. Lean owns this constructor rule;
            # the independent covariance matrix checks its actual answer.
            require(not relation_ids(source_ref, target_ref),
                    f"{label}: migrated pointer-mutability relation retained an eager answer")
            return
        require(relation_ids(source_ref, target_ref),
                f"{label}: exact source/destination covariance query is absent")


def body_payload(row):
    return pool_entry(document, "bodies", row["body"])


instance_rows = document["instances"]
all_body_rows = list(document["body_roots"]) + [
    row for row in instance_rows if isinstance(row.get("body"), int)
]


def calls_in(body):
    payload = body_payload(body)
    for block in payload.get("basic_blocks", []):
        terminator = block.get("terminator", {}).get("kind", {})
        if terminator.get("variant") == "Call":
            yield terminator


def operand_type_ref(operand):
    if not isinstance(operand, dict):
        return None
    if operand.get("kind") in ("Copy", "Move"):
        return operand.get("place", {}).get("type")
    constant = operand.get("constant", {})
    return constant.get("type")


def raw_type_matches(term, material_id):
    """Fixture-only exact raw syntax join; never constructs a closed type."""
    if term.get("sort") != "type":
        return False
    shape = types[material_id]["shape"]
    if term == {"kind": "atom", "sort": "type", "tag": "uint", "payload": "u8"}:
        return shape == {"kind": "uint", "unsigned_kind": "u8"}
    if term.get("kind") == "definition" and term.get("tag") == "adt":
        if shape.get("kind") != "adt" or term.get("children") != [] or shape.get("generic_args") != []:
            return False
        physical = document["definitions"][shape["def_id"]]
        return term["definition"] == {key: physical[key] for key in ("crate", "index")}
    if term.get("kind") == "node" and term.get("tag") in ("raw_pointer", "reference"):
        if shape.get("kind") != term["tag"] or shape.get("mutability", {}).get("kind") != term["payload"]:
            return False
        children = term["children"]
        if term["tag"] == "reference":
            if (len(children) != 2 or children[0] != {"kind": "atom", "sort": "region", "tag": "erased", "payload": ""}
                    or shape.get("region") != {"kind": "erased"}):
                return False
            children = children[1:]
        return len(children) == 1 and raw_type_matches(children[0], shape["pointee"])
    return False


def local_type_ref(body, local):
    payload = body_payload(body)
    if payload.get("body_kind") == "copy_template":
        source = document["mir_templates"][payload["template_id"]]
        template = json.loads(source["template"])
        require(source["source_role"] == "runtime" and source["source_promoted"] is None,
                "transfer candidate lost its exact runtime source role")
        require(source["source_def_id"] == body["def_id"]
                and payload["instance_id"] == body["instance_id"],
                "transfer candidate physical source/instance identity differs")
        require(template["parameters"] == [] and payload["generic_args"] == [],
                "transfer fixture raw local join requires an actual parameter-free source")
        term = template["types"][template["skeleton"]["locals"][local]]
        matches = [type_id for type_id in types if raw_type_matches(term, type_id)]
        require(len(matches) == 1,
                "raw candidate local has no unique exact captured type-pool correspondence")
        return matches[0]
    for item in payload.get("locals", []):
        if item.get("local") == local:
            return item.get("type")
    return None


def body_by_path(fragment):
    return [row for row in all_body_rows if fragment in row.get("def_path", "")]


# Recover the exact call operand/destination and the candidate's substituted
# MIR locals. Compare those IDs with covariance rows rather than accepting an
# unrelated catalog row with similar printed type names.
indirect_bodies = body_by_path("indirect_pointer_call")
require(indirect_bodies, "indirect_pointer_call body is absent")
indirect_call = next(
    (
        (body, call)
        for body in indirect_bodies
        for call in calls_in(body)
        if call.get("resolution", {}).get("kind") == "source_function_pointer"
        and "*mut u8" in display(call["resolution"].get("function_type"))
        and "*const u8" in display(call["resolution"].get("function_type"))
    ),
    None,
)
require(indirect_call, "typed indirect FnPtr callsite was not exported")
call_body, call = indirect_call
resolution = call["resolution"]
require("fn_abi" not in resolution and resolution["extra_argument_types"] == [],
        "covered Rust FnPtr call retained a physical ABI answer or unexpected extras")
raw_pointer_type = types[resolution["function_type"]]
require(raw_pointer_type["shape"]["kind"] == "function_pointer"
        and raw_pointer_type["shape"]["signature"]["abi"]["kind"] == "rust"
        and not raw_pointer_type["shape"]["signature"]["c_variadic"],
        "source FnPtr call lost its exact raw Rust signature")
require(isinstance(document["producer"]["abi_session"]["llvm_writable"], bool),
        "source FnPtr call lost canonical ABI session configuration")
pointer_target_rows = [row for row in instance_rows if row.get("def_path", "").endswith("pointer_target")]
require(pointer_target_rows, "pointer_target candidate instance/body is absent")
pointer_target_body = next(
    (row for row in pointer_target_rows if "body" in row),
    None,
)
require(pointer_target_body, "pointer_target candidate has no substituted MIR body")
argument_source = operand_type_ref(call.get("args", [{}])[0].get("operand"))
argument_target = local_type_ref(pointer_target_body, 1)
return_source = local_type_ref(pointer_target_body, 0)
return_target = call.get("destination", {}).get("type")
require(all(value is not None for value in [argument_source, argument_target, return_source, return_target]),
        "indirect pointer call/candidate transfer types could not be recovered")
require(type_id(argument_source) != type_id(argument_target),
        "indirect FnPtr argument fixture did not preserve its distinct MIR types")
require(type_id(return_source) != type_id(return_target),
        "indirect FnPtr return fixture did not preserve its distinct MIR types")
require_transfer(argument_source, argument_target, "indirect FnPtr argument")
require_transfer(return_source, return_target, "indirect FnPtr return")

# Rust's virtual call passes the concrete receiver pointer into the
# instantiated method's receiver local. Find a validated virtual resolution
# for this fixture's trait method, then require its concrete receiver transfer.
resolved_virtual = [
    row
    for row in virtual_rows
    if isinstance(row.get("resolved"), int)
]
require(resolved_virtual, "TransferObject::get has no validated virtual target row")
instance_by_id = {item["instance_id"]: item for item in document["instances"]}
fixture_virtual_targets = [
    instance_by_id.get(row.get("resolved"), {})
    for row in resolved_virtual
]
fixture_virtual_targets = [
    item for item in fixture_virtual_targets
    if "ConcreteObject as TransferObject" in item.get("def_path", "")
    and item.get("def_path", "").endswith("::get")
]
require(
    fixture_virtual_targets,
    "TransferObject::get has no validated concrete virtual target row",
)
virtual_bodies = body_by_path("virtual_call")
require(virtual_bodies, "virtual_call body is absent")
def virtual_request(call):
    resolution = call.get("resolution", {})
    instance = instance_by_id.get(resolution.get("instance_id"), {})
    return (resolution.get("kind") in ("source_instance", "virtual_dispatch")
            and instance.get("instance_kind", {}).get("kind") == "virtual")


virtual_callsite = next((call for body in virtual_bodies for call in calls_in(body)
                         if virtual_request(call)), None)
require(virtual_callsite, "trait-object Virtual source request is absent")
virtual_resolution = virtual_callsite["resolution"]
virtual_instance = instance_by_id[virtual_resolution["instance_id"]]
virtual_kind = virtual_instance["instance_kind"]
virtual_function = types[virtual_resolution["function_type"]]["shape"]
require(virtual_function.get("kind") == "function_definition"
        and virtual_function["def_id"] == virtual_kind["def_id"] == virtual_instance["def_id"]
        and virtual_function["generic_args"] == virtual_instance["generic_args"],
        "Virtual source request lost exact FnDef physical identity/full arguments")
method = document["definitions"][virtual_kind["def_id"]]
require(method["callable_source"]["definition_kind"] == "associated_function"
        and method["callable_source"]["container"] == "trait"
        and method["callable_source"]["has_self"],
        "Virtual source request does not name a trait method")
require(method["raw_path"]["components"][-2:]
        == [{"kind": "type", "name": "TransferObject", "disambiguator": 0},
            {"kind": "value", "name": "get", "disambiguator": 0}],
        "Virtual source method is not the exact fixture trait declaration")
require(len(virtual_instance["generic_args"]) == 1
        and virtual_instance["generic_args"][0]["kind"] == "type",
        "Virtual source request lost its complete Self argument")
self_type = virtual_instance["generic_args"][0]["value"]
require(types[self_type]["shape"]["kind"] == "dynamic_trait_object",
        "Virtual source Self is not the actual dynamic receiver")
require(virtual_kind["dispatch_slot"] == 3,
        "single own method must retain pinned first-method slot after three metadata entries")
if virtual_resolution["kind"] == "source_instance":
    require(set(virtual_resolution) == {"kind", "function_type", "instance_id"},
            "Virtual source request retained an eager ABI/dispatch result")
    require(virtual_instance["kind"] == "identity_only"
            and "virtual_identity" not in virtual_instance and "body" not in virtual_instance,
            "covered Virtual instance retained an eager identity ABI or executable body")
    require(not any(row["instance_id"] == virtual_instance["instance_id"]
                    for row in document["compiler_instance_abis"]),
            "covered Virtual source identity retained an eager FnAbi result row")
else:
    require(method["body_track_caller"] is True,
            "material Virtual dispatch is only valid here for an unported caller-location residual")

dynamic = types[self_type]["shape"]
principal = pool_entry(document, "predicates", dynamic["principal_predicate"])
parent = method["source_environment"]["generic_parent"]
principal_definition = document["definitions"][principal["def_id"]]
require(principal["kind"] == "trait" and principal["generic_args"] == []
        and principal["bound_variables"] == [] and parent["parameter_count"] == 1
        and parent["definition"] == {key: principal_definition[key] for key in ("crate", "index")},
        "Virtual Self principal is not the physical owner trait with exact own arguments")
selected_virtual_rows = [row for row in resolved_virtual
                         if row["original_instance_id"] == virtual_instance["instance_id"]
                         and row["method_definition"] == virtual_kind["def_id"]
                         and row["parent_trait"] == principal["def_id"]
                         and row["vtable_query"]["input_predicates"] == dynamic["predicates"]]
require(len(selected_virtual_rows) == 1,
        "Virtual source identity does not join one exact concrete vtable source owner")
selected_virtual_row = selected_virtual_rows[0]
virtual_target = instance_by_id[selected_virtual_row["resolved"]]
require(virtual_target in fixture_virtual_targets, "Virtual source request resolved to an unrelated concrete method")
virtual_target_body = next(
    (row for row in instance_rows
     if row.get("instance_id") == virtual_target.get("instance_id") and "body" in row),
    None,
)
require(virtual_target_body, "validated virtual target has no substituted MIR body")
receiver_source = next(
    (
        item["type_id"]
        for item in types.values()
        if item.get("shape", {}).get("kind") == "raw_pointer"
        and item.get("shape", {}).get("mutability", {}).get("kind") == "mutable"
        and "ConcreteObject"
        in types.get(item.get("shape", {}).get("pointee"), {})
        .get("shape", {}).get("def_path", "")
    ),
    None,
)
receiver_target = local_type_ref(virtual_target_body, 1)
require(receiver_source is not None and receiver_target is not None and relation_ids(receiver_source, receiver_target),
        "exact virtual receiver transfer from *mut ConcreteObject to callee local is absent")
# Receiver ABI compatibility does not make a raw pointer covariant with a
# reference. Demand discovery must preserve this negative compiler answer.
require_false_relation(receiver_source, receiver_target, "virtual receiver")
virtual_argument_source = operand_type_ref(virtual_callsite.get("args", [{}, {}])[1].get("operand"))
virtual_argument_target = local_type_ref(virtual_target_body, 2)
virtual_return_source = local_type_ref(virtual_target_body, 0)
virtual_return_target = virtual_callsite.get("destination", {}).get("type")
require_transfer(virtual_argument_source, virtual_argument_target,
                "virtual call nonreceiver argument")
require_transfer(virtual_return_source, virtual_return_target,
                "virtual call return")

# pthread_create's generated callback call takes the registration data pointer
# and returns through Miri's source *mut () destination. This exact compiler
# relation is distinct from the C registration function's own FnAbi row.
pthread_callsite = next(
    (
        call
        for body in body_by_path("call_transfer_root")
        for call in calls_in(body)
        if call.get("resolution", {}).get("kind") == "indirect_function_pointer"
        and len(call.get("args", [])) == 4
    ),
    None,
)
require(pthread_callsite, "indirect pthread_create MIR callsite is absent")
pthread_function_type = display(pthread_callsite["resolution"].get("function_type"))
require("usize" in pthread_function_type and "c_void" in pthread_function_type,
        "four-argument pthread_create FnPtr signature is not the exported callsite")
callback_data_source = operand_type_ref(pthread_callsite["args"][3]["operand"])
callback_operand_type = operand_type_ref(pthread_callsite["args"][2]["operand"])
callback_rows = [row for row in instance_rows if row.get("def_path", "").endswith("thread_start")]
callback_body = next(
    (row for row in callback_rows if "body" in row),
    None,
)
require(callback_body is not None and callback_data_source is not None and callback_operand_type is not None,
        "pthread callback target or registration data operand is absent")
callback_signature = display(callback_operand_type)
require("c_void" in callback_signature and "*mut" in callback_signature,
        "pthread callback operand is not the fixture's mutable c_void callback")
callback_argument_target = local_type_ref(callback_body, 1)
require(
    callback_argument_target is not None
    and type_id(callback_data_source) == type_id(callback_argument_target),
    "pthread registration data operand does not match the callback MIR argument local",
)
callback_return_source = local_type_ref(callback_body, 0)
require(
    callback_return_source is not None
    and type_id(callback_return_source) == type_id(callback_argument_target),
    "thread_start return local does not preserve its callback argument type",
)


def is_mutable_unit_pointer(node):
    shape = node.get("shape", {})
    if shape.get("kind") != "raw_pointer":
        return False
    if shape.get("mutability", {}).get("kind") != "mutable":
        return False
    pointee = types.get(shape.get("pointee"), {})
    return (
        pointee.get("shape", {}).get("kind") == "tuple"
        and pointee.get("shape", {}).get("elements", []) == []
    )


unit_pointer_destination = next(
    (
        item["type_id"]
        for item in types.values()
        if is_mutable_unit_pointer(item)
    ),
    None,
)
require_transfer(callback_return_source, unit_pointer_destination,
                "pthread generated callback return")
require(type_id(callback_return_source) != type_id(unit_pointer_destination),
        "pthread callback return did not exercise *mut c_void to *mut ()")

require_false_relation(callback_return_source, unit_pointer_destination,
                       "pthread generated callback return")

# Confirm the registration call itself is retained as an indirect FnPtr call
# and its exact foreign function identity is in the exported instance graph.
instances = document["instances"]
pthread_instances = [
    item
    for item in instances
    if item.get("def_path", "").endswith("pthread_create")
    or item.get("symbol_name") == "pthread_create"
]
require(pthread_instances, "pthread_create foreign instance/candidate is absent")

print(
    "validated typed indirect FnPtr pointer transfer, a resolved virtual target, "
    "and pthread_create callback transfer; candidate discovery is not exhaustive"
)
