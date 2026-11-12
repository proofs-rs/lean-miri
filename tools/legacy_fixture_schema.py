"""Test-only schema projection for immutable historical MIR fixtures.

No rustc invocation occurs. These adaptations provide local regression inputs,
not new producer or reference-execution evidence. Unwind, drop-definition and generic-prefix
seeds are hypothetical representatives preserving historical answers, not
recovered rustc material or new ABI/drop/generic-rebase correspondence evidence.
Tests asserting actual raw materials must use fresh exports. Production mir_json
is strict.
"""
from __future__ import annotations
import copy


def _bound_free_arguments(types, constants, arguments):
    """Conservative historical replay guard; never recover a source binder."""
    pending, seen_types, seen_constants = [arguments], set(), set()
    for _ in range(1_000_000):
        if not pending:
            return True
        value = pending.pop()
        if isinstance(value, list):
            pending.extend(value)
            continue
        if not isinstance(value, dict):
            continue
        kind = value.get("kind", "")
        if kind in ("bound", "dynamic_trait_object"):
            return False
        type_refs, constant_refs = [], []
        if kind in ("type", "const") and type(value.get("value")) is int:
            (type_refs if kind == "type" else constant_refs).append(value["value"])
        for key, child in value.items():
            pending.append(child)
            if key in ("pointee", "element", "base", "inner", "output", "type") and type(child) is int:
                type_refs.append(child)
            if key in ("length", "start", "end") and type(child) is int:
                constant_refs.append(child)
            if key in ("inputs", "elements") and isinstance(child, list):
                (constant_refs if kind == "branch" else type_refs).extend(
                    item for item in child if type(item) is int)
        for identity in type_refs:
            if identity in seen_types:
                continue
            if not 0 <= identity < len(types) or not isinstance(types[identity], dict):
                return False
            shape = types[identity].get("shape")
            if not isinstance(shape, dict):
                return False
            seen_types.add(identity)
            pending.append(shape)
        for identity in constant_refs:
            if identity in seen_constants:
                continue
            if not 0 <= identity < len(constants):
                return False
            seen_constants.add(identity)
            pending.append(constants[identity])
    return False


def adapt_legacy_fixture(document):
    bodies = document.get("bodies")
    old_13_body_encoding = (document.get("schema_version") == 13
                           and "mir_templates" not in document
                           and isinstance(bodies, list) and bool(bodies)
                           and all(isinstance(body, dict) and "body_kind" not in body for body in bodies))
    if document.get("schema_version") not in (11, 12) and not old_13_body_encoding:
        return copy.deepcopy(document)
    result = copy.deepcopy(document)
    result["schema_version"] = 13
    result.setdefault("instance_abis", [])
    # Historical executable bodies remain material. No source template or trait
    # proof is reconstructed from a monomorphic execution fixture.
    result.setdefault("mir_templates", [])
    result.setdefault("compiler_trait_program", {"traits": [], "constructor_scope": {"kind": "all_source_impls"}})
    for body in result.get("bodies", []):
        if isinstance(body, dict):
            body.setdefault("body_kind", "material")
    for node in result.get("types", []):
        shape = node.get("shape", {}) if isinstance(node, dict) else {}
        if shape.get("kind") == "alias":
            # Hypothetical old-component representative, never recovered alias
            # rigidity and never used by genuine compiler correspondence tests.
            shape.setdefault("rigid", False)
        if (shape.get("kind") == "function_definition"
                and "generic_args_bound_variables" not in shape
                and "generic_args" in shape
                and _bound_free_arguments(result.get("types", []), result.get("type_constants", []),
                                         shape["generic_args"])):
            # HYPOTHETICAL component representative: the old binder, including
            # unused variables, is unrecoverable. Never compiler/GI evidence.
            shape["generic_args_bound_variables"] = []
    if "compiler_coroutine_coverage" not in result and isinstance(result.get("bodies"), list):
        result["compiler_coroutine_coverage"] = {
            "body_coroutines": [False] * len(result["bodies"]),
            "coroutines": [], "auxiliary_bodies": []}
    definitions = result.get("definitions", [])
    instances = result.get("instances", [])
    runtime = result.get("compiler_runtime_queries", {})
    flags = {}
    for row in runtime.get("instances", []):
        if not isinstance(row, dict):
            continue
        identity = row.get("instance_id")
        if type(identity) is not int or not 0 <= identity < len(instances):
            continue
        kind = instances[identity].get("instance_kind", {})
        if kind.get("kind") not in ("item", "virtual") and not (
                kind.get("kind") == "shim" and kind.get("shim_kind") == "vtable"):
            continue
        definition = kind.get("def_id")
        flag = row.get("requires_caller_location")
        if type(definition) is not int or not 0 <= definition < len(definitions) or type(flag) is not bool:
            continue
        if definition in flags and flags[definition] != flag:
            raise ValueError("historical caller-location definition flags conflict")
        flags[definition] = flag
    for definition, flag in flags.items():
        definitions[definition]["body_track_caller"] = flag
    for row in runtime.get("virtual", []):
        if not isinstance(row, dict) or "parent_generic_count" in row:
            continue
        identity = row.get("original_instance_id")
        if type(identity) is not int or not 0 <= identity < len(instances):
            continue
        args = instances[identity].get("generic_args", [])
        expected = row.get("rebased_args")
        concrete = row.get("concrete_type")
        # Upstream virtual_self replaces only Self for every legal prefix count.
        # This is an explicitly synthetic representative count, not a recovered
        # rustc definition field. Require the historical oracle to match exactly.
        if args and args[0].get("kind") == "type" and expected == [
                {"kind": "type", "value": concrete}, *args[1:]]:
            row["parent_generic_count"] = 1
    # Explicit hypothetical definition seeds for historical component replay.
    # Uniform false/true oracle groups admit manually-drop/destructor
    # representatives; mixed generic instantiations retain field recursion.
    # These identities are not recovered compiler/drop-impl material.
    drop_answers = {}
    boolean_pool = result.get("boolean_queries", [])
    for node in result.get("types", []):
        if not isinstance(node, dict) or node.get("shape", {}).get("kind") != "adt":
            continue
        definition = node["shape"].get("def_id")
        facts = node.get("compiler_facts", {})
        booleans = facts.get("boolean_queries", {})
        if type(booleans) is int and 0 <= booleans < len(boolean_pool):
            booleans = boolean_pool[booleans]
        answer = booleans.get("needs_drop") if isinstance(booleans, dict) else None
        if type(definition) is int and 0 <= definition < len(definitions) and type(answer) is bool:
            drop_answers.setdefault(definition, set()).add(answer)
    representative_function = next((body.get("source_def_id") for body in result.get("bodies", [])
                                    if isinstance(body, dict) and type(body.get("source_def_id")) is int
                                    and 0 <= body["source_def_id"] < len(definitions)), None)
    for definition, answers in drop_answers.items():
        if answers == {True} and representative_function is None:
            continue  # Missing identities remain missing material, never false.
        if "adt_drop" not in definitions[definition]:
            definitions[definition]["adt_drop"] = {
                "manually_drop": answers == {False},
                "destructor": representative_function if answers == {True} else None}
    for abi in result.get("fn_abis", []):
        if isinstance(abi, dict) and type(abi.get("can_unwind")) is bool:
            # Synthetic equivalent result for component replays, not recovered
            # rustc ABI/configuration inputs and not ABI correspondence evidence.
            abi["unwind_seed"] = {"abi": {"kind": "rust", "unwind": None},
                                  "definition": None, "panic_unwinds": abi.pop("can_unwind"),
                                  "panic_in_drop_unwinds": True}
    return result


def load_fixture_document(path):
    """Read a saved fixture through explicit adaptation then the strict reader."""
    import gzip
    import json
    from pathlib import Path
    from mir_json import decode_mir_document
    source = Path(path)
    raw = gzip.decompress(source.read_bytes()) if source.suffix == ".gz" else source.read_bytes()
    return decode_mir_document(adapt_legacy_fixture(json.loads(raw)))


def load_fixture_inspection_document(path):
    from mir_json import inspection_document
    return inspection_document(load_fixture_document(path))
