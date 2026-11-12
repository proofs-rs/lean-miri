"""Test-only schema projection for immutable historical MIR fixtures.

No rustc invocation occurs. These adaptations provide local regression inputs,
not new producer or reference-execution evidence. Unwind and generic-prefix
seeds are hypothetical representatives preserving historical answers, not
recovered rustc material or new ABI/generic-rebase correspondence evidence.
Tests asserting actual raw materials must use fresh exports. Production mir_json
is strict.
"""
from __future__ import annotations
import copy


def adapt_legacy_fixture(document):
    if document.get("schema_version") not in (11, 12):
        return copy.deepcopy(document)
    result = copy.deepcopy(document)
    result["schema_version"] = 13
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
