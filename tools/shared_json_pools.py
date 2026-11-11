"""Lossless wire projection for maintained schema-8 compiler fixtures.

This only moves repeated values into exact-equality pools. It does not rerun
rustc, change compiler facts, or provide new reference-execution evidence.
"""
from __future__ import annotations

import copy
import json

SHARED_POOLS = {
    "layout_values": dict, "boolean_queries": dict, "discriminants": dict,
    "initialization_ranges": list, "relocations": list, "backtrace_spans": list,
    "statement_kinds": dict, "source_infos": dict,
}
FIELD_POOLS = {name: name for name in (
    "boolean_queries", "discriminants", "initialization_ranges", "relocations", "backtrace_spans")}
FIELD_POOLS["source_info"] = "source_infos"


def _walk(value, transform):
    if isinstance(value, list):
        return [_walk(item, transform) for item in value]
    if not isinstance(value, dict):
        return value
    result = {}
    for key, child in value.items():
        if key in FIELD_POOLS:
            result[key] = None if key == "discriminants" and child is None else transform(FIELD_POOLS[key], child)
        elif key == "statements" and isinstance(child, list):
            result[key] = [{**_walk({field: item for field, item in statement.items() if field != "kind"}, transform),
                            "kind": transform("statement_kinds", statement["kind"])} for statement in child]
        else:
            result[key] = _walk(child, transform)
    return result


def pool_document(document):
    """Project schema 8 to 9, asserting exact inverse including null/false/[]."""
    if document.get("schema_version") != 8:
        raise ValueError("fixture pooling requires schema 8")
    pools = {name: [] for name in SHARED_POOLS}
    keys = {name: {} for name in SHARED_POOLS}

    def intern(name, value):
        # Resolve nested fields first: statement kinds can contain TLS allocations.
        value = _walk(value, intern)
        key = json.dumps(value, sort_keys=True, separators=(",", ":"))
        if key not in keys[name]:
            keys[name][key] = len(pools[name])
            pools[name].append(value)
        return keys[name][key]

    result = _walk(copy.deepcopy(document), intern)
    result["layouts"] = [intern("layout_values", row) for row in result["layouts"]]
    result.update(pools)
    result["schema_version"] = 9
    assert expand_document(result, schema_version=8) == document, "pool projection changed payloads"
    return result


def expand_document(document, *, schema_version=9):
    """Return an independent semantic inspection view with shared payloads resolved.

    Callers retaining wire identities should use the original document. Lean's
    streaming decoder validates each payload and its use in the actual context.
    """
    def resolve(name, index):
        rows = document.get(name)
        if type(index) is not int or index < 0 or not isinstance(rows, list) or index >= len(rows):
            raise ValueError(f"{name} reference {index!r} is out of range")
        return _walk(copy.deepcopy(rows[index]), resolve)

    result = _walk({key: copy.deepcopy(value) for key, value in document.items()
                    if key not in SHARED_POOLS}, resolve)
    result["layouts"] = [resolve("layout_values", index) for index in result["layouts"]]
    result["schema_version"] = schema_version
    return result
