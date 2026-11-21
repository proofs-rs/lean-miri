"""Exact payload sharing for the current compiler input format."""
from __future__ import annotations

import copy
import json

SHARED_POOLS = {
    "initialization_ranges": list, "relocations": list,
    "statement_kinds": dict, "source_infos": dict,
}
FIELD_POOLS = {name: name for name in (
    "initialization_ranges", "relocations")}
FIELD_POOLS["source_info"] = "source_infos"


def _walk(value, transform):
    if isinstance(value, list):
        return [_walk(item, transform) for item in value]
    if not isinstance(value, dict):
        return value
    result = {}
    for key, child in value.items():
        if key in FIELD_POOLS:
            result[key] = transform(FIELD_POOLS[key], child)
        elif key == "statements" and isinstance(child, list):
            result[key] = [{**_walk({field: item for field, item in statement.items() if field != "kind"}, transform),
                            "kind": transform("statement_kinds", statement["kind"])} for statement in child]
        else:
            result[key] = _walk(child, transform)
    return result


def pool_document(document):
    """Share repeated payloads of a current expanded input without changing values."""
    if type(document.get("schema_version")) is not int or document["schema_version"] != 17:
        raise ValueError("fixture pooling requires schema 17")
    document = {key: copy.deepcopy(value) for key, value in document.items()
                if key not in SHARED_POOLS}
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
    result.update(pools)
    assert expand_document(result) == document, "pool sharing changed payloads"
    return result


def expand_document(document):
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
    return result
