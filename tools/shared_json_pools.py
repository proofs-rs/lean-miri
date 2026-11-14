"""Wire projection for maintained compiler fixtures.

This removes unused diagnostic metadata and moves repeated values into exact-equality
pools. It does not rerun rustc or provide new reference-execution evidence.
"""
from __future__ import annotations

import copy
import json

SHARED_POOLS = {
    "layout_values": dict, "boolean_queries": dict, "discriminants": dict,
    "initialization_ranges": list, "relocations": list, "backtrace_spans": list,
    "statement_kinds": dict, "source_infos": dict, "abi_arguments": dict,
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
        if key in ("mir_templates", "ctfe_scalar_sources"):
            # These are raw immutable declaration/frame material. In particular,
            # CTFE statements have inline kind objects, not statement_kinds pool
            # references. Neither source format participates in execution-body
            # payload pooling; preserve its complete subtree in both directions.
            result[key] = copy.deepcopy(child)
        elif key in FIELD_POOLS:
            result[key] = None if key == "discriminants" and child is None else transform(FIELD_POOLS[key], child)
        elif key == "fn_abis" and isinstance(child, list):
            result[key] = [{**_walk({field: item for field, item in abi.items()
                                   if field not in ("return", "arguments")}, transform),
                            "return": transform("abi_arguments", abi["return"]),
                            "arguments": [transform("abi_arguments", item) for item in abi["arguments"]]}
                           for abi in child]
        elif key == "statements" and isinstance(child, list):
            result[key] = [{**_walk({field: item for field, item in statement.items() if field != "kind"}, transform),
                            "kind": transform("statement_kinds", statement["kind"])} for statement in child]
        else:
            result[key] = _walk(child, transform)
    return result


def project_unused_metadata(document):
    """Drop fields the interpreter never consumes; preserve diagnostic text."""
    result = copy.deepcopy(document)
    for body in result.get("bodies", []):
        if body.get("tainted_by_errors") is not None:
            raise ValueError("cannot project tainted MIR")
        for key in ("mentioned_items", "var_debug_info", "user_type_annotations",
                    "source_instance_kind", "tainted_by_errors", "source_promoted",
                    "coroutine_info", "pass_count"):
            body.pop(key, None)
        for local in body.get("locals", []):
            for key in ("local_info", "mutability", "layout"):
                local.pop(key, None)
        for scope in body.get("source_scopes", []):
            scope.pop("local_data", None)
    for span in result.get("spans", []):
        if isinstance(span.get("ctxt"), dict):
            span["ctxt"] = span["ctxt"]["rustc_debug"]
    return result


def pool_document(document):
    """Test-only schema-8 pooling followed by explicit schema-13 adaptation."""
    if document.get("schema_version") != 8:
        raise ValueError("fixture pooling requires schema 8")
    document = project_unused_metadata(document)
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
    result["schema_version"] = 11
    assert expand_document(result, schema_version=8) == document, "pool projection changed payloads"
    try:
        from .legacy_fixture_schema import adapt_legacy_fixture
    except ImportError:
        from legacy_fixture_schema import adapt_legacy_fixture
    return adapt_legacy_fixture(result)


def expand_document(document, *, schema_version=None):
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
    result["schema_version"] = document["schema_version"] if schema_version is None else schema_version
    return result
