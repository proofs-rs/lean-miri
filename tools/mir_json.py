"""Strict reader and fixture writer for kind-separated numeric MIR tables.

The diagnostic view expands immutable semantic metadata. Compiler type,
instance and allocation references remain bare numeric IDs; local indices keep
their original scope. Historical generic shared graphs are not active input.
"""
from __future__ import annotations

import gzip
import json
from pathlib import Path
from typing import Any
import zlib

SEMANTIC_TABLES_FIELD = "semantic_tables"
SEMANTIC_TABLES_SCHEMA_VERSION = 1
SEMANTIC_KINDS = (
    "spans", "layouts", "function_abis", "generic_args", "regions",
    "constants", "signatures", "binders", "predicates",
    "definitions", "instance_kinds", "argument_abis", "abi_attributes",
    "abi_registers", "cast_targets", "patterns",
)
IDENTITY_FIELDS = ("type_id", "instance_id", "allocation_id", "predicate_id")

class MirJSONError(ValueError):
    """Malformed or unsupported current MIR JSON document."""


def _tag(parent):
    value = parent.get("kind", "")
    return value if isinstance(value, str) else ""


def field_kind(field: str, parent: dict[str, Any]) -> str | None:
    """Schema roles synchronized with the exporter and Lean SemanticTables."""
    tag = _tag(parent)
    if field in {"span", "preamble_def_span", "callsite_span", "function_span", "root_span"}:
        return "spans"
    direct = {"layout": "layouts", "fn_abi": "function_abis", "abi_query": "function_abis",
              "generic_args": "generic_args", "rebased_args": "generic_args",
              "region": "regions", "signature": "signatures", "pattern": "patterns",
              "bound_variables": "binders", "signature_bound_variables": "binders",
              "const": "constants", "constant": "constants", "normalized_operand": "constants",
              "instance_kind": "instance_kinds", "source_instance_kind": "instance_kinds"}
    if field in {"def_id", "instance_def_id", "trait_def_id", "scope_def_id",
                 "method_definition", "parent_trait", "definition", "owner_def_id",
                 "source_def_id", "call_once_def_id", "closure_def_id",
                 "coroutine_closure_def_id", "start_lang_item", "compiler_entry", "hoisted_from"}:
        return "definitions"
    if field in direct:
        return direct[field]
    if field == "signature_query" and ("function_kind" in parent or parent.get("query") ==
            "instantiate_bound_regions_with_erased(fn_sig(instance.def_id()).instantiate(instance.args))"):
        return "signatures"
    if field == "arguments" and tag == "expression":
        return "generic_args"
    if ((field == "length" and tag == "array") or
        (field == "count" and tag == "Repeat") or
        (field in {"start", "end"} and tag == "range")):
        return "constants"
    if field == "value":
        return {"lifetime": "regions", "const": "constants"}.get(tag)
    return None


def _child_role(key, parent, owner_kind, query):
    if key == "value" and query in {"abi_query", "signature_query"}:
        return {"abi_query": "function_abis", "signature_query": "signatures"}[query]
    if owner_kind == "function_abis" and key == "return":
        return "argument_abis"
    if key in {"attributes", "metadata_attributes"} and (
        owner_kind == "cast_targets" or _tag(parent) in {"Direct", "Indirect", "IndirectUnsized"}
    ):
        return "abi_attributes"
    if key in {"first", "second"} and parent.get("kind") == "Pair":
        return "abi_attributes"
    if key == "target" and parent.get("kind") == "Cast":
        return "cast_targets"
    if key == "rest_register" and owner_kind == "cast_targets":
        return "abi_registers"
    return field_kind(key, parent)


def _element_role(key, parent, owner_kind):
    if key == "required_consts":
        return "constants"
    if key == "line_spans":
        return "spans"
    if key == "elements" and parent.get("kind") == "branch":
        return "constants"
    if key == "patterns" and parent.get("kind") == "or":
        return "patterns"
    if key == "arguments" and owner_kind == "function_abis":
        return "argument_abis"
    if key == "prefix_registers" and owner_kind == "cast_targets":
        return "abi_registers"
    if key in {"input_predicates", "output_predicates", "predicates"}:
        return "predicates"
    return None


def _record_kind(value):
    keys = value.keys()
    if {"type", "constant", "span", "user_type_annotation"} <= keys:
        return "constants"
    if len(value) == 2 and {"crate", "index"} <= keys:
        return "definitions"
    if {"calling_convention", "fixed_count"} <= keys:
        return "function_abis"
    if {"inputs", "output", "c_variadic"} <= keys:
        return "signatures"
    if {"abi_align_bytes", "size_bytes"} <= keys:
        return "layouts"
    if {"lo", "hi", "ctxt", "start"} <= keys:
        return "spans"
    if len(value) == 3 and {"type", "layout", "mode"} <= keys:
        return "argument_abis"
    if {"regular_bits", "arg_extension"} <= keys:
        return "abi_attributes"
    if len(value) == 2 and {"size_bits", "kind"} <= keys:
        return "abi_registers"
    if {"prefix_registers", "rest_register"} <= keys:
        return "cast_targets"
    return None


def _natural(value: Any, path: str) -> int:
    if type(value) is not int or value < 0:
        raise MirJSONError(f"{path}: expected a non-negative integer ID")
    return value


def decode_mir_document(document: Any) -> dict[str, Any]:
    """Validate every semantic node and return a shared diagnostic view."""
    if not isinstance(document, dict):
        raise MirJSONError("MIR document root must be an object")
    if document.get("schema") != "lean-miri-rustc-mir":
        raise MirJSONError("document is not a lean-miri-rustc-mir export")
    if type(document.get("schema_version")) is not int or document["schema_version"] != 4:
        raise MirJSONError("current MIR root schema_version must be 4")
    if "shared_payloads" in document:
        raise MirJSONError("obsolete shared_payloads graph; expected semantic_tables")
    catalog = document.get(SEMANTIC_TABLES_FIELD)
    if not isinstance(catalog, dict):
        raise MirJSONError("current MIR document must contain semantic_tables")
    if set(catalog) != {"schema_version", *SEMANTIC_KINDS}:
        raise MirJSONError("semantic_tables must contain exactly schema_version and the semantic kind arrays")
    if type(catalog["schema_version"]) is not int or catalog["schema_version"] != SEMANTIC_TABLES_SCHEMA_VERSION:
        raise MirJSONError("semantic_tables schema_version must be 1")
    for kind in SEMANTIC_KINDS:
        if not isinstance(catalog[kind], list):
            raise MirJSONError(f"semantic_tables.{kind} must be an array")
    predicate_indices = {}
    for index, node in enumerate(catalog["predicates"]):
        if not isinstance(node, dict):
            raise MirJSONError("semantic_tables.predicates entries must be identity records")
        identity = _natural(node.get("predicate_id"), f"semantic_tables.predicates[{index}].predicate_id")
        if identity in predicate_indices:
            raise MirJSONError(f"duplicate predicate identity {identity}")
        predicate_indices[identity] = index
    cache = {}
    active = set()

    def lookup(kind, identity):
        identity = _natural(identity, kind)
        index = predicate_indices.get(identity) if kind == "predicates" else identity
        if index is None or index >= len(catalog[kind]):
            raise MirJSONError(f"dangling {kind} reference {identity}")
        key = kind, index
        if key in active:
            raise MirJSONError(f"cycle in semantic_tables at {kind}[{index}]")
        if key not in cache:
            active.add(key)
            try:
                cache[key] = expand(catalog[kind][index], owner_kind=kind)
            finally:
                active.remove(key)
        return cache[key]

    def expand(value, role=None, owner_kind=None, query=None):
        if value is None:
            return None
        if role is not None:
            return lookup(role, value)
        if isinstance(value, list):
            return [expand(child) for child in value]
        if not isinstance(value, dict):
            return value
        if "$lean_miri_shared_ref" in value:
            raise MirJSONError("obsolete $lean_miri_shared_ref marker")
        if len(value) == 1 and next(iter(value)) in IDENTITY_FIELDS:
            raise MirJSONError("obsolete object-shaped compiler identity reference")
        result = {}
        for key, child in value.items():
            if key in {"entry_instance", "fallback_instance", "instance", "instance_id", "original_instance_id"} and child is not None and value.get("status") != "debug_payload":
                _natural(child, key)
            element_role = _element_role(key, value, owner_kind)
            if element_role is not None:
                if not isinstance(child, list):
                    raise MirJSONError(f"{key}: expected an array of numeric references")
                result[key] = [expand(item, element_role) for item in child]
            else:
                child_query = "abi_query" if key == "abi_query" else (
                    "signature_query" if key == "signature_query" and (
                        "function_kind" in value or value.get("query") ==
                        "instantiate_bound_regions_with_erased(fn_sig(instance.def_id()).instantiate(instance.args))"
                    ) else None)
                result[key] = expand(child, _child_role(key, value, owner_kind, query), query=child_query)

        return result

    for kind in SEMANTIC_KINDS:
        for index, node in enumerate(catalog[kind]):
            identity = node["predicate_id"] if kind == "predicates" else index
            lookup(kind, identity)
    return expand({key: value for key, value in document.items()
                   if key != SEMANTIC_TABLES_FIELD})


def encode_mir_document(document: dict[str, Any]) -> dict[str, Any]:
    """Encode a mutable diagnostic view for synthetic fixture mutations.

    This is a source-derived transport adapter, not compiler evidence. Identity
    numbers are preserved; only immutable metadata is structurally interned.
    """
    if "semantic_tables" in document or "shared_payloads" in document:
        raise MirJSONError("fixture encoder expects an expanded document")
    tables = {kind: [] for kind in SEMANTIC_KINDS}
    indices = {kind: {} for kind in SEMANTIC_KINDS}
    predicates = {}
    instance_identities = {
        row["instance_id"]: (row["instance_kind"], row["generic_args"])
        for row in document.get("instances", [])
        if isinstance(row, dict) and "instance_id" in row and "instance_kind" in row and "generic_args" in row
    }

    def visit(value, role=None, preserve_identity=False):
        if value is None:
            return None
        if role == "definitions" and isinstance(value, str):
            parts = value.split(":")
            if len(parts) == 2 and all(part.isdecimal() for part in parts):
                value = {"crate": int(parts[0]), "index": int(parts[1])}
        if isinstance(value, dict):
            if (not preserve_identity and {"instance_id", "instance_kind", "generic_args"} <= value.keys()
                and value.keys() <= {"instance_id", "instance_kind", "generic_args"}):
                identity = _natural(value["instance_id"], "instance_id")
                if instance_identities.get(identity) != (value["instance_kind"], value["generic_args"]):
                    raise MirJSONError(f"instance reference {identity} differs from canonical identity")
                return identity
            role = role or _record_kind(value)
            if "$lean_miri_shared_ref" in value:
                raise MirJSONError("obsolete $lean_miri_shared_ref marker")
            if len(value) == 1 and next(iter(value)) in IDENTITY_FIELDS:
                return _natural(next(iter(value.values())), next(iter(value)))
            result = {}
            for key in sorted(value):
                child = value[key]
                if key in {"line_spans", "required_consts"} or (key == "elements" and value.get("kind") == "branch") or (key == "patterns" and value.get("kind") == "or"):
                    element_role = "spans" if key == "line_spans" else "patterns" if key == "patterns" else "constants"
                    result[key] = [visit(item, element_role) for item in child]
                else:
                    result[key] = visit(child, field_kind(key, value))
            if "predicate_id" in result and _tag(value) in {"trait", "auto_trait", "projection"}:
                identity = _natural(result["predicate_id"], "predicate_id")
                if identity in predicates and predicates[identity] != result:
                    raise MirJSONError(f"conflicting predicate identity {identity}")
                predicates[identity] = result
                return identity
        elif isinstance(value, list):
            result = [visit(child) for child in value]
        else:
            result = value
        if role is None:
            return result
        key = json.dumps(result, sort_keys=True, separators=(",", ":"), ensure_ascii=False)
        if key not in indices[role]:
            indices[role][key] = len(tables[role])
            tables[role].append(result)
        return indices[role][key]

    result = {key: ([visit(row, preserve_identity=True) for row in value]
                    if key == "instances" and isinstance(value, list) else visit(value))
              for key, value in sorted(document.items())}
    tables["predicates"] = [predicates[key] for key in sorted(predicates)]
    result["semantic_tables"] = {"schema_version": 1, **tables}
    return result


def load_mir_document(path: str | Path) -> dict[str, Any]:
    """Read, validate, and expand one current numeric-table MIR JSON file."""
    try:
        source = Path(path)
        if source.suffix == ".gz":
            with gzip.open(source, "rt", encoding="utf-8") as stream:
                document = json.load(stream)
        else:
            document = json.loads(source.read_text(encoding="utf-8"))
    except (OSError, EOFError, UnicodeError, json.JSONDecodeError, zlib.error) as exc:
        raise MirJSONError(f"cannot read MIR JSON {path}: {exc}") from exc
    return decode_mir_document(document)


TYPE_REFERENCE_FIELDS = frozenset({
    "type", "input_type", "output_type", "function_type", "self_type", "pointee",
    "element", "base", "target_type", "source_type", "normalized_type", "inner_type",
    "cast_type", "return_type", "function_pointer_type", "input_source", "input_target",
    "source_pointee_type", "target_pointee_type", "source_tail_type", "target_tail_type",
    "source_tail", "target_tail", "receiver_type", "field_type", "result_type",
    "clone_type", "coroutine_type", "drop_type", "element_type", "implementation_coroutine_type",
    "inner", "pointee_type", "pointer_tag_integer", "proxy_coroutine_type", "query_input_type",
    "type_name_result_type", "yield_type", "resume_type", "str_type", "resulting_type",
    "layout_query_input_type", "implicit_overflow_tuple_type",
})
TYPE_REFERENCE_ARRAYS = frozenset({"inputs", "input_types", "extra_argument_types", "field_types"})


def _core_child_context(parent, key, context):
    if key == "compiler_runtime_primitives":
        return "runtime_primitives"
    if key in {"compiler_libc_type_layouts", "compiler_windows_type_layouts"}:
        return "type_layout_catalog"
    if context == "type_layout_catalog" and key == "entries":
        return "type_queries"
    if key in {"compiler_named_types", "type_queries"}:
        return "type_queries"
    if context == "type_queries":
        return "type_query"
    if context == "runtime_primitives" and key in {"caller_location_type", "ordering_enum"}:
        return "type_query"
    if key in {"mut_pointer_type", "mut_reference_type"} and "input_type_id" in parent:
        return "type_query"
    if key == "drop_glue" and "input_type_id" in parent:
        return "instance_query"
    if key == "resolved" and {"original_instance_id", "method_definition"} <= parent.keys():
        return "instance_query"
    if key == "allocation_query":
        return "allocation_query"
    return "ordinary"


def core_references(value, _context="ordinary"):
    """Yield type/instance/allocation references from a diagnostic view.

    Explicit identity fields on full rows are included. Local/block/scope and
    scalar numeric payloads are never treated as global compiler identities.
    This inventory supports fixture coverage assertions, not readiness checks.
    """
    if isinstance(value, list):
        for child in value:
            yield from core_references(child, _context)
    elif isinstance(value, dict):
        if value.get("status") == "debug_payload":
            return
        for key, child in value.items():
            query = value.get("query_kind")
            child_context = _core_child_context(value, key, _context)
            if type(child) is int and (_context in {"type_queries", "runtime_primitives"}
                                      or child_context == "type_query"):
                yield "type_id", child
            elif type(child) is int and child_context == "instance_query":
                yield "instance_id", child
            elif type(child) is int and key == "allocation_query":
                yield "allocation_id", child
            elif key in {"type_id", "input_type_id"} and type(child) is int:
                yield "type_id", child
            elif key in {"instance_id", "original_instance_id"} and type(child) is int:
                yield "instance_id", child
            elif key in {"allocation_id", "vtable_allocation_id", "key_allocation_id", "opaque_allocation_id"} and type(child) is int:
                yield "allocation_id", child
            elif key in TYPE_REFERENCE_FIELDS and type(child) is int:
                yield "type_id", child
            elif key == "output" and "inputs" in value and type(child) is int:
                yield "type_id", child
            elif _context == "runtime_primitives" and key not in {"caller_location_type", "ordering_enum"} and type(child) is int:
                yield "type_id", child
            elif key in {"entry_instance", "fallback_instance", "instance"} and type(child) is int:
                yield "instance_id", child
            elif (key in {"allocation", "existing_allocation"} or key == "target" and "storage_offset_bytes" in value) and type(child) is int:
                yield "allocation_id", child
            elif key == "covered_allocation_ids" and isinstance(child, list):
                for identity in child:
                    if type(identity) is int:
                        yield "allocation_id", identity
            elif key == "value" and (_context == "type_query" or query == "box_type" or value.get("kind") == "type") and type(child) is int:
                yield "type_id", child
            elif key == "value" and (_context == "instance_query" or query in {"resolve_fn_ptr", "resolve_closure_fn_once"}) and type(child) is int:
                yield "instance_id", child
            elif key == "value" and _context == "allocation_query" and type(child) is int:
                yield "allocation_id", child
            elif (key in TYPE_REFERENCE_ARRAYS or key == "elements" and value.get("kind") == "tuple") and isinstance(child, list):
                for identity in child:
                    if type(identity) is int:
                        yield "type_id", identity
            yield from core_references(child, child_context)
