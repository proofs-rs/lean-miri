"""Read MIR documents without replacing typed pool references with payloads."""

from __future__ import annotations

import gzip
import json
from pathlib import Path
from typing import Any
import zlib

try:  # Support package imports and direct scripts under tools/.
    from .shared_json_pools import SHARED_POOLS, expand_document
    from .coroutine_json import validate_catalog
except ImportError:
    from shared_json_pools import SHARED_POOLS, expand_document
    from coroutine_json import validate_catalog

POOL_NAMES = frozenset({"types", "allocations", "instances", "fn_abis", "spans",
                        "definitions", "type_constants", "bodies", "predicates"})


class MirJSONError(ValueError):
    """Malformed or unsupported MIR document."""


def decode_mir_document(document: Any) -> dict[str, Any]:
    if not isinstance(document, dict):
        raise MirJSONError("MIR document root must be an object")
    if document.get("schema") != "lean-miri-rustc-mir":
        raise MirJSONError("document is not a lean-miri-rustc-mir export")
    if type(document.get("schema_version")) is not int or document["schema_version"] != 13:
        raise MirJSONError("MIR root schema_version must be 13")
    for name in sorted(POOL_NAMES):
        if not isinstance(document.get(name), list):
            raise MirJSONError(f"{name} must be a pool array")
        if any(not isinstance(row, dict) for row in document[name]):
            raise MirJSONError(f"{name} definitions must be objects")
    layouts = document.get("layouts")
    if not isinstance(layouts, list) or any(type(index) is not int or index < 0 for index in layouts):
        raise MirJSONError("layouts must be a nonnegative reference array")
    for name, row_type in SHARED_POOLS.items():
        rows = document.get(name)
        if not isinstance(rows, list) or any(not isinstance(row, row_type) for row in rows):
            raise MirJSONError(f"{name} must be a pool of {row_type.__name__} values")
    files = document.get("files")
    if not isinstance(files, list) or any(not isinstance(name, str) for name in files):
        raise MirJSONError("files must be a string array")
    images = document.get("byte_images")
    if not isinstance(images, list) or any(not isinstance(image, str) for image in images):
        raise MirJSONError("byte_images must be a string array")
    try:
        validate_catalog(document)
    except (ValueError, KeyError, TypeError) as exc:
        raise MirJSONError(f"invalid compiler_coroutine_coverage: {exc}") from exc
    return document


def pool_entry(document: dict[str, Any], pool: str, index: Any) -> Any:
    if pool == "layouts":
        references = document.get("layouts", [])
        if type(index) is not int or index < 0 or index >= len(references):
            raise MirJSONError(f"layouts reference {index!r} is out of range")
        if isinstance(references[index], dict):
            return references[index]  # Explicit semantic inspection view.
        return pool_entry(document, "layout_values", references[index])
    if pool not in POOL_NAMES and pool not in SHARED_POOLS:
        raise MirJSONError(f"unknown MIR pool {pool!r}")
    rows = document.get(pool)
    if not isinstance(rows, list):
        raise MirJSONError(f"{pool} must be a pool array")
    if pool == "allocations":
        if type(index) is not int or index < 0:
            raise MirJSONError(f"{pool} reference {index!r} is out of range")
        matches = []
        for row in rows:
            if not isinstance(row, dict):
                raise MirJSONError("allocations definitions must be objects")
            if row.get("kind") == "function":
                for identity in row.get("identities", []):
                    if identity[0] == index:
                        matches.append({"kind": "function", "instance_id": row["instance_id"],
                                        "allocation_id": identity[0], "source_alloc_id": identity[1]})
            elif row.get("allocation_id") == index:
                matches.append(row)
        if len(matches) != 1:
            raise MirJSONError(f"allocations reference {index!r} does not identify one graph node")
        return matches[0]
    if type(index) is not int or index < 0 or index >= len(rows):
        raise MirJSONError(f"{pool} reference {index!r} is out of range")
    row = rows[index]
    row_type = SHARED_POOLS.get(pool, dict)
    if not isinstance(row, row_type):
        raise MirJSONError(f"{pool}[{index}] must be an object")
    return row


def load_mir_document(path: str | Path) -> dict[str, Any]:
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


def inspection_document(document: dict[str, Any]) -> dict[str, Any]:
    """Resolve payloads for analysis while retaining graph/type/layout identity IDs."""
    try:
        return expand_document(document)
    except ValueError as exc:
        raise MirJSONError(str(exc)) from exc


def load_mir_inspection_document(path: str | Path) -> dict[str, Any]:
    """Load a schema-13 document and explicitly resolve shared inspection payloads."""
    return inspection_document(load_mir_document(path))
