"""Read MIR documents without replacing typed pool references with payloads."""

from __future__ import annotations

import gzip
import json
from pathlib import Path
from typing import Any
import zlib

POOL_NAMES = frozenset({"types", "allocations", "instances", "layouts", "fn_abis", "spans",
                        "definitions", "type_constants", "bodies", "predicates"})


class MirJSONError(ValueError):
    """Malformed or unsupported MIR document."""


def decode_mir_document(document: Any) -> dict[str, Any]:
    if not isinstance(document, dict):
        raise MirJSONError("MIR document root must be an object")
    if document.get("schema") != "lean-miri-rustc-mir":
        raise MirJSONError("document is not a lean-miri-rustc-mir export")
    if type(document.get("schema_version")) is not int or document["schema_version"] != 4:
        raise MirJSONError("MIR root schema_version must be 4")
    for name in sorted(POOL_NAMES):
        if not isinstance(document.get(name), list):
            raise MirJSONError(f"{name} must be a pool array")
        if any(not isinstance(row, dict) for row in document[name]):
            raise MirJSONError(f"{name} definitions must be objects")
    return document


def pool_entry(document: dict[str, Any], pool: str, index: Any) -> dict[str, Any]:
    if pool not in POOL_NAMES:
        raise MirJSONError(f"unknown MIR pool {pool!r}")
    rows = document.get(pool)
    if not isinstance(rows, list):
        raise MirJSONError(f"{pool} must be a pool array")
    if type(index) is not int or index < 0 or index >= len(rows):
        raise MirJSONError(f"{pool} reference {index!r} is out of range")
    row = rows[index]
    if not isinstance(row, dict):
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
