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
    if type(document.get("schema_version")) is not int or document["schema_version"] not in (8, 9):
        raise MirJSONError("MIR root schema_version must be 8 or 9")
    for name in sorted(POOL_NAMES):
        if not isinstance(document.get(name), list):
            raise MirJSONError(f"{name} must be a pool array")
        if any(not isinstance(row, dict) for row in document[name]):
            raise MirJSONError(f"{name} definitions must be objects")
    files = document.get("files")
    if not isinstance(files, list) or any(not isinstance(name, str) for name in files):
        raise MirJSONError("files must be a string array")
    images = document.get("byte_images")
    if not isinstance(images, list) or any(not isinstance(image, str) for image in images):
        raise MirJSONError("byte_images must be a string array")
    if document["schema_version"] == 8:
        if any(isinstance(row.get("field_offsets_bytes"), dict) for row in document["layouts"]):
            raise MirJSONError("compact array field offsets require schema 9")
        for body in document["bodies"]:
            for block in body.get("basic_blocks", []):
                resolution = block.get("terminator", {}).get("kind", {}).get("resolution", {})
                if resolution.get("kind") == "llvm_intrinsic":
                    raise MirJSONError("LLVM no-ABI call evidence requires schema 9")
    return document


def pool_entry(document: dict[str, Any], pool: str, index: Any) -> dict[str, Any]:
    if pool not in POOL_NAMES:
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
