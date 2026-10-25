"""Strict reader for the current shared-payload MIR JSON wire format.

Active MIR consumers must use this module instead of ``json.load``.  The
on-disk document keeps ordinary root metadata inline and stores shared payload
nodes in a bottom-up graph.  This reader validates that graph before exposing
the familiar expanded JSON view to existing validators.

Historical evidence archives are intentionally not accepted here: callers
which compare historical documents should read those as historical JSON and
use this decoder only for current exporter output.
"""

from __future__ import annotations

import json
import gzip
from pathlib import Path
from typing import Any
import zlib

SHARED_PAYLOADS_FIELD = "shared_payloads"
SHARED_REF_FIELD = "$lean_miri_shared_ref"
SHARED_PAYLOADS_SCHEMA_VERSION = 2


class MirJSONError(ValueError):
    """Malformed or unsupported current MIR JSON document."""


def decode_mir_document(document: Any) -> dict[str, Any]:
    """Validate and expand one current MIR shared-payload graph document."""
    if not isinstance(document, dict):
        raise MirJSONError("MIR document root must be an object")
    if SHARED_REF_FIELD in document:
        raise MirJSONError(f"reserved {SHARED_REF_FIELD!r} marker is not valid at the document root")
    if document.get("schema") != "lean-miri-rustc-mir":
        raise MirJSONError("document is not a lean-miri-rustc-mir export")
    if document.get("schema_version") != 3:
        raise MirJSONError("current MIR root schema_version must be 3")

    catalog = document.get(SHARED_PAYLOADS_FIELD)
    if not isinstance(catalog, dict):
        raise MirJSONError("current MIR document must contain a shared_payloads graph")
    if set(catalog) != {"schema_version", "nodes"}:
        raise MirJSONError("shared_payloads must contain only schema_version and nodes")
    if catalog.get("schema_version") != SHARED_PAYLOADS_SCHEMA_VERSION:
        raise MirJSONError(
            f"shared_payloads schema_version must be {SHARED_PAYLOADS_SCHEMA_VERSION}"
        )
    nodes = catalog.get("nodes")
    if not isinstance(nodes, list):
        raise MirJSONError("shared_payloads.nodes must be an array")

    cache: dict[int, Any] = {}

    def expand(value: Any, *, parent_node: int | None, active: set[int]) -> Any:
        if isinstance(value, list):
            return [expand(child, parent_node=parent_node, active=active) for child in value]
        if not isinstance(value, dict):
            return value

        if SHARED_REF_FIELD in value:
            if set(value) != {SHARED_REF_FIELD}:
                raise MirJSONError(f"reserved {SHARED_REF_FIELD!r} marker must be a one-key reference object")
            index = value[SHARED_REF_FIELD]
            if isinstance(index, bool) or not isinstance(index, int) or index < 0:
                raise MirJSONError(f"{SHARED_REF_FIELD} must contain a non-negative integer")
            if index in active:
                raise MirJSONError(f"cycle in shared_payloads graph at node {index}")
            if index >= len(nodes):
                raise MirJSONError(f"shared_payloads reference {index} is out of range")
            if parent_node is not None and index >= parent_node:
                raise MirJSONError(
                    f"shared_payloads node {parent_node} has a forward reference to node {index}"
                )
            if index not in cache:
                active.add(index)
                try:
                    cache[index] = expand(nodes[index], parent_node=index, active=active)
                finally:
                    active.remove(index)
            # Preserve graph sharing in memory. Decoded documents are read-only
            # views; callers that need to mutate one occurrence should deepcopy
            # the document root first.
            return cache[index]

        return {
            key: expand(child, parent_node=parent_node, active=active)
            for key, child in value.items()
        }

    # Decode every node, including nodes that happen not to be referenced by
    # the root, so malformed/reserved content cannot hide in unused payloads.
    for index in range(len(nodes)):
        if index not in cache:
            cache[index] = expand(nodes[index], parent_node=index, active={index})

    result = {
        key: expand(value, parent_node=None, active=set())
        for key, value in document.items()
        if key != SHARED_PAYLOADS_FIELD
    }
    return result


def load_mir_document(path: str | Path) -> dict[str, Any]:
    """Read, validate, and expand one current MIR shared-payload JSON file."""
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
