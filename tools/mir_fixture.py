"""Explicit transport conversion for retained compiler evidence in tests.

Only fixture builders and historical comparisons use this module. Active MIR
readers accept schema 4 only. Conversion preserves semantic data and compiler
identities; it does not rerun rustc or certify old evidence against new semantics.
"""
import gzip
import hashlib
import json
from pathlib import Path

from mir_json import decode_mir_document, encode_mir_document, MirJSONError


def read_evidence(path):
    path = Path(path)
    if path.suffix == ".gz":
        with gzip.open(path, "rt", encoding="utf-8") as stream:
            return json.load(stream)
    return json.loads(path.read_text(encoding="utf-8"))


def historical_view(document):
    if document.get("schema_version") == 4:
        return decode_mir_document(document)
    if document.get("schema") != "lean-miri-rustc-mir" or document.get("schema_version") not in {2, 3}:
        raise MirJSONError("unrecognized historical MIR evidence")
    nodes = document.get("shared_payloads", {}).get("nodes", [])
    cache = {}
    active = set()

    def expand(value):
        if isinstance(value, list):
            return [expand(child) for child in value]
        if not isinstance(value, dict):
            return value
        marker = "$lean_miri_shared_ref"
        if marker in value:
            if set(value) != {marker}:
                raise MirJSONError("malformed historical reference")
            identity = value[marker]
            if type(identity) is not int or identity < 0 or identity >= len(nodes):
                raise MirJSONError("historical reference outside catalog")
            if identity in active:
                raise MirJSONError("cyclic historical reference")
            if identity not in cache:
                active.add(identity)
                try:
                    cache[identity] = expand(nodes[identity])
                finally:
                    active.remove(identity)
            return cache[identity]
        return {key: expand(child) for key, child in value.items()}

    return expand({key: value for key, value in document.items() if key != "shared_payloads"})


def _current_schema_fields(value):
    """Rename historical TLS memory images without assigning allocation IDs.

    The image describes a fresh allocation for each runtime thread. It is not
    a reference to the compilation's canonical allocation table.
    """
    if isinstance(value, list):
        return [_current_schema_fields(child) for child in value]
    if not isinstance(value, dict):
        return value
    result = {key: _current_schema_fields(child) for key, child in value.items()}
    if result.get("kind") == "ThreadLocalRef":
        initializer = result.get("initializer")
        if isinstance(initializer, dict) and "allocation" in initializer:
            if "allocation_template" in initializer:
                raise MirJSONError("historical TLS initializer has both allocation and allocation_template")
            result["initializer"] = {
                "allocation_template" if key == "allocation" else key: child
                for key, child in initializer.items()
            }
    if (result.get("kind") == "static" and "symbol" in result and
            "declaration" in result and "allocation" in result):
        if "allocation_query" in result:
            raise MirJSONError("historical selected static has both allocation and allocation_query")
        result = {"allocation_query" if key == "allocation" else key: child
                  for key, child in result.items()}
    return result


def convert_evidence(document):
    expanded = _current_schema_fields(historical_view(document))
    expanded["schema_version"] = 4
    return encode_mir_document(expanded)


def prepare_schema3_replay(source_path, output_path):
    """Prepare a separate schema-4 test input from verified schema-3 evidence.

    Callers verify the original archive/reference identity before this step.
    The returned manifest records the transport change; the original reference
    remains bound to source bytes and is never relabeled as observing output.
    This helper is deliberately outside every active input reader.
    """
    source_path, output_path = Path(source_path), Path(output_path)
    source_bytes = source_path.read_bytes()
    source = json.loads(source_bytes)
    if type(source.get("schema_version")) is not int or source["schema_version"] != 3:
        raise MirJSONError("saved replay preparation requires schema_version 3")
    converted = convert_evidence(source)
    decode_mir_document(converted)
    output_bytes = (json.dumps(converted, separators=(",", ":"), ensure_ascii=False) + "\n").encode()
    with output_path.open("xb") as stream:
        stream.write(output_bytes)
    return {
        "conversion": "schema3_to_schema4_test_transport_only",
        "compiler_reexecuted": False,
        "source": str(source_path), "execution_input": str(output_path),
        "source_sha256": hashlib.sha256(source_bytes).hexdigest(),
        "execution_sha256": hashlib.sha256(output_bytes).hexdigest(),
        "source_bytes": len(source_bytes), "execution_bytes": len(output_bytes),
        "reference_identity": "original_source_bytes_only",
    }
