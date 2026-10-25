#!/usr/bin/env python3
"""Attach the required empty v2 shared graph to archived eval-core fixtures.

This helper is for the maintained eval-core unit runner only. It does not
rewrite or regenerate the archived compiler exports.
"""

import argparse
import hashlib
import json
from pathlib import Path
import sys

CATALOG_MEMBER = '"shared_payloads":{"schema_version":2,"nodes":[]}'


def reject_duplicate_keys(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON object key: {key!r}")
        result[key] = value
    return result


def reject_non_json_constant(value):
    raise ValueError(f"non-JSON numeric constant: {value}")


DECODER = json.JSONDecoder(
    object_pairs_hook=reject_duplicate_keys,
    parse_constant=reject_non_json_constant,
)


def skip_space(text, offset):
    while offset < len(text) and text[offset] in " \t\r\n":
        offset += 1
    return offset


def parse_document(text):
    start = skip_space(text, 0)
    document, end = DECODER.raw_decode(text, start)
    if text[end:].strip():
        raise ValueError("trailing non-whitespace after the JSON document")
    if not isinstance(document, dict):
        raise ValueError("eval-core fixture root must be a JSON object")
    return document, start, end


def top_level_member_spans(text, start, end):
    """Return each root key's value span, retaining exact original text."""
    spans = {}
    offset = skip_space(text, start)
    if offset >= end or text[offset] != "{":
        raise ValueError("eval-core fixture root must be a JSON object")
    offset += 1
    while True:
        offset = skip_space(text, offset)
        if offset >= end:
            raise ValueError("unterminated JSON object")
        if text[offset] == "}":
            return spans
        key, key_end = DECODER.raw_decode(text, offset)
        if not isinstance(key, str):
            raise ValueError("JSON object key was not a string")
        if key in spans:
            raise ValueError(f"duplicate top-level JSON object key: {key!r}")
        offset = skip_space(text, key_end)
        if offset >= end or text[offset] != ":":
            raise ValueError(f"missing colon after top-level key {key!r}")
        value_start = skip_space(text, offset + 1)
        _, value_end = DECODER.raw_decode(text, value_start)
        spans[key] = (value_start, value_end)
        offset = skip_space(text, value_end)
        if offset >= end:
            raise ValueError("unterminated JSON object")
        if text[offset] == ",":
            offset += 1
        elif text[offset] == "}":
            return spans
        else:
            raise ValueError(f"expected comma or object end after key {key!r}")


def exact_json_equal(left, right):
    """Compare JSON types, list order, object key order, and scalar values."""
    if type(left) is not type(right):
        return False
    if isinstance(left, dict):
        return list(left) == list(right) and all(
            exact_json_equal(left[key], right[key]) for key in left
        )
    if isinstance(left, list):
        return len(left) == len(right) and all(
            exact_json_equal(a, b) for a, b in zip(left, right)
        )
    return left == right


def prepare_schema3_fixture(source_path, output_path):
    source_bytes = source_path.read_bytes()
    source_text = source_bytes.decode("utf-8")
    source_doc, root_start, root_end = parse_document(source_text)
    if source_doc.get("schema") != "lean-miri-rustc-mir":
        raise ValueError("unexpected eval-core MIR schema name")
    if type(source_doc.get("schema_version")) is not int or source_doc["schema_version"] != 2:
        raise ValueError("archived eval-core input must have schema_version 2")
    if "shared_payloads" in source_doc:
        raise ValueError("archived schema-2 input unexpectedly already has shared_payloads")

    spans = top_level_member_spans(source_text, root_start, root_end)
    if "schema_version" not in spans:
        raise ValueError("archived eval-core input is missing top-level schema_version")
    version_start, version_end = spans["schema_version"]
    if source_text[version_start:version_end] != "2":
        raise ValueError("schema_version must be the exact JSON integer token 2")

    # Replace only the schema number, then append the catalog before the root
    # close. All other source characters remain byte-for-byte in place.
    root_close = root_end - 1
    if source_text[root_close] != "}":
        raise ValueError("JSON parser did not locate the root object terminator")
    addition = ("," if source_doc else "") + CATALOG_MEMBER
    converted_text = (
        source_text[:version_start]
        + "3"
        + source_text[version_end:root_close]
        + addition
        + source_text[root_close:]
    )

    converted_doc, converted_start, converted_end = parse_document(converted_text)
    expected_doc = dict(source_doc)
    expected_doc["schema_version"] = 3
    expected_doc["shared_payloads"] = {"schema_version": 2, "nodes": []}
    if not exact_json_equal(converted_doc, expected_doc):
        raise ValueError("converted document differs outside the two intended schema fields")
    if list(converted_doc) != list(source_doc) + ["shared_payloads"]:
        raise ValueError("conversion changed existing root field order")

    # Reversing only the two authorized textual edits must recover the exact
    # archived source string, including whitespace and numeric spellings.
    without_catalog = (
        converted_text[:root_close]
        + converted_text[root_close + len(addition):]
    )
    restored_text = (
        without_catalog[:version_start]
        + "2"
        + without_catalog[version_start + 1:]
    )
    if restored_text != source_text:
        raise ValueError("conversion changed source text outside schema_version/catalog")

    output_bytes = converted_text.encode("utf-8")
    # Verify round-trip once more before writing any output.
    if not exact_json_equal(json.loads(
        output_bytes,
        object_pairs_hook=reject_duplicate_keys,
        parse_constant=reject_non_json_constant,
    ), expected_doc):
        raise ValueError("serialized schema-3 output failed exact structural verification")
    output_path.write_bytes(output_bytes)
    return {
        "source": str(source_path),
        "output": str(output_path),
        "source_sha256": hashlib.sha256(source_bytes).hexdigest(),
        "output_sha256": hashlib.sha256(output_bytes).hexdigest(),
        "source_bytes": len(source_bytes),
        "output_bytes": len(output_bytes),
        "schema_version": "2 -> 3",
        "shared_payloads": {"schema_version": 2, "nodes": []},
        "unchanged_existing_fields": len(source_doc) - 1,
        "all_other_json_exactly_unchanged": True,
    }


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args(argv)
    try:
        result = prepare_schema3_fixture(args.source, args.output)
    except (OSError, UnicodeDecodeError, ValueError, json.JSONDecodeError) as error:
        print(f"schema-3 fixture preparation failed: {error}", file=sys.stderr)
        return 1
    print(json.dumps(result, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
