#!/usr/bin/env python3
"""Copy a maintained schema-3 eval-core input without adapting compiler data."""
import argparse
import hashlib
import json
from pathlib import Path
import sys


def reject_duplicate_keys(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON object key: {key!r}")
        result[key] = value
    return result


def reject_non_json_constant(value):
    raise ValueError(f"non-JSON numeric constant: {value}")


def prepare_schema3_fixture(source_path, output_path):
    raw = source_path.read_bytes()
    document = json.loads(raw, object_pairs_hook=reject_duplicate_keys,
                          parse_constant=reject_non_json_constant)
    if not isinstance(document, dict) or document.get("schema") != "lean-miri-rustc-mir":
        raise ValueError("unexpected eval-core MIR schema name")
    if type(document.get("schema_version")) is not int or document["schema_version"] != 3:
        raise ValueError("maintained eval-core input must have schema_version 3")
    catalog = document.get("shared_payloads")
    if not isinstance(catalog, dict) or catalog.get("schema_version") != 2 or not isinstance(catalog.get("nodes"), list):
        raise ValueError("maintained eval-core input must contain its shared graph")
    output_path.write_bytes(raw)
    return {"source": str(source_path), "output": str(output_path),
            "source_sha256": hashlib.sha256(raw).hexdigest(),
            "output_sha256": hashlib.sha256(raw).hexdigest(),
            "schema_version": 3, "all_json_exactly_unchanged": True}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args(argv)
    try:
        result = prepare_schema3_fixture(args.source, args.output)
    except (OSError, UnicodeDecodeError, ValueError) as error:
        print(f"schema-3 fixture preparation failed: {error}", file=sys.stderr)
        return 1
    print(json.dumps(result, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
