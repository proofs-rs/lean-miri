#!/usr/bin/env python3
"""Validate and copy a maintained MIR input without adapting compiler data."""
import argparse
import hashlib
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "tools"))
from mir_json import decode_mir_document


def reject_duplicate_keys(pairs):
    result = {}
    for key, value in pairs:
        if key in result:
            raise ValueError(f"duplicate JSON object key: {key!r}")
        result[key] = value
    return result


def reject_non_json_constant(value):
    raise ValueError(f"non-JSON numeric constant: {value}")


def copy_fixture(source_path, output_path):
    raw = source_path.read_bytes()
    document = json.loads(raw, object_pairs_hook=reject_duplicate_keys,
                          parse_constant=reject_non_json_constant)
    decode_mir_document(document)
    output_path.write_bytes(raw)
    return {"source": str(source_path), "output": str(output_path),
            "source_sha256": hashlib.sha256(raw).hexdigest(),
            "output_sha256": hashlib.sha256(raw).hexdigest(),
            "schema_version": 7, "all_json_exactly_unchanged": True}


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("source", type=Path)
    parser.add_argument("output", type=Path)
    args = parser.parse_args(argv)
    try:
        result = copy_fixture(args.source, args.output)
    except (OSError, UnicodeDecodeError, ValueError) as error:
        print(f"fixture validation failed: {error}", file=sys.stderr)
        return 1
    print(json.dumps(result, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
