#!/usr/bin/env python3
"""Project an immutable historical fixture to the current test-only input schema."""
import argparse
import hashlib
import json
from pathlib import Path
import sys

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "tools"))
from mir_json import decode_mir_document
from legacy_fixture_schema import adapt_legacy_fixture


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
    document = adapt_legacy_fixture(document)
    decode_mir_document(document)
    adapted = (json.dumps(document, separators=(",", ":")) + "\n").encode()
    output_path.write_bytes(adapted)
    return {"source": str(source_path), "output": str(output_path),
            "source_sha256": hashlib.sha256(raw).hexdigest(),
            "output_sha256": hashlib.sha256(adapted).hexdigest(),
            "schema_version": 13, "all_json_exactly_unchanged": False,
            "adaptation": "test-only legacy schema projection; no new rustc evidence"}


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
