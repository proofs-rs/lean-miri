#!/usr/bin/env python3
"""Check a fresh exporter document has only rustc supplied executable constants."""
import argparse
import collections
import json
from pathlib import Path


def constants(value):
    if isinstance(value, dict):
        constant = value.get("constant")
        if isinstance(constant, dict) and constant.get("kind") in {
            "literal_const", "evaluated_const", "type_constant", "unevaluated_const"
        }:
            yield constant
        for child in value.values():
            yield from constants(child)
    elif isinstance(value, list):
        for child in value:
            yield from constants(child)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("document", type=Path)
    args = parser.parse_args()
    document = json.loads(args.document.read_text())
    assert document["schema"] == "lean-miri-rustc-mir"
    assert not document["ctfe_scalar_sources"], "raw CTFE source catalogue remains populated"
    assert not document["mir_templates"], "runtime source templates remain populated"
    bodies = [body for body in document["bodies"] if body["body_kind"] == "material"]
    assert bodies, "no concrete executable body was exported"
    counts = collections.Counter(constant["kind"] for body in bodies for constant in constants(body))
    assert counts["evaluated_const"] > 0, "fixture did not exercise rustc evaluation"
    assert not counts["type_constant"] and not counts["unevaluated_const"], counts
    print(f"PASS rustc concrete constants: {len(bodies)} bodies, {dict(counts)}")


if __name__ == "__main__":
    main()
