#!/usr/bin/env python3
"""Derive focused decoder edge inputs from an archived genuine export."""
import copy
import json
import pathlib
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[2] / "tools"))
from mir_json import load_mir_document


def replace_first_span(value):
    if isinstance(value, dict):
        for key, child in value.items():
            if key == "span" and "scope" in value and isinstance(child, dict) and all(
                item in child for item in ("lo", "hi", "start", "end", "ctxt", "file")
            ):
                value[key] = {"$lean_miri_shared_ref": 0}
                return True
            if replace_first_span(child):
                return True
    elif isinstance(value, list):
        for child in value:
            if replace_first_span(child):
                return True
    return False


def replace_first_debug(value):
    if isinstance(value, dict):
        for key, child in value.items():
            if key == "file" and isinstance(child, dict) and child.get("status") == "debug_payload":
                value[key] = {"status": "unsupported", "rustc_debug": "malformed diagnostic"}
                return True
            if replace_first_debug(child):
                return True
    elif isinstance(value, list):
        for child in value:
            if replace_first_debug(child):
                return True
    return False


def main(source: str, output: str) -> None:
    # Derive semantic mutations from the validated expanded document. An empty
    # valid catalog lets every case reach its intended semantic decoder check.
    base = load_mir_document(source)
    base["shared_payloads"] = {"schema_version": 2, "nodes": []}
    out = pathlib.Path(output)
    out.mkdir(parents=True, exist_ok=True)
    cases = {}

    value = copy.deepcopy(base)
    value["schema_version"] = 999
    cases["bad-schema-version"] = value

    value = copy.deepcopy(base)
    value["bodies"][0]["phase"] = {"kind": 17, "phase": "optimized", "status": "supported"}
    cases["bad-mir-phase-tag"] = value

    value = copy.deepcopy(base)
    region = None
    def find_region(item):
        nonlocal region
        if region is not None:
            return
        if isinstance(item, dict):
            if isinstance(item.get("region"), dict) and "kind" in item["region"]:
                region = item["region"]
                return
            for child in item.values():
                find_region(child)
        elif isinstance(item, list):
            for child in item:
                find_region(child)
    find_region(value)
    if region is None:
        raise SystemExit("base input has no compiler region evidence")
    region["kind"] = 17
    cases["bad-region-tag"] = value

    value = copy.deepcopy(base)
    if not replace_first_debug(value):
        raise SystemExit("base input has no debug payload")
    cases["bad-debug-payload"] = value

    value = copy.deepcopy(base)
    if not replace_first_span(value):
        raise SystemExit("base input has no source span")
    cases["missing-span-catalog"] = value

    def first_statement(document):
        return document["bodies"][0]["basic_blocks"][0]["statements"][0]

    value = copy.deepcopy(base)
    statement = first_statement(value)
    statement["variant"] = "Coverage"
    statement["coverage"] = {"kind": "future_coverage", "status": "supported"}
    cases["coverage-tag-wrapper"] = value

    value = copy.deepcopy(base)
    statement = first_statement(value)
    statement["variant"] = "AscribeUserType"
    statement["user_type_projection"] = {"status": "supported"}
    statement["variance"] = {"kind": "future_variance", "status": "supported"}
    cases["user-projection-wrapper"] = value

    for name, document in cases.items():
        path = out / f"{name}.json"
        path.write_text(json.dumps(document, separators=(",", ":")), encoding="utf-8")
        print(f"{path} {path.stat().st_size}")


if __name__ == "__main__":
    if len(sys.argv) != 3:
        raise SystemExit("usage: make_runtime_decode_cases165.py <base.json> <output-dir>")
    main(sys.argv[1], sys.argv[2])
