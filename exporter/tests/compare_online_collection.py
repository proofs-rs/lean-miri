#!/usr/bin/env python3
"""Compare two current transport exports across online collection.

Only invocation paths, vtable ID renaming/table order, and the explicitly
validated migration of per-call virtual candidates to a dense index differ.
The existing HashSet-ordered instance ABI catalog is compared as a multiset;
all other semantic fields and array order must agree exactly.
"""
import argparse
import json
from pathlib import Path
import sys
sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "tools"))
from mir_json import load_mir_document


def query_keys(document):
    result = {}
    for row in document["compiler_vtable_queries"]:
        key = (row["input_type"]["type_id"], tuple(p["predicate_id"] for p in row["input_predicates"]))
        if row["query_id"] in result or key in result.values():
            raise ValueError("duplicate vtable query ID or semantic key")
        result[row["query_id"]] = key
    return result


def normalize(document, keys, slots=None):
    def walk(value):
        if isinstance(value, list):
            return [walk(child) for child in value]
        if not isinstance(value, dict):
            return value
        result = {}
        for key, child in value.items():
            if key == "candidate_query_ids":
                if slots is None:
                    raise ValueError("candidate exporter retained per-call candidate IDs")
                actual = slots[value["instance_id"]]
                expected = sorted(keys[index] for index in child)
                if actual != expected:
                    raise ValueError("per-call candidate meaning differs from the dense instance slot")
            elif key == "query_id":
                result[key] = keys[child]
            else:
                result[key] = walk(child)
        return result
    result = walk(document)
    result.pop("invocation", None)
    result.get("producer", {}).pop("invocation", None)
    result["compiler_vtable_queries"].sort(key=lambda row: row["query_id"])
    result["compiler_instance_abis"].sort(key=lambda row: json.dumps(row, sort_keys=True))
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("baseline", type=Path)
    parser.add_argument("candidate", type=Path)
    args = parser.parse_args()
    baseline = load_mir_document(args.baseline)
    candidate = load_mir_document(args.candidate)
    before_keys, after_keys = query_keys(baseline), query_keys(candidate)
    index = candidate.pop("compiler_virtual_candidates")
    if index["schema_version"] != 1 or len(index["by_instance"]) != len(candidate["instances"]):
        raise ValueError("invalid candidate index cardinality/schema")
    slots = []
    for slot in index["by_instance"]:
        if slot is not None and (slot != sorted(set(slot)) or any(i not in after_keys for i in slot)):
            raise ValueError("invalid candidate query ID slot")
        slots.append(None if slot is None else sorted(after_keys[index] for index in slot))
    expected = {}
    for row in candidate["compiler_runtime_queries"]["virtual"]:
        expected.setdefault(row["original_instance_id"], set()).add(row["vtable_query"]["query_id"])
    for instance_id, slot in enumerate(index["by_instance"]):
        if (slot or []) != sorted(expected.get(instance_id, set())):
            raise ValueError("candidate slot differs from exact original-instance compiler rows")
    left, right = normalize(baseline, before_keys, slots), normalize(candidate, after_keys)
    different = sorted(key for key in left.keys() | right.keys()
                       if key not in left or key not in right or left[key] != right[key])
    if different:
        raise SystemExit("semantic sections differ: " + ", ".join(different))
    print("exact semantic metadata match; virtual candidate migration checked")


if __name__ == "__main__":
    main()
