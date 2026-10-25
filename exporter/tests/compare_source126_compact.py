#!/usr/bin/env python3
"""Compare source125/126 exports, resolving only source126's compact body refs."""

import json
import sys
from copy import deepcopy
from collections import Counter
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "tools"))
from mir_json import load_mir_document

MIR_BODY_WRAPPER_FIELDS = {
    # export_body adds these after mir_body_with_constant_queries_json has
    # compared/serialized mir_body_json; they are not part of the referenced MIR.
    "constant_query_context",
    "entry_instance",
    "def_path",
    "def_id",
    "is_static",
    "thread_local_static",
    "promoted_bodies",
}


def load(path):
    return json.loads(Path(path).read_text(encoding="utf-8"))


def canonical(value):
    """Restore legacy embedded normalized bodies and drop debug-only templates."""
    refs = 0

    def visit(node):
        nonlocal refs
        if isinstance(node, list):
            return [visit(item) for item in node]
        if not isinstance(node, dict):
            return node

        result = {}
        for key, child in node.items():
            if key == "normalization_template":
                continue
            if key == "constant_query_context" and isinstance(child, dict):
                context = dict(child)
                normalization = context.get("normalization")
                if isinstance(normalization, dict) and "body_ref" in normalization:
                    assert normalization.get("status") == "supported"
                    assert normalization["body_ref"] == "source_body", normalization
                    source_body = {
                        source_key: source_value
                        for source_key, source_value in node.items()
                        if source_key not in MIR_BODY_WRAPPER_FIELDS | {"normalization_template"}
                    }
                    context["normalization"] = {
                        "status": "supported",
                        "body": visit(source_body),
                    }
                    refs += 1
                result[key] = visit(context)
            else:
                result[key] = visit(child)
        return result

    result = visit(value)
    return result, refs


def count_coverage_and_unsupported(document):
    coverage = 0
    unsupported = Counter()

    def visit(node, path="$", in_debug=False):
        nonlocal coverage
        if isinstance(node, list):
            for index, child in enumerate(node):
                visit(child, f"{path}[{index}]", in_debug)
        elif isinstance(node, dict):
            if node.get("status") == "debug_payload":
                return
            if node.get("variant") == "Coverage":
                coverage += 1
            status = node.get("status")
            if status in ("unsupported", "incomplete", "unknown"):
                reason = json.dumps(node.get("reason", node.get("error")), sort_keys=True)
                unsupported[(path, status, node.get("kind"), reason)] += 1
            for key, child in node.items():
                if key != "normalization_template":
                    visit(child, f"{path}.{key}", in_debug)

    visit(document)
    return coverage, unsupported


def first_difference(left, right, path="$", limit=300):
    if type(left) is not type(right):
        return path, repr(left)[:limit], repr(right)[:limit]
    if isinstance(left, dict):
        for key in sorted(left.keys() | right.keys()):
            child_path = f"{path}.{key}"
            if key not in left:
                return child_path, "<missing>", repr(right[key])[:limit]
            if key not in right:
                return child_path, repr(left[key])[:limit], "<missing>"
            difference = first_difference(left[key], right[key], child_path, limit)
            if difference is not None:
                return difference
        return None
    if isinstance(left, list):
        if len(left) != len(right):
            return f"{path}.length", str(len(left)), str(len(right))
        for index, (left_item, right_item) in enumerate(zip(left, right)):
            difference = first_difference(left_item, right_item, f"{path}[{index}]", limit)
            if difference is not None:
                return difference
        return None
    if left != right:
        return path, repr(left)[:limit], repr(right)[:limit]
    return None


def main(old_path, new_path):
    # The legacy checkpoint is historical evidence and intentionally remains
    # readable as its original JSON. The newly generated active export uses
    # the shared-payload graph wire format.
    old = load(old_path)
    new = deepcopy(load_mir_document(new_path))
    # The wire schema version changed when the shared-payload graph was added;
    # compare semantic payloads rather than this transport metadata.
    old.pop("schema_version", None)
    new.pop("schema_version", None)
    old_canonical, old_refs = canonical(old)
    new_canonical, new_refs = canonical(new)
    assert old_refs == 0, f"legacy export unexpectedly contains compact refs: {old_refs}"
    assert new_refs > 0, "source126 export emitted no genuine source_body references"
    difference = first_difference(old_canonical, new_canonical)
    assert difference is None, f"legacy and compact exports differ at {difference}"

    for name, document in (("legacy", old), ("compact", new)):
        caller_rows = document.get("compiler_caller_location_constants")
        assert isinstance(caller_rows, list) and caller_rows, f"{name} export has no caller-location rows"
    assert old.get("compiler_caller_location_constants") == new.get("compiler_caller_location_constants"), \
        "caller-location compiler rows changed"

    old_coverage, old_unsupported = count_coverage_and_unsupported(old_canonical)
    new_coverage, new_unsupported = count_coverage_and_unsupported(new_canonical)
    assert old_coverage > 0 and new_coverage == old_coverage, \
        f"coverage statement inventory changed: legacy={old_coverage}, compact={new_coverage}"
    assert old_unsupported, "fixture exports no unsupported/incomplete diagnostics to compare"
    assert old_unsupported == new_unsupported, "unsupported/incomplete diagnostic inventory changed"
    print(
        "source126 canonical export match: "
        f"body_refs={new_refs}, caller_location_rows={len(new['compiler_caller_location_constants'])}, "
        f"coverage_statements={new_coverage}, diagnostic_statuses={sum(old_unsupported.values())}"
    )


if __name__ == "__main__":
    if len(sys.argv) != 3:
        raise SystemExit("usage: compare_source126_compact.py LEGACY.json COMPACT.json")
    main(sys.argv[1], sys.argv[2])
