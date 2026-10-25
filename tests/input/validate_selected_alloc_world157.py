#!/usr/bin/env python3
"""Check raw producer crosswalks for the selected function/vtable slice."""
import pathlib
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[2] / "tools"))
from mir_json import load_mir_document


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(message)


def function_key(node: dict) -> tuple:
    return (
        node["instance_id"],
        node["instance_def_id"],
        node["instance_def_path"],
        node["generic_args"],
    )


def vtable_key(node: dict) -> tuple:
    return (node["type"], node["predicates"])


def main(path: str) -> None:
    document = load_mir_document(path)
    world = document["compiler_alloc_id_world"]
    require(world["schema"] == "rustc_alloc_id_world_v1", "wrong world schema")
    require(world["profile"] == "prepared_post_export", "wrong prepared profile")
    rows = world["raw_pool"]
    frontier = world["frontier"]
    through = frontier["last_reserved_source_alloc_id"]
    require(len(rows) == through, "raw pool length differs from source frontier")
    require(frontier["final_sentinel_source_alloc_id"] == through, "wrong final sentinel")
    require(frontier["next_source_alloc_id"] == through + 1, "wrong next source ID")
    by_source = {}
    for index, row in enumerate(rows, 1):
        require(row["source_alloc_id"] == index, f"noncontiguous source ID at row {index}")
        by_source[index] = row
    sentinel = rows[-1]
    require((sentinel["kind"], sentinel["status"], sentinel["allocation_id"]) ==
            ("dangling", "dangling", None), "final pool row is not dangling")

    nodes = {node["allocation_id"]: node for node in document["allocations"]}
    selected_counts = {"function": 0, "vtable": 0}
    probe_counts = {"preexisting_hit": 0, "miss_reserved_by_probe": 0}
    for row_index, catalog in enumerate(world["dedup_catalog"]):
        kind = catalog["key_kind"]
        if kind not in selected_counts:
            continue
        selected_counts[kind] += 1
        salts = catalog["salts"]
        require(len(salts) == 32, f"catalog row {row_index} does not have 32 salts")
        key_node = nodes[catalog["key_allocation_id"]]
        require(key_node["kind"] == kind and key_node["status"] == "supported",
                f"catalog row {row_index} key node has wrong kind/status")
        typed_key = function_key(key_node) if kind == "function" else vtable_key(key_node)
        require(salts[0]["allocation_id"] == catalog["key_allocation_id"],
                f"catalog row {row_index} salt zero is not the selected key node")
        for salt, result in enumerate(salts):
            require(result["salt"] == salt, f"catalog row {row_index} salt ordering differs")
            outcome = result["probe_result"]
            require(outcome in probe_counts, f"unknown probe outcome {outcome}")
            probe_counts[outcome] += 1
            pool_row = by_source[result["source_alloc_id"]]
            require(pool_row["status"] == "serialized" and
                    pool_row["allocation_id"] == result["allocation_id"],
                    f"catalog row {row_index} salt {salt} source/graph crosswalk differs")
            result_node = nodes[result["allocation_id"]]
            require(result_node["source_alloc_id"] == result["source_alloc_id"],
                    f"catalog row {row_index} salt {salt} node/source witness differs")
            require(result_node["kind"] == kind and result_node["status"] == "supported",
                    f"catalog row {row_index} salt {salt} node kind/status differs")
            result_key = function_key(result_node) if kind == "function" else vtable_key(result_node)
            require(result_key == typed_key,
                    f"catalog row {row_index} salt {salt} changes its exact typed key")

    require(selected_counts == {"function": 1, "vtable": 1}, "fixture must select exactly one function and one vtable key")
    require(probe_counts == {"preexisting_hit": 0, "miss_reserved_by_probe": 64}, "selected salt probes differ from the captured fixture expectations")
    require(world["complete_key_families"] == ["byte_memory"],
            "selected functions/vtables were incorrectly marked exhaustive")
    require({"function", "vtable"}.issubset(set(world["unsupported_key_families"])),
            "nonexhaustive function/vtable families are not marked unsupported")
    print(
        "producer crosswalk PASS: "
        f"prefix={through}, function_keys={selected_counts['function']}, "
        f"vtable_keys={selected_counts['vtable']}, "
        f"selected_salts={sum(selected_counts.values()) * 32}, "
        f"probe_outcomes={probe_counts}, complete={world['complete_key_families']}"
    )


if __name__ == "__main__":
    if len(sys.argv) != 2:
        raise SystemExit("usage: validate_selected_alloc_world157.py <export.json.gz>")
    main(sys.argv[1])
