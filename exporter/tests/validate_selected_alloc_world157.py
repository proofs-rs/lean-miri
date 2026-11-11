#!/usr/bin/env python3
"""Check raw producer crosswalks for the selected function/vtable slice."""
import pathlib
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[2] / "tools"))
from mir_json import load_mir_inspection_document as load_mir_document, pool_entry


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(message)


def function_key(document: dict, node: dict) -> tuple:
    instance = pool_entry(document, "instances", node["instance_id"])
    return (node["instance_id"], instance["def_id"], instance["def_path"], instance["generic_args"])


def vtable_key(node: dict) -> tuple:
    return (node["type"], node["predicates"])


def main(path: str) -> None:
    document = load_mir_document(path)
    world = document["compiler_alloc_id_world"]
    require(world["schema"] == "rustc_alloc_id_world_v2", "wrong world schema")
    require(world["profile"] == "prepared_post_export", "wrong prepared profile")
    rows = world["raw_pool"]
    frontier = world["frontier"]
    through = frontier["last_reserved_source_alloc_id"]
    require(len(rows) == through, "raw pool length differs from source frontier")
    require(frontier["final_sentinel_source_alloc_id"] == through, "wrong final sentinel")
    require(frontier["next_source_alloc_id"] == through + 1, "wrong next source ID")
    require(rows[-1] == {"kind": "dangling", "status": "dangling"},
            "final pool row is not dangling")
    graph_count = sum(len(row["identities"]) if row["kind"] == "function" else 1
                      for row in document["allocations"])
    nodes = {graph: pool_entry(document, "allocations", graph) for graph in range(graph_count)}
    sources = set()
    for graph, node in nodes.items():
        source = node["source_alloc_id"]
        require(type(source) is int and 1 <= source <= through, "source AllocId outside raw prefix")
        require(source not in sources, "duplicate source AllocId witness")
        sources.add(source)
        require(rows[source - 1] is None, "serialized source lacks an implicit raw slot")
    require(sum(row is None for row in rows) == len(nodes), "unmatched serialized raw slot")

    selected_counts = {"function": 0, "vtable": 0}
    for row_index, catalog in enumerate(world["dedup_catalog"]):
        kind = catalog["key_kind"]
        if kind not in selected_counts:
            continue
        selected_counts[kind] += 1
        salts = catalog["salts"]
        require(len(salts) == 32, f"catalog row {row_index} does not have 32 salts")
        key_node = nodes[catalog["key_allocation_id"]]
        require(key_node["kind"] == kind and "status" not in key_node,
                f"catalog row {row_index} key node has wrong kind/status")
        typed_key = function_key(document, key_node) if kind == "function" else vtable_key(key_node)
        require(salts[0] == catalog["key_allocation_id"],
                f"catalog row {row_index} salt zero is not the selected key node")
        for salt, result in enumerate(salts):
            require(type(result) is int, f"catalog row {row_index} salt {salt} is not a graph ID")
            result_node = nodes[result]
            require(rows[result_node["source_alloc_id"] - 1] is None,
                    f"catalog row {row_index} salt {salt} source/graph crosswalk differs")
            require(result_node["kind"] == kind and "status" not in result_node,
                    f"catalog row {row_index} salt {salt} node kind/status differs")
            result_key = function_key(document, result_node) if kind == "function" else vtable_key(result_node)
            require(result_key == typed_key,
                    f"catalog row {row_index} salt {salt} changes its exact typed key")

    require(selected_counts == {"function": 1, "vtable": 1}, "fixture must select exactly one function and one vtable key")
    require(world["complete_key_families"] == ["byte_memory"],
            "selected functions/vtables were incorrectly marked exhaustive")
    require({"function", "vtable"}.issubset(set(world["non_exhaustive_key_families"])),
            "nonexhaustive function/vtable families are not marked non-exhaustive")
    print(
        "producer crosswalk PASS: "
        f"prefix={through}, function_keys={selected_counts['function']}, "
        f"vtable_keys={selected_counts['vtable']}, "
        f"selected_salts={sum(selected_counts.values()) * 32}, "
        f"complete={world['complete_key_families']}"
    )


if __name__ == "__main__":
    if len(sys.argv) != 2:
        raise SystemExit("usage: validate_selected_alloc_world157.py <export.json.gz>")
    main(sys.argv[1])
