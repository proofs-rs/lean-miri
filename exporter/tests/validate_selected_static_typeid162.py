#!/usr/bin/env python3
"""Validate genuine salt-zero static and TypeId allocator-world witnesses."""
import json
import pathlib
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[2] / "tools"))
from mir_json import load_mir_document, pool_entry


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(message)


def main(path: str) -> None:
    document = load_mir_document(path)
    world = document["compiler_alloc_id_world"]
    require(world["schema"] == "rustc_alloc_id_world_v2", "wrong allocator-world schema")
    require(world["profile"] == "prepared_post_export", "wrong allocator-world profile")
    rows = world["raw_pool"]
    frontier = world["frontier"]
    last = frontier["last_reserved_source_alloc_id"]
    require(len(rows) == last, "raw pool length differs from source frontier")
    require(frontier["final_sentinel_source_alloc_id"] == last, "wrong final source sentinel")
    require(frontier["next_source_alloc_id"] == last + 1, "wrong next source ID")
    require(rows[-1] == {"kind": "dangling", "status": "dangling"},
            "final pool row is not dangling")
    graph_count = sum(len(row["identities"]) if row["kind"] == "function" else 1
                      for row in document["allocations"])
    nodes = {graph: pool_entry(document, "allocations", graph) for graph in range(graph_count)}
    sources = set()
    for graph, node in nodes.items():
        source = node["source_alloc_id"]
        require(type(source) is int and 1 <= source <= last, "source AllocId outside raw prefix")
        require(source not in sources, "duplicate source AllocId witness")
        sources.add(source)
        require(rows[source - 1] is None, "serialized source lacks an implicit raw slot")
    require(sum(row is None for row in rows) == len(nodes), "unmatched serialized raw slot")

    selected = {"static": 0, "type_id": 0}
    identities = {"static": set(), "type_id": set()}
    for row_index, catalog in enumerate(world["dedup_catalog"]):
        kind = catalog["key_kind"]
        if kind not in selected:
            continue
        selected[kind] += 1
        require(len(catalog["salts"]) == 1, f"{kind} catalog row {row_index} must have one salt")
        result = catalog["salts"][0]
        require(type(result) is int, f"{kind} row {row_index} result is not a graph ID")
        require(result == catalog["key_allocation_id"],
                f"{kind} row {row_index} result is not its selected graph witness")
        graph_id = result
        key_node = nodes[graph_id]
        require(key_node["kind"] == kind and "status" not in key_node,
                f"{kind} key node kind/status mismatch")
        require(rows[key_node["source_alloc_id"] - 1] is None,
                f"{kind} key source ID does not join its serialized graph node")
        if kind == "static":
            global_info = key_node["global_info"]
            require("status" not in global_info and global_info["is_static"],
                    "selected static lacks supported compiler static metadata")
            require(key_node["def_path"] == "SELECTED_STATIC",
                    "selected static witness is not the fixture's exact static definition")
            identity = json.dumps(key_node["def_id"], sort_keys=True)
            identities[kind].add(identity)
        else:
            typed_key = key_node["type"]
            require(document["types"][typed_key]["display"] == "u32",
                    "selected TypeId witness is not the fixture's exact u32 type")
            identities[kind].add(typed_key)
    require(selected["static"] > 0, "no selected static key")
    require(selected["type_id"] > 0, "no selected TypeId key")
    require(world["complete_key_families"] == ["byte_memory"],
            "selected static/TypeId rows were incorrectly declared exhaustive")
    non_exhaustive = set(world["non_exhaustive_key_families"])
    require({"static", "type_id"}.issubset(non_exhaustive),
            "nonexhaustive static/TypeId families are not marked non-exhaustive")
    print("selected static/TypeId crosswalk PASS: "
          f"prefix={last}, static_keys={selected['static']}, type_id_keys={selected['type_id']}, "
          f"static_identities={len(identities['static'])}, type_id_identities={len(identities['type_id'])}, "
          f"complete={world['complete_key_families']}")


if __name__ == "__main__":
    if len(sys.argv) != 2:
        raise SystemExit("usage: validate_selected_static_typeid162.py <export.json[.gz]>")
    main(sys.argv[1])
