#!/usr/bin/env python3
"""Validate genuine salt-zero static and TypeId allocator-world witnesses."""
import json
import pathlib
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[2] / "tools"))
from mir_json import load_mir_document


def require(condition: bool, message: str) -> None:
    if not condition:
        raise SystemExit(message)


def main(path: str) -> None:
    document = load_mir_document(path)
    world = document["compiler_alloc_id_world"]
    require(world["schema"] == "rustc_alloc_id_world_v1", "wrong allocator-world schema")
    require(world["profile"] == "prepared_post_export", "wrong allocator-world profile")
    rows = world["raw_pool"]
    frontier = world["frontier"]
    last = frontier["last_reserved_source_alloc_id"]
    require(len(rows) == last, "raw pool length differs from source frontier")
    require(frontier["final_sentinel_source_alloc_id"] == last, "wrong final source sentinel")
    require(frontier["next_source_alloc_id"] == last + 1, "wrong next source ID")
    source_rows = {}
    for source_id, row in enumerate(rows, 1):
        require(row["source_alloc_id"] == source_id, f"source AllocId gap at {source_id}")
        source_rows[source_id] = row
    require((rows[-1]["kind"], rows[-1]["status"], rows[-1]["allocation_id"]) ==
            ("dangling", "dangling", None), "last pool row is not the dangling sentinel")

    nodes = {node["allocation_id"]: node for node in document["allocations"]}
    selected = {"static": 0, "type_id": 0}
    outcomes = {"preexisting_hit": 0, "miss_reserved_by_probe": 0}
    identities = {"static": set(), "type_id": set()}
    for row_index, catalog in enumerate(world["dedup_catalog"]):
        kind = catalog["key_kind"]
        if kind not in selected:
            continue
        selected[kind] += 1
        require(len(catalog["salts"]) == 1, f"{kind} catalog row {row_index} must have one salt")
        result = catalog["salts"][0]
        require(result["salt"] == 0, f"{kind} row {row_index} is not salt zero")
        require(result["allocation_id"] == catalog["key_allocation_id"],
                f"{kind} row {row_index} result is not its selected graph witness")
        require(result["probe_result"] in outcomes, f"unknown {kind} probe result")
        outcomes[result["probe_result"]] += 1
        graph_id = result["allocation_id"]
        key_node = nodes[graph_id]
        require(key_node["kind"] == kind and key_node["status"] == "supported",
                f"{kind} key node kind/status mismatch")
        require(key_node["source_alloc_id"] == result["source_alloc_id"],
                f"{kind} key node source witness mismatch")
        pool_row = source_rows[result["source_alloc_id"]]
        require((pool_row["status"], pool_row["allocation_id"]) == ("serialized", graph_id),
                f"{kind} key source ID does not join its serialized graph node")
        if kind == "static":
            global_info = key_node["global_info"]
            require(global_info["status"] == "supported" and global_info["is_static"],
                    "selected static lacks supported compiler static metadata")
            require(key_node["def_path"] == "SELECTED_STATIC",
                    "selected static witness is not the fixture's exact static definition")
            identity = json.dumps(key_node["def_id"], sort_keys=True)
            identities[kind].add(identity)
        else:
            typed_key = key_node["type"]["type_id"]
            require(document["types"][typed_key]["display"] == "u32",
                    "selected TypeId witness is not the fixture's exact u32 type")
            identities[kind].add(typed_key)
    require(selected["static"] > 0, "no selected static key")
    require(selected["type_id"] > 0, "no selected TypeId key")
    require(world["complete_key_families"] == ["byte_memory"],
            "selected static/TypeId rows were incorrectly declared exhaustive")
    unsupported = set(world["unsupported_key_families"])
    require({"static", "type_id"}.issubset(unsupported),
            "nonexhaustive static/TypeId families are not marked unsupported")
    print("selected static/TypeId crosswalk PASS: "
          f"prefix={last}, static_keys={selected['static']}, type_id_keys={selected['type_id']}, "
          f"static_identities={len(identities['static'])}, type_id_identities={len(identities['type_id'])}, "
          f"probe_outcomes={outcomes}, complete={world['complete_key_families']}")


if __name__ == "__main__":
    if len(sys.argv) != 2:
        raise SystemExit("usage: validate_selected_static_typeid162.py <export.json[.gz]>")
    main(sys.argv[1])
