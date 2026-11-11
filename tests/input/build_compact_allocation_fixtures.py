#!/usr/bin/env python3
"""Construct decoder-only allocation identity and byte-sharing controls."""
import copy
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tools"))
from shared_json_pools import expand_document, pool_document

OUT = ROOT / "scratch/compact-allocation-inputs"


def base():
    return expand_document(json.loads((ROOT / "tests/input/fixtures/strict-unit.json").read_text()), schema_version=8)


def memory(graph, source, *, initialized=True, mutability="mutable", relocations=None):
    return {"allocation_id": graph, "source_alloc_id": source, "kind": "memory",
            "size_bytes": 8, "align_bytes": 8, "mutability": mutability,
            "byte_image_id": 0,
            "initialization_ranges": [{"state": "initialized" if initialized else "uninitialized",
                "start_bytes": 0, "end_bytes_exclusive": 8}],
            "relocations": relocations or []}


def relocation(target):
    return {"storage_offset_bytes": 0, "target": target,
            "target_offset_encoded_bytes": "00" * 8, "immutable": True, "shared_ref": True}


def world_control():
    doc = base()
    doc["byte_images"] = ["00" * 8]
    identities = [[graph, 2 * graph + 1] for graph in range(1, 33)]
    doc["allocations"] = [memory(0, 1),
        {"kind": "function", "instance_id": 0, "identities": identities}]
    raw = [{"kind": "dangling", "status": "dangling"} for _ in range(66)]
    for source in [1, *[identity[1] for identity in identities]]:
        raw[source - 1] = None
    raw[1] = {"kind": "function", "status": "opaque"}
    doc["compiler_alloc_id_world"] = {
        "schema": "rustc_alloc_id_world_v2", "profile": "prepared_post_export",
        "frontier": {"last_reserved_source_alloc_id": 66,
            "final_sentinel_source_alloc_id": 66, "next_source_alloc_id": 67},
        "global_pool_complete_through": 66, "raw_pool": raw,
        "dedup_catalog": [{"key_kind": "function", "key_allocation_id": 1,
            "salts": list(range(1, 33))}],
        "complete_key_families": ["byte_memory"],
        "non_exhaustive_key_families": ["function", "vtable", "static", "type_id",
            "memory_const_allocation"]}
    return doc


def tls_declaration(foreign, image_id=None):
    allocation = None if image_id is None else {
        "size_bytes": 0, "align_bytes": 1, "mutability": "immutable",
        "byte_image_id": image_id, "initialization_ranges": [], "relocations": []}
    return {"def_id": 0, "global_info": {"nested": False, "size_bytes": 0,
        "align_bytes": 1, "mutability": "immutable", "is_static": True,
        "is_foreign_item": foreign, "thread_local": True},
        "initializer": {"allocation": allocation}}


def body_tls(declaration):
    doc = base()
    statement = {"source_info": {"span": 0, "scope": 0}, "kind": {"variant": "Assign",
        "place": {"local": 0, "type": 0, "projection": []},
        "rvalue": {"kind": "ThreadLocalRef", **declaration}}}
    doc["bodies"][0]["basic_blocks"][0]["statements"] = [statement]
    return doc


def write(name, doc):
    if isinstance(doc, dict) and doc.get("schema") == "lean-miri-rustc-mir":
        version = doc["schema_version"]
        doc["schema_version"] = 8
        doc = pool_document(doc)
        if version != 8:
            doc["schema_version"] = version
    (OUT / f"{name}.json").write_text(json.dumps(doc, separators=(",", ":")) + "\n")


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    write("valid-foreign-tls-declaration", tls_declaration(True))
    write("foreign-tls-declaration-image", tls_declaration(True, 999))
    write("valid-body-tls-image", body_tls(tls_declaration(False, 0)))
    write("foreign-body-tls-image", body_tls(tls_declaration(True, 999)))
    write("dangling-body-tls-image", body_tls(tls_declaration(False, 999)))
    control = world_control()
    write("valid-noncontiguous-salts", control)
    for name, mutate in [
        ("unmatched-raw-null", lambda d: d["compiler_alloc_id_world"]["raw_pool"].__setitem__(3, None)),
        ("null-sentinel", lambda d: d["compiler_alloc_id_world"]["raw_pool"].__setitem__(-1, None)),
        ("node-at-opaque-source", lambda d: d["compiler_alloc_id_world"]["raw_pool"].__setitem__(0, {"kind": "function", "status": "opaque"})),
        ("duplicate-salt-result", lambda d: d["compiler_alloc_id_world"]["dedup_catalog"][0]["salts"].__setitem__(31, 1)),
        ("short-salts", lambda d: d["compiler_alloc_id_world"]["dedup_catalog"][0]["salts"].pop()),
        ("missing-function-key", lambda d: d["compiler_alloc_id_world"].__setitem__("dedup_catalog", [])),
        ("opaque-eligible-byte-image", lambda d: d["compiler_alloc_id_world"]["raw_pool"].__setitem__(1,
            {"kind": "memory", "status": "opaque", "memory_mutability": "immutable",
             "memory_align_bytes": 1, "memory_all_bytes_initialized": True,
             "memory_has_provenance": False})),
    ]:
        doc = copy.deepcopy(control)
        mutate(doc)
        write(name, doc)
    no_world = copy.deepcopy(control)
    del no_world["compiler_alloc_id_world"]
    write("valid-grouped-without-world", no_world)
    for name, mutate in [
        ("obsolete-schema", lambda d: d.__setitem__("schema_version", 6)),
        ("missing-byte-image", lambda d: d["allocations"][0].pop("byte_image_id")),
        ("zero-group-source-id", lambda d: d["allocations"][1]["identities"][0].__setitem__(1, 0)),
        ("zero-source-id", lambda d: d["allocations"][0].__setitem__("source_alloc_id", 0)),
        ("duplicate-source-id", lambda d: d["allocations"][1]["identities"][0].__setitem__(1, 1)),
        ("duplicate-graph-id", lambda d: d["allocations"][1]["identities"][0].__setitem__(0, 0)),
        ("shuffled-group-identities", lambda d: d["allocations"][1]["identities"].reverse()),
        ("empty-function-group", lambda d: d["allocations"][1].__setitem__("identities", [])),
        ("dangling-byte-image", lambda d: d["allocations"][0].__setitem__("byte_image_id", 1)),
        ("duplicate-byte-image", lambda d: d["byte_images"].append(d["byte_images"][0])),
    ]:
        doc = copy.deepcopy(no_world)
        mutate(doc)
        write(name, doc)
    shared = base()
    shared["byte_images"] = ["00" * 8]
    shared["allocations"] = [memory(0, 7, mutability="immutable", relocations=[relocation(1)]),
        memory(1, 19, initialized=False, relocations=[relocation(0)])]
    write("valid-shared-bytes-cycle", shared)


if __name__ == "__main__":
    main()
