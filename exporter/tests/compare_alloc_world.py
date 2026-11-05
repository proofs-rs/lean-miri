#!/usr/bin/env python3
"""Compare separate genuine exports with the reference and normalized worlds."""
import pathlib
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[2] / "tools"))
from mir_json import load_mir_document
from alloc_world_rows import allocation_world_rows


def main(reference, normalized):
    old, new = load_mir_document(reference), load_mir_document(normalized)
    worlds = [doc["compiler_alloc_id_world"] for doc in (old, new)]
    if [w["schema"] for w in worlds] != ["rustc_alloc_id_world_v1", "rustc_alloc_id_world_v2"]:
        raise SystemExit("comparison requires legacy then compact world")
    if allocation_world_rows(old) != allocation_world_rows(new):
        raise SystemExit("complete source AllocId pool facts differ")
    omitted = {"schema", "raw_pool", "raw_kinds", "opaque_memory"}
    if {k: v for k, v in worlds[0].items() if k not in omitted} != {
            k: v for k, v in worlds[1].items() if k not in omitted}:
        raise SystemExit("world frontier/catalog/completeness facts differ")
    if {k: v for k, v in old.items() if k != "compiler_alloc_id_world"} != {
            k: v for k, v in new.items() if k != "compiler_alloc_id_world"}:
        raise SystemExit("normalizing the world changed other compiler evidence")
    print("complete source pool/catalog/frontier and all other document fields: identical")


if __name__ == "__main__":
    if len(sys.argv) != 3:
        raise SystemExit("usage: compare_alloc_world.py REFERENCE.json NORMALIZED.json")
    main(*sys.argv[1:])
