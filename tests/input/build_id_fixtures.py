#!/usr/bin/env python3
"""Build strict decoder ID cases from a synthetic successful-schema input.

The synthetic unit fixture is a decoder-only input, not a Rust/Miri execution.
"""
import json
import sys
import pathlib

ROOT = pathlib.Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tools"))
from shared_json_pools import expand_document, pool_document

OUT = ROOT / "scratch/decoder-id-inputs"
EXPORTS = ROOT / "tests/input/fixtures"


def write(name, value):
    if isinstance(value, dict) and value.get("schema") == "lean-miri-rustc-mir":
        version = value["schema_version"]
        value["schema_version"] = 8
        value = pool_document(value)
        if version != 8:
            value["schema_version"] = version
    (OUT / f"{name}.json").write_text(json.dumps(value, separators=(",", ":")) + "\n")


def pool(doc, name):
    return doc[name]


def alter_type_ids(doc, edits):
    """Mutate declared identities to test dense table validation."""
    table = pool(doc, "types")
    for index, new_id in edits.items():
        table[index]["type_id"] = new_id


def alter_last_type_id(doc, new_id):
    alter_type_ids(doc, {len(pool(doc, "types")) - 1: new_id})


def permute_type_rows(doc):
    table = pool(doc, "types")
    assert len(table) >= 2
    doc["types"] = [table[-1], *table[1:-1], table[0]]


def set_table_empty(doc, key):
    doc[key] = []


def base():
    return expand_document(json.loads((EXPORTS / "strict-unit.json").read_text()), schema_version=8)


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    doc = base()
    del doc["types"][0]["shape"]["kind"]
    write("missing-type-shape-kind", doc)
    doc = base()
    del doc["layouts"][doc["types"][0]["layout"]]["size_bytes"]
    write("missing-type-layout-size", doc)

    write("valid-dense", base())
    doc = base()
    permute_type_rows(doc)
    write("permuted-type-rows", doc)

    doc = base()
    table = pool(doc, "types")
    first_id = table[0]["type_id"]
    alter_type_ids(doc, {1: len(table) + 100, len(table) - 1: first_id})
    # Both defects are present; the first noncanonical table position must fail.
    write("duplicate-and-range-first", doc)

    for name, value in [
        ("out-of-range-type-id", len(pool(base(), "types")) + 100),
        ("negative-type-id", -1),
        ("malformed-table-type-id", "bad"),
    ]:
        doc = base()
        alter_last_type_id(doc, value)
        write(name, doc)

    for name, value in [
        ("dangling-type", 10**30), ("malformed-type-reference", "bad"),
    ]:
        doc = base()
        doc["bodies"][0]["locals"][0]["type"] = value
        write(name, doc)

    for name, value in [
        ("dangling-allocation", 99999), ("malformed-allocation-reference", "bad"),
    ]:
        doc = base()
        memory = doc["allocations"][0]
        memory["size_bytes"] = 8
        doc["byte_images"].append("00" * 8)
        memory["byte_image_id"] = len(doc["byte_images"]) - 1
        memory["initialization_ranges"] = [
            {"state": "initialized", "start_bytes": 0, "end_bytes_exclusive": 8}
        ]
        memory["relocations"] = [{"storage_offset_bytes": 0, "target": value,
            "target_offset_encoded_bytes": "00" * 8, "immutable": True, "shared_ref": False}]
        write(name, doc)

    for name, value in [
        ("dangling-instance", 10**30), ("malformed-instance-reference", "bad"),
    ]:
        doc = base()
        doc["body_roots"][0]["entry_instance"] = value
        write(name, doc)

    for name, value in [("dangling-body-instance", 10**30),
                        ("malformed-body-instance", "bad"),
                        ("negative-body-instance", -1)]:
        doc = base()
        doc["bodies"][0]["instance_id"] = value
        write(name, doc)

    doc = base()
    doc["synthetic_debug_payload"] = {
        "status": "debug_payload", "type_id": 10**30,
        "allocation_id": 10**30, "instance_id": 10**30,
    }
    write("nested-debug-payload-skips-references", doc)

    doc = base()
    # Removing an unreferenced pool is valid; retain a real catalog edge.
    doc["compiler_global_byte_queries"]["covered_allocation_ids"] = [0]
    write("valid-allocation-reference", doc)
    set_table_empty(doc, "allocations")
    write("empty-allocations", doc)
    doc = base()
    set_table_empty(doc, "instances")
    write("empty-instances", doc)


if __name__ == "__main__":
    main()
