#!/usr/bin/env python3
"""Build strict decoder ID cases from a synthetic successful-schema input.

The synthetic unit fixture is a decoder-only input, not a Rust/Miri execution.
"""
import json
import pathlib

ROOT = pathlib.Path(__file__).resolve().parents[2]
OUT = ROOT / "scratch/decoder-id-inputs"
EXPORTS = ROOT / "tests/input/fixtures"


def write(name, value):
    (OUT / f"{name}.json").write_text(json.dumps(value, separators=(",", ":")) + "\n")


def resolved_table(doc, name):
    return doc[name]


def alter_type_ids(doc, edits):
    """Mutate rows in the inlined schema-3 table."""
    table = resolved_table(doc, "types")
    for index, new_id in edits.items():
        table[index]["type_id"] = new_id


def alter_last_type_id(doc, new_id):
    alter_type_ids(doc, {len(resolved_table(doc, "types")) - 1: new_id})


def permute_type_rows(doc):
    table = resolved_table(doc, "types")
    assert len(table) >= 2
    doc["types"] = [table[-1], *table[1:-1], table[0]]


def set_table_empty(doc, key):
    doc[key] = []


def base():
    return json.loads((EXPORTS / "strict-unit.json").read_text())


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    doc = base()
    del doc["types"][0]["shape"]["kind"]
    write("missing-type-shape-kind", doc)
    doc = base()
    del doc["types"][0]["layout"]["size_bytes"]
    write("missing-type-layout-size", doc)

    doc = base()
    permute_type_rows(doc)
    write("valid-permuted-dense", doc)

    doc = base()
    table = resolved_table(doc, "types")
    first_id = table[0]["type_id"]
    alter_type_ids(doc, {1: len(table) + 100, len(table) - 1: first_id})
    # Both defects are present; the full duplicate scan wins over range checks.
    write("duplicate-and-range-first", doc)

    for name, value in [
        ("out-of-range-type-id", len(resolved_table(base(), "types")) + 100),
        ("negative-type-id", -1),
        ("malformed-table-type-id", "bad"),
    ]:
        doc = base()
        alter_last_type_id(doc, value)
        write(name, doc)

    for name, marker, value in [
        ("dangling-type", "type_id", 10**30),
        ("dangling-allocation", "allocation_id", 10**30),
        ("malformed-type-reference", "type_id", "bad"),
        ("malformed-allocation-reference", "allocation_id", "bad"),
    ]:
        doc = base()
        doc["synthetic_decoder_probe"] = {marker: value}
        write(name, doc)

    for name, value in [
        ("dangling-instance", 10**30),
        ("malformed-instance-reference", "bad"),
    ]:
        doc = base()
        doc["synthetic_decoder_probe"] = {"instance_id": value}
        write(name, doc)

    doc = base()
    doc["synthetic_debug_payload"] = {
        "status": "debug_payload", "type_id": 10**30,
        "allocation_id": 10**30, "instance_id": 10**30,
    }
    write("nested-debug-payload-skips-references", doc)

    doc = base()
    set_table_empty(doc, "allocations")
    write("empty-allocations", doc)
    doc = base()
    set_table_empty(doc, "instances")
    write("empty-instances", doc)


if __name__ == "__main__":
    main()
