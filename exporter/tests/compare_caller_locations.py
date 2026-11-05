#!/usr/bin/env python3
"""Check recipes against actual span_as_caller_location compiler images.

The comparison adapter repeats only the two u32 writes from the pinned provider;
all other bytes, init ranges, relocation flags and referenced filename images
must agree. It deliberately ignores only compilation-local graph/source IDs.
"""
import json
import pathlib
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[2] / "tools"))
from mir_json import load_mir_document


def projection(doc, row, recipe):
    nodes = {n["allocation_id"]: n for n in doc["allocations"]}
    value = row["template_value" if recipe else "value"]
    if row["status"] != "supported" or value["kind"] != "pointer_scalar" or value["offset_bytes"] != 0:
        raise ValueError("fixture lacks a supported root pointer")
    image = dict(nodes[value["allocation"]["allocation_id"]])
    data = bytearray.fromhex(image["bytes_hex"])
    if recipe:
        if row["recipe_schema"] != "caller_location_template_v1":
            raise ValueError("unexpected recipe schema")
        ptr_ty = doc["types"][row["result_type"]["type_id"]]
        loc_ty = doc["types"][ptr_ty["shape"]["pointee"]["type_id"]]
        offsets = loc_ty["layout"]["fields"]["offsets_bytes"]
        endian = doc["runtime_target_data_layout"]["endian"]
        for index, number in [(1, row["line_u32"]), (2, row["column_u32"])]:
            offset = offsets[index]
            if not 0 <= number < 2**32 or not 0 <= offset <= len(data) - 4:
                raise ValueError("invalid coordinate/field range")
            data[offset:offset+4] = number.to_bytes(4, endian)
    image["bytes_hex"] = data.hex()
    image.pop("allocation_id")
    image.pop("source_alloc_id")
    relocations = []
    for relocation in image["relocations"]:
        relocation = dict(relocation)
        filename = dict(nodes[relocation["target"]["allocation_id"]])
        filename.pop("allocation_id")
        filename.pop("source_alloc_id")
        if filename["relocations"]:
            raise ValueError("caller filename unexpectedly has provenance")
        relocation["target"] = filename
        relocations.append(relocation)
    image["relocations"] = relocations
    pointer = {k: v for k, v in value.items() if k not in ("allocation", "type")}
    result_type = doc["types"][row["result_type"]["type_id"]]["display"]
    return image, pointer, result_type


def main(reference, normalized):
    old, new = load_mir_document(reference), load_mir_document(normalized)
    def rows(doc):
        result = {}
        for row in doc["compiler_caller_location_constants"]:
            key = json.dumps(row["span"], sort_keys=True)
            if key in result and result[key] != row:
                raise ValueError("conflicting duplicate source span")
            result[key] = row
        return result
    old_rows, new_rows = rows(old), rows(new)
    if old_rows.keys() != new_rows.keys() or not old_rows:
        raise SystemExit("source span coverage changed or is empty")
    for key, row in old_rows.items():
        if projection(old, row, False) != projection(new, new_rows[key], True):
            raise SystemExit("recipe differs from actual compiler image at " + key)
    print(f"caller locations: {len(old_rows)} exact compiler images/flags/filenames match recipes")


if __name__ == "__main__":
    if len(sys.argv) != 3:
        raise SystemExit("usage: compare_caller_locations.py REFERENCE.json RECIPES.json")
    main(*sys.argv[1:])
