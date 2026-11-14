#!/usr/bin/env python3
"""Check transitive type dependencies of the ABI rows actually compared.

Unrelated source-catalogue types are counted separately. Nominal field types,
generic type arguments, signatures and array-constant types are traversed; an
unknown shape is an error rather than evidence of Dynamic absence.
"""
import argparse
import hashlib
import json
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument("document", type=Path)
parser.add_argument("--name", action="append", default=[])
parser.add_argument("--expected-instance-keys", type=int, default=0)
parser.add_argument("--all-functions", action="store_true")
args = parser.parse_args()
doc = json.loads(args.document.read_text())
roots, abi_ids = set(), set()
instances = 0
for row in doc["compiler_instance_abis"]:
    node = doc["instances"][row["instance_id"]]
    if node["def_path"].split("::")[-1] in args.name:
        instances += 1
        abi_ids.add(row["abi_query"])
        roots.update(row["extra_argument_types"])
assert instances == args.expected_instance_keys, (instances, args.expected_instance_keys)
if args.all_functions:
    for row in doc["compiler_function_facts"]["pointer_abis"]:
        abi_ids.add(row["abi_query"])
        roots.add(row["type_id"])
        roots.update(row["extra_argument_types"])
    for row in doc["compiler_function_facts"]["helper_signatures"]:
        abi_ids.add(row["abi_query"])
        roots.update(row["signature"]["inputs"])
        roots.add(row["signature"]["output"])
assert abi_ids, "no selected ABI roots"
for index in abi_ids:
    abi = doc["fn_abis"][index]
    roots.update(doc["abi_arguments"][arg]["type"] for arg in abi["arguments"] + [abi["return"]])

pending, visited = list(roots), set()


def generic_arguments(values):
    for value in values:
        if value["kind"] == "type":
            pending.append(value["value"])
        elif value["kind"] == "const":
            constant(value["value"])
        else:
            assert value["kind"] == "lifetime", value


def constant(index):
    value = doc["type_constants"][index]
    assert "type" in value, ("unsupported constant dependency", value)
    pending.append(value["type"])


while pending:
    index = pending.pop()
    if index in visited:
        continue
    assert type(index) is int and 0 <= index < len(doc["types"]), ("missing type", index)
    visited.add(index)
    shape = doc["types"][index]["shape"]
    kind = shape["kind"]
    assert not kind.startswith("dynamic"), ("Dynamic in compared ABI dependency closure", index)
    if kind in {"bool", "char", "str", "never", "int", "uint", "float", "foreign"}:
        pass
    elif kind == "tuple":
        pending.extend(shape["elements"])
    elif kind == "array":
        pending.append(shape["element"])
        constant(shape["length"])
    elif kind == "slice":
        pending.append(shape["element"])
    elif kind in {"raw_pointer", "reference"}:
        pending.append(shape["pointee"])
    elif kind == "pattern_type":
        pending.append(shape["base"])
    elif kind in {"function_pointer", "function_definition"}:
        generic_arguments(shape.get("generic_args", []))
        signature = shape["signature"]
        pending.extend(signature["inputs"])
        pending.append(signature["output"])
    elif kind == "adt":
        generic_arguments(shape["generic_args"])
        for variant in shape["variants"]:
            pending.extend(field["type"] for field in variant["fields"])
    else:
        raise AssertionError(("unsupported type dependency shape", index, kind))

global_dynamic = sum(node["shape"]["kind"].startswith("dynamic") for node in doc["types"])
print(json.dumps({"document": str(args.document),
    "sha256": hashlib.sha256(args.document.read_bytes()).hexdigest(),
    "selected_instance_keys": instances, "selected_abi_records": len(abi_ids),
    "transitive_type_count": len(visited), "dynamic_in_selected_dependencies": 0,
    "unrelated_dynamic_catalogue_types": global_dynamic}, sort_keys=True))
