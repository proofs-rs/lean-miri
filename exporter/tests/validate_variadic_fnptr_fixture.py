#!/usr/bin/env python3
"""Check that variadic FnPtr ABI metadata is exported without querying an
unrelated nonvariadic function-pointer candidate with variadic extras.
"""
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "tools"))
from mir_json import load_mir_document


def require(condition, message):
    if not condition:
        raise SystemExit(message)


document = load_mir_document(sys.argv[1])
types = {item["type_id"]: item for item in document["types"]}
function_facts = document["compiler_function_facts"]
pointer_abis = function_facts["pointer_abis"]

nonvariadic = [
    item for item in types.values()
    if item.get("display") == "fn(i32) -> i32"
    and item.get("shape", {}).get("kind") == "function_pointer"
]
variadic = [
    item for item in types.values()
    if item.get("display") == 'unsafe extern "C" fn(i32, ...) -> i32'
    and item.get("shape", {}).get("kind") == "function_pointer"
]
i32_types = [
    item for item in types.values()
    if item.get("display") == "i32" and item.get("shape", {}).get("kind") == "int"
]
require(nonvariadic, "nonvariadic fn(i32) -> i32 candidate type is absent")
require(variadic, "variadic unsafe extern C FnPtr type is absent")
require(i32_types, "i32 extra operand type is absent")

nonvariadic_id = nonvariadic[0]["type_id"]
variadic_id = variadic[0]["type_id"]
i32_id = i32_types[0]["type_id"]

variadic_rows = [row for row in pointer_abis if row.get("type_id") == variadic_id]
extra_rows = [
    row for row in variadic_rows
    if row.get("extra_argument_types") == [{"type_id": i32_id}]
]
require(extra_rows, "variadic FnPtr has no ABI query row with one i32 extra")
require(
    any(
        row.get("abi_query", {}).get("status") == "supported"
        and row["abi_query"].get("value", {}).get("c_variadic") is True
        for row in extra_rows
    ),
    "variadic extra-i32 ABI query is not supported/c_variadic",
)

nonvariadic_rows = [row for row in pointer_abis if row.get("type_id") == nonvariadic_id]
require(nonvariadic_rows, "nonvariadic function-pointer ABI row is absent")
require(
    all(not row.get("extra_argument_types") for row in nonvariadic_rows),
    "nonvariadic candidate unexpectedly has an extra-bearing ABI query",
)
require(
    any(
        row.get("abi_query", {}).get("status") == "supported"
        and row["abi_query"].get("value", {}).get("c_variadic") is False
        for row in nonvariadic_rows
    ),
    "nonvariadic candidate has no supported empty-extra nonvariadic ABI row",
)
print(
    "validated variadic FnPtr ABI with one i32 extra; nonvariadic function-pointer "
    "candidate has only empty-extra ABI rows"
)
