#!/usr/bin/env python3
"""Check that variadic FnPtr ABI metadata is exported without querying an
unrelated nonvariadic function-pointer candidate with variadic extras.
"""
import json
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "tools"))
from mir_json import load_mir_inspection_document as load_mir_document, pool_entry


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
    if row.get("extra_argument_types") == [i32_id]
]
require(extra_rows, "variadic FnPtr has no ABI query row with one i32 extra")
require(
    any(
        pool_entry(document, "fn_abis", row["abi_query"]).get("c_variadic") is not None
        and pool_entry(document, "fn_abis", row["abi_query"]).get("c_variadic") is True
        for row in extra_rows
    ),
    "variadic extra-i32 ABI query is not supported/c_variadic",
)

nonvariadic_rows = [row for row in pointer_abis if row.get("type_id") == nonvariadic_id]
require(not nonvariadic_rows, "covered nonvariadic Rust FnPtr retained an eager ABI query")
raw = nonvariadic[0]["shape"]
require(raw["signature_bound_variables"] == [], "nonvariadic source signature acquired a binder")
require(raw["signature"] == {
    "inputs": [i32_id], "output": i32_id, "safety": {"kind": "safe"},
    "abi": {"kind": "rust", "unwind": None}, "c_variadic": False, "splatted": None,
}, "nonvariadic source signature differs from the exact fixture constructor")
require(document["producer"]["abi_session"] == {
    "panic": "abort", "panic_in_drop": "unwind", "optimization": "no",
    "llvm_writable": False, "box_noalias": True,
    "incremental_enabled": False, "sanitizers": [],
}, "source ABI canonical session differs from the pinned fixture configuration")
trace = Path(sys.argv[2]).read_text().splitlines()
key = "signature=Binder { value: fn(i32) -> i32, bound_vars: [] } extra=[]"
rows = [line for line in trace if line.startswith("lean_miri_fn_pointer_abi_call ") and line.endswith(key)]
require(any("route=catalog-source queried=false " in line for line in rows),
        "nonvariadic candidate did not reach source ABI admission")
require(not any("queried=true " in line for line in rows),
        "unrelated nonvariadic candidate caused an explicit physical ABI query")
print("validated exact variadic extra-i32 ABI residual; exact nonvariadic raw signature/session and zero explicit ABI calls")
