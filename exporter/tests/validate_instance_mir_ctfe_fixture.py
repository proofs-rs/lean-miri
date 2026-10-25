#!/usr/bin/env python3
"""Validate source116 external Ctor and #[rustc_comptime] instance MIR rows."""
import json
import pathlib
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[2] / "tools"))
from mir_json import load_mir_document


def require(condition, message):
    if not condition:
        raise SystemExit(f"CTFE instance MIR fixture: {message}")


def walk(value):
    if isinstance(value, dict):
        yield value
        for child in value.values():
            yield from walk(child)
    elif isinstance(value, list):
        for child in value:
            yield from walk(child)


def main(path):
    document = load_mir_document(path)
    expected = {
        "ctfe_producer_types::Pair": (2, 4),
        "ctfe_producer_types::Token::Number": (2, 11),
        "ctfe_producer_types::compile_time_add": (2, 17),
        "ctfe_producer_types::Opcode::compile_time_xor": (2, 21),
    }
    rows = {row.get("def_path"): row for row in document["instances"]}
    for def_path, (crate, index) in expected.items():
        require(def_path in rows, f"missing instance row {def_path}")
        row = rows[def_path]
        require(row["def_id"] == {"crate": crate, "index": index},
                f"{def_path} DefId changed: {row['def_id']}")
        require(row["instance_kind"] == {"def_id": {"crate": crate, "index": index}, "kind": "item"},
                f"{def_path} is not an Item instance: {row['instance_kind']}")
        require(row["kind"] == "instance_mir" and row["status"] == "supported",
                f"{def_path} is not supported instance MIR: {row['kind']} / {row['status']}")
        require(row["body_instantiation"] == {"kind": "substituted_and_normalized", "status": "supported"},
                f"{def_path} body was not normalized: {row.get('body_instantiation')}")
        require(row["instance_args_are_monomorphic"] is True,
                f"{def_path} arguments are not monomorphic")
        require(row["body_template_is_polymorphic"] is False,
                f"{def_path} body template is polymorphic")
        body = row["body"]
        require(body["source_def_id"] == {"crate": crate, "index": index},
                f"{def_path} loaded body has a different source DefId")
        require(body["source_instance_kind"] == row["instance_kind"],
                f"{def_path} loaded body has a different source instance kind")
        require(body["basic_blocks"], f"{def_path} loaded body has no basic blocks")
        for node in walk(body["basic_blocks"]):
            require(node.get("status") != "unsupported",
                    f"{def_path} body contains unsupported node {node}")

    pair = rows["ctfe_producer_types::Pair"]["body"]["basic_blocks"]
    pair_aggregate = [n for n in walk(pair) if n.get("kind") == "Aggregate"]
    require(any(n.get("aggregate_kind", {}).get("def_path") == "ctfe_producer_types::Pair"
                for n in pair_aggregate), "tuple constructor body lacks its Pair ADT aggregate")
    variant_aggregate = [n for n in walk(rows["ctfe_producer_types::Token::Number"]["body"]["basic_blocks"])
                         if n.get("kind") == "Aggregate"]
    require(any(n.get("aggregate_kind", {}).get("def_path") == "ctfe_producer_types::Token"
                and n.get("aggregate_kind", {}).get("variant_index") == 1
                for n in variant_aggregate), "enum constructor body lacks Token::Number variant 1")

    add_body = rows["ctfe_producer_types::compile_time_add"]["body"]["basic_blocks"]
    xor_body = rows["ctfe_producer_types::Opcode::compile_time_xor"]["body"]["basic_blocks"]
    require(any(n.get("kind") == "BinaryOp" and n.get("operator", {}).get("kind") == "add_with_overflow"
                for n in walk(add_body)), "compile_time_add body lacks supported addition")
    require(any(n.get("kind") == "BinaryOp" and n.get("operator", {}).get("kind") == "bit_xor"
                for n in walk(xor_body)), "compile_time_xor body lacks supported xor")

    calls = []
    for caller in ("make_pair", "make_token"):
        caller_row = rows[caller]
        for block in caller_row["body"]["basic_blocks"]:
            terminator = block.get("terminator", {}).get("kind", {})
            if terminator.get("variant") == "Call":
                calls.append(terminator)
    require(len(calls) == 2, f"expected two constructor call sites, found {len(calls)}")
    for call in calls:
        resolution = call.get("resolution", {})
        require(call.get("call_source", {}).get("kind") == "normal_call",
                f"constructor call is not a normal call: {call.get('call_source')}")
        require(resolution.get("kind") == "indirect_function_pointer"
                and resolution.get("status") == "supported",
                f"constructor call resolution changed: {resolution}")
    print("validated four supported normalized external instance_mir bodies and two indirect constructor call sites")


if __name__ == "__main__":
    if len(sys.argv) != 2:
        raise SystemExit("usage: validate_instance_mir_ctfe_fixture.py EXPORT.json")
    main(sys.argv[1])
