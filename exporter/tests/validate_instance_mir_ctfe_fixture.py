#!/usr/bin/env python3
"""Validate source116 external Ctor and #[rustc_comptime] instance MIR rows."""
import json
import pathlib
import sys

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[2] / "tools"))
from mir_json import load_mir_inspection_document as load_mir_document, pool_entry


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


def physical_definition(document, definition_id):
    definition = pool_entry(document, "definitions", definition_id)
    identity = (definition.get("crate"), definition.get("index"))
    require(all(type(part) is int and part >= 0 for part in identity),
            f"invalid physical definition at pool ID {definition_id}: {identity}")
    return identity


def source_body(document, row):
    body = pool_entry(document, "bodies", row["body"])
    require(body["instance_id"] == row["instance_id"], "body concrete instance differs")
    if body["body_kind"] == "copy_template":
        require(set(body) == {"body_kind", "template_id", "instance_id", "generic_args", "promoted_bodies"},
                "raw body reference has unexpected fields")
        template_id = body["template_id"]
        require(type(template_id) is int and 0 <= template_id < len(document["mir_templates"]),
                "raw body template reference is absent")
        source = document["mir_templates"][template_id]
        require(source["source_def_id"] == row["def_id"] and source["def_path"] == row["def_path"],
                "raw body source owner differs from complete instance")
        require(source["source_role"] == "runtime" and source["source_promoted"] is None
                and source["injection_phase"] is None and body["promoted_bodies"] == [],
                "raw body source runtime/promoted/injection role differs")
        require(body["generic_args"] == row["generic_args"], "raw body full instance arguments differ")
        template = json.loads(source["template"])
        require(template["parameters"] == [
            {"type": "type", "const": "constant", "lifetime": "region"}[arg["kind"]]
            for arg in row["generic_args"]], "raw body parameter sorts differ from full instance arguments")
        require(template["skeleton"]["phase"] == "runtime_optimized", "raw runtime MIR phase differs")
        return source, template["skeleton"]["blocks"], template
    require(body["body_kind"] == "material" and body["source_role"] == "runtime",
            "expected runtime material MIR or exact raw template reference")
    require(body["phase"] == {"kind": "runtime", "phase": "post_cleanup"}
            and body["injection_phase"] is None, "comptime instance lost its actual CTFE MIR phase")
    return body, body["basic_blocks"], None


def constructor(document, row, adt_identity, variant):
    source, blocks, template = source_body(document, row)
    require(template is not None and template["parameters"] == [] and row["generic_args"] == [],
            "constructor fixture requires its exact parameter-free raw source")
    aggregates = [node for node in walk(blocks) if node.get("kind") == "adt"]
    require(len(aggregates) == 1, "constructor must retain exactly one raw ADT aggregate")
    aggregate = aggregates[0]
    ty = template["types"][aggregate["type"]]
    require(ty == {"kind": "definition", "sort": "type", "tag": "adt",
                   "definition": {"crate": adt_identity[0], "index": adt_identity[1]}, "children": []}
            and aggregate["variant"] == variant,
            "constructor raw aggregate physical ADT/variant changed")


def main(path):
    document = load_mir_document(path)
    expected = {
        "ctfe_producer_types::Pair": (2, 4, (5, 0)),
        "ctfe_producer_types::Token::Number": (2, 11, (9, 4)),
        "ctfe_producer_types::compile_time_add": (2, 17, (15, 0)),
        "ctfe_producer_types::Opcode::compile_time_xor": (2, 21, (24, 4)),
    }
    rows = {row.get("def_path"): row for row in document["instances"]}
    for def_path, (crate, index, source_start) in expected.items():
        matches = [row for row in document["instances"] if row.get("def_path") == def_path]
        require(len(matches) == 1, f"expected one complete instance row {def_path}, found {len(matches)}")
        row = matches[0]
        # Pool IDs depend on source-material demand order. Compare rustc's
        # physical DefId, while retaining all additional raw declaration data.
        identity = physical_definition(document, row["def_id"])
        require(identity == (crate, index),
                f"{def_path} physical DefId changed: {identity}")
        require(sum(physical_definition(document, offset) == identity
                    for offset in range(len(document["definitions"]))) == 1,
                f"{def_path} has duplicate physical definition identities")
        require(row["instance_kind"] == {"def_id": row["def_id"], "kind": "item"},
                f"{def_path} is not an Item instance: {row['instance_kind']}")
        require(row["kind"] == "instance_mir" and "status" not in row,
                f"{def_path} is not supported instance MIR: {row['kind']}")
        body, blocks, _ = source_body(document, row)
        require(body["source_def_id"] == row["def_id"],
                f"{def_path} source owner differs from its complete instance")
        require(physical_definition(document, body["source_def_id"]) == identity,
                f"{def_path} loaded body has a different physical source DefId")
        span = pool_entry(document, "spans", body["span"])
        source_file = document["files"][span["file"]]
        require('name: "producer-types/src/lib.rs"' in source_file,
                f"{def_path} loaded body has a different source file: {source_file}")
        require(not span["is_dummy"]
                and (span["start"]["line"], span["start"]["column"]) == source_start,
                f"{def_path} loaded body has a different source position: {span}")
        require("source_instance_kind" not in body,
                f"{def_path} loaded body contains an unused source instance kind")
        require(blocks, f"{def_path} loaded body has no basic blocks")
        for node in walk(blocks):
            require(node.get("status") != "unsupported",
                    f"{def_path} body contains unsupported node {node}")

    constructor(document, rows["ctfe_producer_types::Pair"], (2, 3), 0)
    constructor(document, rows["ctfe_producer_types::Token::Number"], (2, 7), 1)

    add_body = pool_entry(document, "bodies", rows["ctfe_producer_types::compile_time_add"]["body"])["basic_blocks"]
    xor_body = pool_entry(document, "bodies", rows["ctfe_producer_types::Opcode::compile_time_xor"]["body"])["basic_blocks"]
    require(any(n.get("kind") == "BinaryOp" and n.get("operator", {}).get("kind") == "add_with_overflow"
                for n in walk(add_body)), "compile_time_add body lacks supported addition")
    require(any(n.get("kind") == "BinaryOp" and n.get("operator", {}).get("kind") == "bit_xor"
                for n in walk(xor_body)), "compile_time_xor body lacks supported xor")

    calls = []
    for caller in ("make_pair", "make_token"):
        caller_row = rows[caller]
        for block in pool_entry(document, "bodies", caller_row["body"])["basic_blocks"]:
            terminator = block.get("terminator", {}).get("kind", {})
            if terminator.get("variant") == "Call":
                calls.append(terminator)
    require(len(calls) == 2, f"expected two constructor call sites, found {len(calls)}")
    for call in calls:
        resolution = call.get("resolution", {})
        require(call.get("call_source", {}).get("kind") == "normal_call",
                f"constructor call is not a normal call: {call.get('call_source')}")
        require(resolution.get("kind") == "indirect_function_pointer"
                and "status" not in resolution,
                f"constructor call resolution changed: {resolution}")
    print("validated four supported normalized external instance_mir bodies and two indirect constructor call sites")


if __name__ == "__main__":
    if len(sys.argv) != 2:
        raise SystemExit("usage: validate_instance_mir_ctfe_fixture.py EXPORT.json")
    main(sys.argv[1])
