#!/usr/bin/env python3
"""Hash-check and splice exact pinned immediate-write helper bodies."""

import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
LOCKED = {
    entry["path"]: entry
    for entry in json.loads((ROOT / "upstream/source-lock.json").read_text())["files"]
}


def read(relative: str) -> str:
    raw = (ROOT / relative).read_bytes()
    expected = LOCKED[relative]["sha256"]
    actual = hashlib.sha256(raw).hexdigest()
    if actual != expected:
        raise SystemExit(f"pinned source hash mismatch for {relative}: {actual} != {expected}")
    return raw.decode()


def item(source: str, marker: str) -> str:
    start = source.index(marker)
    opening = source.index("{", start)
    depth = 0
    for index in range(opening, len(source)):
        if source[index] == "{":
            depth += 1
        elif source[index] == "}":
            depth -= 1
            if depth == 0:
                return source[start:index + 1]
    raise ValueError(f"unclosed source item {marker}")


OPERAND = "upstream/rustc-source/compiler/rustc_const_eval/src/interpret/operand.rs"
PLACE = "upstream/rustc-source/compiler/rustc_const_eval/src/interpret/place.rs"
operand = read(OPERAND)
place = read(PLACE)

pieces = [
    "#[derive(Clone, Copy, Debug)]" + item(operand, "pub enum Immediate<"),
    "impl<Prov: Provenance> Immediate<Prov> {",
    item(operand, "pub fn assert_matches_abi("),
    "}",
    "impl<'tcx, M: Machine<'tcx>> InterpCx<'tcx, M> {",
    item(place, "fn write_immediate_to_mplace_no_validate("),
    "}",
]

template = (ROOT / "tests/memory_operand/write_reference.rs.in").read_text()
(Path(sys.argv[1])).write_text(template.replace("@ORIGINAL_ITEMS@", "\n".join(pieces)))
