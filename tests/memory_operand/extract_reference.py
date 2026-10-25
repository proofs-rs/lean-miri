#!/usr/bin/env python3
"""Hash-check and splice exact pinned immediate-memory helper bodies."""

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
ALLOCATION = "upstream/rustc-source/compiler/rustc_middle/src/mir/interpret/allocation.rs"
operand = read(OPERAND)
place = read(PLACE)
read(ALLOCATION)  # Scalar storage methods are called from the pinned Allocation API.

pieces = [
    "#[derive(Clone, Copy, Debug)]" + item(operand, "pub enum Immediate<"),
    item(operand, "impl<Prov: Provenance> From<Scalar<Prov>>"),
]

# Keep the source ImmTy constructors used by the exact read methods.
pieces += [
    "struct ImmTy<'tcx, Prov: Provenance> { pub imm: Immediate<Prov>, pub layout: TyAndLayout<'tcx> }",
    "impl<'tcx, Prov: Provenance> ImmTy<'tcx, Prov> {",
    item(operand, "pub fn from_scalar("),
    item(operand, "pub fn from_immediate("),
    item(operand, "pub fn uninit("),
    "}",
]

pieces += [
    "impl<'tcx, M: Machine<'tcx>> InterpCx<'tcx, M> {",
    item(operand, "fn read_immediate_from_mplace_raw("),
    item(operand, "pub fn read_immediate_raw("),
    "}",
]

reference = (ROOT / "tests/memory_operand/reference.rs.in").read_text()
(Path(sys.argv[1])).write_text(reference.replace("@ORIGINAL_ITEMS@", "\n".join(pieces)))
