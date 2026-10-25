#!/usr/bin/env python3
"""Reuse the exact Immediate extraction and add unchanged operand/local items."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile

root = Path(__file__).resolve().parents[2]
locked = {item["path"]: item for item in json.loads((root / "upstream/source-lock.json").read_text())["files"]}

def read(relative):
    raw = (root / relative).read_bytes()
    if hashlib.sha256(raw).hexdigest() != locked[relative]["sha256"]:
        raise ValueError(f"pinned source changed: {relative}")
    return raw.decode()

def item(text, marker):
    start = text.index(marker)
    opening = text.index("{", start)
    depth = 0
    for index in range(opening, len(text)):
        if text[index] == "{":
            depth += 1
        elif text[index] == "}":
            depth -= 1
            if depth == 0:
                return text[start:index + 1]
    raise ValueError(f"unclosed source item: {marker}")

with tempfile.TemporaryDirectory() as work:
    immediate = Path(work) / "immediate.rs"
    subprocess.run([sys.executable, str(root / "tests/immediate/extract_reference.py"), str(immediate)], check=True)
    prelude = immediate.read_text().split("#[derive(Clone,Copy,Debug,PartialEq)]\nstruct AddressProvenance")[0]
prelude = prelude.replace("rustc_private,try_trait_v2", "rustc_private,try_trait_v2,yeet_expr")
operand = read("upstream/rustc-source/compiler/rustc_const_eval/src/interpret/operand.rs")
place = read("upstream/rustc-source/compiler/rustc_const_eval/src/interpret/place.rs")
stack = read("upstream/rustc-source/compiler/rustc_const_eval/src/interpret/stack.rs")
pieces = [prelude, "use std::cell::Cell; use rustc_middle::throw_ub; use rustc_middle::mir::interpret::Misalignment;",
          "type TyAndLayout<'tcx> = &'tcx str; enum Either<L,R>{Left(L),Right(R)} use Either::{Left,Right};",
          "#[derive(Clone,Copy,Debug)]" + item(place, "pub(super) struct MemPlace<"),
          "impl<Prov: Provenance> MemPlace<Prov> {", item(place, "fn map_provenance("),
          item(place, "fn to_ref("), "}",
          "#[derive(Clone,Copy,Debug)]" + item(operand, "pub(super) enum Operand<"),
          "#[derive(Clone,Copy,Debug)]" + item(stack, "pub(super) enum LocalValue<"),
          item(stack, "pub struct LocalState<"), "impl<'tcx, Prov: Provenance> LocalState<'tcx, Prov> {"]
for marker in ["pub fn make_live_uninit(", "pub fn as_mplace_or_imm_ghost(", "pub(super) fn access(", "pub(super) fn access_mut("]:
    pieces.append(item(stack, marker))
pieces += ["}", (root / "tests/operand/reference.rs.in").read_text().replace("fn main(){", "pub fn run_reference(){")]
generated = "\n".join(pieces)
attribute, rest = generated.split("\n", 1)
Path(sys.argv[1]).write_text(attribute + "\nmod source {\n" + rest + "\n}\nfn main(){source::run_reference()}\n")
