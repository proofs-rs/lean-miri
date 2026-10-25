#!/usr/bin/env python3
"""Hash-check and extract selected complete original Immediate impl items."""
import hashlib
import json
from pathlib import Path
import sys

root = Path(__file__).resolve().parents[2]
locked = {item["path"]: item for item in json.loads((root / "upstream/source-lock.json").read_text())["files"]}

def read(relative):
    raw = (root / relative).read_bytes()
    if hashlib.sha256(raw).hexdigest() != locked[relative]["sha256"]:
        raise ValueError(f"pinned source hash mismatch: {relative}")
    return raw.decode()

def item(source, marker):
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
    raise ValueError(f"unclosed item {marker}")

operand = read("upstream/rustc-source/compiler/rustc_const_eval/src/interpret/operand.rs")
place = read("upstream/rustc-source/compiler/rustc_const_eval/src/interpret/place.rs")
pieces = ["#[derive(Clone,Copy,Debug)]" + item(operand, "pub enum Immediate<"),
          "#[derive(Clone,Copy,Debug)]" + item(place, "pub enum MemPlaceMeta<"),
          item(operand, "impl<Prov: Provenance> From<Scalar<Prov>>"),
          "impl<Prov: Provenance> Immediate<Prov> {"]
for method in ["new_pointer_with_meta", "new_slice", "new_dyn_trait", "to_scalar", "to_scalar_int",
               "to_scalar_pair", "to_scalar_and_meta", "clear_provenance", "has_provenance"]:
    pieces.append(item(operand, "pub fn " + method))
pieces += ["}", item(place, "impl<Prov: Provenance> MemPlaceMeta<Prov>")]
template = (root / "tests/immediate/reference.rs.in").read_text()
Path(sys.argv[1]).write_text(template.replace("@ORIGINAL_ITEMS@", "\n".join(pieces)))
