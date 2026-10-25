#!/usr/bin/env python3
"""Build a comparator around hash-checked Miri/rustc source methods."""
import hashlib
import json
from pathlib import Path
import sys


def item(text, marker):
    start = text.index(marker)
    opening = text.index("{", start)
    depth = 0
    for pos in range(opening, len(text)):
        if text[pos] == "{":
            depth += 1
        elif text[pos] == "}":
            depth -= 1
            if depth == 0:
                return text[start:pos + 1]
    raise ValueError(f"unterminated source item: {marker}")


def checked(root, relative):
    lock = json.loads((root / "upstream/source-lock.json").read_text())
    entries = {entry["path"]: entry for entry in lock["files"]}
    data = (root / relative).read_bytes()
    if hashlib.sha256(data).hexdigest() != entries[relative]["sha256"]:
        raise ValueError(f"source hash mismatch: {relative}")
    return data.decode()


def generate(root):
    miri = checked(root, "upstream/miri-source/src/data_structures/range_object_map.rs")
    abi = checked(root, "upstream/rustc-source/compiler/rustc_abi/src/lib.rs")
    allocation = checked(root, "upstream/rustc-source/compiler/rustc_middle/src/mir/interpret/allocation.rs")
    # `find_offset` is made public only so the differential harness can inspect
    # Rust's private search result; its body is otherwise copied verbatim.
    miri = miri.replace("    fn find_offset(&self, offset: Size)",
                        "    pub fn find_offset(&self, offset: Size)", 1)
    if miri.count("pub fn find_offset(&self, offset: Size)") != 1:
        raise ValueError("could not apply the find_offset visibility shim")
    pieces = [
        "use std::ops::{Add, Sub};",
        "extern crate self as rustc_abi;",
        "extern crate self as rustc_const_eval;",
        "#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)] pub struct Size { raw: u64 }",
        "impl Size { pub const ZERO: Size = Size { raw: 0 }; pub fn from_bytes(raw: u64) -> Size { Size { raw } } pub fn bytes(self) -> u64 { self.raw } }",
        item(abi, "impl Add for Size {"),
        item(abi, "impl Sub for Size {"),
        "#[derive(Clone, Copy, Debug)] pub struct AllocRange { pub start: Size, pub size: Size }",
        "pub fn alloc_range(start: Size, size: Size) -> AllocRange { AllocRange { start, size } }",
        "impl AllocRange {" + item(allocation, "pub fn end(self) -> Size {") + "}",
        "pub mod interpret { pub use crate::{alloc_range, AllocRange}; }",
        "mod source {\n" + miri + "\n}",
    ]
    template = (root / "tests/range_object_map/reference.rs.in").read_text()
    return "\n".join(pieces) + "\n" + template


if __name__ == "__main__":
    Path(sys.argv[1]).write_text(generate(Path(__file__).resolve().parents[2]))
