#!/usr/bin/env python3
"""Hash-check and wrap the pinned Miri DedupRangeMap source for differential tests."""
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
    dedup = checked(root, "upstream/miri-source/src/data_structures/dedup_range_map.rs")
    abi = checked(root, "upstream/rustc-source/compiler/rustc_abi/src/lib.rs")
    size_methods = ["pub fn from_bytes(", "pub fn bytes(self)"]
    pieces = [
        "extern crate self as rustc_abi;",
        "#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Default)] pub struct Size { raw: u64 }",
        "impl Size { pub const ZERO: Size = Size { raw: 0 }; " +
            " ".join(item(abi, marker) for marker in size_methods) + " }",
        "mod source {\n" + dedup + "\n}",
    ]
    template = (root / "tests/dedup_range_map/reference.rs.in").read_text()
    return "\n".join(pieces) + "\n" + template


if __name__ == "__main__":
    Path(sys.argv[1]).write_text(generate(Path(__file__).resolve().parents[2]))
