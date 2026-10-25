#!/usr/bin/env python3
"""Extract the exact pinned AllocMap::reserve implementation."""
import hashlib
import json
from pathlib import Path
import sys


SOURCE = "upstream/rustc-source/compiler/rustc_middle/src/mir/interpret/mod.rs"


def generate(root: Path) -> str:
    lock = json.loads((root / "upstream/source-lock.json").read_text())
    expected = {entry["path"]: entry["sha256"] for entry in lock["files"]}[SOURCE]
    data = (root / SOURCE).read_bytes()
    actual = hashlib.sha256(data).hexdigest()
    if actual != expected:
        raise ValueError(f"pinned source hash mismatch for {SOURCE}: {actual}")
    source = data.decode()
    marker = "    fn reserve(&self) -> AllocId {"
    start = source.index(marker)
    opening = source.index("{", start)
    depth = 0
    for position in range(opening, len(source)):
        if source[position] == "{":
            depth += 1
        elif source[position] == "}":
            depth -= 1
            if depth == 0:
                method = source[start:position + 1]
                template = (root / "tests/memory_state/alloc_id_reference.rs.in").read_text()
                return template.replace("/* EXTRACTED_RESERVE */", method)
    raise ValueError("unterminated rustc AllocMap::reserve")


if __name__ == "__main__":
    Path(sys.argv[1]).write_text(generate(Path(__file__).resolve().parents[2]))
