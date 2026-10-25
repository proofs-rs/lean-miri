#!/usr/bin/env python3
"""Embed hash-checked rustc allocator lifecycle methods into a small shim."""
import hashlib
import json
from pathlib import Path
import sys


SOURCE = "upstream/rustc-source/compiler/rustc_const_eval/src/interpret/memory.rs"
MARKERS = {
    "/* EXTRACTED_ALLOCATE_PTR */": "    pub fn allocate_ptr(",
    "/* EXTRACTED_INSERT_ALLOCATION */": "    pub fn insert_allocation(",
    "/* EXTRACTED_DEALLOCATE_PTR */": "    pub fn deallocate_ptr(",
}


def checked_source(root: Path) -> str:
    lock = json.loads((root / "upstream/source-lock.json").read_text())
    expected = {entry["path"]: entry["sha256"] for entry in lock["files"]}[SOURCE]
    data = (root / SOURCE).read_bytes()
    actual = hashlib.sha256(data).hexdigest()
    if actual != expected:
        raise ValueError(f"pinned source hash mismatch for {SOURCE}: {actual}")
    return data.decode()


def item(source: str, marker: str) -> str:
    start = source.index(marker)
    opening = source.index("{", start)
    depth = 0
    for position in range(opening, len(source)):
        if source[position] == "{":
            depth += 1
        elif source[position] == "}":
            depth -= 1
            if depth == 0:
                return source[start:position + 1]
    raise ValueError(f"unterminated source item: {marker}")


def generate(root: Path) -> str:
    source = checked_source(root)
    template = (root / "tests/memory_state/lifecycle_reference.rs.in").read_text()
    for placeholder, marker in MARKERS.items():
        template = template.replace(placeholder, item(source, marker))
    return template


if __name__ == "__main__":
    Path(sys.argv[1]).write_text(generate(Path(__file__).resolve().parents[2]))
