#!/usr/bin/env python3
"""Embed the pinned rustc global-allocation accessor in a test shim."""
import hashlib
import json
from pathlib import Path
import sys


SOURCE = "upstream/rustc-source/compiler/rustc_const_eval/src/interpret/memory.rs"
MARKER = "/* EXTRACTED_GET_GLOBAL_ALLOC */"
METHOD = "    fn get_global_alloc("


def extract(source: str) -> str:
    start = source.index(METHOD)
    opening = source.index("{", start)
    depth = 0
    for position in range(opening, len(source)):
        if source[position] == "{":
            depth += 1
        elif source[position] == "}":
            depth -= 1
            if depth == 0:
                return source[start:position + 1]
    raise ValueError("unterminated get_global_alloc source method")


def generate(root: Path) -> str:
    lock = json.loads((root / "upstream/source-lock.json").read_text())
    expected = {entry["path"]: entry["sha256"] for entry in lock["files"]}[SOURCE]
    data = (root / SOURCE).read_bytes()
    actual = hashlib.sha256(data).hexdigest()
    if actual != expected:
        raise ValueError(f"pinned source hash mismatch for {SOURCE}: {actual}")
    template = (root / "tests/memory_state/global_access_reference.rs.in").read_text()
    return template.replace(MARKER, extract(data.decode()))


if __name__ == "__main__":
    Path(sys.argv[1]).write_text(generate(Path(__file__).resolve().parents[2]))
