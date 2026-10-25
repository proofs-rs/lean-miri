#!/usr/bin/env python3
"""Hash-check and extract rustc's allocation-info and liveness methods."""
import hashlib
import json
from pathlib import Path
import sys


SOURCE = "upstream/rustc-source/compiler/rustc_const_eval/src/interpret/memory.rs"
METHODS = {
    "EXTRACTED_GET_FN_ALLOC": "    fn get_fn_alloc(&self, id: AllocId)",
    "EXTRACTED_IS_ALLOC_LIVE": "    pub fn is_alloc_live(&self, id: AllocId)",
    "EXTRACTED_GET_ALLOC_INFO": "    pub fn get_alloc_info(&self, id: AllocId)",
}


def extract(source: str, marker: str) -> str:
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
    raise ValueError(f"unterminated method starting at {marker!r}")


def generate(root: Path) -> str:
    lock = json.loads((root / "upstream/source-lock.json").read_text())
    expected = {entry["path"]: entry["sha256"] for entry in lock["files"]}[SOURCE]
    data = (root / SOURCE).read_bytes()
    actual = hashlib.sha256(data).hexdigest()
    if actual != expected:
        raise ValueError(f"pinned source hash mismatch for {SOURCE}: {actual}")
    source = data.decode()
    template = (root / "tests/memory_state/global_info_reference.rs.in").read_text()
    for name, marker in METHODS.items():
        template = template.replace(f"/* {name} */", extract(source, marker))
    return template


if __name__ == "__main__":
    Path(sys.argv[1]).write_text(generate(Path(__file__).resolve().parents[2]))
