#!/usr/bin/env python3
"""Build a stable Rust shim around byte-exact init-mask source blocks."""

from __future__ import annotations

import hashlib
import sys
from pathlib import Path

EXPECTED_BLOB = "4dfa22624cbac24572f91df0673ea7ddb486bfb8"
MARKER = "// @PINNED_INIT_MASK_IMPLS@"
BLOCK_STARTS = (
    ("impl InitMask {", "\n/// The actual materialized blocks"),
    ("impl InitMaskMaterialized {", "\n/// A contiguous chunk of initialized or uninitialized memory."),
    ("impl InitChunk {", "\nimpl InitMask {"),
    ("impl InitMask {", "\n/// Yields ["),
    ("impl<'a> Iterator for InitChunkIter<'a> {", "\n/// Run-length encoding of the uninit mask."),
)
COPY_START = "pub struct InitCopy {"

def git_blob_sha1(data: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(data)).encode("ascii") + b"\0" + data).hexdigest()

def extract(source_path: Path, template_path: Path, output_path: Path) -> None:
    data = source_path.read_bytes()
    actual = git_blob_sha1(data)
    if actual != EXPECTED_BLOB:
        raise ValueError(f"pinned init_mask.rs blob mismatch: expected {EXPECTED_BLOB}, got {actual}")
    source = data.decode("utf-8")
    fragments: list[str] = []
    cursor = 0
    for start_marker, end_marker in BLOCK_STARTS:
        start = source.index(start_marker, cursor)
        end = source.index(end_marker, start)
        fragments.append(source[start:end].rstrip())
        cursor = end
    copy_start = source.index(COPY_START)
    fragments.append(source[copy_start:].rstrip())
    template = template_path.read_text(encoding="utf-8")
    if template.count(MARKER) != 1:
        raise ValueError("Rust shim must contain exactly one extraction marker")
    output_path.write_text(template.replace(MARKER, "\n\n".join(fragments)), encoding="utf-8")
    print(f"extracted hash-checked rustc init-mask functions ({EXPECTED_BLOB})")

def main() -> None:
    if len(sys.argv) != 4:
        raise SystemExit("usage: extract_reference.py PINNED_INIT_MASK_RS RUST_TEMPLATE OUTPUT_RS")
    extract(Path(sys.argv[1]), Path(sys.argv[2]), Path(sys.argv[3]))

if __name__ == "__main__":
    main()
