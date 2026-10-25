#!/usr/bin/env python3
"""Hash-check and extract the exact pinned memory access helper bodies."""

import hashlib
import json
from pathlib import Path
import sys

root = Path(__file__).resolve().parents[2]
relative = "upstream/rustc-source/compiler/rustc_const_eval/src/interpret/memory.rs"
lock = json.loads((root / "upstream/source-lock.json").read_text())
expected = next(entry["sha256"] for entry in lock["files"] if entry["path"] == relative)
data = (root / relative).read_bytes()
actual = hashlib.sha256(data).hexdigest()
if actual != expected:
    raise SystemExit(f"memory.rs source hash mismatch: expected {expected}, got {actual}")
source = data.decode("utf-8")
starts_ends = [
    ("    fn check_and_deref_ptr<T, R: Borrow<Self>>(", "\n    pub(super) fn check_misalign("),
    ("    pub(super) fn is_ptr_misaligned(", "\n    /// Checks a pointer for misalignment."),
]
fragments = []
for start_marker, end_marker in starts_ends:
    start = source.index(start_marker)
    end = source.index(end_marker, start)
    fragments.append(source[start:end].rstrip())
template = (root / "tests/allocation/access_reference.rs.in").read_text()
marker = "// @PINNED_ACCESS_FUNCTIONS@"
if template.count(marker) != 1:
    raise SystemExit("Rust access shim must contain exactly one extraction marker")
Path(sys.argv[1]).write_text(template.replace(marker, "\n\n".join(fragments)))
print(f"extracted hash-checked memory access helpers ({expected})")
