#!/usr/bin/env python3
"""Hash-check and extract unchanged allocation access methods from rustc."""

import hashlib
import json
from pathlib import Path
import sys

root = Path(__file__).resolve().parents[2]
relative = "upstream/rustc-source/compiler/rustc_const_eval/src/interpret/memory.rs"
lock = json.loads((root / "upstream/source-lock.json").read_text())
entry = next(item for item in lock["files"] if item["path"] == relative)
data = (root / relative).read_bytes()
actual = hashlib.sha256(data).hexdigest()
if actual != entry["sha256"]:
    raise SystemExit(f"memory.rs source hash mismatch: expected {entry['sha256']}, got {actual}")
blob = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
if blob != entry["git_blob"]:
    raise SystemExit(f"memory.rs Git blob mismatch: expected {entry['git_blob']}, got {blob}")
source = data.decode("utf-8")

fragments = []
for start_marker, end_marker in [
    ("    fn check_and_deref_ptr<T, R: Borrow<Self>>(", "\n    pub(super) fn check_misalign("),
    ("    pub fn get_ptr_alloc<'a>(", "\n    /// Return the `extra` field of the given allocation."),
    ("    pub fn get_ptr_alloc_mut<'a>(", "\n    /// Return the `extra` field of the given allocation."),
]:
    start = source.index(start_marker)
    end = source.index(end_marker, start)
    fragments.append(source[start:end].rstrip())

template = (root / "tests/allocation_access/reference.rs.in").read_text()
marker = "// @PINNED_ACCESS_FUNCTIONS@"
if template.count(marker) != 1:
    raise SystemExit("Rust allocation access shim must contain exactly one extraction marker")
Path(sys.argv[1]).write_text(template.replace(marker, "\n\n".join(fragments)))
print(f"extracted three hash-checked memory.rs methods ({entry['sha256']}; blob {entry['git_blob']})")
