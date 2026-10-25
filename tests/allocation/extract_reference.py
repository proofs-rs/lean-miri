#!/usr/bin/env python3
"""Verify the pinned allocation source before using its rustc-private API."""

import hashlib
import json
from pathlib import Path
import sys

root = Path(__file__).resolve().parents[2]
relative = "upstream/rustc-source/compiler/rustc_middle/src/mir/interpret/allocation.rs"
lock = json.loads((root / "upstream/source-lock.json").read_text())
expected = next(entry["sha256"] for entry in lock["files"] if entry["path"] == relative)
actual = hashlib.sha256((root / relative).read_bytes()).hexdigest()
if actual != expected:
    raise SystemExit(f"allocation source hash mismatch: expected {expected}, got {actual}")
template = (root / "tests/allocation/reference.rs.in").read_text()
Path(sys.argv[1]).write_text(template)
print(f"verified pinned rustc allocation source ({expected})")
