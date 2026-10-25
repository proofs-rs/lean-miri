#!/usr/bin/env python3
"""Verify the pinned scalar source files, then materialize the API harness."""

from __future__ import annotations

import hashlib
import json
from pathlib import Path
import sys


ROOT = Path(__file__).resolve().parents[2]
LOCK = json.loads((ROOT / "upstream/source-lock.json").read_text())
SOURCES = (
    "upstream/rustc-source/compiler/rustc_middle/src/ty/consts/int.rs",
    "upstream/rustc-source/compiler/rustc_middle/src/mir/interpret/value.rs",
    "upstream/rustc-source/compiler/rustc_middle/src/mir/interpret/allocation.rs",
)


def main() -> None:
    manifest = {item["path"]: item for item in LOCK["files"]}
    for relative in SOURCES:
        source = ROOT / relative
        expected = manifest[relative]["sha256"]
        actual = hashlib.sha256(source.read_bytes()).hexdigest()
        if actual != expected:
            raise SystemExit(f"{relative}: SHA-256 mismatch: {actual} != {expected}")
        print(f"verified pinned scalar source {relative} ({expected})")

    output = Path(sys.argv[1])
    output.write_text((ROOT / "tests/scalar/reference.rs.in").read_text())


if __name__ == "__main__":
    main()
