#!/usr/bin/env python3
"""Verify the exact interpreter sources and Miri binary used by this test."""

import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
EXPECTED_RUSTC = "8eb778d04094d3af4b26580cab327e0413eb1e02"
EXPECTED_MIRI = "93c45edea8b148a6b6f05ec9384449a04217143f"
SOURCE_PATHS = [
    "upstream/rustc-source/compiler/rustc_const_eval/src/interpret/cast.rs",
    "upstream/rustc-source/compiler/rustc_const_eval/src/interpret/intrinsics.rs",
]


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


lock = json.loads((ROOT / "upstream/source-lock.json").read_text(encoding="utf-8"))
assert lock["pins"]["rustc"]["commit"] == EXPECTED_RUSTC
assert lock["pins"]["miri"]["commit"] == EXPECTED_MIRI
for relative in SOURCE_PATHS:
    record = next(item for item in lock["files"] if item["path"] == relative)
    assert record["component"] == "rustc_const_eval_interpret"
    actual = sha256(ROOT / relative)
    assert actual == record["sha256"], f"pinned source hash mismatch for {relative}"

build = json.loads((ROOT / "scratch/lake/miri-reference-build.json").read_text(encoding="utf-8"))
assert build["rustc_commit"] == EXPECTED_RUSTC
binary = ROOT / "scratch/lake/miri-target/debug/miri"
assert sha256(binary) == build["binary_sha256"], "pinned reference Miri binary changed"
print("validated pinned cast.rs/intrinsics.rs and reference Miri binary")
