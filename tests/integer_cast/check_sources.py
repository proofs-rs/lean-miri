#!/usr/bin/env python3
"""Verify the exact interpreter sources and Miri binary used by this test."""

import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
EXPECTED_RUSTC = "8144389c895da997dbdecaa635e41d6a50be6ffd"
EXPECTED_MIRI = "7fa591d7d4dd9af8154becbc8332f8096f8323b1"
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

build = json.loads((ROOT / "scratch/miri-reference-build.json").read_text(encoding="utf-8"))
assert build["rustc_commit"] == EXPECTED_RUSTC
binary = ROOT / "upstream/miri-source/target/debug/miri"
assert sha256(binary) == build["binary_sha256"], "pinned reference Miri binary changed"
print("validated pinned cast.rs/intrinsics.rs and reference Miri binary")
