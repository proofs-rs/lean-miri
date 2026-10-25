#!/usr/bin/env python3
"""Extract selected exact GlobalStateInner code after verifying pinned source."""

from __future__ import annotations

import hashlib
import sys
from pathlib import Path


EXPECTED_BORROW_TRACKER = "65660956220eac0d8270b273ac1074454f1c6f75"


def git_blob_sha1(contents: bytes) -> str:
    header = b"blob " + str(len(contents)).encode("ascii") + b"\0"
    return hashlib.sha1(header + contents).hexdigest()


def extract(source_path: Path, template_path: Path, output_path: Path) -> None:
    source_bytes = source_path.read_bytes()
    actual = git_blob_sha1(source_bytes)
    if actual != EXPECTED_BORROW_TRACKER:
        raise ValueError(
            f"pinned borrow_tracker source blob mismatch: expected {EXPECTED_BORROW_TRACKER}, got {actual}"
        )
    source = source_bytes.decode("utf-8")

    def block(start_marker: str, end_marker: str) -> str:
        start = source.index(start_marker)
        end = source.index(end_marker, start)
        return source[start:end].rstrip()

    replacements = {
        "// @PINNED_BOR_TAG@": block(
            "/// Tracking pointer provenance",
            "/// Per-call-stack-frame data for borrow tracking",
        ),
        "// @PINNED_PROTECTOR_KIND@": block(
            "/// The flavor of the protector.",
            "/// Utilities for initialization and ID generation",
        ),
        "// @PINNED_NEW_PTR_END_CALL_ROOT_TAG@": "\n\n".join(
            [
                block("    /// Generates a new pointer tag.", "    pub fn new_frame"),
                block("    fn end_call(", "    pub fn root_ptr_tag"),
                block("    pub fn root_ptr_tag(", "    pub fn remove_unreachable_allocs"),
            ]
        ),
    }
    generated = template_path.read_text(encoding="utf-8")
    for marker, body in replacements.items():
        if generated.count(marker) != 1:
            raise ValueError(f"Rust shim must contain exactly one marker: {marker}")
        generated = generated.replace(marker, body)
    output_path.write_text(generated, encoding="utf-8")
    print("extracted pinned BorTag, ProtectorKind, and GlobalStateInner methods after Git blob hash check")


if __name__ == "__main__":
    if len(sys.argv) != 4:
        raise SystemExit(
            "usage: extract_global_state_reference.py BORROW_TRACKER_RS TEMPLATE_RS OUTPUT_RS"
        )
    extract(Path(sys.argv[1]), Path(sys.argv[2]), Path(sys.argv[3]))
