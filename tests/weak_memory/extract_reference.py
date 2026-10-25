#!/usr/bin/env python3
"""Insert exact pinned Miri StoreBuffer methods into the controlled-RNG shim."""

from __future__ import annotations

import hashlib
import sys
from pathlib import Path


EXPECTED_BLOB = "4838144d1d8625379f28ead9864bcfea72a16cc0"


def git_blob_sha1(contents: bytes) -> str:
    header = b"blob " + str(len(contents)).encode("ascii") + b"\0"
    return hashlib.sha1(header + contents).hexdigest()


def method(source: str, start: str, end: str) -> str:
    first = source.index(start)
    last = source.index(end, first)
    return source[first:last].rstrip()


def extract(source_path: Path, template_path: Path) -> str:
    source_bytes = source_path.read_bytes()
    actual = git_blob_sha1(source_bytes)
    if actual != EXPECTED_BLOB:
        raise ValueError(f"pinned weak_memory.rs blob mismatch: expected {EXPECTED_BLOB}, got {actual}")
    source = source_bytes.decode("utf-8")
    template = template_path.read_text(encoding="utf-8")

    replacements = {
        "@MIRI_STORE_BUFFER_NEW@": method(
            source,
            "    fn new(init: Option<Scalar>) -> Self {",
            "    /// Reads from the last store in modification order, if any.",
        ),
        "@MIRI_READ_FROM_LAST_STORE@": method(
            source,
            "    /// Reads from the last store in modification order, if any.",
            "    fn buffered_read(",
        ),
        "@MIRI_BUFFERED_READ@": method(
            source,
            "    fn buffered_read(",
            "    fn buffered_write(",
        ),
        "@MIRI_BUFFERED_WRITE@": method(
            source,
            "    fn buffered_write(",
            "    /// Selects a valid store element in the buffer.",
        ),
        "@MIRI_FETCH_STORE@": method(
            source,
            "    /// Selects a valid store element in the buffer.",
            "    /// ATOMIC STORE IMPL in the paper",
        ),
        "@MIRI_STORE_IMPL@": method(
            source,
            "    /// ATOMIC STORE IMPL in the paper",
            "\n}\n\nimpl StoreElement",
        ),
        "@MIRI_LOAD_IMPL@": method(
            source,
            "    /// ATOMIC LOAD IMPL in the paper",
            "\n}\n\nimpl<'tcx> EvalContextExt",
        ),
        "@MIRI_STORE_BUFFER_ALLOC_NEW@": method(
            source,
            "    pub fn new_allocation() -> Self {",
            "    /// When a non-atomic write happens on a location",
        ),
        "@MIRI_STORE_BUFFER_ALLOC_NON_ATOMIC_WRITE@": method(
            source,
            "    pub fn non_atomic_write(&self, range: AllocRange, global: &DataRaceState) {",
            "    /// Gets a store buffer associated with an atomic object",
        ),
        "@MIRI_STORE_BUFFER_ALLOC_GET@": method(
            source,
            "    fn get_store_buffer<'tcx>(",
            "    /// Gets a mutable store buffer associated with an atomic object",
        ),
        "@MIRI_STORE_BUFFER_ALLOC_GET_OR_CREATE@": method(
            source,
            "    fn get_or_create_store_buffer_mut<'tcx>(",
            "\n}\n\nimpl<'tcx> StoreBuffer",
        ),
    }
    for marker, replacement in replacements.items():
        if marker not in template:
            raise ValueError(f"missing template marker: {marker}")
        template = template.replace(marker, replacement)
    return template


def main() -> None:
    source, template, output = map(Path, sys.argv[1:4])
    output.write_text(extract(source, template), encoding="utf-8")


if __name__ == "__main__":
    main()
