#!/usr/bin/env python3
"""Inject hash-checked GlobalState methods from pinned Miri into Rust shims."""

from __future__ import annotations

import hashlib
import sys
from pathlib import Path


EXPECTED_BLOB = "acf45c84bcc6d0f491ef5306ef6662390b96d11a"


def git_blob_sha1(contents: bytes) -> str:
    header = b"blob " + str(len(contents)).encode("ascii") + b"\0"
    return hashlib.sha1(header + contents).hexdigest()


def section(source: str, start: str, end: str) -> str:
    first = source.index(start)
    last = source.index(end, first)
    return source[first:last].rstrip()


def extract(source_path: Path, template_path: Path) -> str:
    contents = source_path.read_bytes()
    actual = git_blob_sha1(contents)
    if actual != EXPECTED_BLOB:
        raise ValueError(f"pinned data_race.rs blob mismatch: expected {EXPECTED_BLOB}, got {actual}")
    source = contents.decode("utf-8")
    template = template_path.read_text(encoding="utf-8")
    fragments = {
        "// @MIRI_FIND_REUSE_CANDIDATE@": section(
            source,
            "    fn find_vector_index_reuse_candidate(&self) -> Option<VectorIdx> {",
            "    // Hook for thread creation",
        ),
        "// @MIRI_ATOMIC_FENCE@": section(
            source,
            "    fn atomic_fence<'tcx>(",
            "    /// Attempt to perform a synchronized operation",
        ),
        "// @MIRI_MAYBE_SYNC@": section(
            source,
            "    fn maybe_perform_sync_operation<'tcx>(",
            "    /// Internal utility to identify a thread stored internally",
        ),
        "// @MIRI_SYNC_CLOCK@": section(
            source,
            "    pub(super) fn sync_clock(&self, access_range: AllocRange) -> VClock {",
            "    /// Detect data-races for an unsynchronized read operation.",
        ).replace("pub(super) fn sync_clock", "fn sync_clock", 1),
    }
    for marker, fragment in fragments.items():
        if marker not in template:
            continue
        if template.count(marker) != 1:
            raise ValueError(f"Rust shim must contain exactly one {marker} marker")
        template = template.replace(marker, fragment)
    atomic_marker = "// @MIRI_ATOMIC_ACCESS_CHECK@"
    if atomic_marker in template:
        if template.count(atomic_marker) != 1:
            raise ValueError("Rust shim must contain exactly one atomic access check marker")
        atomic_check = section(
            source,
            "    fn atomic_access_check(\n",
            "    /// Update the data-race detector for an atomic read occurring at the",
        )
        template = template.replace(atomic_marker, atomic_check)
    return template


def main() -> None:
    source, template, output = map(Path, sys.argv[1:4])
    output.write_text(extract(source, template), encoding="utf-8")


if __name__ == "__main__":
    main()
