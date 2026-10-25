#!/usr/bin/env python3
"""Inject the exact runnable-thread iterator from pinned Miri scheduler.rs."""

from __future__ import annotations

import hashlib
import sys
from pathlib import Path


EXPECTED_BLOB = "6364710fb89051cc0a451424aedfc5c70d6884e6"
MARKER = "// @MIRI_SCHEDULER_CANDIDATE_ITERATOR@"


def git_blob_sha1(contents: bytes) -> str:
    header = b"blob " + str(len(contents)).encode("ascii") + b"\0"
    return hashlib.sha1(header + contents).hexdigest()


def main() -> None:
    source_path, template_path, output_path = map(Path, sys.argv[1:4])
    contents = source_path.read_bytes()
    actual = git_blob_sha1(contents)
    if actual != EXPECTED_BLOB:
        raise ValueError(
            f"pinned scheduler.rs blob mismatch: expected {EXPECTED_BLOB}, got {actual}"
        )
    source = contents.decode("utf-8")
    start = "        let mut threads_iter = thread_manager\n"
    end = "        // Pick a new thread, and switch to it.\n"
    first = source.index(start)
    last = source.index(end, first)
    fragment = source[first:last].rstrip()
    template = template_path.read_text(encoding="utf-8")
    if template.count(MARKER) != 1:
        raise ValueError(f"Rust shim must contain exactly one {MARKER}")
    output_path.write_text(template.replace(MARKER, fragment), encoding="utf-8")


if __name__ == "__main__":
    main()
