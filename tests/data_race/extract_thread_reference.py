#!/usr/bin/env python3
"""Inject selected exact ThreadManager methods from the pinned Miri source."""

from __future__ import annotations

import hashlib
import sys
from pathlib import Path


EXPECTED_BLOB = "3966ea360b516dac9320c1aae297d3eb3779548d"


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
        raise ValueError(f"pinned thread.rs blob mismatch: expected {EXPECTED_BLOB}, got {actual}")
    source = contents.decode("utf-8")
    template = template_path.read_text(encoding="utf-8")
    fragments = {
        "// @MIRI_THREAD_NEW@": section(
            source,
            "    fn new(name: Option<&str>, on_stack_empty: Option<StackEmptyCallback<'tcx>>) -> Self {",
            "\n}\n\nimpl VisitProvenance for Thread",
        ),
        "// @MIRI_THREAD_LOOKUP@": section(
            source,
            "    pub fn thread_id_try_from(&self, id: impl TryInto<u32>) -> Result<ThreadId, ThreadLookupError> {",
            "    /// Check if we have an allocation for the given thread local static for the",
        ),
        "// @MIRI_CREATE_THREAD@": section(
            source,
            "    fn create_thread(&mut self, on_stack_empty: StackEmptyCallback<'tcx>) -> ThreadId {",
            "    /// Set an active thread and return the id of the thread that was active before.",
        ),
        "// @MIRI_SET_ACTIVE@": section(
            source,
            "    pub(super) fn set_active_thread(&mut self, id: ThreadId) -> ThreadId {",
            "    /// Get the id of the currently active thread.",
        ),
        "// @MIRI_LIVE_COUNT@": section(
            source,
            "    pub fn get_live_thread_count(&self) -> usize {",
            "    /// Has the given thread terminated?",
        ),
        "// @MIRI_DETACH@": section(
            source,
            "    fn detach_thread(&mut self, id: ThreadId, allow_terminated_joined: bool) -> InterpResult<'tcx> {",
            "    /// Set the name of the given thread.",
        ),
        "// @MIRI_BLOCK@": section(
            source,
            "    fn block_thread(\n        &mut self,",
            "    pub fn fixed_scheduling(&self) -> bool {",
        ),
    }
    for marker, fragment in fragments.items():
        if template.count(marker) != 1:
            raise ValueError(f"Rust shim must contain exactly one {marker}")
        template = template.replace(marker, fragment)
    return template.replace("pub(super)", "pub")


def main() -> None:
    source, template, output = map(Path, sys.argv[1:4])
    output.write_text(extract(source, template), encoding="utf-8")


if __name__ == "__main__":
    main()
