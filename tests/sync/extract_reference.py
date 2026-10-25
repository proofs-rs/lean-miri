#!/usr/bin/env python3
"""Insert unmodified pinned Miri Mutex state and mutex_lock source into a shim."""

from __future__ import annotations

import hashlib
import sys
from pathlib import Path


EXPECTED_SHA1 = "3e848a071e2a67792eada4625b1751eec119b21d"


def item(source: str, marker: str, include_derive: bool = False) -> str:
    marker_at = source.index(marker)
    start = source.rfind("\n", 0, marker_at) + 1
    if include_derive:
        previous_end = start - 1
        previous_start = source.rfind("\n", 0, previous_end) + 1
        if source[previous_start:previous_end].strip().startswith("#[derive("):
            start = previous_start
    opening = source.index("{", marker_at)
    depth = 0
    for position in range(opening, len(source)):
        char = source[position]
        if char == "{":
            depth += 1
        elif char == "}":
            depth -= 1
            if depth == 0:
                return source[start:position + 1]
    raise ValueError(f"unterminated source item: {marker}")


def main() -> None:
    if len(sys.argv) != 4:
        raise SystemExit("usage: extract_reference.py SYNC_RS TEMPLATE OUTPUT")
    source_path, template_path, output_path = map(Path, sys.argv[1:])
    source = source_path.read_bytes()
    actual_sha1 = hashlib.sha1(source).hexdigest()
    if actual_sha1 != EXPECTED_SHA1:
        raise SystemExit(
            f"pinned sync.rs SHA-1 mismatch: expected {EXPECTED_SHA1}, got {actual_sha1}"
        )
    text = source.decode("utf-8")
    template = template_path.read_text(encoding="utf-8")
    output = template.replace("// @MIRI_MUTEX_STATE@", item(text, "struct Mutex {", True))
    output = output.replace("// @MIRI_MUTEX_LOCK@", item(text, "fn mutex_lock("))
    output = output.replace("// @MIRI_MUTEX_UNLOCK@", item(text, "fn mutex_unlock("))
    output = output.replace("// @MIRI_RWLOCK_STATE@", item(text, "struct RwLock {", True))
    output = output.replace("// @MIRI_RWLOCK_IS_LOCKED@", item(text, "fn is_locked(&self)"))
    output = output.replace("// @MIRI_RWLOCK_IS_WRITE_LOCKED@", item(text, "fn is_write_locked(&self)"))
    output = output.replace("// @MIRI_RWLOCK_READER_LOCK@", item(text, "fn rwlock_reader_lock("))
    output = output.replace("// @MIRI_RWLOCK_WRITER_LOCK@", item(text, "fn rwlock_writer_lock("))
    if "@MIRI_" in output:
        raise SystemExit("unfilled source extraction marker")
    output_path.write_text(output, encoding="utf-8")


if __name__ == "__main__":
    main()
