#!/usr/bin/env python3
"""Compare the shared source-backed lifecycle observations from Lean and Rust."""
from pathlib import Path
import sys


TAGS = [
    "allocate ",
    "root-failure ",
    "init-failure ",
    "oversized ",
    "global-kind-assert ",
    "host-exhaustion ",
    "kind-failure ",
    "layout-failure ",
    "dealloc-hook-failure ",
    "deallocated ",
    "double-free ",
    "non-base-free ",
    "global-deallocation ",
]


def selected(path: Path) -> list[str]:
    lines = path.read_text().splitlines()
    output = []
    for tag in TAGS:
        matches = [line for line in lines if line.startswith(tag)]
        if len(matches) != 1:
            raise ValueError(f"expected one `{tag.strip()}` observation in {path}, got {len(matches)}")
        output.append(matches[0])
    return output


if __name__ == "__main__":
    rust_lines = selected(Path(sys.argv[1]))
    lean_lines = selected(Path(sys.argv[2]))
    if rust_lines != lean_lines:
        for tag, rust, lean in zip(TAGS, rust_lines, lean_lines):
            if rust != lean:
                print(f"{tag.strip()} differs:\n  rust: {rust}\n  lean: {lean}", file=sys.stderr)
        raise SystemExit(1)
