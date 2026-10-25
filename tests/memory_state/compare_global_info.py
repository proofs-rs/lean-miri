#!/usr/bin/env python3
"""Compare liveness and allocation-info rows from source and Lean."""
from pathlib import Path
import sys


TAGS = [
    "info local ",
    "info extra-fn ",
    "info va-list ",
    "info cached-global ",
    "info global-static ",
    "info global-function ",
    "info vtable ",
    "info typeid ",
    "info dead ",
    "live ",
]


def selected(path: Path) -> list[str]:
    lines = path.read_text().splitlines()
    result = []
    for tag in TAGS:
        matches = [line for line in lines if line.startswith(tag)]
        if len(matches) != 1:
            raise ValueError(f"expected one `{tag.strip()}` observation in {path}, got {len(matches)}")
        result.append(matches[0])
    return result


if __name__ == "__main__":
    rust_lines = selected(Path(sys.argv[1]))
    lean_lines = selected(Path(sys.argv[2]))
    if rust_lines != lean_lines:
        for tag, rust, lean in zip(TAGS, rust_lines, lean_lines):
            if rust != lean:
                print(f"{tag.strip()} differs:\n  rust: {rust}\n  lean: {lean}", file=sys.stderr)
        raise SystemExit(1)
