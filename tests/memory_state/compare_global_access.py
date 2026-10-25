#!/usr/bin/env python3
"""Compare outcomes and hook ordering from rustc and Lean global lookup."""
from pathlib import Path
import sys


def rows(path: str) -> dict[str, str]:
    result: dict[str, str] = {}
    for line in Path(path).read_text().splitlines():
        if not line.startswith("global "):
            continue
        parts = line.split(maxsplit=2)
        if len(parts) != 3 or parts[0] != "global":
            raise ValueError(f"unexpected global-access row: {line!r}")
        label = parts[1]
        if label in result:
            raise ValueError(f"duplicate global-access row {label!r}")
        result[label] = parts[2]
    return result


expected = rows(sys.argv[1])
actual = rows(sys.argv[2])
if expected != actual:
    labels = sorted(expected.keys() | actual.keys())
    for label in labels:
        if expected.get(label) != actual.get(label):
            print(f"{label}: rust={expected.get(label)!r} lean={actual.get(label)!r}")
    raise SystemExit(1)
print(f"matched {len(expected)} global-allocation lookup observations")
