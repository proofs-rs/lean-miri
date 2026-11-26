#!/usr/bin/env python3
"""Fail when a Cargo.lock names crates.io packages that are not in the local cargo cache.

The vendoring tool can download missing archives. Callers that must stay on the
cache use this check first.
"""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from vendor_pinned_crates import missing_cached_crates


def main(argv):
    if len(argv) != 3:
        print("usage: require_cached_crates.py LOCK CARGO_CACHE", file=sys.stderr)
        return 2
    lock_path, cargo_cache = Path(argv[1]), Path(argv[2])
    missing = missing_cached_crates(lock_path, cargo_cache)
    if missing:
        print(
            f"{len(missing)} pinned crates are missing from the cargo cache {cargo_cache}",
            file=sys.stderr)
        print("\n".join(missing[:20]), file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main(sys.argv))
