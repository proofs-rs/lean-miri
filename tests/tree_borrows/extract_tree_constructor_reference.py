#!/usr/bin/env python3
"""Insert the exact pinned `Tree::new` implementation into a standalone shim."""

from __future__ import annotations

import hashlib
import sys
from pathlib import Path


EXPECTED_TREE = "b58a7cfeba92ece2dab1977f65f9070fd8cd71ad"
EXPECTED_RANGE_MAP = "56e9883b1caaf65a3f769cd5c91fbdbb81547f1b"
EXPECTED_TREE_BORROWS_MOD = "bf38ca356df45e5f365c0ae64bfe7738a0d43e1e"


def main() -> None:
    if len(sys.argv) != 6:
        raise SystemExit("usage: extract_tree_constructor_reference.py TREE_RS RANGE_MAP_RS TREE_BORROWS_MOD_RS TEMPLATE_RS OUTPUT_RS")
    source_path, range_map_path, mod_path, template_path, output_path = map(Path, sys.argv[1:])
    contents = source_path.read_bytes()
    header = b"blob " + str(len(contents)).encode("ascii") + b"\0"
    actual = hashlib.sha1(header + contents).hexdigest()
    if actual != EXPECTED_TREE:
        raise ValueError(f"pinned tree.rs blob mismatch: expected {EXPECTED_TREE}, got {actual}")
    range_contents = range_map_path.read_bytes()
    range_header = b"blob " + str(len(range_contents)).encode("ascii") + b"\0"
    actual_range_map = hashlib.sha1(range_header + range_contents).hexdigest()
    if actual_range_map != EXPECTED_RANGE_MAP:
        raise ValueError(
            f"pinned dedup_range_map.rs blob mismatch: expected {EXPECTED_RANGE_MAP}, got {actual_range_map}"
        )
    mod_contents = mod_path.read_bytes()
    mod_header = b"blob " + str(len(mod_contents)).encode("ascii") + b"\0"
    actual_mod = hashlib.sha1(mod_header + mod_contents).hexdigest()
    if actual_mod != EXPECTED_TREE_BORROWS_MOD:
        raise ValueError(
            f"pinned tree_borrows/mod.rs blob mismatch: expected {EXPECTED_TREE_BORROWS_MOD}, got {actual_mod}"
        )
    source = contents.decode("utf-8")
    range_source = range_contents.decode("utf-8")
    mod_source = mod_contents.decode("utf-8")
    start_marker = "impl Tree {\n    /// Create a new tree, with only a root pointer."
    end_marker = "\n}\n\nimpl<'tcx> Tree {"
    start = source.index(start_marker)
    end = source.index(end_marker, start) + len("\n}")
    body = source[start:end].rstrip()
    generated = template_path.read_text(encoding="utf-8")
    new_child_start = "    /// Insert a new tag in the tree."
    sifa_start = "    /// Restores the SIFA \"children are stronger\"/\"parents are weaker\" invariant after a retag:"
    dealloc_start = "    /// Deallocation requires"
    child_begin = source.index(new_child_start)
    child_end = source.index(sifa_start, child_begin)
    sifa_end = source.index(dealloc_start, child_end)
    new_child_and_sifa = "\n\n".join([
        source[child_begin:child_end].rstrip(),
        source[child_end:sifa_end].rstrip(),
    ])
    range_start = range_source.index("use std::ops;")
    range_end = range_source.index("#[cfg(test)]\nmod tests", range_start)
    range_map_body = range_source[range_start:range_end].rstrip()
    new_permission_impl = mod_source.index("impl<'tcx> NewPermission {")
    new_permission_start = mod_source.index("    fn new(\n        pointee: Ty<'tcx>", new_permission_impl)
    new_permission_end = mod_source.index(
        "\n    }\n}\n\n/// Retagging/reborrowing.", new_permission_start
    ) + len("\n    }")
    new_permission_body = mod_source[new_permission_start:new_permission_end].rstrip()
    replacements = {
        "// @PINNED_TREE_NEW_IMPL@": body,
        "// @PINNED_TREE_NEW_CHILD_AND_SIFA@": new_child_and_sifa,
        "// @PINNED_DEDUP_RANGE_MAP_BODY@": range_map_body,
        "// @PINNED_NEW_PERMISSION_NEW@": new_permission_body,
    }
    for marker, replacement in replacements.items():
        if generated.count(marker) != 1:
            raise ValueError(f"Rust shim must contain exactly one marker: {marker}")
        generated = generated.replace(marker, replacement)
    output_path.write_text(generated, encoding="utf-8")
    print("extracted pinned NewPermission::new, Tree constructors, SIFA helper, and DedupRangeMap after Git blob hash checks")


if __name__ == "__main__":
    main()
