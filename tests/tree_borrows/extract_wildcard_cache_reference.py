#!/usr/bin/env python3
"""Extract exact exposed-cache helpers after checking their pinned source blobs."""

from __future__ import annotations

import hashlib
import sys
from pathlib import Path


EXPECTED = {
    "wildcard": "a3f7d6176555d193163f909fbd48b08118294f8b",
    "tree": "b58a7cfeba92ece2dab1977f65f9070fd8cd71ad",
    "unimap": "6400a62f444f0a3ec481747e05fa90f2fb1cd40c",
}


def git_blob_sha1(contents: bytes) -> str:
    header = b"blob " + str(len(contents)).encode("ascii") + b"\0"
    return hashlib.sha1(header + contents).hexdigest()


def checked(path: Path, name: str) -> str:
    contents = path.read_bytes()
    actual = git_blob_sha1(contents)
    if actual != EXPECTED[name]:
        raise ValueError(f"pinned {name} source mismatch: expected {EXPECTED[name]}, got {actual}")
    return contents.decode("utf-8")


def main() -> None:
    if len(sys.argv) != 6:
        raise SystemExit(
            "usage: extract_wildcard_cache_reference.py WILDCARD_RS TREE_RS UNIMAP_RS TEMPLATE_RS OUTPUT_RS"
        )
    wildcard_path, tree_path, unimap_path, template_path, output_path = map(Path, sys.argv[1:])
    wildcard = checked(wildcard_path, "wildcard")
    checked(tree_path, "tree")
    checked(unimap_path, "unimap")

    def block(start_marker: str, end_marker: str) -> str:
        start = wildcard.index(start_marker)
        end = wildcard.index(end_marker, start)
        return wildcard[start:end].rstrip()

    replacements = {
        "// @PINNED_WILDCARD_LEVEL_AND_RELATEDNESS@": "\n\n".join([
            block("/// Represents the maximum access level", "/// Where the access happened relative to the current node."),
            block("/// Where the access happened relative to the current node.", "/// Caches information about where in the tree"),
        ]),
        "// @PINNED_EXPOSED_CACHE_TYPES@": block(
            "/// Caches information about where in the tree",
            "impl ExposedCache {",
        ),
        "// @PINNED_ACCESS_RELATEDNESS_BODY@": block(
            "    pub fn access_relatedness(",
            "    pub fn update_exposure(",
        ),
        "// @PINNED_UPDATE_EXPOSURE_BODY@": block(
            "    pub fn update_exposure(",
            "    /// Removes a node from the datastructure.",
        ),
    }
    generated = template_path.read_text(encoding="utf-8")
    for marker, body in replacements.items():
        if generated.count(marker) != 1:
            raise ValueError(f"Rust shim must contain exactly one marker: {marker}")
        generated = generated.replace(marker, body)
    output_path.write_text(generated, encoding="utf-8")
    print("extracted pinned WildcardAccessLevel, ExposedCache, and helper bodies after Git blob hash checks")


if __name__ == "__main__":
    main()
