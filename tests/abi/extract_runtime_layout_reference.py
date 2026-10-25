#!/usr/bin/env python3
"""Build a small rustc_abi caller shim with the pinned method bodies verbatim."""

from __future__ import annotations

import hashlib
import pathlib
import sys


ROOT = pathlib.Path(__file__).resolve().parents[2]
LIB = ROOT / "upstream/rustc-source/compiler/rustc_abi/src/lib.rs"
REG = ROOT / "upstream/rustc-source/compiler/rustc_abi/src/callconv/reg.rs"
TEMPLATE = ROOT / "tests/abi/runtime_layout_reference.rs.in"
WRAPPING = ROOT / "upstream/rustc-source/compiler/rustc_abi/src/wrapping_range.rs"

EXPECTED = {
    LIB: "cb17753001ba161ed2bdc0617a9bf679b23cf04982aaee7f73d492782cb7ec94",
    WRAPPING: "32a3be9c253af1e346e10ca76cf1074ec25a9dcda5723b470c6c30a0a12009ba",
    REG: "57c26608b68555d63ec74e4f6bbe2019ecb101406ad054285aa5ec5e25a77688",
}


def read_pinned(path: pathlib.Path, expected: str) -> str:
    data = path.read_bytes()
    actual = hashlib.sha256(data).hexdigest()
    if actual != expected:
        raise SystemExit(f"pinned source hash mismatch for {path.relative_to(ROOT)}: {actual}")
    return data.decode()


def matching_brace(source: str, open_at: int) -> int:
    depth = 0
    i = open_at
    state = "code"
    block_depth = 0
    while i < len(source):
        ch = source[i]
        nxt = source[i + 1] if i + 1 < len(source) else ""
        if state == "line":
            if ch == "\n":
                state = "code"
            i += 1
            continue
        if state == "block":
            if ch == "/" and nxt == "*":
                block_depth += 1
                i += 2
                continue
            if ch == "*" and nxt == "/":
                block_depth -= 1
                i += 2
                if block_depth == 0:
                    state = "code"
                continue
            i += 1
            continue
        if state in ("string", "char"):
            if ch == "\\":
                i += 2
                continue
            if (state == "string" and ch == '"') or (state == "char" and ch == "'"):
                state = "code"
            i += 1
            continue
        if ch == "/" and nxt == "/":
            state = "line"
            i += 2
            continue
        if ch == "/" and nxt == "*":
            state = "block"
            block_depth = 1
            i += 2
            continue
        if ch == '"':
            state = "string"
            i += 1
            continue
        if ch == "'":
            # Lifetimes are not literals. A character literal has a nearby closing quote.
            end = i + 1
            escaped = False
            while end < min(i + 8, len(source)):
                if source[end] == "\\" and not escaped:
                    escaped = True
                    end += 1
                    continue
                if source[end] == "'" and not escaped:
                    break
                if source[end] == "\n":
                    break
                escaped = False
                end += 1
            if end < len(source) and source[end] == "'":
                state = "char"
                i += 1
                continue
        if ch == "{":
            depth += 1
        elif ch == "}":
            depth -= 1
            if depth == 0:
                return i
        i += 1
    raise ValueError("unbalanced source braces")


def block(source: str, marker: str) -> str:
    start = source.index(marker)
    open_at = source.index("{", start)
    return source[start : matching_brace(source, open_at) + 1]


def method(source: str, name: str) -> str:
    marker = f"pub fn {name}"
    try:
        start = source.index(marker)
    except ValueError:
        marker = f"fn {name}"
        start = source.index(marker)
    open_at = source.index("{", start)
    return source[start : matching_brace(source, open_at) + 1]


def main() -> None:
    if len(sys.argv) != 2:
        raise SystemExit("usage: extract_runtime_layout_reference.py OUTPUT.rs")
    lib = read_pinned(LIB, EXPECTED[LIB])
    wrapping = read_pinned(WRAPPING, EXPECTED[WRAPPING])
    reg = read_pinned(REG, EXPECTED[REG])

    selected = [
        block(lib, "impl Default for TargetDataLayout {"),
        block(lib, "impl Integer {"),
        block(lib, "impl IntegerType {"),
        block(lib, "impl Float {"),
        block(lib, "impl Numeric {"),
        block(lib, "impl Primitive {"),
        block(lib, "impl Scalar {"),
        block(lib, "impl BackendLaneCount {"),
        block(lib, "impl NumScalableVectors {"),
        block(lib, "impl BackendRepr {"),
        block(reg, "impl RegKind {"),
        "impl Reg {\n" + method(reg, "align") + "\n}",
    ]
    target_methods = "\n\n".join(
        method(lib, name)
        for name in (
            "pointer_size",
            "pointer_size_in",
            "pointer_offset",
            "pointer_offset_in",
            "pointer_align",
            "pointer_align_in",
            "ptr_sized_integer",
            "ptr_sized_integer_in",
            "c_vector_align",
            "rust_vector_align",
        )
    )
    target_impl = "impl TargetDataLayout {\n" + target_methods + "\n}"
    methods = "\n\n".join([target_impl, *selected])
    output = TEMPLATE.read_text().replace("// SOURCE_METHODS", methods)
    output = output.replace(
        "UPSTREAM_WRAPPING_RANGE_PATH", str(WRAPPING.resolve())
    )
    pathlib.Path(sys.argv[1]).write_text(output)


if __name__ == "__main__":
    main()
