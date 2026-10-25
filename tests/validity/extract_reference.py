#!/usr/bin/env python3
"""Hash-check pinned validity code and insert exact source functions in the shim."""

import hashlib
import json
from pathlib import Path
import sys

root = Path(__file__).resolve().parents[2]
lock = json.loads((root / "upstream/source-lock.json").read_text())


def checked_source(relative: str) -> str:
    expected = next(entry["sha256"] for entry in lock["files"] if entry["path"] == relative)
    data = (root / relative).read_bytes()
    actual = hashlib.sha256(data).hexdigest()
    if actual != expected:
        raise SystemExit(f"{relative} source hash mismatch: expected {expected}, got {actual}")
    return data.decode("utf-8")


relative = "upstream/rustc-source/compiler/rustc_const_eval/src/interpret/validity.rs"
source = checked_source(relative)


def extract_method(start_marker: str) -> str:
    start = source.index(start_marker)
    opening = source.index("{", start)
    depth = 0
    state = "normal"
    escaped = False
    index = opening
    while index < len(source):
        char = source[index]
        following = source[index + 1] if index + 1 < len(source) else ""
        if state == "normal":
            if char == '"':
                state = "string"
            elif char == "'":
                # Lifetimes occur in signatures, before the opening brace. The
                # extracted bodies here contain no character literals.
                state = "char"
            elif char == "/" and following == "/":
                state = "line"
                index += 1
            elif char == "/" and following == "*":
                state = "block"
                index += 1
            elif char == "{":
                depth += 1
            elif char == "}":
                depth -= 1
                if depth == 0:
                    return source[start : index + 1]
        elif state == "string":
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                state = "normal"
        elif state == "char":
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == "'":
                state = "normal"
        elif state == "line":
            if char == "\n":
                state = "normal"
        elif state == "block":
            if char == "*" and following == "/":
                state = "normal"
                index += 1
        index += 1
    raise SystemExit(f"unterminated source method {start_marker!r}")


ref_tracking_empty = extract_method("    pub fn empty() -> Self {")
ref_tracking_next = extract_method("    pub fn next(&mut self) -> Option<(T, PATH)> {")
ref_tracking_track = extract_method("    fn track(&mut self, val: T, path: impl FnOnce() -> PATH) {")
new_impl = source.index("impl<'tcx, T: Clone + Eq + Hash + std::fmt::Debug> RefTracking<T, Path<'tcx>>")
new_marker = "    pub fn new(val: T, ty: Ty<'tcx>) -> Self {"
if source.index(new_marker) < new_impl:
    raise SystemExit("extracted RefTracking::new from an unexpected impl")
ref_tracking_new = extract_method(new_marker)
fmt_start = source.index("fn fmt_range(r: WrappingRange, max_hi: u128) -> String {")
fmt_end = source.index("\n}\n\n/// We want to show a nice path", fmt_start) + 2
fmt_range = source[fmt_start:fmt_end]
write_path = extract_method("fn write_path(out: &mut String, path: &[PathElem<'_>]) {")

method_start = source.index("    fn visit_scalar(\n")
method_end = source.index("\n    fn in_mutable_memory", method_start)
method = source[method_start:method_end]
body_start = method.index("{\n") + 2
body_end = method.rfind("\n    }")
if body_end < body_start or "fn visit_scalar" not in method:
    raise SystemExit("could not isolate the source visit_scalar body")
visit_body = method[body_start:body_end]

template = (root / "tests/validity/reference.rs.in").read_text()
for marker, replacement in [
    ("// @FMT_RANGE_SOURCE@", fmt_range),
    ("// @WRITE_PATH_SOURCE@", write_path),
    ("        // @VISIT_SCALAR_BODY@", visit_body),
    ("    // @REF_TRACKING_EMPTY@", ref_tracking_empty),
    ("    // @REF_TRACKING_NEXT@", ref_tracking_next),
    ("    // @REF_TRACKING_TRACK@", ref_tracking_track),
    ("    // @REF_TRACKING_NEW@", ref_tracking_new),
]:
    if template.count(marker) != 1:
        raise SystemExit(f"expected one extraction marker {marker!r}")
    template = template.replace(marker, replacement)

Path(sys.argv[1]).write_text(template)
print(f"verified and extracted pinned validity source ({hashlib.sha256((root / relative).read_bytes()).hexdigest()})")
