#!/usr/bin/env python3
"""Extract the unchanged pinned binary_int_op body; use real rustc ScalarInt."""
import hashlib
import json
from pathlib import Path
import sys

root = Path(__file__).resolve().parents[2]
relative = "upstream/rustc-source/compiler/rustc_const_eval/src/interpret/operator.rs"
lock = json.loads((root / "upstream/source-lock.json").read_text())
expected = next(row["sha256"] for row in lock["files"] if row["path"] == relative)
data = (root / relative).read_bytes()
if hashlib.sha256(data).hexdigest() != expected:
    raise SystemExit("pinned operator source hash mismatch")
source = data.decode()
start = source.index("    fn binary_int_op(")
body_start = source.index("{", start)
end = source.index("\n    /// Computes the total size", body_start)
# Only the signature's compiler-context lifetime/type parameters are replaced.
# The complete method body is retained, including every UB and assertion branch.
body = source[body_start:end].rstrip()
template = (root / "tests/integer_ops/reference.rs.in").read_text()
template = template.replace("@BINARY_INT_OP_BODY@", body)
for name, next_name in [("binary_char_op", "binary_bool_op"), ("binary_bool_op", "binary_float_op")]:
    start = source.index(f"    fn {name}(")
    opening = source.index("{", start)
    finish = source.index(f"    fn {next_name}", opening)
    template = template.replace(f"@{name.upper()}_BODY@", source[opening:finish].rstrip())
Path(sys.argv[1]).write_text(template)
