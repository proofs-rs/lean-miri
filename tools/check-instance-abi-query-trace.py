#!/usr/bin/env python3
"""Explicit exporter ABI-call control; rustc-internal query execution is outside this trace."""
import argparse
from collections import Counter
from pathlib import Path
import re

parser = argparse.ArgumentParser()
parser.add_argument("oracle")
parser.add_argument("candidate")
parser.add_argument("--keys", type=int, default=10)
parser.add_argument("--unsupported-name", default="unused")
args = parser.parse_args()
pattern = re.compile(r"^lean_miri_instance_abi_call route=(\S+) queried=(true|false) instance=(.*)$")


def load(path):
    rows = []
    for line in Path(path).read_text().splitlines():
        if line.startswith("lean_miri_instance_abi_call "):
            match = pattern.fullmatch(line)
            if not match:
                raise SystemExit("malformed ABI trace: " + line)
            rows.append((match[1], match[2] == "true", match[3]))
    if not rows:
        raise SystemExit("missing exporter ABI-call instrumentation")
    return rows


oracle = load(args.oracle)
candidate = load(args.candidate)
identities = {identity for _, queried, identity in oracle if queried and "::identity)" in identity}
if len(identities) != args.keys:
    raise SystemExit(f"expected {args.keys} independent generic ABI oracle keys, got {len(identities)}")
for identity in sorted(identities):
    old = sum(queried and key == identity for _, queried, key in oracle)
    new = sum(queried and key == identity for _, queried, key in candidate)
    raw = sum(not queried and key == identity for _, queried, key in candidate)
    if not old or new or not raw:
        raise SystemExit(f"ABI query elimination failed: before={old}, after={new}, raw={raw}: {identity}")
    print(f"PASS complete identity ABI key: explicit calls {old}->0; raw requests {raw}: {identity}")
if not any(queried and f"::{args.unsupported_name})" in identity for _, queried, identity in candidate):
    raise SystemExit("missing unsupported residual ABI control")
if any(not queried and f"::{args.unsupported_name})" in identity for _, queried, identity in candidate):
    raise SystemExit("unsupported signature escaped the raw ABI capability boundary")
print(f"PASS unsupported {args.unsupported_name} signature keeps its explicit ABI query")
for label, rows in [("oracle", oracle), ("candidate", candidate)]:
    print(label, dict(Counter((route, queried) for route, queried, _ in rows)))
