#!/usr/bin/env python3
"""Audit additional ordinary-Item ABI omission against actual exporter calls."""
import argparse
import re
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument("oracle")
parser.add_argument("candidate")
args = parser.parse_args()
pattern = re.compile(r"^lean_miri_instance_abi_call route=(\S+) queried=(true|false) instance=(.*)$")


def rows(path):
    result = []
    for line in Path(path).read_text().splitlines():
        if not line.startswith("lean_miri_instance_abi_call "):
            continue
        match = pattern.fullmatch(line)
        if not match:
            raise SystemExit("malformed ABI call trace: " + line)
        result.append((match[2] == "true", match[3]))
    if not result:
        raise SystemExit("missing ABI call instrumentation")
    return result


oracle, candidate = rows(args.oracle), rows(args.candidate)
for name in ("mutate", "shared", "capture"):
    identities = {key for queried, key in oracle if queried and f"::{name})" in key}
    if len(identities) != 1:
        raise SystemExit(f"expected one complete {name} oracle key, got {len(identities)}")
    key = next(iter(identities))
    before = sum(queried and identity == key for queried, identity in oracle)
    after = sum(queried and identity == key for queried, identity in candidate)
    raw = sum(not queried and identity == key for queried, identity in candidate)
    if not before or after or not raw:
        raise SystemExit(f"{name} ABI omission failed: before={before}, after={after}, raw={raw}")
    print(f"PASS {name} complete ABI key: explicit calls {before}->0; raw requests {raw}")
