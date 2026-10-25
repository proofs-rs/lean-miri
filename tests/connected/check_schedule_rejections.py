#!/usr/bin/env python3
"""Fail-closed review checks against the first retained successful replay."""
import sys
import hashlib
import json
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(sys.argv[3]).resolve()
HERE.mkdir(parents=True, exist_ok=False)
SNAPSHOT = Path(sys.argv[1]).resolve()
SOURCE_LOG = Path(sys.argv[2]).resolve()
VALIDATOR = ROOT / "tests/connected/validate_schedule.py"

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def invalid_index(text):
    marker = "choice_events=#["
    tail = text.split(marker, 1)[1]
    for match in re.finditer(r"\{ request := (.*?)\},", tail, re.S):
        chunk = match.group(1)
        req = re.search(r"Request\.index\s*\(.*?\)\s*(\d+)", chunk, re.S)
        val = re.search(r"Input\.index\s*\(.*?\)\s*(\d+)", chunk, re.S)
        if req and val:
            support = int(req.group(1))
            altered = chunk[:val.start(1)] + str(support) + chunk[val.end(1):]
            return text[:text.index(marker) + len(marker) + match.start(1)] + altered + text[text.index(marker) + len(marker) + match.end(1):]
    raise ValueError("cannot locate an index request/input event")

original = SOURCE_LOG.read_text()
variants = {
    "truncate-terminal": original.rsplit("sc_ordering_control_fixture=PASS", 1)[0],
    "invalid-index": invalid_index(original),
    "missing-step-end": re.sub(r"^sc264_core_step_end choice_cursor=\d+\n", "", original, count=1, flags=re.M),
}
records = []
for name, text in variants.items():
    log = HERE / f"{name}.log"
    report = HERE / f"{name}.json"
    stdout = HERE / f"{name}.stdout"
    stderr = HERE / f"{name}.stderr"
    log.write_text(text)
    cmd = ["python3", str(VALIDATOR), str(SNAPSHOT), str(log), str(report)]
    completed = subprocess.run(cmd, cwd=ROOT, capture_output=True, text=True)
    stdout.write_text(completed.stdout)
    stderr.write_text(completed.stderr)
    records.append({
        "case": name,
        "command": cmd,
        "exit_code": completed.returncode,
        "expected_rejection": completed.returncode != 0,
        "source_log_sha256": sha(SOURCE_LOG),
        "variant_log": str(log),
        "variant_log_sha256": sha(log),
        "validator_sha256": sha(VALIDATOR),
        "snapshot_sha256": sha(SNAPSHOT),
        "stdout": completed.stdout,
        "stderr": completed.stderr,
    })

result = {
    "schema": "sc-practical-validator-negative-review-v1",
    "source_log": str(SOURCE_LOG),
    "source_log_sha256": sha(SOURCE_LOG),
    "validator": str(VALIDATOR),
    "validator_sha256": sha(VALIDATOR),
    "snapshot_sha256": sha(SNAPSHOT),
    "cases": records,
    "all_rejected": all(row["expected_rejection"] for row in records),
}
(HERE / "results.json").write_text(json.dumps(result, indent=2) + "\n")
print(json.dumps({"all_rejected": result["all_rejected"],
                  "cases": [{"case": row["case"], "exit_code": row["exit_code"]} for row in records]}))
if not result['all_rejected']:
    raise SystemExit('validator accepted a deliberately invalid log')
