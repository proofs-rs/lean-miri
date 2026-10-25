#!/usr/bin/env python3
"""Run pinned upstream programs as reference observations for future MIR comparison.

This does not execute Lean or establish UB freedom. A seed fixes an observation,
not the set of behaviors quantified over by the verification semantics.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[2]


def classify(code, stderr):
    if code == 0:
        return "returned"
    if "error: Undefined Behavior:" in stderr:
        return "undefined_behavior"
    if "error: unsupported operation:" in stderr:
        return "unsupported"
    if re.search(r"^thread 'main'(?: \(\d+\))? panicked at", stderr, re.MULTILINE):
        return "panic"
    return "other_stop"


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, default=ROOT / "scratch/reference-programs.json")
    args = parser.parse_args()
    cases = json.loads((ROOT / "tests/reference_programs/cases.json").read_text())
    lock = json.loads((ROOT / "upstream/source-lock.json").read_text())
    sysroot = ROOT / "scratch/miri-sysroot"
    toolchain = ROOT / ".rustup/toolchains/miri-exporter-8144389c895d"
    env = dict(os.environ)
    env["LD_LIBRARY_PATH"] = str(toolchain / "lib") + (":" + env["LD_LIBRARY_PATH"] if env.get("LD_LIBRARY_PATH") else "")
    env["MIRI_SYSROOT"] = str(sysroot)
    binary = ROOT / "upstream/miri-source/target/debug/miri"
    build = json.loads((ROOT / "scratch/miri-reference-build.json").read_text())
    if hashlib.sha256(binary.read_bytes()).hexdigest() != build["binary_sha256"]:
        raise SystemExit("reference Miri binary changed since recorded build; rerun setup-miri-reference.sh")
    version = subprocess.run([str(binary), "--version"], env=env, capture_output=True, text=True, check=True).stdout.strip()
    records = []
    failures = []
    for case in cases["cases"]:
        source = ROOT / case["source"]
        if hashlib.sha256(source.read_bytes()).hexdigest() != case["sha256"]:
            raise SystemExit(f"pinned reference fixture hash mismatch: {source}")
        command = [str(binary), "--sysroot", str(sysroot), "--edition=2021",
                   "-Zmiri-tree-borrows", "-Zmiri-seed=0", *case["flags"], str(source)]
        try:
            result = subprocess.run(command, cwd=ROOT, env=env, text=True, capture_output=True, timeout=60)
            outcome = classify(result.returncode, result.stderr)
            records.append(dict(case, outcome=outcome, returncode=result.returncode,
                                stdout=result.stdout, stderr=result.stderr, command=command))
        except subprocess.TimeoutExpired:
            outcome = "timeout"
            records.append(dict(case, outcome=outcome, command=command))
        print(f"{case['id']}: {outcome}", flush=True)
        if outcome != case["expected"]:
            failures.append(f"{case['id']}: expected {case['expected']}, got {outcome}")
    artifact = dict(schema_version=1, checked_utc=datetime.now(timezone.utc).isoformat(),
                    pins=lock["pins"], reference_version=version, semantics=cases["semantics"],
                    reference_build=build, cases=records,
                    lean_comparison=False, ub_freedom_proof=False)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(artifact, indent=2) + "\n")
    if failures:
        raise SystemExit("\n".join(failures))


if __name__ == "__main__":
    main()
