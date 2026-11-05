#!/usr/bin/env python3
"""Run the project caller-location fixture through the unchanged UI pass oracle.

Build native_runner and the miri-reference exporter first. This is a separate
project fixture comparison, not an expansion of the pinned upstream inventory.
"""
import argparse
import importlib.util
import json
import os
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
spec = importlib.util.spec_from_file_location("caller_location_ui_driver", ROOT / "tools/check-upstream-ui.py")
driver = importlib.util.module_from_spec(spec)
spec.loader.exec_module(driver)
from suite import Case


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--exporter", type=Path, default=ROOT / "exporter/target/release/lean-miri-mir-exporter")
    parser.add_argument("--runner", type=Path, default=ROOT / ".lake/build/bin/native_runner")
    parser.add_argument("--sysroot", type=Path, default=ROOT / "scratch/miri-sysroot")
    parser.add_argument("--output", type=Path, default=ROOT / "scratch/caller-location-runtime")
    parser.add_argument("--timeout", type=float, default=900)
    args = parser.parse_args()
    for name in ("exporter", "runner", "sysroot", "output"):
        setattr(args, name, getattr(args, name).resolve())
    args.export_timeout, args.memory_limit, args.keep_inputs = 900, None, False
    if not args.exporter.is_file() or not args.runner.is_file():
        parser.error("build the reference exporter and native_runner first")
    args.output.mkdir(parents=True, exist_ok=False)
    toolchain = ROOT / ".rustup/toolchains/miri-exporter-8144389c895d"
    env = os.environ | {"PATH": str(toolchain / "bin") + ":" + os.environ["PATH"],
        "LD_LIBRARY_PATH": str(toolchain / "lib"), "MIRI_SYSROOT": str(args.sysroot),
        "ELAN_HOME": str(ROOT / ".elan"), "LEAN_MIRI_PREPARED_ALLOC_ID_WORLD": "1",
        "LEAN_MIRI_RUN_PREPARED_MIRI": "1", "LEAN_NUM_THREADS": "1"}
    for key in list(env):
        if key.startswith("LEAN_MIRI_REFERENCE_"):
            del env[key]
    env["LEAN_MIRI_REFERENCE_EMPTY_ENV"] = "1"
    # This module is private to this process; only the fixture root differs.
    driver.SOURCES = ROOT
    case = Case("tests/fixtures/caller_location_recipe.rs")
    before = driver.source_fingerprint()
    binaries = {name: driver.sha256(getattr(args, name)) for name in ("exporter", "runner")}
    result = driver.run_case(case, args, env, args.output)
    if driver.source_fingerprint() != before or any(
            driver.sha256(getattr(args, name)) != digest for name, digest in binaries.items()):
        raise RuntimeError("project sources or binaries changed during comparison")
    if driver.sha256(ROOT / case.path) != result["source_sha256"]:
        raise RuntimeError("fixture changed during comparison")
    result.update(project_source_sha256=before, **{name + "_sha256": value for name, value in binaries.items()})
    (args.output / "result.json").write_text(json.dumps(result, indent=2) + "\n")
    print(result["status"])
    if result["status"] != "passed":
        raise SystemExit(1)


if __name__ == "__main__":
    main()
