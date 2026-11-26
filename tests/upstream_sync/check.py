"""Fresh finite controls for the November Miri synchronization/ABI changes.

Requires this checkout's built native_runner and reference-feature exporter.
These Linux controls execute actual pthread and compiler ABI queries.
"""
import argparse
import importlib.util
import json
import os
from pathlib import Path
from types import SimpleNamespace
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tools"))
spec = importlib.util.spec_from_file_location("ui_driver", ROOT / "tools/check-upstream-ui.py")
driver = importlib.util.module_from_spec(spec)
spec.loader.exec_module(driver)
from suite import discover


def main():
    parser = argparse.ArgumentParser(__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--exporter", type=Path, default=ROOT / "scratch/lake/exporter-miri-reference/release/lean-miri-mir-exporter")
    parser.add_argument("--runner", type=Path, default=ROOT / ".lake/build/bin/native_runner")
    args = parser.parse_args()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    toolchain = ROOT / ".rustup/toolchains/miri-exporter-8eb778d04094"
    env = dict(os.environ)
    env["PATH"] = str(toolchain / "bin") + ":" + env["PATH"]
    env["LD_LIBRARY_PATH"] = str(toolchain / "lib") + ":" + env.get("LD_LIBRARY_PATH", "")
    env["LEAN_MIRI_PREPARED_ALLOC_ID_WORLD"] = "1"
    env["LEAN_MIRI_RUN_PREPARED_MIRI"] = "1"
    settings = SimpleNamespace(exporter=args.exporter.resolve(),
        runner=args.runner.resolve(), sysroot=ROOT / "scratch/lake/miri-sysroot",
        export_timeout=180, timeout=180, memory_limit=12 * 1024**3, keep_inputs=True)
    sealed = {str(path): driver.sha256(path) for path in (settings.exporter, settings.runner)}
    driver.SOURCES = ROOT / "tests/upstream_sync"
    records = []
    for case in discover(driver.SOURCES):
        fixture = case.id
        assert not case.reasons, case.reasons
        record = driver.run_case(case, settings, env, output)
        records.append(record)
        (output / "results.json").write_text(json.dumps(records, indent=2) + "\n")
        if record["status"] != "passed":
            raise AssertionError(json.dumps({"fixture": fixture, "status": record["status"],
                "terminal": record.get("terminal"), "directory": record["directory"]}, indent=2))
        assert not record["reference_profile_differences"], record
        assert not record["lean_profile_differences"], record
        print("passed:", fixture, flush=True)
    assert sealed == {str(path): driver.sha256(path) for path in (settings.exporter, settings.runner)}
    (output / "artifacts.json").write_text(json.dumps(sealed, indent=2) + "\n")
    print("Upstream synchronization and CFI controls passed")


if __name__ == "__main__":
    main()
