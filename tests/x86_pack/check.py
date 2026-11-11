"""Fresh finite comparisons for signed/unsigned x86 pack saturation and lane order.

Requires this checkout's built native_runner and reference-feature exporter.
This checks the actual dispatcher and memory operations, not a copied pack model.
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
from suite import Case


def main():
    parser = argparse.ArgumentParser(__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    toolchain = ROOT / ".rustup/toolchains/miri-exporter-8144389c895d"
    env = dict(os.environ)
    env["PATH"] = str(toolchain / "bin") + ":" + env["PATH"]
    env["LD_LIBRARY_PATH"] = str(toolchain / "lib") + ":" + env.get("LD_LIBRARY_PATH", "")
    env["LEAN_MIRI_PREPARED_ALLOC_ID_WORLD"] = "1"
    env["LEAN_MIRI_RUN_PREPARED_MIRI"] = "1"
    settings = SimpleNamespace(exporter=ROOT / "exporter/target/release/lean-miri-mir-exporter",
        runner=ROOT / ".lake/build/bin/native_runner", sysroot=ROOT / "scratch/miri-sysroot",
        export_timeout=180, timeout=180, memory_limit=12 * 1024**3, keep_inputs=True)
    sealed = {str(path): driver.sha256(path) for path in (settings.exporter, settings.runner)}
    driver.SOURCES = ROOT / "tests/x86_pack"
    records = []
    for fixture in ("unsigned_upper.rs", "signed_control.rs", "boundaries.rs"):
        case = Case(fixture, flags=["-C", "target-feature=+sse4.1,+avx2,+avx512f,+avx512bw"])
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
    print("Pack comparisons passed: signed controls, unsigned saturation boundaries, 128-bit chunk order")


if __name__ == "__main__":
    main()
