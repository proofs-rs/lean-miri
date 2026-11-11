"""Exact LLVM no-ABI dispatch controls; Unsupported never counts as guest safety.
Run after building this checkout's reference-feature exporter and native_runner.
"""
import argparse
import importlib.util
import json
import os
import sys
from pathlib import Path
from types import SimpleNamespace

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tools"))
spec = importlib.util.spec_from_file_location("ui_driver", ROOT / "tools/check-upstream-ui.py")
driver = importlib.util.module_from_spec(spec)
spec.loader.exec_module(driver)
from suite import Case, SOURCES


def main():
    parser = argparse.ArgumentParser(__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    toolchain = ROOT / ".rustup/toolchains/miri-exporter-8144389c895d"
    env = dict(os.environ)
    env["PATH"] = str(toolchain / "bin") + ":" + env["PATH"]
    env["LD_LIBRARY_PATH"] = str(toolchain / "lib") + ":" + env.get("LD_LIBRARY_PATH", "")
    env["LEAN_MIRI_PREPARED_ALLOC_ID_WORLD"] = "1"
    env["LEAN_MIRI_RUN_PREPARED_MIRI"] = "1"
    settings = SimpleNamespace(exporter=ROOT / "exporter/target/release/lean-miri-mir-exporter",
        runner=ROOT / ".lake/build/bin/native_runner", sysroot=ROOT / "scratch/miri-sysroot",
        export_timeout=180, timeout=180, memory_limit=12 * 1024**3, keep_inputs=True)
    binary_hashes = [driver.sha256(settings.exporter), driver.sha256(settings.runner)]
    driver.SOURCES = ROOT / "tests/llvm_no_abi"
    records = []
    errors = []
    for path, kind, detail in [
        ("pass/pause-arithmetic.rs", "exit", ""),
        ("fail/argument-count.rs", "ub", "incorrect number of arguments"),
        ("unsupported/unknown.rs", "unsupported", "lean_miri_unknown"),
        ("invalid/layout.rs", "failed", "project_to_simd requires SIMD type"),
        ("clash/exported-symbol.rs", "failed", "symbol shim clashing"),
    ]:
        case = Case(path)
        record = driver.run_case(case, settings, env, args.output)
        records.append(record)
        try:
            terminal = record.get("terminal", {})
            assert terminal.get("kind") == kind, record
            assert detail in terminal.get("detail", ""), record
            assert not record.get("reference_profile_differences"), record
            assert not record.get("lean_profile_differences"), record
            if kind == "exit":
                assert record["status"] == "passed", record
            elif kind == "ub":
                outcome = record["reference"]["reference"]["outcome"]
                assert outcome.get("kind") == "miri_evaluation_error", record
                reference_log = (Path(record["directory"]) / "export.log").read_text()
                assert "Undefined Behavior: incorrect number of arguments for `llvm.x86.sse2.pause`: got 1, expected 0" in reference_log, record
                assert "argument-count.rs:6:" in reference_log, record
                assert any(frame.get("line") == 6 and frame.get("file", "").endswith(path)
                           for frame in terminal.get("frames", [])), record
            else:
                assert record["status"] != "passed", record
                reference_log = (Path(record["directory"]) / "export.log").read_text()
                if kind == "unsupported":
                    assert "llvm.x86.lean_miri_unknown" in reference_log, record
                elif path.startswith("clash/"):
                    assert "shim" in reference_log and "llvm.x86.sse2.pause" in reference_log, record
                else:
                    # An invalid LLVM signature hits the pinned Miri assertion;
                    # the Lean model must reject it, never fabricate a layout.
                    assert record["reference"]["reference"]["outcome"]["kind"] == "miri_panicked", record
        except (AssertionError, KeyError):
            errors.append({"case": path, "status": record.get("status"),
                           "terminal": {key: record.get("terminal", {}).get(key) for key in ("kind", "detail")}})
    # Preserve the upstream missing-feature source and its original directive/oracle.
    driver.SOURCES = SOURCES
    case = next(c for c in driver.discover() if c.id == "fail/intrinsics/intrinsic_target_feature.rs")
    record = driver.run_case(case, settings, env, args.output)
    records.append(record)
    if record["status"] != "passed":
        errors.append({"case": case.id, "status": record["status"],
                       "terminal": {key: record.get("terminal", {}).get(key) for key in ("kind", "detail")}})
    assert binary_hashes == [driver.sha256(settings.exporter), driver.sha256(settings.runner)]
    (args.output / "results.json").write_text(json.dumps(records, indent=2) + "\n")
    if errors:
        raise AssertionError(json.dumps(errors, indent=2))
    print("LLVM controls passed: positive execution, argument-count UB, target-feature UB, layout rejection, unknown Unsupported")


if __name__ == "__main__":
    main()
