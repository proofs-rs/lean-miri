#!/usr/bin/env python3
"""Finite source-pinned null/nonzero backtrace-pointer diagnostic comparisons."""
import argparse
import importlib.util
import json
import os
from pathlib import Path
import re
import sys
from types import SimpleNamespace

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
sys.path.insert(0, str(ROOT / "tests/upstream_ui"))
from suite import discover, category_lean

spec = importlib.util.spec_from_file_location("function_pointer_driver", ROOT / "tools/check-upstream-ui.py")
driver = importlib.util.module_from_spec(spec)
spec.loader.exec_module(driver)


def main():
    parser = argparse.ArgumentParser(__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--exporter", type=Path, default=ROOT / "scratch/lake/exporter-miri-reference/release/lean-miri-mir-exporter")
    parser.add_argument("--runner", type=Path, default=ROOT / ".lake/build/bin/native_runner")
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    toolchain = ROOT / ".rustup/toolchains/miri-exporter-8eb778d04094"
    env = dict(os.environ)
    for key in list(env):
        if key.startswith("LEAN_MIRI_REFERENCE_"):
            del env[key]
    env.update(PATH=str(toolchain / "bin") + ":" + env["PATH"],
        LD_LIBRARY_PATH=str(toolchain / "lib") + ":" + env.get("LD_LIBRARY_PATH", ""),
        LEAN_MIRI_PREPARED_ALLOC_ID_WORLD="1", LEAN_MIRI_RUN_PREPARED_MIRI="1")
    settings = SimpleNamespace(exporter=args.exporter.resolve(),
        runner=args.runner.resolve(), sysroot=ROOT / "scratch/lake/miri-sysroot",
        export_timeout=180, timeout=180, memory_limit=12 * 1024**3, keep_inputs=True)
    hashes = [driver.sha256(settings.exporter), driver.sha256(settings.runner)]
    records = []
    for sources, path, address, category in [
        (ROOT / "tests/upstream_ui/fixtures/function_pointers", "fail/null-backtrace-pointer.rs", 0, "null_pointer"),
        (ROOT / "tests/upstream_ui/fixtures/function_pointers", "fail/nonzero-backtrace-pointer.rs", 1, "no_provenance"),
        (ROOT / "tests/upstream_ui/fixtures/function_pointers", "pass/backtrace-pointer.rs", None, None),
    ]:
        driver.SOURCES = sources
        case = next(case for case in discover(sources) if case.path == path)
        assert not case.reasons, case.reasons
        record = driver.run_case(case, settings, env, args.output)
        assert record["status"] == "passed", record
        assert record["category"] == category, record
        assert record["terminal"]["kind"] == ("ub" if case.fail else "exit"), record
        assert not record["reference_profile_differences"] and not record["lean_profile_differences"], record
        detail = record["terminal"]["detail"]
        if address is not None:
            assert re.search(r"danglingIntegerPointer " + str(address) + r" 0 .*dereferenceable", detail), detail
        else:
            assert detail == "0", detail
        if address:
            assert not category_lean(detail, "null_pointer"), detail
        records.append(record)
        print("strict backtrace diagnostic PASS", path, address, flush=True)
    assert not category_lean("DanglingIntPointer", "null_pointer")
    assert hashes == [driver.sha256(settings.exporter), driver.sha256(settings.runner)]
    (args.output / "summary.json").write_text(json.dumps({"cases": records, "binary_sha256": hashes}, indent=2))


if __name__ == "__main__":
    main()
