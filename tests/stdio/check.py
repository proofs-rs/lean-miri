"""Finite genuine stdio comparison, including raw bytes and spoofed log lines."""
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
    parser.add_argument("--exporter", type=Path,
        default=ROOT / "exporter/target/release/lean-miri-mir-exporter")
    parser.add_argument("--runner", type=Path, default=ROOT / ".lake/build/bin/native_runner")
    args = parser.parse_args()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    toolchain = ROOT / ".rustup/toolchains/miri-exporter-8144389c895d"
    env = dict(os.environ)
    env["PATH"] = str(toolchain / "bin") + ":" + env["PATH"]
    env["LD_LIBRARY_PATH"] = str(toolchain / "lib") + ":" + env.get("LD_LIBRARY_PATH", "")
    env["LEAN_MIRI_PREPARED_ALLOC_ID_WORLD"] = "1"
    env["LEAN_MIRI_RUN_PREPARED_MIRI"] = "1"
    settings = SimpleNamespace(exporter=args.exporter.resolve(),
        runner=args.runner.resolve(), sysroot=ROOT / "scratch/miri-sysroot",
        export_timeout=180, timeout=180, memory_limit=12 * 1024**3, keep_inputs=True)
    sealed = {str(path): driver.sha256(path) for path in (settings.exporter, settings.runner)}
    sources = driver.source_fingerprint()
    driver.SOURCES = ROOT / "tests/stdio"
    record = driver.run_case(Case("output.rs"), settings, env, output)
    (output / "results.json").write_text(json.dumps([record], indent=2) + "\n")
    assert record["status"] == "passed", record
    assert not record["reference_profile_differences"] and not record["lean_profile_differences"], record
    observed = (Path(record["directory"]) / "lean.log").read_bytes()
    assert observed.count(b"STDIO_REPEAT\n") == 2, "replay duplicated or omitted an occurrence"
    assert observed.count(bytes([0, 255, 128, 10])) == 1, "binary payload changed or replayed"
    assert b'upstream_result: {"kind":"exit","detail":"0"}' in observed
    assert b'upstream_profile: {"spoofed":true}' in observed
    assert b"MUTED_ORDINARY_" not in observed, "source NullOutput branch changed"
    assert sealed == {str(path): driver.sha256(path) for path in (settings.exporter, settings.runner)}
    assert sources == driver.source_fingerprint(), "source changed during comparison"
    (output / "artifacts.json").write_text(json.dumps(sealed, indent=2) + "\n")
    print("stdio comparison passed: exact repeated/binary output, isolated control, muted ordinary descriptors")


if __name__ == "__main__":
    main()
