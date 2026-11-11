"""Finite genuine startup/weak-symbol controls and explicit metadata negatives.

Run with a schema-compatible immutable native runner and a reference-feature
exporter. Mutated inputs below are reader negatives, not genuine comparisons.
"""
import argparse
import importlib.util
import json
import os
from pathlib import Path
import sys
from types import SimpleNamespace

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tools"))
spec = importlib.util.spec_from_file_location("ui_driver", ROOT / "tools/check-upstream-ui.py")
driver = importlib.util.module_from_spec(spec)
spec.loader.exec_module(driver)
from suite import Case


def prepare_negative(kind, source, target):
    # A separate preparation process releases the large decoded compiler graph
    # before starting the native reader. Never hold two copies beside a guest.
    document = json.loads(Path(source).read_text())
    if kind in ("missing-start", "mismatched-start-type"):
        main = next(row for row in document["compiler_main_queries"]["entries"]
                    if row["signature_query"]["compiler_selected_entry"])
        pointer = main["signature_query"]["function_pointer_type"]
        output = document["compiler_runtime_primitives"]["isize"]
        exact = lambda row: row["signature"]["inputs"][:1] == [pointer] and row["signature"]["output"] == output
        rows = document["compiler_function_facts"]["helper_signatures"]
        assert any(exact(row) for row in rows)
        if kind == "missing-start":
            document["compiler_function_facts"]["helper_signatures"] = [row for row in rows if not exact(row)]
        else:
            for row in rows:
                if exact(row):
                    row["signature"]["inputs"][0] = document["compiler_runtime_primitives"]["unit"]
    else:
        symbol = kind.removeprefix("missing-")
        rows = document["compiler_named_shim_abis"]
        assert any(row["name"] == symbol for row in rows)
        document["compiler_named_shim_abis"] = [row for row in rows if row["name"] != symbol]
    with Path(target).open("w") as stream:
        json.dump(document, stream, separators=(",", ":"))


def main():
    parser = argparse.ArgumentParser(__doc__)
    parser.add_argument("--runner", type=Path, required=True)
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
        runner=args.runner.resolve(), sysroot=ROOT / "scratch/miri-sysroot",
        export_timeout=180, timeout=180, memory_limit=12 * 1024**3, keep_inputs=True)
    binary_hashes = [driver.sha256(settings.exporter), driver.sha256(settings.runner)]
    driver.SOURCES = ROOT / "exporter/fixtures/fail_closed"
    records = {}
    for path in ["start_result.rs", "runtime_getrandom.rs", "runtime_cxa.rs"]:
        record = driver.run_case(Case(path), settings, env, args.output)
        records[path] = record
        assert record["status"] == "passed", record
        assert record["terminal"]["kind"] == "exit" and record["terminal"]["detail"] == "0", record
        assert not record["reference_profile_differences"] and not record["lean_profile_differences"], record
        print("genuine PASS", path, flush=True)

    negatives = []

    def reject(name, path, expected):
        snapshot = args.output / (name + ".json")
        source = Path(records[path]["directory"]) / "input.json"
        preparation = driver.invoke([sys.executable, __file__, "--prepare-negative", name, str(source), str(snapshot)],
            env, args.output / (name + "-prepare.log"), settings.timeout, settings.memory_limit)
        assert preparation == 0, (name, "preparation", preparation)
        log = args.output / (name + ".log")
        command = [str(settings.runner), str(snapshot), "--ui-source", str(driver.SOURCES / path),
                   "--ui-flags", "[]"]
        code = driver.invoke(command, env, log, settings.timeout, settings.memory_limit)
        assert code == 0, (name, code, log)
        terminal = [json.loads(line.removeprefix("upstream_result: "))
                    for line in log.read_text().splitlines() if line.startswith("upstream_result: ")]
        assert len(terminal) == 1, (name, log)
        assert terminal[0]["kind"] in ("unsupported", "failed"), terminal[0]
        assert expected in terminal[0]["detail"], terminal[0]
        negatives.append({"name": name, "terminal": terminal[0]})
        print("negative PASS", name, flush=True)

    reject("missing-start", "start_result.rs", "missing exact compiler dummy-signature ABI query")
    reject("mismatched-start-type", "start_result.rs", "missing exact compiler dummy-signature ABI query")
    for path, symbol in [("runtime_getrandom.rs", "getrandom"), ("runtime_cxa.rs", "__cxa_thread_atexit_impl")]:
        reject("missing-" + symbol, path, "missing exact named compiler shim ABI query " + symbol)
    assert binary_hashes == [driver.sha256(settings.exporter), driver.sha256(settings.runner)]
    (args.output / "summary.json").write_text(json.dumps({"genuine": records, "negative": negatives,
        "binary_sha256": binary_hashes}, indent=2))
    print("PASS genuine3 and mutated-reader4; immutable binaries retained", flush=True)


if __name__ == "__main__":
    if len(sys.argv) == 5 and sys.argv[1] == "--prepare-negative":
        prepare_negative(*sys.argv[2:])
    else:
        main()
