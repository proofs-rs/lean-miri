"""Strict original shared-reborrow comparison and mutated-reader controls.

The genuine case must terminate successfully in both interpreters. Missing,
mismatched and conflicting covariance evidence is tested only on explicitly
mutated snapshots, never accepted as guest safety evidence.
"""
import argparse
import json
import os
from pathlib import Path
import sys
from types import SimpleNamespace

from check_generated_abi import ROOT, driver, Case

CASE = "pass/reborrow-coerce-shared.rs"


def pairs(document):
    found = set()

    def visit(value):
        if isinstance(value, dict):
            if value.get("kind") == "Reborrow" and value["mutability"]["kind"] == "immutable":
                found.add((value["place"]["type"], value["type"]))
            for child in value.values():
                visit(child)
        elif isinstance(value, list):
            for child in value:
                visit(child)

    visit(document["statement_kinds"])
    assert found and all(source != target for source, target in found)
    return found


def prepare(kind, source, target):
    document = json.loads(Path(source).read_text())
    actual = pairs(document)
    rows = document["compiler_covariance_queries"]
    matching = lambda row: (row["source_type"], row["target_type"]) in actual
    exact = [row for row in rows if matching(row)]
    assert len(exact) == len(actual) and all(row["value"] is False for row in exact)
    if kind == "missing":
        document["compiler_covariance_queries"] = [row for row in rows if not matching(row)]
    elif kind == "mismatched":
        for row in exact:
            row["target_type"] = document["compiler_runtime_primitives"]["unit"]
    elif kind == "conflicting":
        document["compiler_covariance_queries"] += [dict(row, value=True) for row in exact]
    else:
        raise ValueError(kind)
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
    hashes = [driver.sha256(settings.exporter), driver.sha256(settings.runner)]
    record = driver.run_case(Case(CASE), settings, env, args.output)
    assert record["status"] == "passed", record
    assert record["terminal"]["kind"] == "exit" and record["terminal"]["detail"] == "0", record
    assert not record["reference_profile_differences"] and not record["lean_profile_differences"], record
    print("genuine PASS", CASE, flush=True)
    snapshot = Path(record["directory"]) / "input.json"
    negatives = []
    for kind in ["missing", "mismatched", "conflicting"]:
        modified = args.output / (kind + ".json")
        code = driver.invoke([sys.executable, __file__, "--prepare", kind, str(snapshot), str(modified)],
            env, args.output / (kind + "-prepare.log"), settings.timeout, settings.memory_limit)
        assert code == 0, (kind, "preparation", code)
        log = args.output / (kind + ".log")
        code = driver.invoke([str(settings.runner), str(modified), "--ui-source", str(driver.SOURCES / CASE),
            "--ui-flags", "[]"], env, log, settings.timeout, settings.memory_limit)
        assert code == 0, (kind, code)
        terminal = [json.loads(line.removeprefix("upstream_result: "))
                    for line in log.read_text().splitlines() if line.startswith("upstream_result: ")]
        expected = "conflicting compiler covariance query results" if kind == "conflicting" else "missing exact rustc covariance relation query"
        assert len(terminal) == 1 and terminal[0]["kind"] == "unsupported", terminal
        assert expected in terminal[0]["detail"], terminal[0]
        negatives.append({"kind": kind, "terminal": terminal[0]})
        print("negative PASS", kind, flush=True)
    assert hashes == [driver.sha256(settings.exporter), driver.sha256(settings.runner)]
    (args.output / "summary.json").write_text(json.dumps({"genuine": record,
        "negative": negatives, "binary_sha256": hashes}, indent=2))
    print("PASS genuine1 and mutated-reader3; immutable binaries retained", flush=True)


if __name__ == "__main__":
    if len(sys.argv) == 5 and sys.argv[1] == "--prepare":
        prepare(*sys.argv[2:])
    else:
        main()
