"""Finite source ABI oracles and separate same-TyCtxt execution comparisons.

Oracle queries can perturb rustc's allocation history. The diagnostic export
therefore has no prepared allocation world; execution uses a separate export.
Their Rust flags and ID-independent declaration inventories must agree;
this is not a proof that the two translated graphs are equivalent.
"""
import argparse
from collections import Counter
import importlib.util
import json
import os
import re
from pathlib import Path
import subprocess
import sys
from types import SimpleNamespace

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tests/upstream_ui"))
sys.path.insert(0, str(ROOT / "tools"))
from suite import Case

SPEC = importlib.util.spec_from_file_location("abi_ui_driver", ROOT / "tools/check-upstream-ui.py")
driver = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(driver)


class AbiCase(Case):
    @property
    def fail(self):
        return self.path.endswith("_mismatch.rs")


def main():
    parser = argparse.ArgumentParser(__doc__)
    parser.add_argument("--runner", type=Path, required=True)
    parser.add_argument("--exporter", type=Path, required=True)
    parser.add_argument("--sysroot", type=Path, default=ROOT / "scratch/lake/miri-sysroot")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    args.output = args.output.resolve()
    args.output.mkdir(parents=True, exist_ok=False)
    toolchain = ROOT / ".rustup/toolchains/miri-exporter-8eb778d04094"
    env = dict(os.environ, ELAN_HOME=str(ROOT / ".elan"), LEAN_NUM_THREADS="1")
    env["PATH"] = str(toolchain / "bin") + ":" + str(ROOT / ".elan/bin") + ":" + env["PATH"]
    env["LD_LIBRARY_PATH"] = str(toolchain / "lib") + ":" + env.get("LD_LIBRARY_PATH", "")
    env["LEAN_MIRI_PREPARED_ALLOC_ID_WORLD"] = "1"
    env["LEAN_MIRI_RUN_PREPARED_MIRI"] = "1"
    settings = SimpleNamespace(exporter=args.exporter.resolve(), runner=args.runner.resolve(),
        sysroot=args.sysroot.resolve(), export_timeout=300, timeout=300,
        memory_limit=12 * 1024**3, keep_inputs=True)
    frozen = [driver.sha256(settings.exporter), driver.sha256(settings.runner)]
    driver.SOURCES = ROOT / "tests/fixtures/abi"
    base_flags = ["-Cpanic=abort", "-Zmir-opt-level=0", "-Zalways-encode-mir", "--cfg=miri"]
    records = []
    oracle_env = dict(env)
    oracle_env.pop("LEAN_MIRI_PREPARED_ALLOC_ID_WORLD")
    oracle_env.pop("LEAN_MIRI_RUN_PREPARED_MIRI")
    for name in ("optimized_indirect", "cfi", "cfi_mismatch", "variadic", "variadic_mismatch", "x87"):
        if name == "x87":
            directory = args.output / name
            directory.mkdir()
            command = [str(settings.exporter), "--output", str(directory / "oracle-input.json")]
            for root in ("aligned", "transparent", "aggregate", "mixed", "higher_ranked"):
                command += ["--root", root]
            command += ["--", str(driver.SOURCES / "x87.rs"), "--crate-type=lib", "--edition=2024",
                        "--sysroot", str(settings.sysroot), *base_flags]
            record = {"name": name, "execution": "not applicable: ABI-only library roots"}
        else:
            flags = base_flags + (["-Copt-level=2"] if name == "optimized_indirect" else [])
            record = driver.run_case(AbiCase(name + ".rs", edition="2024", flags=flags), settings, env, args.output)
            assert record["status"] == "passed", record
            assert not record["reference_profile_differences"] and not record["lean_profile_differences"], record
            directory = Path(record["directory"])
            command = record["command"].copy()
            command[command.index("--output") + 1] = str(directory / "oracle-input.json")
        oracle = directory / "oracle.json"
        command[command.index("--"):command.index("--")] = ["--oracle-output", str(oracle)]
        code = driver.invoke(command, oracle_env, directory / "oracle-export.log", settings.export_timeout,
                             settings.memory_limit)
        assert code == 0, (name, "oracle export", code)
        if name != "x87":
            prepared = json.loads((directory / "input.json").read_text())
            diagnostic = json.loads((directory / "oracle-input.json").read_text())
            assert prepared["invocation"]["rustc_args"] == diagnostic["invocation"]["rustc_args"], name
            type_inventory = lambda document: Counter(
                (row["source_layout"]["type_id_hash"], row["display"], row["shape"]["kind"])
                for row in document["types"])
            instance_inventory = lambda document: Counter(
                (row.get("def_path"), row["kind"]) for row in document["instances"])
            root_inventory = lambda document: Counter(row["def_path"] for row in document["body_roots"])
            assert type_inventory(prepared) == type_inventory(diagnostic), (name, "type declaration inventory differs")
            assert instance_inventory(prepared) == instance_inventory(diagnostic), (name, "instance declaration inventory differs")
            assert root_inventory(prepared) == root_inventory(diagnostic), (name, "root inventory differs")
            record["oracle_relation"] = "same Rust source/flags and ID-independent declaration inventories; separately byte-bound snapshots, not graph equivalence"
        with (directory / "oracle-check.log").open("w") as log:
            subprocess.run([sys.executable, "tools/check-source-queries.py", "--skip-build",
                            str(directory / "oracle-input.json"), str(oracle)],
                           cwd=ROOT, env=oracle_env, stdout=log, stderr=subprocess.STDOUT, check=True)
        if name == "x87":
            match = re.search(r"higher-ranked FnPtr comparisons=(\d+)",
                              (directory / "oracle-check.log").read_text())
            assert match and int(match[1]) > 0, "valid higher-ranked function pointer was not compared"
        record["oracle_input_sha256"] = driver.sha256(directory / "oracle-input.json")
        record["oracle_sha256"] = driver.sha256(oracle)
        records.append(record)
        print("source ABI PASS", name, flush=True)
    assert frozen == [driver.sha256(settings.exporter), driver.sha256(settings.runner)]
    (args.output / "summary.json").write_text(json.dumps({"cases": records, "binary_sha256": frozen}, indent=2))


if __name__ == "__main__":
    main()
