#!/usr/bin/env python3
"""Finite original/control comparisons and mutations of fresh coroutine evidence.

Requires a built coherent schema-13 exporter/native pair. No builds or flag/budget
changes are performed. Serialize heavy checks externally with the guest lock.
"""
import argparse
import gc
import importlib.util
import json
import os
from pathlib import Path
import sys
from types import SimpleNamespace

ROOT = Path(__file__).resolve().parents[1]
sys.path[:0] = [str(ROOT / "tools"), str(ROOT / "tests/upstream_ui")]
from suite import discover
from mir_json import load_mir_document, pool_entry
from run_guarded import run

spec = importlib.util.spec_from_file_location("coroutine_ui", ROOT / "tools/check-upstream-ui.py")
driver = importlib.util.module_from_spec(spec)
spec.loader.exec_module(driver)


def check_queries(control, output, env, settings):
    code = run(["lake", "env", "lean", "--run", "tests/input/CoroutineNativeQueries.lean", str(control)],
        cwd=ROOT, env=env, log=output / "native-query.log", timeout=180, memory_limit=settings.memory_limit)
    assert code.returncode == 0, code
    document = load_mir_document(control)
    catalog = document["compiler_coroutine_coverage"]
    mutations = []
    def save(name, expected):
        target = output / (name + ".json")
        with target.open("w") as stream:
            json.dump(document, stream, separators=(",", ":"))
        mutations.append((target, expected))
    old = catalog["coroutines"]
    catalog["coroutines"] = old[1:]
    save("missing-witness", "marked body has no witness")
    catalog["coroutines"] = old
    auxiliary = catalog["auxiliary_bodies"][0]
    definition = auxiliary["source_kind"]["def_id"]
    auxiliary["source_kind"]["def_id"] = (definition + 1) % len(document["definitions"])
    assert auxiliary["source_kind"]["def_id"] != definition
    save("source-definition", "auxiliary source kind differs from body definition")
    auxiliary["source_kind"]["def_id"] = definition
    selected = None
    for row in catalog["coroutines"]:
        node = document["types"][row["coroutine_type"]]
        for parent in node["compiler_facts"]["projection_queries"]["parents"]:
            if parent["variant"] is not None:
                actual = pool_entry(document, "layouts", parent["layout"])
                for index in range(len(document["layouts"])):
                    other = pool_entry(document, "layouts", index)
                    if other["fields"]["field_count"] == actual["fields"]["field_count"] and other["size_bytes"] != actual["size_bytes"]:
                        selected = (parent, index)
                        break
            if selected:
                break
        if selected:
            break
    assert selected, "control must provide a bound-valid wrong physical variant layout"
    parent, wrong_layout = selected
    original_layout = parent["layout"]
    parent["layout"] = wrong_layout
    save("physical-variant", "selected query differs from exact physical variant")
    parent["layout"] = original_layout
    del document, catalog, old, auxiliary, selected, parent
    gc.collect()
    for snapshot, expected in mutations:
        code = run(["lake", "env", "lean", "--run", "tests/input/CoroutineReject.lean", str(snapshot), expected],
            cwd=ROOT, env=env, log=snapshot.with_suffix(".log"), timeout=180, memory_limit=settings.memory_limit)
        assert code.returncode == 0, (snapshot, code)
        print("PASS constructed decoder mutation", snapshot.stem, flush=True)
    return [path.stem for path, _ in mutations]


def main():
    parser = argparse.ArgumentParser(__doc__)
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    toolchain = ROOT / ".rustup/toolchains/miri-exporter-8144389c895d"
    env = dict(os.environ)
    for key in list(env):
        if key.startswith("LEAN_MIRI_REFERENCE_"):
            del env[key]
    env.update(PATH=str(ROOT / ".elan/bin") + ":" + str(toolchain / "bin") + ":" + env["PATH"],
        ELAN_HOME=str(ROOT / ".elan"),
        LD_LIBRARY_PATH=str(toolchain / "lib") + ":" + env.get("LD_LIBRARY_PATH", ""),
        LEAN_MIRI_PREPARED_ALLOC_ID_WORLD="1", LEAN_MIRI_RUN_PREPARED_MIRI="1")
    settings = SimpleNamespace(exporter=ROOT / "exporter/target/release/lean-miri-mir-exporter",
        runner=ROOT / ".lake/build/bin/native_runner", sysroot=ROOT / "scratch/miri-sysroot",
        export_timeout=180, timeout=180, memory_limit=12 * 1024**3, keep_inputs=True)
    hashes = [driver.sha256(settings.exporter), driver.sha256(settings.runner)]
    originals = {f"pass/{name}.rs@{revision}" for name in ("future-self-referential", "generators")
                 for revision in ("tree", "tree_implicit_writes")}
    records, control = [], None
    for sources, selected in [(ROOT / "upstream/miri-source/tests", originals),
                              (ROOT / "tests/upstream_ui/fixtures/coroutines", None)]:
        driver.SOURCES = sources
        cases = [case for case in discover(sources) if selected is None or case.id in selected]
        assert len(cases) == (4 if selected is not None else 2)
        for case in cases:
            assert not case.reasons, case.reasons
            record = driver.run_case(case, settings, env, args.output)
            assert record["status"] == "passed", record
            assert record["terminal"]["kind"] == "exit" and record["terminal"]["detail"] == "0", record
            assert not record["reference_profile_differences"] and not record["lean_profile_differences"], record
            snapshot = Path(record["directory"]) / "input.json"
            document = load_mir_document(snapshot)
            assert document["schema_version"] == 13
            coverage = document["compiler_coroutine_coverage"]
            assert coverage["coroutines"] and coverage["auxiliary_bodies"]
            owners = {document["bodies"][row["owner_body"]]["instance_id"] for row in coverage["coroutines"]}
            assert owners <= {row["instance_id"] for row in document["compiler_instance_abis"]}
            assert not owners & {row["instance_id"] for row in document["compiler_native_signature_queries"]}
            if selected is None and control is None:
                control = snapshot
            del document, coverage
            gc.collect()
            records.append(record)
            print("PASS strict coroutine comparison", case.id, flush=True)
    assert control is not None
    mutations = check_queries(control, args.output, env, settings)
    assert hashes == [driver.sha256(settings.exporter), driver.sha256(settings.runner)]
    (args.output / "summary.json").write_text(json.dumps({"cases": records,
        "binary_sha256": hashes, "decoder_mutations": mutations}, indent=2))


if __name__ == "__main__":
    main()
