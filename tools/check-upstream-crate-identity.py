#!/usr/bin/env python3
"""Finite source crate-name/type-name and extern-static-layout comparisons.

Expected names below are test assertions, never command-line name synthesis.
The compiler owns filename normalization, source attributes and explicit flags.
"""
import argparse
import importlib.util
import json
import os
from pathlib import Path
import sys
from types import SimpleNamespace

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
sys.path.insert(0, str(ROOT / "tests/upstream_ui"))
from suite import discover

spec = importlib.util.spec_from_file_location("crate_identity_driver", ROOT / "tools/check-upstream-ui.py")
driver = importlib.util.module_from_spec(spec)
spec.loader.exec_module(driver)


def verify_metadata(snapshot, expected_name, explicit):
    # Separate process: release the decoded compiler graph before another guest.
    document = json.loads(Path(snapshot).read_text())
    frames = document["compiler_frame_metadata"]
    names = [row["name"] for row in frames["crates"] if row["crate"] == frames["local_crate"]]
    assert names == [expected_name], names
    arguments = document["producer"]["input_settings"]["rustc_args"]
    assert "--crate-name=upstream_ui" not in arguments
    if explicit == "yes":
        index = arguments.index("--crate-name")
        assert arguments[index + 1] == expected_name
    else:
        assert not any(arg == "--crate-name" or arg.startswith("--crate-name=") for arg in arguments)
    print("compiler-owned local crate verified:", expected_name)


def main():
    parser = argparse.ArgumentParser(__doc__)
    parser.add_argument("--runner", type=Path, required=True)
    parser.add_argument("--exporter", type=Path, default=ROOT / "exporter/target/release/lean-miri-mir-exporter")
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    toolchain = ROOT / ".rustup/toolchains/miri-exporter-8144389c895d"
    env = dict(os.environ)
    for key in list(env):
        if key.startswith("LEAN_MIRI_REFERENCE_"):
            del env[key]
    env.update(PATH=str(toolchain / "bin") + ":" + env["PATH"],
        LD_LIBRARY_PATH=str(toolchain / "lib") + ":" + env.get("LD_LIBRARY_PATH", ""),
        LEAN_MIRI_PREPARED_ALLOC_ID_WORLD="1", LEAN_MIRI_RUN_PREPARED_MIRI="1")
    settings = SimpleNamespace(exporter=args.exporter.resolve(), runner=args.runner.resolve(),
        sysroot=ROOT / "scratch/miri-sysroot", export_timeout=180, timeout=180,
        memory_limit=12 * 1024**3, keep_inputs=True)
    hashes = [driver.sha256(settings.exporter), driver.sha256(settings.runner)]
    originals = ROOT / "upstream/miri-source/tests"
    fixtures = ROOT / "tests/upstream_ui/fixtures/crate_names"
    records = []
    for sources, targets in [
        (originals, {"fail/extern_static/wrong_size.rs": "wrong_size",
                     "fail/extern_static/wrong_size_shim.rs": "wrong_size_shim"}),
        (fixtures, {"pass/hyphen-name.rs": "hyphen_name",
                    "pass/attribute-name.rs": "source_attribute",
                    "pass/directive-name.rs": "source_flag_override"}),
    ]:
        driver.SOURCES = sources
        selected = {case.path: case for case in discover(sources) if case.path in targets}
        assert set(selected) == set(targets)
        for path, name in targets.items():
            case = selected[path]
            assert not case.reasons, case.reasons
            record = driver.run_case(case, settings, env, args.output)
            assert record["status"] == "passed", record
            assert not record["reference_profile_differences"] and not record["lean_profile_differences"], record
            assert record["terminal"]["kind"] == ("ub" if case.fail else "exit"), record
            if case.fail:
                assert record["category"] == "extern_static_layout", record
            else:
                assert record["terminal"]["detail"] == "0", record
            command = [sys.executable, __file__, "--verify-metadata",
                       str(Path(record["directory"]) / "input.json"), name,
                       "yes" if path == "pass/directive-name.rs" else "no"]
            code = driver.invoke(command, env, Path(record["directory"]) / "crate-name.log",
                                 settings.timeout, settings.memory_limit)
            assert code == 0, (path, "metadata", code)
            records.append(record)
            print("strict comparison and actual crate-name PASS", path, name, flush=True)
    assert hashes == [driver.sha256(settings.exporter), driver.sha256(settings.runner)]
    (args.output / "summary.json").write_text(json.dumps({"cases": records,
        "binary_sha256": hashes, "checker_sha256": driver.sha256(Path(__file__))}, indent=2))
    print("PASS original2 and type-name3; source/reference/FNV/profile/name bindings retained", flush=True)


if __name__ == "__main__":
    if len(sys.argv) == 5 and sys.argv[1] == "--verify-metadata":
        verify_metadata(*sys.argv[2:])
    else:
        main()
