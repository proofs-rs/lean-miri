#!/usr/bin/env python3
"""Fresh raw-source export/trace controls; no builds or Lean artifact writes.

The trace covers the producer's two explicit enclosing runtime/covariance body
instantiation sites. It does not count compiler-internal operations or metadata
auxiliary-snapshot normalization as executable-body acquisitions.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess

from mir_json import load_mir_document

ROOT = Path(__file__).resolve().parents[1]
PREFIX = "LEAN_MIRI_MIR_SOURCE_QUERY\t"


def source_events(text):
    events = []
    for line in text.splitlines():
        if not line.startswith(PREFIX):
            continue
        parts = line.split("\t")
        if len(parts) != 5 or parts[2] not in ("queried=true", "queried=false"):
            raise ValueError("malformed explicit source-body query trace")
        crate, index = (int(value) for value in parts[3].split(":"))
        events.append({"route": parts[1], "queried": parts[2] == "queried=true",
                       "physical": (crate, index), "instance": parts[4]})
    return events


def check_source_events(events, monomorphic):
    selected = {(row["physical"], row["instance"]) for row in events
                if row["route"] == "runtime-extended" and not row["queried"]}
    if not selected or not monomorphic.issubset({owner for owner, _ in selected}):
        raise ValueError("actual monomorphic Extended source trace absent")
    for row in events:
        if row["queried"] and (row["physical"], row["instance"]) in selected:
            raise ValueError("selected Extended instance acquired an enclosing executable body")
    return selected


def export(args, fixture, name):
    output = args.output / (name + ".json")
    env = dict(os.environ)
    env["PATH"] = str(args.rustc.parent) + os.pathsep + env.get("PATH", "")
    env["LD_LIBRARY_PATH"] = str(args.rustc.parent.parent / "lib") + os.pathsep + env.get("LD_LIBRARY_PATH", "")
    env["LEAN_MIRI_PREPARED_ALLOC_ID_WORLD"] = "1"
    env["LEAN_MIRI_MIR_SOURCE_TRACE"] = "1"
    command = [str(args.exporter), "--output", str(output), "--root", "root", "--",
               str(fixture), "--crate-name", name.replace("-", "_"), "--crate-type=lib",
               "--edition=2024", "-Zmir-opt-level=0", "--sysroot", str(args.sysroot)]
    result = subprocess.run(command, cwd=ROOT, env=env, text=True, capture_output=True)
    (args.output / (name + ".stdout")).write_text(result.stdout)
    (args.output / (name + ".stderr")).write_text(result.stderr)
    if result.returncode:
        raise RuntimeError(f"actual export {name} failed with exit {result.returncode}: {result.stderr}")
    return output, load_mir_document(output), source_events(result.stderr)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--exporter", type=Path, required=True)
    parser.add_argument("--oracle", type=Path, required=True,
                        help="compiled tools/extended-source-mir-oracle.rs")
    parser.add_argument("--lake", type=Path,
                        help="run focused Lean checks after export/oracle capture (no builds)")
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--sysroot", type=Path, required=True)
    parser.add_argument("--rustc", type=Path, default=ROOT / ".rustup/toolchains/miri-exporter-8144389c895d/bin/rustc")
    args = parser.parse_args()
    args.exporter, args.output, args.sysroot, args.rustc = (value.resolve() for value in
        (args.exporter, args.output, args.sysroot, args.rustc))
    args.output.mkdir(parents=True, exist_ok=True)
    extended, document, events = export(args, Path("tests/repro/compiler-queries/source-mir-extended.rs"), "source_mir_extended")
    oracle_dir = args.output / "oracle"
    oracle_dir.mkdir(exist_ok=True)
    oracle_command = [str(args.oracle.resolve()), *document["producer"]["input_settings"]["rustc_args"]]
    oracle_env = dict(os.environ)
    oracle_env["LD_LIBRARY_PATH"] = str(args.rustc.parent.parent / "lib") + os.pathsep + oracle_env.get("LD_LIBRARY_PATH", "")
    oracle_env["EXTENDED_SOURCE_MIR_OUT"] = str(oracle_dir)
    oracle_run = subprocess.run(oracle_command, cwd=ROOT, env=oracle_env, text=True, capture_output=True)
    (args.output / "oracle.stdout").write_text(oracle_run.stdout)
    (args.output / "oracle.stderr").write_text(oracle_run.stderr)
    if oracle_run.returncode:
        raise RuntimeError(f"independent oracle failed: {oracle_run.stderr}")
    rows = json.loads((oracle_dir / "oracle.json").read_text())
    if len(rows) != 42:
        raise ValueError("full same-flags normalized oracle domain changed")
    negatives = json.loads((oracle_dir / "negative-controls.json").read_text())
    interfaces = json.loads((oracle_dir / "interface-controls.json").read_text())
    if len(negatives) != 35 or any(not row.get("error") for row in negatives) or len(interfaces) != 4:
        raise ValueError("raw-source rejection/FnDef interface control domain changed")
    physical = {(item["crate"], item["index"]) for item in document["definitions"]}
    retained, unsupported = [], []
    for row in rows:
        owner = row["physical_owner"]
        (retained if (owner["crate"], owner["index"]) in physical else unsupported).append(row)
    if len(retained) != 41 or len(unsupported) != 1 or unsupported[0]["name"] != "raw_pointer":
        raise ValueError("retained-source/expected-Unsupported World domain changed")
    for name, selection in (("world-retained.json", retained), ("world-unsupported.json", unsupported)):
        (oracle_dir / name).write_text(json.dumps(selection, indent=2) + "\n")
    (args.output / "oracle-scope-manifest.json").write_text(json.dumps({
        "producer_input_sha256": hashlib.sha256(extended.read_bytes()).hexdigest(),
        "oracle_executable_sha256": hashlib.sha256(args.oracle.read_bytes()).hexdigest(),
        "retained_sha256": hashlib.sha256((oracle_dir / "world-retained.json").read_bytes()).hexdigest(),
        "unsupported_sha256": hashlib.sha256((oracle_dir / "world-unsupported.json").read_bytes()).hexdigest(),
        "command": oracle_command, "flags_source": "exact producer.input_settings.rustc_args",
        "full_mir_rows": len(rows), "raw_source_rejection_controls": len(negatives),
        "fndef_interface_controls": len(interfaces),
        "retained_indices": [index for index, row in enumerate(rows) if row in retained],
        "unsupported_indices": [index for index, row in enumerate(rows) if row in unsupported], "world_retained_rows": len(retained),
        "expected_unsupported": [{"name": row["name"], "physical_owner": row["physical_owner"],
                                  "reason": "physical definition absent from producer universe"} for row in unsupported],
        "selection": "unchanged complete oracle rows selected by physical definition membership; no expected-body rewriting",
        "oracle_sha256": hashlib.sha256((oracle_dir / "oracle.json").read_bytes()).hexdigest()
    }, indent=2) + "\n")
    wanted = {"ordinary_cast", "ordinary_reference", "ordinary_raw_pointer"}
    monomorphic = set()
    for source in document["mir_templates"]:
        if source["def_path"] in wanted:
            if json.loads(source["template"])["parameters"]:
                raise ValueError("monomorphic Extended fixture unexpectedly acquired generic parameters")
            definition = document["definitions"][source["source_def_id"]]
            monomorphic.add((definition["crate"], definition["index"]))
    if len(monomorphic) != len(wanted):
        raise ValueError("actual monomorphic source templates absent")
    selected = check_source_events(events, monomorphic)
    poisoned = list(events)
    row = next(row for row in events if row["route"] == "runtime-extended" and not row["queried"])
    poisoned.append({**row, "route": "runtime-residual", "queried": True})
    try:
        check_source_events(poisoned, monomorphic)
    except ValueError as error:
        if "acquired an enclosing executable body" not in str(error):
            raise
    else:
        raise ValueError("poisoned executable-body acquisition trace was accepted")
    no_resume, source_only, no_resume_events = export(args, Path("tests/repro/compiler-queries/coroutine-source-no-resume.rs"), "coroutine_source_no_resume")
    coverage = source_only["compiler_coroutine_coverage"]
    if (len(coverage["generic_sources"]) != 1 or coverage["coroutines"] or coverage["auxiliary_bodies"]
            or any(coverage["body_coroutines"])):
        raise ValueError("type-only coroutine discovery duplicated raw sources or fabricated runtime/auxiliary bodies")
    if sum(isinstance(node["shape"], dict) and node["shape"].get("kind") == "coroutine"
           for node in source_only["types"]) != 2:
        raise ValueError("type-only coroutine fixture lost repeated-u8/distinct-u64 identities")
    report = {"exporter_sha256": hashlib.sha256(args.exporter.read_bytes()).hexdigest(),
              "inputs": {path.name: hashlib.sha256(path.read_bytes()).hexdigest() for path in (extended, no_resume)},
              "extended_instance_keys": len(selected), "monomorphic_source_definitions": sorted(monomorphic),
              "explicit_body_trace_events": len(events), "type_only_trace_events": len(no_resume_events),
              "scope": "two explicit enclosing runtime/covariance body acquisition sites only; metadata auxiliary normalization and other compiler queries remain separate"}
    (args.output / "source-trace-report.json").write_text(json.dumps(report, indent=2) + "\n")
    if args.lake:
        checks = [
            ("ExtendedSourceMir", [oracle_dir / "oracle.json"]),
            ("ExtendedSourceWorld", [extended, oracle_dir / "world-retained.json", oracle_dir / "world-unsupported.json"]),
            ("CoroutineTypeSource", [no_resume]),
        ]
        for name, inputs in checks:
            command = [str(args.lake.resolve()), "env", "lean", "--run",
                       str(ROOT / "tests" / "compiler_queries" / (name + ".lean")), *map(str, inputs)]
            result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True)
            (args.output / (name + ".log")).write_text(result.stdout + result.stderr)
            if result.returncode:
                raise RuntimeError(f"{name} failed: {result.stdout}{result.stderr}")
            print(result.stdout.strip())
    print(f"PASS {len(selected)} actual Extended instance keys, three monomorphic source definitions, poisoned trace rejection and type-only raw coroutine source reuse")


if __name__ == "__main__":
    main()
