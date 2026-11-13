#!/usr/bin/env python3
"""Actual associated source-call export, independent selection and World checks."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
from mir_json import load_mir_document

ROOT = Path(__file__).resolve().parents[1]


def run(command, env, output):
    result = subprocess.run(command, cwd=ROOT, env=env, text=True, capture_output=True)
    output.with_suffix(".stdout").write_text(result.stdout)
    output.with_suffix(".stderr").write_text(result.stderr)
    if result.returncode:
        raise RuntimeError(f"{command[0]} failed: {result.stdout}{result.stderr}")
    return result.stdout


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("exporter", "oracle", "sysroot", "output"):
        parser.add_argument("--" + name, type=Path, required=True)
    parser.add_argument("--rustc", type=Path, default=ROOT / ".rustup/toolchains/miri-exporter-8144389c895d/bin/rustc")
    parser.add_argument("--lake", type=Path)
    parser.add_argument("--runner", type=Path, help="existing native_runner; never builds")
    args = parser.parse_args()
    for name in ("exporter", "oracle", "sysroot", "output", "rustc"):
        setattr(args, name, getattr(args, name).resolve())
    args.output.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ)
    env["LD_LIBRARY_PATH"] = str(args.rustc.parent.parent / "lib") + os.pathsep + env.get("LD_LIBRARY_PATH", "")
    env["PATH"] = str(args.rustc.parent) + os.pathsep + env.get("PATH", "")
    env["LEAN_MIRI_PREPARED_ALLOC_ID_WORLD"] = "1"
    env["LEAN_MIRI_MIR_SOURCE_TRACE"] = "1"
    report = {"scope": "actual method-syntax AssocFn; annotated UFCS remains unsupported",
              "lean": "UNRUN", "runtime": "UNRUN", "exports": {}}
    for name, roots in (("default", []), ("root-only", ["--root", "root"])):
        path = args.output / (name + ".json")
        command = [str(args.exporter), "--output", str(path), *roots, "--",
                   "tests/repro/compiler-queries/source-trait-call.rs", "--crate-name", "source_trait_call",
                   "--crate-type=bin", "--edition=2024", "-Zmir-opt-level=0", "--sysroot", str(args.sysroot)]
        run(command, env, args.output / (name + "-export"))
        document = load_mir_document(path)
        command = [str(args.oracle), *document["producer"]["input_settings"]["rustc_args"]]
        oracle_text = run(command, env, args.output / (name + "-oracle"))
        oracle_path = args.output / (name + "-oracle.json")
        oracle_path.write_text(oracle_text)
        oracle = json.loads(oracle_text)
        if oracle["negative_controls"] != 2:
            raise ValueError("associated source-call rejection domain changed")
        owner = oracle["trait_method"]
        indices = [index for index, definition in enumerate(document["definitions"])
                   if all(definition[key] == owner[key] for key in ("crate", "index"))]
        if len(indices) != 1:
            raise ValueError("raw associated declaration scope absent or duplicated")
        if any(row["instance_kind"].get("kind") == "item" and row.get("def_id") == indices[0]
               for row in document["instances"]):
            raise ValueError("trait declaration fabricated an Item instance")
        trait_type_ids = {row["type_id"] for row in document["types"]
                          if row.get("shape", {}).get("kind") == "function_definition"
                          and row["shape"].get("def_id") == indices[0]}
        if any(row["type_id"] in trait_type_ids
               for row in document["compiler_function_facts"]["types"]):
            raise ValueError("trait declaration acquired an instance-bearing/function-pointer catalogue fact")
        report["exports"][name] = {"oracle_command": command,
            "producer_sha256": hashlib.sha256(path.read_bytes()).hexdigest(),
            "oracle_sha256": hashlib.sha256(oracle_text.encode()).hexdigest()}
        if args.lake:
            command = [str(args.lake.resolve()), "env", "lean", "--run",
                       str(ROOT / "tests/compiler_queries/SourceTraitCallWorld.lean"), str(path), str(oracle_path)]
            if name == "root-only":
                command.append("expect-missing-impl-source")
            print(run(command, env, args.output / (name + "-world")).strip())
    if args.lake:
        report["lean"] = "PASS default full caller/selected impl World and root-only missing impl source guard"
    if args.runner:
        execution = run([str(args.runner.resolve()), str(args.output / "default.json"), "--seed", "0"], env,
                        args.output / "runtime")
        if "run: finalized_exit code=0;" not in execution:
            raise RuntimeError("trait source guest did not finalize with exit zero: " + execution)
        print("PASS actual trait source guest finalized_exit code=0")
        report["runtime"] = "PASS actual guest seed0 finalized_exit code=0"
    (args.output / "manifest.json").write_text(json.dumps(report, indent=2) + "\n")
    print("PASS actual associated source declarations, independent impl selection, two rejection controls and no fabricated trait Item")


if __name__ == "__main__":
    main()
