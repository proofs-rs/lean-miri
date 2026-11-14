#!/usr/bin/env python3
"""Capture actual annotated operands with exact producer flags; optionally run Lean."""
import argparse
import copy
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location("extended_source_checks", ROOT / "tools/check-extended-source-mir.py")
shared = importlib.util.module_from_spec(spec)
spec.loader.exec_module(shared)


def annotations(value):
    if isinstance(value, dict):
        if value.get("kind") in ("annotated_zero_sized", "annotated_scalar"):
            yield value
        for child in value.values():
            yield from annotations(child)
    elif isinstance(value, list):
        for child in value:
            yield from annotations(child)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ("exporter", "oracle", "sysroot", "output"):
        parser.add_argument("--" + name, type=Path, required=True)
    parser.add_argument("--rustc", type=Path, default=ROOT / ".rustup/toolchains/miri-exporter-8144389c895d/bin/rustc")
    parser.add_argument("--lake", type=Path)
    args = parser.parse_args()
    for name in ("exporter", "oracle", "sysroot", "output", "rustc"):
        setattr(args, name, getattr(args, name).resolve())
    args.output.mkdir(parents=True, exist_ok=True)
    source, document, _ = shared.export(args, Path("tests/repro/compiler-queries/source-mir-annotated.rs"), "source_mir_annotated")
    output = args.output / "oracle"
    output.mkdir(exist_ok=True)
    command = [str(args.oracle), *document["producer"]["input_settings"]["rustc_args"]]
    env = dict(os.environ)
    env["LD_LIBRARY_PATH"] = str(args.rustc.parent.parent / "lib") + os.pathsep + env.get("LD_LIBRARY_PATH", "")
    env["EXTENDED_SOURCE_MIR_OUT"] = str(output)
    result = subprocess.run(command, cwd=ROOT, env=env, text=True, capture_output=True)
    (args.output / "oracle.stdout").write_text(result.stdout)
    (args.output / "oracle.stderr").write_text(result.stderr)
    if result.returncode:
        raise RuntimeError(result.stderr)
    rows = json.loads((output / "oracle.json").read_text())
    negatives = json.loads((output / "negative-controls.json").read_text())
    if len(rows) != 8 or len(negatives) != 8 or any(not row.get("error") for row in negatives):
        raise ValueError("annotated actual body/rejection domain changed")
    for row in rows:
        before, after = list(annotations(row["source"])), list(annotations(row["expected"]))
        if not before or len(before) != len(after):
            raise ValueError("actual annotated operands disappeared")
        for raw, normalized in zip(before, after):
            if raw["span"] != normalized["span"] or raw["user_type"] != normalized["user_type"]:
                raise ValueError("normalization lost annotation index/span provenance")
            marker = raw["user_type"]
            if marker["table_state"] != "cleared_post_borrowck" or marker["entries"] != []:
                raise ValueError("actual annotation table is not cleared")
    malformed = []
    for mutation in ("missing", "wrong_state", "nonempty", "large_index", "extra_field"):
        template = copy.deepcopy(rows[0]["source"])
        operand = next(annotations(template))
        if mutation == "missing":
            del operand["user_type"]
        elif mutation == "wrong_state":
            operand["user_type"]["table_state"] = "uncleared"
        elif mutation == "nonempty":
            operand["user_type"]["entries"] = [0]
        elif mutation == "large_index":
            operand["user_type"]["index"] = 2**32
        else:
            operand["user_type"]["unexpected"] = 0
        malformed.append(template)
    malformed_path = output / "malformed-annotations.json"
    malformed_path.write_text(json.dumps(malformed, indent=2) + "\n")
    manifest = {"oracle_command": command, "flags_source": "exact producer.input_settings.rustc_args",
                "full_actual_bodies": len(rows), "raw_source_negatives": len(negatives),
                "malformed_decoder_controls": len(malformed), "lean_result": "UNRUN",
                "oracle_sha256": hashlib.sha256((output / "oracle.json").read_bytes()).hexdigest(),
                "producer_input_sha256": hashlib.sha256(source.read_bytes()).hexdigest()}
    if args.lake:
        command = [str(args.lake.resolve()), "env", "lean", "--run",
                   str(ROOT / "tests/compiler_queries/AnnotatedSourceMir.lean"),
                   str(output / "oracle.json"), str(malformed_path)]
        result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True)
        (args.output / "AnnotatedSourceMir.log").write_text(result.stdout + result.stderr)
        manifest["lean_result"] = "PASS" if result.returncode == 0 else "FAIL"
        (args.output / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
        if result.returncode:
            raise RuntimeError(result.stdout + result.stderr)
        print(result.stdout.strip())
    else:
        (args.output / "manifest.json").write_text(json.dumps(manifest, indent=2) + "\n")
    print("PASS eight actual annotated body captures and eight raw-source negatives; reify remains unsupported")


if __name__ == "__main__":
    main()
