#!/usr/bin/env python3
"""Create a content-hash manifest for one rustc MIR exporter document.

The manifest records explicit compiler arguments, the exporter and MIR output
artifacts, the pinned source inventory, Rust source files named by rustc, and
external compiler artifacts named by --extern. It deliberately does not claim
to discover environment-provided inputs, linker search contents, macro include
graphs, or every artifact emitted into Cargo's output directory.
"""

from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
from typing import Any

try:  # Supports both ``python tools/exporter_provenance.py`` and package imports.
    from .mir_json import load_mir_document
except ImportError:  # pragma: no cover - exercised by direct script invocation
    from mir_json import load_mir_document


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for block in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(block)
    return digest.hexdigest()


def display_path(path: Path, root: Path) -> str:
    try:
        return path.relative_to(root).as_posix()
    except ValueError:
        return str(path)


def file_record(path: Path, root: Path, role: str) -> dict[str, Any]:
    resolved = path.resolve()
    if not resolved.is_file():
        return {"role": role, "path": display_path(resolved, root), "status": "unavailable"}
    return {
        "role": role,
        "path": display_path(resolved, root),
        "status": "hashed",
        "size_bytes": resolved.stat().st_size,
        "sha256": sha256(resolved),
    }


def argument_value(args: list[str], flag: str) -> str | None:
    for index, argument in enumerate(args):
        if argument == flag and index + 1 < len(args):
            return args[index + 1]
        if argument.startswith(flag + "="):
            return argument[len(flag) + 1 :]
    return None


def rustc_sources(args: list[str], cwd: Path, root: Path) -> list[dict[str, Any]]:
    paths = sorted(
        {
            (cwd / argument).resolve()
            for argument in args
            if argument.endswith(".rs") and not argument.startswith("-")
        },
        key=str,
    )
    return [file_record(path, root, "rustc_source_argument") for path in paths]


def extern_artifacts(args: list[str], cwd: Path, root: Path) -> list[dict[str, Any]]:
    externs: set[tuple[str, str]] = set()
    index = 0
    while index < len(args):
        argument = args[index]
        if argument == "--extern" and index + 1 < len(args):
            index += 1
            value = args[index]
        elif argument.startswith("--extern="):
            value = argument[len("--extern=") :]
        else:
            index += 1
            continue
        name, separator, path = value.partition("=")
        if separator:
            externs.add((name, path))
        else:
            externs.add((name, ""))
        index += 1

    records = []
    for name, raw_path in sorted(externs):
        if not raw_path:
            records.append({"role": "rustc_extern_artifact", "crate": name, "status": "compiler_search_path_only"})
            continue
        record = file_record(cwd / raw_path, root, "rustc_extern_artifact")
        record["crate"] = name
        records.append(record)
    return records


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--document", type=Path, required=True, help="exporter MIR JSON document")
    parser.add_argument("--exporter", type=Path, required=True, help="built exporter executable")
    parser.add_argument("--manifest", type=Path, required=True, help="write provenance JSON here")
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1], help="project root")
    options = parser.parse_args()

    root = options.root.resolve()
    document_path = options.document.resolve()
    # Load decoded semantic metadata while file_record below hashes the exact
    # raw wire bytes that the exporter wrote.
    document = load_mir_document(document_path)
    invocation = document.get("invocation")
    if not isinstance(invocation, dict):
        parser.error("the MIR document has no invocation record; rebuild with the current exporter")
    args = invocation.get("rustc_args")
    if not isinstance(args, list) or not all(isinstance(arg, str) for arg in args):
        parser.error("invocation.rustc_args must be the exact string argument array")
    cwd_raw = invocation.get("working_directory")
    if not isinstance(cwd_raw, str):
        parser.error("invocation.working_directory is required to resolve compiler paths")
    cwd = Path(cwd_raw).resolve()

    # Modules split out of main.rs affect the producer just as main.rs does.
    # Record every Rust source under src, with deterministic ordering;
    # this remains a listed-source manifest, not a build-hermeticity claim.
    project_files = [
        *sorted((root / "exporter/src").rglob("*.rs")),
        root / "exporter/build.rs",
        root / "exporter/Cargo.toml",
        root / "exporter/Cargo.lock",
        root / "tools/mir_json.py",
        root / "tools/exporter_provenance.py",
    ]
    source_lock = root / "upstream/source-lock.json"
    rustc_file_manifest = root / "upstream/rustc-selected-files.txt"
    manifest = {
        "schema": "lean-miri-exporter-provenance",
        "schema_version": 1,
        "scope": "content hashes for listed artifacts and explicit rustc path inputs; this is not an exhaustive build-hermeticity claim",
        "producer": document.get("producer", {}),
        "invocation": invocation,
        "project_sources": [file_record(path, root, "exporter_build_source") for path in project_files],
        "pinned_source_inventory": {
            "source_lock": file_record(source_lock, root, "upstream_source_lock"),
            "rustc_selected_file_manifest": file_record(rustc_file_manifest, root, "rustc_selected_path_manifest"),
        },
        "input_sources": rustc_sources(args, cwd, root),
        "dependency_artifacts": extern_artifacts(args, cwd, root),
        "artifacts": {
            "exporter_binary": file_record(options.exporter, root, "exporter_executable"),
            "mir_document": file_record(document_path, root, "mir_export_json"),
            "compiler_products": {
                "status": "not_hashed",
                "reason": "the wrapper writes MIR JSON before rustc finishes codegen; compiler output files are intentionally not inferred from directory scans",
            },
        },
        "limitations": [
            "Only .rs source paths present as explicit rustc arguments are hashed; include! and macro-generated file dependencies are not discovered.",
            "Only --extern artifacts with explicit paths are hashed; artifacts resolved from search paths are listed but unavailable.",
            "Environment variables, linker search directory contents, proc-macro inputs, and compiler outputs are not claimed as covered.",
            "rustc_args_fingerprint_fnv1a64 is a convenience identifier, not an integrity digest; use the recorded argument array and file SHA-256 values.",
        ],
    }
    destination = options.manifest.resolve()
    destination.parent.mkdir(parents=True, exist_ok=True)
    destination.write_text(json.dumps(manifest, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"wrote provenance manifest: {destination}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
