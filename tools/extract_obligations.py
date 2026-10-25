#!/usr/bin/env python3
"""Deterministic source-review candidates, NOT a Rust parser/completeness proof.

Keep comments and strings deliberately: false positives remain visible for review
instead of silently discarding possible obligations. Macro expansions, aliases,
generated code and cross-crate calls require additional analysis.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re

PATTERNS = {
    "ub": r"\b(?:throw_ub\w*|err_ub\w*|UndefinedBehavior|UbError)\b",
    "unsupported": r"\b(?:throw_unsup\w*|err_unsup\w*|UnsupportedOpInfo)\b",
    "invalid_program": r"\b(?:throw_inval\w*|err_inval\w*|InvalidProgramInfo)\b",
    "nondeterministic_choice": r"\b(?:random|random_range|random_bool|choose|shuffle|sample)\s*(?:\(|::)",
    "state_declaration": r"\b(?:struct|enum)\s+[A-Za-z_]\w*",
    "external_dependency": r"\b(?:use|extern\s+crate)\s+(?:rustc_\w+|rand|libc|genmc)\b",
    "mir_dispatch": r"\b(?:StatementKind|TerminatorKind|Rvalue|Intrinsic|UnOp|BinOp|CastKind)::",
    "machine_hook": r"\b(?:fn\s+(?:before_|after_|atomic_|call_|enforce_|validate_|retag|find_mir)|impl.*\bMachine\b)",
}


def scan_file(path, relative):
    data = path.read_bytes()
    digest = hashlib.sha256(data).hexdigest()
    result = []
    compiled = {key: re.compile(value) for key, value in PATTERNS.items()}
    for number, line in enumerate(data.decode("utf-8").splitlines(), 1):
        for category, pattern in compiled.items():
            if pattern.search(line):
                result.append({"path": relative, "line": number,
                               "category": category, "source_sha256": digest,
                               "text": line.strip(), "review": "pending"})
    return result


def collect(root):
    candidates = []
    files = []
    lock_path = root / "upstream/source-lock.json"
    if lock_path.is_file():
        lock = json.loads(lock_path.read_text())
        files = [root / item["path"] for item in lock["files"]
                 if item["path"].endswith(".rs")]
        if not files:
            raise ValueError("Source lock contains no Rust source files")
    else:
        for tree in ("upstream/miri-source/src", "upstream/rustc-source/compiler"):
            directory = root / tree
            if not directory.is_dir():
                raise ValueError(f"Missing source directory: {directory}")
            files.extend(directory.rglob("*.rs"))
    for path in sorted(files):
        candidates.extend(scan_file(path, path.relative_to(root).as_posix()))
    return {"schema_version": 1, "status": "review-candidates-only", "language": "Rust",
            "limitations": ["Lexical scan includes comments and strings.",
                            "Not a Rust parser; does not expand macros or resolve calls.",
                            "Extracted sources may not include every rustc dependency.",
                            "Native C/C++ sources are not scanned by these Rust patterns.",
                            "No absence/completeness or semantic equivalence claim."],
            "scanned_files": len(files), "candidates": candidates}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--output", type=Path, required=True)
    args = parser.parse_args()
    result = collect(args.root.resolve())
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n")
    counts = {key: sum(item["category"] == key for item in result["candidates"])
              for key in PATTERNS}
    print(json.dumps({"scanned_files": result["scanned_files"], "candidates": counts}))


if __name__ == "__main__":
    main()
