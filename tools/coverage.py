#!/usr/bin/env python3
"""Validate Lean-Miri source coverage records against the pinned source tree.

The module inventory is deliberately separate from feature obligations: listing
every upstream file does not establish that its behavior has been ported.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
from collections import Counter
from pathlib import Path, PurePosixPath
from typing import Any


STATUSES = ("Not ported", "Ported", "Tested", "Specified", "Proved")
STATUS_EVIDENCE = {
    "Not ported": (),
    "Ported": ("lean_definitions",),
    "Tested": ("lean_definitions", "tests"),
    "Specified": ("lean_definitions", "specifications"),
    "Proved": ("lean_definitions", "specifications", "proofs"),
}
SHA256_RE = re.compile(r"^[0-9a-fA-F]{64}$")
GIT_OBJECT_RE = re.compile(r"^(?:[0-9a-fA-F]{40}|[0-9a-fA-F]{64})$")
SOURCE_EXTENSIONS = {".rs", ".c", ".cc", ".cpp", ".cxx", ".h", ".hh", ".hpp", ".hxx", ".inc", ".m", ".mm", ".s", ".S"}
EVIDENCE_EXTENSIONS = {
    "lean_definitions": {".lean"},
    "tests": {".lean", ".rs", ".py", ".sh", ".in"},
    "specifications": {".lean"},
    "proofs": {".lean"},
}


class CoverageError(Exception):
    pass


def _read_json(path: Path) -> Any:
    try:
        return json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:
        raise CoverageError(f"missing file: {path}") from exc
    except json.JSONDecodeError as exc:
        raise CoverageError(f"invalid JSON in {path}: {exc}") from exc


def _write_json(path: Path, value: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n", encoding="utf-8")


def _safe_repo_path(value: Any, label: str) -> str:
    if not isinstance(value, str) or not value:
        raise CoverageError(f"{label} must be a non-empty relative path")
    path = PurePosixPath(value)
    if path.is_absolute() or ".." in path.parts or "." in path.parts or "\\" in value:
        raise CoverageError(f"{label} is not a safe repository-relative path: {value!r}")
    return path.as_posix()


def _source_lock(root: Path) -> tuple[dict[str, dict[str, Any]], list[str], dict[str, int]]:
    lock_path = root / "upstream/source-lock.json"
    lock = _read_json(lock_path)
    if not isinstance(lock, dict):
        raise CoverageError("upstream/source-lock.json must contain a JSON object")
    if lock.get("schema_version") != 1:
        raise CoverageError("upstream/source-lock.json must have schema_version 1")
    pins = lock.get("pins")
    if not isinstance(pins, dict) or not pins:
        raise CoverageError("upstream/source-lock.json must record upstream pins as a non-empty object")
    for name, pin in pins.items():
        if not isinstance(pin, dict):
            raise CoverageError(f"source-lock pin {name!r} must record repository and commit")
        repository = pin.get("repository", pin.get("repo"))
        commit = pin.get("commit")
        if not isinstance(repository, str) or not repository.strip():
            raise CoverageError(f"source-lock pin {name!r} has no repository")
        if not isinstance(commit, str) or not GIT_OBJECT_RE.fullmatch(commit):
            raise CoverageError(f"source-lock pin {name!r} has an invalid commit identity")

    raw_roots = lock.get("coverage_roots")
    if not isinstance(raw_roots, list) or not raw_roots:
        raise CoverageError("upstream/source-lock.json must record non-empty coverage_roots")
    roots: list[str] = []
    for i, item in enumerate(raw_roots):
        raw_path = item.get("path") if isinstance(item, dict) else item
        roots.append(_safe_repo_path(raw_path, f"coverage_roots[{i}].path"))
    if len(roots) != len(set(roots)):
        raise CoverageError("upstream/source-lock.json has duplicate coverage roots")

    raw_files = lock.get("files")
    if not isinstance(raw_files, list):
        raise CoverageError("upstream/source-lock.json files must be a list")
    files: dict[str, dict[str, Any]] = {}
    for i, item in enumerate(raw_files):
        if not isinstance(item, dict):
            raise CoverageError(f"upstream/source-lock.json files[{i}] must be an object")
        path = _safe_repo_path(item.get("path"), f"upstream/source-lock.json files[{i}].path")
        if path in files:
            raise CoverageError(f"upstream/source-lock.json contains duplicate source path: {path}")
        digest = item.get("sha256")
        if digest is not None and (not isinstance(digest, str) or not SHA256_RE.fullmatch(digest)):
            raise CoverageError(f"upstream/source-lock.json has invalid SHA256 for {path}")
        component = item.get("component")
        if not isinstance(component, str) or not component:
            raise CoverageError(f"upstream/source-lock.json must name the component for {path}")
        git_blob = item.get("git_blob")
        if not isinstance(git_blob, str) or not GIT_OBJECT_RE.fullmatch(git_blob):
            raise CoverageError(f"upstream/source-lock.json must record a Git blob identity for {path}")
        files[path] = {
            "component": component,
            "git_blob": git_blob.lower(),
            "sha256": digest.lower() if digest else None,
        }
    if not files:
        raise CoverageError("upstream/source-lock.json contains no source files")

    raw_expected = lock.get("coverage_expected_rust_modules", {})
    if not isinstance(raw_expected, dict):
        raise CoverageError("coverage_expected_rust_modules must be an object when present")
    expected: dict[str, int] = {}
    for raw_path, count in raw_expected.items():
        path = _safe_repo_path(raw_path, "coverage_expected_rust_modules path")
        if path not in roots:
            raise CoverageError(f"expected Rust module count names an unknown coverage root: {path}")
        if not isinstance(count, int) or isinstance(count, bool) or count < 0:
            raise CoverageError(f"expected Rust module count for {path} must be a non-negative integer")
        expected[path] = count
    return files, roots, expected


def _scan_roots(root: Path, roots: list[str], excluded_directories: list[str] | None = None) -> tuple[set[str], list[str]]:
    found: set[str] = set()
    issues: list[str] = []
    excluded_directories = excluded_directories or []
    for rel in roots:
        target = root / rel
        if not target.exists():
            issues.append(f"coverage root is missing: {rel}")
            continue
        if target.is_file():
            candidates = [target] if target.suffix in SOURCE_EXTENSIONS else []
        elif target.is_dir():
            candidates = sorted(p for p in target.rglob("*") if p.is_file() and p.suffix in SOURCE_EXTENSIONS)
        else:
            issues.append(f"coverage root is neither file nor directory: {rel}")
            continue
        for path in candidates:
            candidate = path.relative_to(root).as_posix()
            if any(candidate == excluded or candidate.startswith(excluded + "/") for excluded in excluded_directories):
                continue
            found.add(candidate)
    return found, issues


def _is_excluded(path: str, excluded_directories: list[str]) -> bool:
    return any(path == excluded or path.startswith(excluded + "/") for excluded in excluded_directories)


def _file_sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _git_blob_id(path: Path, hex_length: int) -> str:
    algorithm = "sha1" if hex_length == 40 else "sha256"
    data_length = path.stat().st_size
    digest = hashlib.new(algorithm)
    digest.update(f"blob {data_length}\0".encode("ascii"))
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def sync_modules(root: Path) -> list[str]:
    """Create/update module rows from source-lock, preserving unchanged review."""
    source_files, _, _ = _source_lock(root)
    tracking_path = root / "tracking" / "modules.json"
    old_rows: dict[str, dict[str, Any]] = {}
    if tracking_path.exists():
        old_doc = _read_json(tracking_path)
        if not isinstance(old_doc, dict) or not isinstance(old_doc.get("modules"), list):
            raise CoverageError("tracking/modules.json must contain a modules list")
        for row in old_doc["modules"]:
            if isinstance(row, dict) and isinstance(row.get("path"), str):
                old_rows[row["path"]] = row

    rows: list[dict[str, Any]] = []
    for path in sorted(source_files):
        source = source_files[path]
        old = old_rows.get(path, {})
        unchanged = old.get("sha256") == source["sha256"] and old.get("component") == source["component"]
        if unchanged:
            row = dict(old)
        else:
            row = {
                "path": path,
                "component": source["component"],
                "sha256": source["sha256"],
                "scope": "whole_module",
                "decomposition_status": "pending",
                "status": "Not ported",
                "lean_definitions": [],
                "tests": [],
                "specifications": [],
                "proofs": [],
            }
        row["path"] = path
        row["component"] = source["component"]
        row["sha256"] = source["sha256"]
        row["scope"] = "whole_module"
        row.setdefault("decomposition_status", "pending")
        rows.append(row)
    _write_json(tracking_path, {"schema_version": 1, "modules": rows})

    feature_path = root / "tracking" / "features.json"
    if not feature_path.exists():
        _write_json(feature_path, {"schema_version": 1, "features": []})
    exclusion_path = root / "tracking" / "exclusions.json"
    if not exclusion_path.exists():
        _write_json(exclusion_path, {"schema_version": 1, "exclusions": []})
    return [path for path in sorted(source_files) if path not in old_rows]


def _validate_evidence(root: Path, owner: str, record: dict[str, Any], issues: list[str]) -> None:
    status = record.get("status")
    if status not in STATUSES:
        issues.append(f"{owner}: invalid status {status!r}")
        return
    for field, label in (("lean_definitions", "Lean definition"), ("tests", "test"),
                         ("specifications", "specification"), ("proofs", "proof")):
        links = record.get(field, [])
        if not isinstance(links, list) or any(not isinstance(link, str) for link in links):
            issues.append(f"{owner}: {field} must be a list of paths")
            continue
        if field in STATUS_EVIDENCE[status] and not links:
            issues.append(f"{owner}: status {status!r} requires at least one {label} link")
        for link in links:
            try:
                safe_link = _safe_repo_path(link, f"{owner} {field} link")
            except CoverageError as exc:
                issues.append(str(exc))
                continue
            if safe_link.startswith("upstream/"):
                issues.append(f"{owner}: evidence must point to project code or tests, not upstream source: {safe_link}")
            if Path(safe_link).suffix not in EVIDENCE_EXTENSIONS[field]:
                issues.append(f"{owner}: {field} evidence has unsupported file type: {safe_link}")
            if field == "tests" and not safe_link.startswith(("tests/", "MiriTests/")):
                issues.append(f"{owner}: test evidence must be under tests/ or MiriTests/: {safe_link}")
            if not (root / safe_link).is_file():
                issues.append(f"{owner}: linked evidence file does not exist: {safe_link}")


def validate(root: Path) -> tuple[list[str], dict[str, int]]:
    issues: list[str] = []
    source_files, coverage_roots, expected_rust = _source_lock(root)
    exclusion_doc = _read_json(root / "tracking" / "exclusions.json")
    raw_exclusions = exclusion_doc.get("exclusions", []) if isinstance(exclusion_doc, dict) else []
    excluded_directories: list[str] = []
    if isinstance(raw_exclusions, list):
        for exclusion in raw_exclusions:
            if isinstance(exclusion, dict) and exclusion.get("scope") == "directory":
                try:
                    excluded_directories.append(_safe_repo_path(exclusion.get("path"), "directory exclusion path"))
                except CoverageError:
                    pass
    found, scan_issues = _scan_roots(root, coverage_roots, excluded_directories)
    issues.extend(scan_issues)

    for rel, expected_count in sorted(expected_rust.items()):
        target = root / rel
        if not target.exists():
            continue
        if target.is_file():
            actual_count = int(target.suffix == ".rs" and not _is_excluded(rel, excluded_directories))
        elif target.is_dir():
            actual_count = sum(
                1 for path in target.rglob("*.rs")
                if path.is_file() and not _is_excluded(path.relative_to(root).as_posix(), excluded_directories)
            )
        else:
            continue
        if actual_count != expected_count:
            issues.append(f"Rust module count for coverage root {rel}: expected {expected_count}, found {actual_count}")

    for path in sorted(found - set(source_files)):
        issues.append(f"unlocked source file under coverage roots: {path}")
    for path in sorted(set(source_files) - found):
        issues.append(f"locked source is absent from coverage roots: {path}")
    for path, source in sorted(source_files.items()):
        digest = source["sha256"]
        if digest is None:
            issues.append(f"source-lock has no content SHA256 yet: {path}")
            continue
        local = root / path
        if not local.is_file():
            issues.append(f"locked Rust source file is missing: {path}")
        else:
            if _file_sha256(local) != digest:
                issues.append(f"source SHA256 mismatch: {path}")
            if _git_blob_id(local, len(source["git_blob"])) != source["git_blob"]:
                issues.append(f"source Git blob mismatch: {path}")

    module_doc = _read_json(root / "tracking" / "modules.json")
    if not isinstance(module_doc, dict) or module_doc.get("schema_version") != 1 or not isinstance(module_doc.get("modules"), list):
        raise CoverageError("tracking/modules.json must have schema_version 1 and a modules list")
    module_rows: dict[str, dict[str, Any]] = {}
    for i, row in enumerate(module_doc["modules"]):
        if not isinstance(row, dict):
            issues.append(f"tracking/modules.json modules[{i}] must be an object")
            continue
        try:
            path = _safe_repo_path(row.get("path"), f"module row {i} path")
        except CoverageError as exc:
            issues.append(str(exc))
            continue
        if path in module_rows:
            issues.append(f"duplicate module inventory path: {path}")
        module_rows[path] = row
    if not module_rows:
        issues.append("module inventory is empty; coverage cannot pass vacuously")
    for path in sorted(set(source_files) - set(module_rows)):
        issues.append(f"source unit omitted from tracking/modules.json: {path}")
    for path in sorted(set(module_rows) - set(source_files)):
        issues.append(f"tracked source unit is absent from upstream/source-lock.json: {path}")
    for path in sorted(set(source_files) & set(module_rows)):
        row = module_rows[path]
        source = source_files[path]
        if row.get("scope") != "whole_module":
            issues.append(f"{path}: module status scope must be whole_module; track partial work as feature obligations")
        decomposition_status = row.get("decomposition_status")
        if decomposition_status not in ("pending", "reviewed"):
            issues.append(f"{path}: decomposition_status must be pending or reviewed")
        if row.get("status") != "Not ported" and decomposition_status != "reviewed":
            issues.append(f"{path}: whole-module status requires reviewed decomposition")
        if row.get("component") != source["component"]:
            issues.append(f"module component differs from source-lock: {path}")
        if row.get("sha256") != source["sha256"]:
            issues.append(f"module SHA256 differs from source-lock: {path}")
        if row.get("status") not in STATUSES:
            issues.append(f"{path}: invalid status {row.get('status')!r}")
        else:
            _validate_evidence(root, path, row, issues)

    feature_doc = _read_json(root / "tracking" / "features.json")
    if not isinstance(feature_doc, dict) or feature_doc.get("schema_version") != 1 or not isinstance(feature_doc.get("features"), list):
        raise CoverageError("tracking/features.json must have schema_version 1 and a features list")
    features = feature_doc["features"]
    if not features:
        issues.append("feature obligation inventory is empty; semantic coverage cannot pass vacuously")
    feature_ids: set[str] = set()
    feature_modules: set[str] = set()
    semantic_feature_count = 0
    for i, feature in enumerate(features):
        if not isinstance(feature, dict):
            issues.append(f"feature row {i} must be an object")
            continue
        feature_id = feature.get("id")
        if not isinstance(feature_id, str) or not feature_id.strip():
            issues.append(f"feature row {i} needs a non-empty id")
        elif feature_id in feature_ids:
            issues.append(f"duplicate feature id: {feature_id}")
        else:
            feature_ids.add(feature_id)
        if not isinstance(feature.get("description"), str) or not feature["description"].strip():
            issues.append(f"feature {feature_id or i}: needs a concrete description")
        members = feature.get("source_modules")
        if not isinstance(members, list) or not members:
            issues.append(f"feature {feature_id or i}: source_modules must be a non-empty list")
            members = []
        for member in members:
            try:
                path = _safe_repo_path(member, f"feature {feature_id or i} source module")
            except CoverageError as exc:
                issues.append(str(exc))
                continue
            if path not in source_files:
                issues.append(f"feature {feature_id or i}: unknown source module {path}")
            feature_modules.add(path)
        kind = feature.get("kind")
        if kind not in ("semantic_feature", "module_decomposition"):
            issues.append(f"feature {feature_id or i}: kind must be semantic_feature or module_decomposition")
        refs = feature.get("source_refs")
        referenced_modules: set[str] = set()
        if kind == "semantic_feature":
            semantic_feature_count += 1
            if not isinstance(refs, list) or not refs:
                issues.append(f"feature {feature_id or i}: source_refs must identify at least one upstream symbol")
                refs = []
        elif kind == "module_decomposition":
            if refs not in (None, []):
                issues.append(f"feature {feature_id or i}: module_decomposition rows must not claim a specific symbol")
            refs = []
            if feature.get("decomposition_status") != "pending":
                issues.append(f"feature {feature_id or i}: module_decomposition must be explicitly pending")
            if feature.get("status") != "Not ported":
                issues.append(f"feature {feature_id or i}: pending module decomposition must stay Not ported")
        for ref_index, ref in enumerate(refs):
            ref_owner = f"feature {feature_id or i} source_refs[{ref_index}]"
            if not isinstance(ref, dict):
                issues.append(f"{ref_owner} must be an object")
                continue
            try:
                ref_path = _safe_repo_path(ref.get("path"), f"{ref_owner}.path")
            except CoverageError as exc:
                issues.append(str(exc))
                continue
            if ref_path not in source_files:
                issues.append(f"{ref_owner}: unknown source module {ref_path}")
                continue
            referenced_modules.add(ref_path)
            symbol = ref.get("symbol")
            if not isinstance(symbol, str) or not symbol.strip():
                issues.append(f"{ref_owner}: symbol must identify the function, variant, or rule under review")
            line = ref.get("line")
            if not isinstance(line, int) or isinstance(line, bool) or line < 1:
                issues.append(f"{ref_owner}: line must be a positive integer")
            else:
                source_path = root / ref_path
                if source_path.is_file():
                    line_count = len(source_path.read_text(encoding="utf-8").splitlines())
                    if line > line_count:
                        issues.append(f"{ref_owner}: line {line} is past end of {ref_path} ({line_count} lines)")
            if ref.get("source_sha256") != source_files[ref_path]["sha256"]:
                issues.append(f"{ref_owner}: source_sha256 differs from source-lock for {ref_path}")
        if kind == "semantic_feature" and referenced_modules != set(members):
            issues.append(f"feature {feature_id or i}: source_modules must exactly match paths in source_refs")
        _validate_evidence(root, f"feature {feature_id or i}", feature, issues)

    if semantic_feature_count == 0:
        issues.append("no semantic feature obligations have been reviewed; module placeholders do not establish semantic coverage")

    if not isinstance(exclusion_doc, dict) or exclusion_doc.get("schema_version") != 1 or not isinstance(exclusion_doc.get("exclusions"), list):
        raise CoverageError("tracking/exclusions.json must have schema_version 1 and an exclusions list")
    exclusions: set[str] = set()
    exclusion_paths: set[str] = set()
    for i, exclusion in enumerate(exclusion_doc["exclusions"]):
        if not isinstance(exclusion, dict):
            issues.append(f"exclusion row {i} must be an object")
            continue
        try:
            path = _safe_repo_path(exclusion.get("path"), f"exclusion row {i} path")
        except CoverageError as exc:
            issues.append(str(exc))
            continue
        if path in exclusion_paths:
            issues.append(f"duplicate exclusion: {path}")
        exclusion_paths.add(path)
        scope = exclusion.get("scope", "file")
        if scope == "file":
            if path not in source_files:
                issues.append(f"exclusion refers to unknown source module: {path}")
            exclusions.add(path)
        elif scope == "directory":
            if not (root / path).is_dir():
                issues.append(f"directory exclusion does not name an existing directory: {path}")
            if any(source_path == path or source_path.startswith(path + "/") for source_path in source_files):
                issues.append(f"directory exclusion contains locked source units and would hide tracked code: {path}")
        else:
            issues.append(f"exclusion {path}: scope must be file or directory")
        if not isinstance(exclusion.get("reason"), str) or not exclusion["reason"].strip():
            issues.append(f"exclusion {path}: needs a specific reason")
        if exclusion.get("reviewed") is not True:
            issues.append(f"exclusion {path}: not reviewed")
        if not isinstance(exclusion.get("reviewed_by"), str) or not exclusion["reviewed_by"].strip():
            issues.append(f"exclusion {path}: needs reviewed_by")
    for path in sorted(set(source_files) - feature_modules - exclusions):
        row = module_rows.get(path, {})
        if row.get("decomposition_status") != "pending":
            issues.append(f"source module has no feature obligation or reviewed exclusion: {path}")

    module_counts = Counter(row.get("status") for row in module_rows.values())
    feature_counts = Counter(
        feature.get("status") for feature in features if isinstance(feature, dict)
    )
    counts = {status: module_counts.get(status, 0) for status in STATUSES}
    counts.update({f"feature:{status}": feature_counts.get(status, 0) for status in STATUSES})
    counts.update({"features": len(features), "exclusions": len(exclusion_paths), "modules": len(module_rows)})
    return issues, counts


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("sync", "check", "report"))
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parent.parent,
                        help="repository root (defaults to the directory containing tools/)")
    args = parser.parse_args(argv)
    root = args.root.resolve()
    try:
        if args.command == "sync":
            new = sync_modules(root)
            print(f"Synchronized module inventory; added {len(new)} source module(s).")
            return 0
        issues, counts = validate(root)
        if args.command == "report":
            print(json.dumps({"counts": counts, "issues": issues}, indent=2, sort_keys=True))
            return 1 if issues else 0
        print("Module status counts: " + ", ".join(f"{key}={counts[key]}" for key in STATUSES))
        print("Feature status counts: " + ", ".join(f"{key}={counts[f'feature:{key}']}" for key in STATUSES))
        print(f"Feature obligations={counts['features']}; reviewed exclusions={counts['exclusions']}")
        for issue in issues:
            print(f"ERROR: {issue}", file=sys.stderr)
        if issues:
            print(f"Coverage validation failed with {len(issues)} issue(s).", file=sys.stderr)
            return 1
        print("Coverage records match the pinned source tree and all links resolve.")
        return 0
    except CoverageError as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
