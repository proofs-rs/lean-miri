#!/usr/bin/env python3
"""Generate conservative, syntax-backed per-symbol source obligations.

AST-discovered rows start Not ported. This tool records source identity and
syntax facts; it never infers that a Rust function or enum variant is ported.
"""

from __future__ import annotations

import argparse
import gzip
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
from typing import Any


if __package__:
    from .tracker_io import TrackerIOError, read_json, write_json
else:
    from tracker_io import TrackerIOError, read_json, write_json


AST_ORIGIN = "syn-ast-v1"
AST_SCHEMA = "syn-ast-inventory-v1"
FEATURE_GENERATED_FIELDS = {
    "id", "kind", "description", "source_modules", "source_refs", "status",
    "lean_definitions", "tests", "specifications", "proofs", "origin",
    "ast_kind", "ast_evidence",
}
EVIDENCE_FIELDS = ("lean_definitions", "tests", "specifications", "proofs")


class FeatureUpdateError(Exception):
    pass


def _json_bytes(value: Any, *, indent: int | None = 2) -> bytes:
    return (json.dumps(value, ensure_ascii=False, indent=indent, sort_keys=True) + "\n").encode("utf-8")


def load_inventory(path: Path) -> dict[str, Any]:
    try:
        raw = path.read_bytes()
    except OSError as exc:
        raise FeatureUpdateError(f"cannot read AST inventory {path}: {exc}") from exc
    try:
        contents = gzip.decompress(raw) if raw.startswith(b"\x1f\x8b") else raw
        inventory = json.loads(contents)
    except (OSError, EOFError, gzip.BadGzipFile, json.JSONDecodeError) as exc:
        raise FeatureUpdateError(f"invalid AST inventory {path}: {exc}") from exc
    if not isinstance(inventory, dict):
        raise FeatureUpdateError("AST inventory must contain a JSON object")
    return inventory


def _sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def validate_inventory(root: Path, inventory: dict[str, Any]) -> dict[str, dict[str, Any]]:
    if inventory.get("schema_version") != 1:
        raise FeatureUpdateError("AST inventory schema_version must be 1")
    analyzer = inventory.get("analyzer")
    if not isinstance(analyzer, dict) or analyzer.get("schema") != AST_SCHEMA:
        raise FeatureUpdateError(f"AST inventory must use analyzer schema {AST_SCHEMA}")
    if analyzer.get("syn_version") != "2.0.108":
        raise FeatureUpdateError("AST inventory syn version differs from the pinned analyzer")
    for field, relative in (
        ("manifest_sha256", "tools/source-analysis/Cargo.toml"),
        ("cargo_lock_sha256", "tools/source-analysis/Cargo.lock"),
        ("source_sha256", "tools/source-analysis/src/main.rs"),
    ):
        analyzer_file = root / relative
        if not analyzer_file.is_file() or analyzer.get(field) != _sha256(analyzer_file):
            raise FeatureUpdateError(f"AST inventory is stale: analyzer input changed: {relative}")

    lock_path = root / "upstream/source-lock.json"
    try:
        lock_bytes = lock_path.read_bytes()
        lock = json.loads(lock_bytes)
    except (OSError, json.JSONDecodeError) as exc:
        raise FeatureUpdateError(f"cannot read upstream/source-lock.json: {exc}") from exc
    expected_lock_hash = hashlib.sha256(lock_bytes).hexdigest()
    source_lock = inventory.get("source_lock")
    if not isinstance(source_lock, dict) or source_lock.get("sha256") != expected_lock_hash:
        raise FeatureUpdateError("AST inventory is stale: upstream/source-lock.json SHA256 changed; refresh it")

    locked_files = {
        item["path"]: item for item in lock.get("files", [])
        if isinstance(item, dict) and isinstance(item.get("path"), str) and item["path"].endswith(".rs")
    }
    source_files = inventory.get("source_files")
    if not isinstance(source_files, list):
        raise FeatureUpdateError("AST inventory source_files must be a list")
    source_by_path: dict[str, dict[str, Any]] = {}
    for row in source_files:
        if not isinstance(row, dict) or not isinstance(row.get("path"), str):
            raise FeatureUpdateError("AST inventory contains an invalid source_files row")
        path = row["path"]
        if path in source_by_path:
            raise FeatureUpdateError(f"AST inventory contains duplicate source file: {path}")
        source_by_path[path] = row
        if row.get("parsed") is not True:
            raise FeatureUpdateError(f"AST file did not parse: {path}: {row.get('parse_error')}")
        locked = locked_files.get(path)
        if locked is None:
            raise FeatureUpdateError(f"AST inventory contains a source outside source-lock: {path}")
        expected = locked.get("sha256")
        if row.get("source_sha256") != expected:
            raise FeatureUpdateError(f"AST source hash differs from source-lock: {path}")
        local = root / path
        if not local.is_file():
            raise FeatureUpdateError(f"AST source file is missing: {path}")
        if _sha256(local) != expected:
            raise FeatureUpdateError(f"AST inventory is stale: source contents changed: {path}")
    if set(source_by_path) != set(locked_files):
        missing = sorted(set(locked_files) - set(source_by_path))
        extra = sorted(set(source_by_path) - set(locked_files))
        raise FeatureUpdateError(f"AST inventory Rust-file set differs from source-lock (missing={missing[:4]}, extra={extra[:4]})")
    return source_by_path


def _feature_id(kind: str, path: str, symbol: str, line: int) -> str:
    identity = "\0".join((AST_ORIGIN, kind, path, symbol, str(line))).encode("utf-8")
    return f"ast:{kind}:{hashlib.sha256(identity).hexdigest()[:20]}"


def _base_feature(path: str, component: str, source_sha256: str, kind: str,
                  symbol: str, line: int, ast_evidence: dict[str, Any]) -> dict[str, Any]:
    label = {
        "rust_function_body": "function or method",
        "enum_variant": "enum variant",
    }[kind]
    description = (
        f"AST-discovered {label} `{symbol}` requires semantic review of its behavior and dependencies; "
        "this row records syntax only and makes no port-completion claim."
    )
    return {
        "id": _feature_id(kind, path, symbol, line),
        "kind": "semantic_feature",
        "description": description,
        "source_modules": [path],
        "source_refs": [{
            "path": path,
            "symbol": symbol,
            "line": line,
            "source_sha256": source_sha256,
        }],
        "status": "Not ported",
        "lean_definitions": [],
        "tests": [],
        "specifications": [],
        "proofs": [],
        "origin": AST_ORIGIN,
        "ast_kind": kind,
        "ast_evidence": ast_evidence,
    }


def build_ast_features(inventory: dict[str, Any], source_by_path: dict[str, dict[str, Any]] | None = None) -> list[dict[str, Any]]:
    """Turn function/method bodies and enum variants into Not ported obligations."""
    if source_by_path is None:
        rows = inventory.get("source_files")
        if not isinstance(rows, list):
            raise FeatureUpdateError("AST inventory source_files must be a list")
        source_by_path = {row["path"]: row for row in rows if isinstance(row, dict) and isinstance(row.get("path"), str)}

    generated: list[dict[str, Any]] = []
    for symbol in inventory.get("symbols", []):
        if not isinstance(symbol, dict) or symbol.get("kind") not in ("function", "method", "trait_method"):
            continue
        path = symbol.get("path")
        name = symbol.get("symbol")
        span = symbol.get("span")
        if not isinstance(path, str) or not isinstance(name, str) or not isinstance(span, dict):
            raise FeatureUpdateError("AST function symbol lacks path, symbol, or source span")
        source = source_by_path.get(path)
        if source is None:
            raise FeatureUpdateError(f"AST function references unknown source file: {path}")
        line = span.get("line")
        if not isinstance(line, int) or isinstance(line, bool) or line < 1:
            raise FeatureUpdateError(f"AST function has invalid source line: {path}:{line}")
        evidence = {
            "span": span,
            "has_body": symbol.get("has_body"),
            "body_span": symbol.get("body_span"),
            "body_token_sha256": symbol.get("body_token_sha256"),
            "owner": symbol.get("owner"),
            "machine_context": bool(symbol.get("machine_context")),
            "machine_hook_candidate": bool(symbol.get("machine_hook_candidate")),
        }
        generated.append(_base_feature(path, source.get("component", ""), source["source_sha256"],
                                       "rust_function_body", name, line, evidence))

    for variant in inventory.get("enum_variants", []):
        if not isinstance(variant, dict):
            raise FeatureUpdateError("AST enum_variants contains a non-object row")
        path = variant.get("path")
        name = variant.get("symbol")
        span = variant.get("span")
        if not isinstance(path, str) or not isinstance(name, str) or not isinstance(span, dict):
            raise FeatureUpdateError("AST enum variant lacks path, symbol, or source span")
        source = source_by_path.get(path)
        if source is None:
            raise FeatureUpdateError(f"AST enum variant references unknown source file: {path}")
        line = span.get("line")
        if not isinstance(line, int) or isinstance(line, bool) or line < 1:
            raise FeatureUpdateError(f"AST enum variant has invalid source line: {path}:{line}")
        evidence = {
            "span": span,
            "enum_name": variant.get("enum_name"),
            "enum_category": variant.get("enum_category"),
            "shape": variant.get("shape"),
            "fields": variant.get("fields", []),
        }
        generated.append(_base_feature(path, source.get("component", ""), source["source_sha256"],
                                       "enum_variant", name, line, evidence))

    generated.sort(key=lambda feature: (
        feature["source_modules"][0], feature["source_refs"][0]["line"],
        feature["ast_kind"], feature["source_refs"][0]["symbol"],
    ))
    ids = [feature["id"] for feature in generated]
    if len(ids) != len(set(ids)):
        raise FeatureUpdateError("AST obligation ID collision")
    return generated


def merge_features(existing: list[dict[str, Any]], generated: list[dict[str, Any]]) -> tuple[list[dict[str, Any]], dict[str, int]]:
    manual: list[dict[str, Any]] = []
    old_ast: dict[str, dict[str, Any]] = {}
    ids: set[str] = set()
    for feature in existing:
        if not isinstance(feature, dict) or not isinstance(feature.get("id"), str):
            raise FeatureUpdateError("existing feature rows must be objects with string ids")
        if feature["id"] in ids:
            raise FeatureUpdateError(f"duplicate existing feature id: {feature['id']}")
        ids.add(feature["id"])
        if feature.get("origin") == AST_ORIGIN:
            old_ast[feature["id"]] = feature
        else:
            manual.append(feature)

    generated_ids = {feature["id"] for feature in generated}
    collision = generated_ids & {feature["id"] for feature in manual}
    if collision:
        raise FeatureUpdateError(f"generated AST feature collides with manual feature id: {sorted(collision)[0]}")

    merged_ast: list[dict[str, Any]] = []
    preserved_rows = 0
    reset = 0
    for fresh in generated:
        previous = old_ast.get(fresh["id"])
        result = dict(fresh)
        if previous is not None:
            same_source = previous.get("source_refs") == fresh.get("source_refs")
            same_ast = previous.get("ast_kind") == fresh.get("ast_kind") and previous.get("ast_evidence") == fresh.get("ast_evidence")
            if same_source and same_ast:
                for field in ("status", *EVIDENCE_FIELDS):
                    if field in previous:
                        result[field] = previous[field]
                for key, value in previous.items():
                    if key not in FEATURE_GENERATED_FIELDS:
                        result[key] = value
                preserved_rows += 1
            else:
                reset += int(previous.get("status", "Not ported") != "Not ported")
        merged_ast.append(result)

    stale = [row for key, row in old_ast.items() if key not in generated_ids]
    stale_reviewed = [row.get("id") for row in stale if row.get("status", "Not ported") != "Not ported"]
    if stale_reviewed:
        raise FeatureUpdateError(
            "AST symbols with advanced status disappeared or moved; reconcile before removing: "
            + ", ".join(stale_reviewed[:5])
        )
    merged = [*manual, *merged_ast]
    stats = {
        "manual_features": len(manual),
        "generated_features": len(merged_ast),
        "new_features": sum(feature["id"] not in old_ast for feature in merged_ast),
        "preserved_ast_rows": preserved_rows,
        "reset_ast_reviews": reset,
        "removed_stale_unreviewed": len(stale),
    }
    return merged, stats


def _subsystem(component: str, path: str) -> str:
    normalized = path.lower()
    if component.startswith("rustc_const_eval"):
        return "rustc_interpreter"
    if component == "rustc_middle_mir":
        return "rustc_mir"
    if component.startswith("rustc_target") or component == "rustc_abi" or component == "rustc_middle_ty_layout":
        return "rustc_abi_layout_target"
    if "/borrow_tracker/" in normalized or "/tree_borrows/" in normalized or "/stacked_borrows/" in normalized:
        return "miri_borrow_tracking"
    if any(part in normalized for part in ("/concurrency/", "/thread/", "/data_race/", "/sync/")):
        return "miri_concurrency"
    if "/intrinsics/" in normalized:
        return "miri_intrinsics"
    if "/shims/" in normalized:
        return "miri_shims"
    if "/machine/" in normalized:
        return "miri_machine"
    if any(part in normalized for part in ("/memory/", "/alloc/", "/allocation/")):
        return "miri_memory_allocation"
    if any(part in normalized for part in ("/eval/", "/mir/")):
        return "miri_interpreter"
    if component == "miri":
        return "miri_other"
    return component


def _source_ref(record: dict[str, Any], source_by_path: dict[str, dict[str, Any]],
                symbol: str | None = None, syntax: str | None = None) -> dict[str, Any]:
    path = record.get("path")
    source = source_by_path.get(path) if isinstance(path, str) else None
    span = record.get("span")
    if not isinstance(path, str) or source is None or not isinstance(span, dict):
        raise FeatureUpdateError(f"dependency graph record lacks a locked source location: {record.get('id')}")
    result: dict[str, Any] = {
        "id": record.get("id"),
        "path": path,
        "component": record.get("component", source.get("component", "")),
        "source_sha256": source["source_sha256"],
        "line": span.get("line"),
        "column": span.get("column"),
        "end_line": span.get("end_line"),
        "end_column": span.get("end_column"),
    }
    if symbol is not None:
        result["symbol"] = symbol
    if syntax is not None:
        result["syntax"] = syntax
    return result


def _dependency_id(kind: str, subsystem: str, target: str, resolution: str = "") -> str:
    data = "\0".join(("dependency-v1", kind, subsystem, target, resolution)).encode("utf-8")
    return f"dep:{hashlib.sha256(data).hexdigest()[:24]}"


def _path_segments(path: str) -> list[str]:
    return [part.strip() for part in path.split("::") if part.strip()]


def _normalized_symbol_segments(symbol: str) -> list[str]:
    result = []
    for segment in _path_segments(symbol):
        if segment.startswith("mod "):
            segment = segment[4:]
        result.append(segment)
    return result


def _selected_crate_namespaces(source_by_path: dict[str, dict[str, Any]]) -> set[str]:
    namespaces: set[str] = set()
    for source in source_by_path.values():
        component = source.get("component", "")
        if component == "miri":
            namespaces.add("miri")
        elif component.startswith("rustc_"):
            candidates = ("rustc_const_eval", "rustc_middle", "rustc_target", "rustc_abi", "rustc_apfloat")
            match = next((name for name in candidates if component == name or component.startswith(name + "_")), None)
            if match is not None:
                namespaces.add(match)
    return namespaces


def _namespace_resolution(target: str, candidate_count: int, selected_namespaces: set[str] | None = None) -> str:
    if candidate_count:
        return "selected_source_name_candidates_not_name_resolved"
    first = _path_segments(target)[:1]
    namespace = first[0] if first else ""
    if selected_namespaces and namespace in selected_namespaces:
        return "pinned_component_path_unresolved"
    if namespace.startswith("rustc_"):
        return "rustc_private_or_unselected_component"
    if namespace in {"std", "core", "alloc", "proc_macro"}:
        return "standard_library_unresolved"
    if namespace in {"crate", "self", "super"}:
        return "selected_relative_path_unresolved"
    return "third_party_or_unselected_source_unresolved"


def build_dependency_inventory(inventory: dict[str, Any], source_by_path: dict[str, dict[str, Any]]) -> dict[str, Any]:
    """Build a location-preserving candidate graph; edges are never semantic coverage claims."""
    symbols = inventory.get("symbols", [])
    selected_namespaces = _selected_crate_namespaces(source_by_path)
    symbol_by_id = {row.get("id"): row for row in symbols if isinstance(row, dict)}
    defs_by_name: dict[str, list[dict[str, Any]]] = {}
    symbols_by_name: dict[Any, list[dict[str, Any]]] = {}
    callable_kinds = {"function", "method", "trait_method"}
    for symbol in symbols:
        if not isinstance(symbol, dict):
            raise FeatureUpdateError("symbols contains a non-object row")
        symbols_by_name.setdefault(symbol.get("name"), []).append(symbol)
        if symbol.get("kind") in callable_kinds:
            defs_by_name.setdefault(symbol.get("name", ""), []).append(symbol)
    for candidates in defs_by_name.values():
        candidates.sort(key=lambda row: row["id"])

    groups: dict[tuple[str, str, str, str], dict[str, Any]] = {}

    def add_group(kind: str, subsystem: str, target: str, resolution: str,
                  site: dict[str, Any], candidate_records: list[dict[str, Any]], basis: str,
                  syntax: str | None = None) -> None:
        key = (subsystem, kind, target, resolution)
        group = groups.get(key)
        if group is None:
            group = {
                "id": _dependency_id(kind, subsystem, target, resolution),
                "kind": kind,
                "subsystem": subsystem,
                "target": target,
                "resolution": resolution,
                "basis": basis,
                "source_refs": [],
                "candidate_refs": [],
                "review_status": "pending",
                "review_note": "",
            }
            groups[key] = group
        ref = _source_ref(site, source_by_path, site.get("enclosing_symbol") or site.get("symbol") or target, syntax)
        group["source_refs"].append(ref)
        for candidate in candidate_records:
            group["candidate_refs"].append(_source_ref(candidate, source_by_path,
                                                        candidate.get("symbol") or candidate.get("name")))

    for call in inventory.get("call_sites", []):
        if not isinstance(call, dict):
            raise FeatureUpdateError("call_sites contains a non-object row")
        candidates = defs_by_name.get(call.get("terminal_name"), []) if call.get("terminal_name") else []
        target = call.get("callee_path") or call.get("callee") or "<indirect-call>"
        if call.get("kind") == "method_call":
            resolution = "trait_or_inherent_method_dispatch_unresolved"
            basis = "receiver-bearing method syntax; candidate methods are same-name only and Rust dispatch is unresolved"
        elif call.get("callee_path"):
            call_segments = _path_segments(call["callee_path"])
            exact = []
            for candidate in candidates:
                candidate_segments = _normalized_symbol_segments(candidate.get("symbol", ""))
                if call_segments and len(candidate_segments) >= len(call_segments) and candidate_segments[-len(call_segments):] == call_segments:
                    exact.append(candidate)
            if exact:
                candidates = exact
                resolution = "qualified_path_suffix_candidates_not_name_resolved"
                basis = "explicit syntax path suffix matches a selected symbol; this is not Rust name/type resolution"
            else:
                resolution = _namespace_resolution(call["callee_path"], len(candidates), selected_namespaces)
                basis = "explicit call path retained; selected same-name candidates are not a resolved edge"
        elif call.get("terminal_name"):
            resolution = _namespace_resolution(call["callee"], len(candidates), selected_namespaces)
            basis = "terminal identifier candidates only; Rust name/type resolution is not performed"
        else:
            resolution = "indirect_call_target_unresolved"
            basis = "callee is not a direct path or method syntax"
        subsystem = _subsystem(call.get("component", ""), call.get("path", ""))
        add_group(call.get("kind", "call"), subsystem, target, resolution, call, candidates, basis, call.get("callee"))

    for imported in inventory.get("imports", []):
        if not isinstance(imported, dict):
            raise FeatureUpdateError("imports contains a non-object row")
        target = imported.get("imported_path", "<unknown-import>")
        terminal = imported.get("terminal_name")
        candidates = symbols_by_name.get(terminal, []) if terminal else []
        if imported.get("is_glob"):
            candidates = []
        resolution = _namespace_resolution(target, len(candidates), selected_namespaces)
        if imported.get("is_glob") and resolution.startswith("selected_source"):
            resolution = "glob_import_unresolved"
        subsystem = _subsystem(imported.get("component", ""), imported.get("path", ""))
        add_group("import", subsystem, target, resolution, imported, candidates,
                  "import path and terminal-name candidates only; aliases, glob contents, privacy and Rust resolution are not inferred",
                  target)

    macro_sites = inventory.get("macro_sites", [])
    definitions_by_name: dict[str, list[dict[str, Any]]] = {}
    for site in macro_sites:
        if site.get("site_kind") == "definition":
            definitions_by_name.setdefault(site.get("macro_name", ""), []).append(site)
    for site in macro_sites:
        if site.get("site_kind") != "invocation":
            continue
        target = site.get("macro_path", "<unknown-macro>")
        candidates = definitions_by_name.get(site.get("macro_name"), [])
        if candidates:
            resolution = "selected_macro_definition_candidates_not_expanded"
        else:
            resolution = "macro_expansion_or_external_macro_unresolved"
        subsystem = _subsystem(site.get("component", ""), site.get("path", ""))
        add_group("macro_invocation", subsystem, target, resolution, site, candidates,
                  "source macro invocation; macro expansion, proc macros and generated code are not analyzed",
                  site.get("classification"))

    matches_by_id = {row.get("id"): row for row in inventory.get("match_arms", []) if isinstance(row, dict)}
    variants_by_id = {row.get("id"): row for row in inventory.get("enum_variants", []) if isinstance(row, dict)}
    dispatch_rows = {row.get("variant_id"): row for row in inventory.get("mir_variant_dispatch_candidates", [])}
    for variant_id, variant in variants_by_id.items():
        if not str(variant.get("enum_category", "")).startswith("mir_"):
            continue
        dispatch = dispatch_rows.get(variant_id, {})
        candidate_arms = [matches_by_id[arm_id] for arm_id in dispatch.get("match_arm_ids", []) if arm_id in matches_by_id]
        entry = {
            "id": _dependency_id("mir_enum_variant_dispatch", variant.get("component", ""), variant.get("symbol", variant_id),
                                 "candidate_match_arms_present_requires_semantic_review" if candidate_arms else "no_syntactic_match_arm_candidate_found"),
            "kind": "mir_enum_variant_dispatch",
            "subsystem": _subsystem(variant.get("component", ""), variant.get("path", "")),
            "target": variant.get("symbol"),
            "resolution": "candidate_match_arms_present_requires_semantic_review" if candidate_arms else "no_syntactic_match_arm_candidate_found",
            "basis": "same-name match pattern relation only; wildcard arms, if-let, macro expansion, reachability and semantic handling are not established",
            "source_refs": [_source_ref(variant, source_by_path, variant.get("symbol"), variant.get("enum_category"))],
            "candidate_refs": [_source_ref(arm, source_by_path, arm.get("pattern"), arm.get("scrutinee")) for arm in candidate_arms],
            "review_status": "pending",
            "review_note": "",
        }
        groups[(entry["subsystem"], entry["kind"], entry["target"], entry["resolution"])] = entry

    for hook in inventory.get("machine_hook_candidates", []):
        if not isinstance(hook, dict):
            raise FeatureUpdateError("machine_hook_candidates contains a non-object row")
        trait_method = symbol_by_id.get(hook.get("trait_method_id"))
        if trait_method is None:
            raise FeatureUpdateError(f"Machine hook references missing trait method: {hook.get('trait_method_id')}")
        impls = [symbol_by_id[item] for item in hook.get("implementation_candidate_ids", []) if item in symbol_by_id]
        resolution = ("name_matched_impl_candidates" if impls else
                      "default_method_no_selected_override_candidate" if hook.get("has_default_body") else
                      "required_hook_no_selected_impl_candidate_found")
        entry = {
            "id": _dependency_id("machine_trait_hook", trait_method.get("component", ""), trait_method.get("symbol", ""),
                                 resolution),
            "kind": "machine_trait_hook",
            "subsystem": _subsystem(trait_method.get("component", ""), trait_method.get("path", "")),
            "target": trait_method.get("symbol"),
            "resolution": resolution,
            "basis": "Machine trait declarations linked to impl Machine methods by equal method name only; type checking, cfg and generated impls are unresolved",
            "source_refs": [_source_ref(trait_method, source_by_path, trait_method.get("symbol"), trait_method.get("signature"))],
            "candidate_refs": [_source_ref(impl, source_by_path, impl.get("symbol"), impl.get("signature")) for impl in impls],
            "review_status": "pending",
            "review_note": "",
        }
        groups[(entry["subsystem"], entry["kind"], entry["target"], entry["resolution"])] = entry

    dependencies = list(groups.values())
    for entry in dependencies:
        for field in ("source_refs", "candidate_refs"):
            unique = {ref["id"]: ref for ref in entry[field]}
            entry[field] = sorted(unique.values(), key=lambda ref: (ref["path"], ref["line"], ref["column"], ref["id"]))
    dependencies.sort(key=lambda entry: (entry["subsystem"], entry["kind"], entry["target"], entry["resolution"]))
    resolution_counts: dict[str, int] = {}
    subsystem_counts: dict[str, int] = {}
    for entry in dependencies:
        resolution_counts[entry["resolution"]] = resolution_counts.get(entry["resolution"], 0) + 1
        subsystem_counts[entry["subsystem"]] = subsystem_counts.get(entry["subsystem"], 0) + 1
    return {
        "schema_version": 1,
        "source_lock_sha256": inventory["source_lock"]["sha256"],
        "analyzer_source_sha256": inventory["analyzer"]["source_sha256"],
        "scope": "Candidate source dependency map generated from pinned selected Rust syntax. It is an analysis aid, not a semantic dependency closure or proof of port completeness.",
        "limitations": [
            "Rust name resolution, type checking, trait solving, cfg selection, macro expansion, derive/procedural macros, include! and generated sources are not analyzed.",
            "Method calls remain dynamically dispatched candidates. Unmatched rustc_ paths are explicitly categorized as rustc-private or unselected components; other unmatched paths are kept as standard, third-party, or unselected-source obligations.",
            "MIR variant-to-match links are syntactic candidates only. They do not establish reachability, exhaustive semantic handling, or treatment under wildcard arms, if-let chains, or macro expansion.",
            "The currently pinned source roots do not include the entire Rust compiler. Parser, type checking, query construction, code generation and build infrastructure are exporter/toolchain boundary candidates, not automatically required Miri runtime semantic ports.",
            "Native C/C++ implementations and fixture inputs are outside this Rust AST graph even when their files are represented in upstream/source-lock.json; their source coverage is tracked separately.",
        ],
        "summary": {
            "dependency_groups": len(dependencies),
            "source_references": sum(len(entry["source_refs"]) for entry in dependencies),
            "candidate_references": sum(len(entry["candidate_refs"]) for entry in dependencies),
            "by_resolution": dict(sorted(resolution_counts.items())),
            "by_subsystem": dict(sorted(subsystem_counts.items())),
        },
        "dependencies": dependencies,
    }


def merge_dependency_reviews(existing: dict[str, Any] | None, generated: dict[str, Any]) -> tuple[dict[str, Any], dict[str, int]]:
    if existing is None:
        return generated, {"preserved_reviews": 0, "reset_reviews": 0, "removed_unreviewed": 0}
    if not isinstance(existing, dict) or existing.get("schema_version") != 1:
        raise FeatureUpdateError("dependency tracker must be an object with schema_version 1")
    previous_rows = existing.get("dependencies")
    if not isinstance(previous_rows, list):
        raise FeatureUpdateError("tracking/dependencies.json.gz dependencies must be a list")
    old: dict[str, dict[str, Any]] = {}
    duplicate_ids: set[str] = set()
    for row in previous_rows:
        if not isinstance(row, dict) or not isinstance(row.get("id"), str):
            raise FeatureUpdateError("dependency rows must have string IDs")
        if row["id"] in old:
            previous = old.pop(row["id"])
            duplicate_ids.add(row["id"])
            reviewed_rows = [item for item in (previous, row)
                             if item.get("review_status", "pending") != "pending" or bool(item.get("review_note"))]
            if reviewed_rows:
                raise FeatureUpdateError(f"duplicate reviewed dependency ID requires manual reconciliation: {row['id']}")
            continue
        if row["id"] in duplicate_ids:
            if row.get("review_status", "pending") != "pending" or bool(row.get("review_note")):
                raise FeatureUpdateError(f"duplicate reviewed dependency ID requires manual reconciliation: {row['id']}")
            continue
        old[row["id"]] = row
    fresh_ids = {row["id"] for row in generated["dependencies"]}
    removed = [row for key, row in old.items() if key not in fresh_ids]
    advanced = [row for row in removed if row.get("review_status", "pending") != "pending"]
    if advanced:
        raise FeatureUpdateError("reviewed dependency groups disappeared; reconcile before removal: " + ", ".join(row["id"] for row in advanced[:5]))
    merged_rows = []
    preserved = 0
    reset = 0
    generated_fields = {"id", "kind", "subsystem", "target", "resolution", "basis", "source_refs", "candidate_refs", "review_status", "review_note"}
    for fresh in generated["dependencies"]:
        previous = old.get(fresh["id"])
        result = dict(fresh)
        if previous is not None:
            same_relation = all(previous.get(field) == fresh.get(field) for field in ("kind", "subsystem", "target", "resolution", "basis", "source_refs", "candidate_refs"))
            if same_relation:
                for field in ("review_status", "review_note"):
                    if field in previous:
                        result[field] = previous[field]
                for field, value in previous.items():
                    if field not in generated_fields:
                        result[field] = value
                preserved += int(result.get("review_status", "pending") != "pending" or bool(result.get("review_note")))
            else:
                reset += int(previous.get("review_status", "pending") != "pending" or bool(previous.get("review_note")))
        merged_rows.append(result)
    result = {**generated, "dependencies": merged_rows}
    return result, {"preserved_reviews": preserved, "reset_reviews": reset,
                    "removed_unreviewed": len(removed) + len(duplicate_ids)}


def _refresh_inventory(root: Path, output_path: Path) -> None:
    cargo = "cargo"
    toolchain_bin = root / ".rustup/toolchains/stable-x86_64-unknown-linux-gnu/bin"
    env = os.environ.copy()
    if toolchain_bin.is_dir():
        env["PATH"] = str(toolchain_bin) + os.pathsep + env.get("PATH", "")
    cargo_home = root / ".cargo"
    rustup_home = root / ".rustup"
    if cargo_home.is_dir():
        env["CARGO_HOME"] = str(cargo_home)
    if rustup_home.is_dir():
        env["RUSTUP_HOME"] = str(rustup_home)
    crate = root / "tools/source-analysis/Cargo.toml"
    if not crate.is_file():
        raise FeatureUpdateError(f"source analyzer manifest is missing: {crate}")
    output_path.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix="lean-miri-syn-") as temporary:
        raw_inventory = Path(temporary) / "inventory.json"
        command = [
            cargo, "run", "--locked", "--offline", "--manifest-path", str(crate), "--",
            str(root), str(raw_inventory),
        ]
        try:
            subprocess.run(command, cwd=root, env=env, check=True)
        except (OSError, subprocess.CalledProcessError) as exc:
            raise FeatureUpdateError(
                f"syn analyzer failed; install the pinned crates with cargo fetch first: {exc}"
            ) from exc
        try:
            compressed = gzip.compress(raw_inventory.read_bytes(), compresslevel=9, mtime=0)
            output_path.write_bytes(compressed)
        except OSError as exc:
            raise FeatureUpdateError(f"cannot write compressed AST inventory {output_path}: {exc}") from exc


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    parser.add_argument("--inventory", type=Path, help="AST JSON or .json.gz; defaults to tools/source-analysis/inventory.json.gz")
    parser.add_argument("--features", type=Path, help="feature tracker; defaults to tracking/features.json")
    parser.add_argument("--dependencies", type=Path, help="dependency candidate tracker; defaults to tracking/dependencies.json.gz")
    parser.add_argument("--refresh-inventory", action="store_true", help="run the pinned syn analyzer and refresh its compressed inventory")
    action = parser.add_mutually_exclusive_group()
    action.add_argument("--write", action="store_true", help="write merged feature rows")
    action.add_argument("--check", action="store_true", help="fail if the feature tracker needs an update")
    args = parser.parse_args(argv)
    root = args.root.resolve()
    inventory_path = args.inventory or root / "tools/source-analysis/inventory.json.gz"
    if not inventory_path.is_absolute():
        inventory_path = root / inventory_path
    features_path = args.features or root / "tracking/features.json"
    if not features_path.is_absolute():
        features_path = root / features_path
    dependencies_path = args.dependencies or root / "tracking/dependencies.json.gz"
    if not dependencies_path.is_absolute():
        dependencies_path = root / dependencies_path
    try:
        if args.refresh_inventory:
            _refresh_inventory(root, inventory_path)
        inventory = load_inventory(inventory_path)
        source_by_path = validate_inventory(root, inventory)
        generated = build_ast_features(inventory, source_by_path)
        generated_dependencies = build_dependency_inventory(inventory, source_by_path)
        try:
            feature_doc = json.loads(features_path.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError) as exc:
            raise FeatureUpdateError(f"cannot read feature tracker {features_path}: {exc}") from exc
        if not isinstance(feature_doc, dict) or feature_doc.get("schema_version") != 1 or not isinstance(feature_doc.get("features"), list):
            raise FeatureUpdateError("tracking/features.json must have schema_version 1 and a features list")
        merged, stats = merge_features(feature_doc["features"], generated)
        result = {**feature_doc, "features": merged}
        try:
            old_dependencies = read_json(dependencies_path) if dependencies_path.exists() else None
        except TrackerIOError as exc:
            raise FeatureUpdateError(f"cannot read dependency tracker {dependencies_path}: {exc}") from exc
        merged_dependencies, dependency_stats = merge_dependency_reviews(old_dependencies, generated_dependencies)
        if args.check:
            # Check canonical JSON without pretty-printing megabytes of temporary
            # text. Keep JSON's type distinctions (e.g. true vs 1), unlike dict ==.
            current = _json_bytes(feature_doc, indent=None)
            proposed = _json_bytes(result, indent=None)
            dependency_current = _json_bytes(old_dependencies, indent=None) if old_dependencies is not None else b""
            dependency_proposed = _json_bytes(merged_dependencies, indent=None)
            if current != proposed or dependency_current != dependency_proposed:
                print(json.dumps(stats, sort_keys=True))
                print(json.dumps(dependency_stats, sort_keys=True))
                print("feature or dependency tracker differs from the syntax inventory; run tools/update_features.py --refresh-inventory --write", file=sys.stderr)
                return 1
        elif args.write:
            features_path.write_bytes(_json_bytes(result))
            try:
                write_json(dependencies_path, merged_dependencies)
            except TrackerIOError as exc:
                raise FeatureUpdateError(str(exc)) from exc
        print(json.dumps({**stats, **dependency_stats, "dependency_groups": len(merged_dependencies["dependencies"]),
                          "inventory_rust_files": len(source_by_path), "inventory_symbols": len(inventory.get("symbols", [])),
                          "enum_variants": len(inventory.get("enum_variants", [])), "tracker_written": bool(args.write)}, sort_keys=True))
        return 0
    except FeatureUpdateError as exc:
        print(f"ERROR: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
