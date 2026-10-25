import hashlib
import json
import tempfile
import unittest
from pathlib import Path

from tools.update_features import (
    AST_ORIGIN,
    FeatureUpdateError,
    build_ast_features,
    build_dependency_inventory,
    merge_features,
    merge_dependency_reviews,
    validate_inventory,
)


class FeatureUpdateTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        self.path = "upstream/miri/src/sample.rs"
        self.content = b"enum State { Cell, Disabled }\nfn transition(x: State) {}\n"
        self.source = self.root / self.path
        self.source.parent.mkdir(parents=True)
        self.source.write_bytes(self.content)
        self.digest = hashlib.sha256(self.content).hexdigest()
        lock = {
            "schema_version": 1,
            "files": [{"path": self.path, "component": "miri", "sha256": self.digest}],
        }
        lock_bytes = (json.dumps(lock) + "\n").encode()
        (self.root / "upstream/source-lock.json").write_bytes(lock_bytes)
        analyzer_files = {
            "tools/source-analysis/Cargo.toml": b"[package]\nname = 'fixture'\n",
            "tools/source-analysis/Cargo.lock": b"version = 4\n",
            "tools/source-analysis/src/main.rs": b"fn main() {}\n",
        }
        for relative, content in analyzer_files.items():
            path = self.root / relative
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(content)
        self.inventory = {
            "schema_version": 1,
            "analyzer": {
                "schema": "syn-ast-inventory-v1",
                "syn_version": "2.0.108",
                "manifest_sha256": hashlib.sha256(analyzer_files["tools/source-analysis/Cargo.toml"]).hexdigest(),
                "cargo_lock_sha256": hashlib.sha256(analyzer_files["tools/source-analysis/Cargo.lock"]).hexdigest(),
                "source_sha256": hashlib.sha256(analyzer_files["tools/source-analysis/src/main.rs"]).hexdigest(),
            },
            "source_lock": {"sha256": hashlib.sha256(lock_bytes).hexdigest()},
            "source_files": [{
                "path": self.path,
                "component": "miri",
                "source_sha256": self.digest,
                "parsed": True,
                "parse_error": None,
            }],
            "symbols": [{
                "id": "s1",
                "path": self.path,
                "kind": "function",
                "name": "transition",
                "symbol": "transition",
                "span": {"line": 2, "column": 0, "end_line": 2, "end_column": 29},
                "has_body": True,
                "body_span": {"line": 2, "column": 25, "end_line": 2, "end_column": 29},
                "body_token_sha256": "c" * 64,
                "owner": None,
                "machine_context": True,
                "machine_hook_candidate": False,
            }],
            "enum_variants": [{
                "id": "v1",
                "path": self.path,
                "component": "miri",
                "enum_name": "State",
                "name": "Cell",
                "symbol": "State::Cell",
                "span": {"line": 1, "column": 13, "end_line": 1, "end_column": 17},
                "shape": "unit",
                "fields": [],
                "enum_category": "other_enum",
            }],
            "call_sites": [{
                "id": "c1", "path": self.path, "component": "miri",
                "enclosing_symbol": "s1", "kind": "method_call", "callee": "read",
                "callee_path": None, "receiver": "memory", "terminal_name": "read",
                "span": {"line": 2, "column": 15, "end_line": 2, "end_column": 25},
            }],
            "imports": [{
                "id": "i1", "path": self.path, "component": "miri", "imported_path": "rustc_private::hidden",
                "terminal_name": "hidden", "is_glob": False,
                "span": {"line": 1, "column": 0, "end_line": 1, "end_column": 25},
            }],
            "macro_sites": [{
                "id": "m1", "path": self.path, "component": "miri", "enclosing_symbol": "s1",
                "macro_path": "throw_ub", "macro_name": "throw_ub", "site_kind": "invocation",
                "classification": "ub", "span": {"line": 2, "column": 30, "end_line": 2, "end_column": 45},
            }],
            "match_arms": [],
            "mir_variant_dispatch_candidates": [],
            "machine_hook_candidates": [],
        }

    def tearDown(self):
        self.tmp.cleanup()

    def test_ast_declarations_create_exact_not_ported_obligations(self):
        source_by_path = validate_inventory(self.root, self.inventory)
        features = build_ast_features(self.inventory, source_by_path)
        self.assertEqual(2, len(features))
        fn = next(feature for feature in features if feature["ast_kind"] == "rust_function_body")
        variant = next(feature for feature in features if feature["ast_kind"] == "enum_variant")
        self.assertEqual("Not ported", fn["status"])
        self.assertEqual("rust_function_body", fn["ast_kind"])
        self.assertTrue(fn["ast_evidence"]["machine_context"])
        self.assertEqual({"path": self.path, "symbol": "transition", "line": 2,
                          "source_sha256": self.digest}, fn["source_refs"][0])
        self.assertEqual("enum_variant", variant["ast_kind"])
        self.assertEqual("State::Cell", variant["source_refs"][0]["symbol"])
        self.assertEqual([], fn["proofs"])

    def test_manual_features_are_preserved_and_unchanged_ast_review_is_kept(self):
        generated = build_ast_features(self.inventory)
        generated[0]["status"] = "Tested"
        generated[0]["lean_definitions"] = ["Miri/Transition.lean"]
        generated[0]["tests"] = ["tests/transition.lean"]
        generated[0]["review_note"] = "Reviewed against the pinned source."
        manual = {"id": "tree-borrows-manual", "status": "Tested", "kind": "semantic_feature"}
        merged, stats = merge_features([manual, *generated], generated)
        self.assertEqual(manual, merged[0])
        self.assertEqual("Tested", merged[1]["status"])
        self.assertEqual(["Miri/Transition.lean"], merged[1]["lean_definitions"])
        self.assertEqual("Reviewed against the pinned source.", merged[1]["review_note"])
        self.assertEqual(2, stats["preserved_ast_rows"])

    def test_changed_source_hash_resets_ast_status_and_evidence(self):
        generated = build_ast_features(self.inventory)
        generated[0]["status"] = "Tested"
        generated[0]["lean_definitions"] = ["Miri/Transition.lean"]
        changed = [dict(row) for row in generated]
        changed[0] = dict(changed[0])
        changed[0]["status"] = "Not ported"
        changed[0]["lean_definitions"] = []
        changed[0]["tests"] = []
        changed[0]["specifications"] = []
        changed[0]["proofs"] = []
        changed[0]["source_refs"] = [dict(changed[0]["source_refs"][0], source_sha256="d" * 64)]
        merged, stats = merge_features(generated, changed)
        self.assertEqual("Not ported", merged[0]["status"])
        self.assertEqual([], merged[0]["lean_definitions"])
        self.assertEqual(1, stats["reset_ast_reviews"])

    def test_disappeared_reviewed_symbol_is_not_silently_dropped(self):
        generated = build_ast_features(self.inventory)
        generated[0]["status"] = "Proved"
        with self.assertRaisesRegex(FeatureUpdateError, "advanced status disappeared or moved"):
            merge_features(generated, generated[1:])

    def test_stale_file_hash_is_rejected_before_updates(self):
        self.source.write_bytes(self.content + b"// changed\n")
        with self.assertRaisesRegex(FeatureUpdateError, "source contents changed"):
            validate_inventory(self.root, self.inventory)

    def test_inventory_source_lock_hash_must_match(self):
        self.inventory["source_lock"]["sha256"] = "0" * 64
        with self.assertRaisesRegex(FeatureUpdateError, "upstream/source-lock.json SHA256 changed"):
            validate_inventory(self.root, self.inventory)

    def test_ast_origin_constant_is_stable(self):
        self.assertEqual("syn-ast-v1", AST_ORIGIN)

    def test_dependency_graph_keeps_dynamic_calls_and_private_imports_with_locations(self):
        source_by_path = validate_inventory(self.root, self.inventory)
        graph = build_dependency_inventory(self.inventory, source_by_path)
        method = next(row for row in graph["dependencies"] if row["kind"] == "method_call")
        private_import = next(row for row in graph["dependencies"] if row["kind"] == "import")
        macro = next(row for row in graph["dependencies"] if row["kind"] == "macro_invocation")
        self.assertEqual("trait_or_inherent_method_dispatch_unresolved", method["resolution"])
        self.assertEqual("rustc_private_or_unselected_component", private_import["resolution"])
        self.assertEqual("macro_expansion_or_external_macro_unresolved", macro["resolution"])
        self.assertEqual("pending", method["review_status"])
        self.assertEqual(self.path, method["source_refs"][0]["path"])
        self.assertEqual(self.digest, method["source_refs"][0]["source_sha256"])
        self.assertEqual(2, method["source_refs"][0]["line"])
        selected_source = dict(source_by_path)
        selected_source["upstream/rustc-apfloat-source/src/lib.rs"] = {"component": "rustc_apfloat"}
        import_row = self.inventory["imports"][0]
        import_row["imported_path"] = "rustc_apfloat::Float"
        graph = build_dependency_inventory(self.inventory, selected_source)
        pinned_import = next(row for row in graph["dependencies"]
                             if row["kind"] == "import" and row["target"] == "rustc_apfloat::Float")
        self.assertEqual("pinned_component_path_unresolved", pinned_import["resolution"])

    def test_new_mir_variant_gets_unclassified_dispatch_obligation(self):
        variant = {
            "id": "v_mir", "path": self.path, "component": "rustc_middle_mir",
            "enum_name": "TerminatorKind", "name": "NewTerminator", "symbol": "TerminatorKind::NewTerminator",
            "span": {"line": 1, "column": 13, "end_line": 1, "end_column": 25},
            "enum_category": "mir_terminator",
        }
        self.inventory["enum_variants"].append(variant)
        graph = build_dependency_inventory(self.inventory, validate_inventory(self.root, self.inventory))
        row = next(item for item in graph["dependencies"] if item["kind"] == "mir_enum_variant_dispatch")
        self.assertEqual("no_syntactic_match_arm_candidate_found", row["resolution"])
        self.assertEqual("pending", row["review_status"])
        self.assertEqual([], row["candidate_refs"])

    def test_dependency_reviews_preserve_only_unchanged_relations(self):
        baseline = build_dependency_inventory(self.inventory, validate_inventory(self.root, self.inventory))
        reviewed = json.loads(json.dumps(baseline))
        row = next(item for item in reviewed["dependencies"] if item["kind"] == "method_call")
        row["review_status"] = "reviewed_candidate"
        row["review_note"] = "Still requires semantic proof."
        merged, stats = merge_dependency_reviews(reviewed, baseline)
        preserved = next(item for item in merged["dependencies"] if item["id"] == row["id"])
        self.assertEqual("reviewed_candidate", preserved["review_status"])
        self.assertEqual(1, stats["preserved_reviews"])
        changed = json.loads(json.dumps(baseline))
        changed_row = next(item for item in changed["dependencies"] if item["id"] == row["id"])
        changed_row["source_refs"][0]["line"] = 99
        merged, stats = merge_dependency_reviews(reviewed, changed)
        reset = next(item for item in merged["dependencies"] if item["id"] == row["id"])
        self.assertEqual("pending", reset["review_status"])
        self.assertEqual(1, stats["reset_reviews"])

    def test_disappeared_reviewed_dependency_is_rejected(self):
        inventory = build_dependency_inventory(self.inventory, validate_inventory(self.root, self.inventory))
        inventory["dependencies"][0]["review_status"] = "reviewed_candidate"
        generated = json.loads(json.dumps(inventory))
        generated["dependencies"] = generated["dependencies"][1:]
        with self.assertRaisesRegex(FeatureUpdateError, "reviewed dependency groups disappeared"):
            merge_dependency_reviews(inventory, generated)


if __name__ == "__main__":
    unittest.main()
