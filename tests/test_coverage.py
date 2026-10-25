import hashlib
import json
import tempfile
import unittest
from pathlib import Path

from tools.coverage import sync_modules, validate


class CoverageValidatorTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.root = Path(self.tmp.name)
        (self.root / "upstream/miri/src").mkdir(parents=True)
        (self.root / "upstream/rust/src/abi").mkdir(parents=True)
        self.sources = {
            "upstream/miri/src/memory.rs": b"pub fn allocate() {}\n",
            "upstream/rust/src/abi/layout.rs": b"pub struct Layout;\n",
        }
        for rel, content in self.sources.items():
            path = self.root / rel
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(content)

        def git_blob_id(content):
            return hashlib.sha1(f"blob {len(content)}\0".encode() + content).hexdigest()

        lock = {
            "schema_version": 1,
            "pins": {
                "miri": {"repo": "https://example.test/miri", "commit": "a" * 40},
                "rust": {"repo": "https://example.test/rust", "commit": "b" * 40},
            },
            "coverage_roots": ["upstream/miri/src", "upstream/rust/src/abi"],
            "coverage_expected_rust_modules": {
                "upstream/miri/src": 1,
                "upstream/rust/src/abi": 1,
            },
            "files": [
                {
                    "path": rel,
                    "component": "miri" if "/miri/" in rel else "rustc_abi",
                    "git_blob": git_blob_id(content),
                    "sha256": hashlib.sha256(content).hexdigest(),
                }
                for rel, content in self.sources.items()
            ],
        }
        (self.root / "upstream/source-lock.json").write_text(json.dumps(lock), encoding="utf-8")
        sync_modules(self.root)

    def tearDown(self):
        self.tmp.cleanup()

    def _write_features(self, features):
        path = self.root / "tracking/features.json"
        path.write_text(json.dumps({"schema_version": 1, "features": features}), encoding="utf-8")

    def _base_feature(self):
        return {
            "id": "memory.allocate",
            "kind": "semantic_feature",
            "description": "Allocate a memory block and record its layout.",
            "source_modules": sorted(self.sources),
            "source_refs": [
                {
                    "path": path,
                    "symbol": "test_fixture",
                    "line": 1,
                    "source_sha256": hashlib.sha256(content).hexdigest(),
                }
                for path, content in sorted(self.sources.items())
            ],
            "status": "Not ported",
            "lean_definitions": [],
            "tests": [],
            "specifications": [],
            "proofs": [],
        }

    def test_sync_tracks_every_locked_source_and_vacuous_features_fail(self):
        module_doc = json.loads((self.root / "tracking/modules.json").read_text())
        self.assertEqual({row["path"] for row in module_doc["modules"]}, set(self.sources))
        issues, _ = validate(self.root)
        self.assertIn("feature obligation inventory is empty; semantic coverage cannot pass vacuously", issues)

    def test_complete_initial_inventory_passes_only_with_feature_mapping(self):
        self._write_features([self._base_feature()])
        issues, counts = validate(self.root)
        self.assertEqual([], issues)
        self.assertEqual(2, counts["modules"])
        self.assertEqual(1, counts["features"])

    def test_missing_module_row_and_new_unlocked_source_are_reported(self):
        self._write_features([self._base_feature()])
        module_path = self.root / "tracking/modules.json"
        module_doc = json.loads(module_path.read_text())
        module_doc["modules"].pop()
        module_path.write_text(json.dumps(module_doc))
        (self.root / "upstream/miri/src/new_module.rs").write_text("pub fn new_code() {}\n")
        (self.root / "upstream/miri/src/new_native.cpp").write_text("void new_code() {}\n")
        issues, _ = validate(self.root)
        self.assertTrue(any("source unit omitted from tracking/modules.json" in issue for issue in issues))
        self.assertTrue(any("unlocked source file under coverage roots" in issue for issue in issues))

    def test_per_root_rust_count_is_checked(self):
        self._write_features([self._base_feature()])
        lock_path = self.root / "upstream/source-lock.json"
        lock = json.loads(lock_path.read_text())
        lock["coverage_expected_rust_modules"]["upstream/miri/src"] = 2
        lock_path.write_text(json.dumps(lock))
        issues, _ = validate(self.root)
        self.assertIn(
            "Rust module count for coverage root upstream/miri/src: expected 2, found 1",
            issues,
        )

    def test_source_hash_mismatch_is_reported(self):
        self._write_features([self._base_feature()])
        (self.root / "upstream/miri/src/memory.rs").write_text("pub fn changed() {}\n")
        issues, _ = validate(self.root)
        self.assertIn("source SHA256 mismatch: upstream/miri/src/memory.rs", issues)

    def test_miri_tests_evidence_root_is_accepted(self):
        feature = self._base_feature()
        feature["tests"] = ["MiriTests/ABI/Primitives.lean"]
        path = self.root / feature["tests"][0]
        path.parent.mkdir(parents=True)
        path.write_text("example : True := trivial\n")
        self._write_features([feature])
        issues, _ = validate(self.root)
        self.assertEqual(issues, [])
        feature["tests"] = ["Other/Primitives.lean"]
        path = self.root / feature["tests"][0]
        path.parent.mkdir(parents=True)
        path.write_text("example : True := trivial\n")
        self._write_features([feature])
        issues, _ = validate(self.root)
        self.assertTrue(any("test evidence must be under" in issue for issue in issues))

    def test_advanced_status_requires_existing_typed_evidence(self):
        self._write_features([self._base_feature()])
        module_path = self.root / "tracking/modules.json"
        module_doc = json.loads(module_path.read_text())
        module_doc["modules"][0]["status"] = "Proved"
        module_path.write_text(json.dumps(module_doc))
        issues, _ = validate(self.root)
        self.assertTrue(any("status 'Proved' requires at least one Lean definition link" in issue for issue in issues))
        self.assertTrue(any("status 'Proved' requires at least one specification link" in issue for issue in issues))
        self.assertTrue(any("status 'Proved' requires at least one proof link" in issue for issue in issues))

    def test_unreviewed_exclusion_is_rejected(self):
        self._write_features([{
            **self._base_feature(),
            "source_modules": ["upstream/miri/src/memory.rs"],
            "source_refs": [{
                "path": "upstream/miri/src/memory.rs",
                "symbol": "test_fixture",
                "line": 1,
                "source_sha256": hashlib.sha256(self.sources["upstream/miri/src/memory.rs"]).hexdigest(),
            }],
        }])
        exclusions = {
            "schema_version": 1,
            "exclusions": [{
                "path": "upstream/rust/src/abi/layout.rs",
                "reason": "Temporarily omitted pending review.",
                "reviewed": False,
                "reviewed_by": "",
            }],
        }
        (self.root / "tracking/exclusions.json").write_text(json.dumps(exclusions))
        issues, _ = validate(self.root)
        self.assertIn("exclusion upstream/rust/src/abi/layout.rs: not reviewed", issues)
        self.assertIn("exclusion upstream/rust/src/abi/layout.rs: needs reviewed_by", issues)

    def test_reviewed_fixture_directory_exclusion_is_explicit(self):
        self._write_features([self._base_feature()])
        fixture_dir = self.root / "upstream/miri/src/test_fixtures"
        fixture_dir.mkdir()
        (fixture_dir / "case.c").write_text("int main(void) { return 0; }\n")
        (fixture_dir / "case.rs").write_text("fn main() {}\n")
        exclusions = {
            "schema_version": 1,
            "exclusions": [{
                "path": "upstream/miri/src/test_fixtures",
                "scope": "directory",
                "reason": "Fixture programs are retained as upstream test inputs and are not runtime source units.",
                "reviewed": True,
                "reviewed_by": "project owner scope review",
            }],
        }
        (self.root / "tracking/exclusions.json").write_text(json.dumps(exclusions))
        issues, counts = validate(self.root)
        self.assertEqual([], issues)
        self.assertEqual(1, counts["exclusions"])


if __name__ == "__main__":
    unittest.main()
