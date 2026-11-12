"""Pinned compiler-fixture projection preserves every retained semantic value."""
import gzip
import hashlib
import json
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
from shared_json_pools import expand_document, pool_document, project_unused_metadata
from mir_json import decode_mir_document
from legacy_fixture_schema import adapt_legacy_fixture


class SharedFixtureProjectionTests(unittest.TestCase):
    def test_pinned_projection_is_lossless(self):
        manifest = json.loads((ROOT / "tests/fixtures/shared-pools-projection.json").read_text())
        self.assertEqual(len(manifest["fixtures"]), 20)
        for row in manifest["fixtures"]:
            with self.subTest(path=row["path"]):
                source = ROOT / row["path"]
                raw = source.read_bytes()
                self.assertEqual(hashlib.sha256(raw).hexdigest(), row["target_file_sha256"])
                if source.suffix == ".gz":
                    raw = gzip.decompress(raw)
                document = json.loads(raw)
                decode_mir_document(adapt_legacy_fixture(document))
                expanded = expand_document(document, schema_version=row["source_schema"])
                canonical = json.dumps(expanded, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode()
                self.assertEqual(hashlib.sha256(canonical).hexdigest(), row["expanded_retained_canonical_sha256"])

    def test_abi_pool_uses_complete_argument(self):
        argument = {"type": 0, "layout": 0, "mode": {"kind": "Direct", "attrs": []}}
        changed_mode = {**argument, "mode": {"kind": "Ignore"}}
        changed_layout = {**argument, "layout": 1}
        changed_type = {**argument, "type": 1}
        source = {"schema_version": 8, "layouts": [], "fn_abis": [
            {"return": argument, "arguments": [argument, changed_mode, changed_layout, changed_type]}]}
        pooled = pool_document(source)
        self.assertEqual(len(pooled["abi_arguments"]), 4)
        self.assertEqual(pooled["fn_abis"][0]["return"], pooled["fn_abis"][0]["arguments"][0])
        expanded = expand_document(pooled, schema_version=8)
        # The historical fixture adapter supplies required empty source seeds;
        # pooling must preserve every original ABI value exactly.
        self.assertEqual(expanded, {**source, "mir_templates": [],
                                   "compiler_trait_program": {"traits": [],
                                       "constructor_scope": {"kind": "all_source_impls"}}})

    def test_unused_metadata_projection_retains_required_consts(self):
        source = {"schema_version": 8, "layouts": [], "spans": [
            {"ctxt": {"status": "debug_payload", "rustc_debug": "#123"}}], "bodies": [{
            "tainted_by_errors": None, "mentioned_items": [], "pass_count": 9,
            "required_consts": ["retained"], "locals": [
                {"type": 2, "layout": 3, "mutability": "mutable", "local_info": {}}],
            "source_scopes": [{"span": 0, "local_data": {}}]}]}
        projected = project_unused_metadata(source)
        self.assertEqual(projected["spans"][0]["ctxt"], "#123")
        self.assertEqual(projected["bodies"], [{"required_consts": ["retained"],
            "locals": [{"type": 2}], "source_scopes": [{"span": 0}]}])
        source["bodies"][0]["tainted_by_errors"] = {"error": "tainted"}
        with self.assertRaisesRegex(ValueError, "tainted MIR"):
            pool_document(source)


if __name__ == "__main__":
    unittest.main()
