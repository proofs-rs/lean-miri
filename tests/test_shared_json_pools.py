"""Pinned compiler-fixture projection preserves every original semantic value."""
import gzip
import hashlib
import json
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
from shared_json_pools import expand_document
from mir_json import decode_mir_document


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
                document = decode_mir_document(json.loads(raw))
                expanded = expand_document(document, schema_version=row["source_schema"])
                canonical = json.dumps(expanded, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode()
                self.assertEqual(hashlib.sha256(canonical).hexdigest(), row["expanded_source_canonical_sha256"])


if __name__ == "__main__":
    unittest.main()
