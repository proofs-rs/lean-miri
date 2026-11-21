"""Current source materials survive exact payload sharing without identity merging."""
import copy
import json
from pathlib import Path
import sys
import unittest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))
from shared_json_pools import SHARED_POOLS, expand_document, pool_document
from mir_json import decode_mir_document


class SharedFixturePoolTests(unittest.TestCase):
    def test_current_maintained_fixture_round_trip(self):
        document = decode_mir_document(json.loads((ROOT / "examples/empty_function/input.json").read_bytes()))
        before = copy.deepcopy(document)
        expanded = expand_document(document)
        pooled = pool_document(expanded)
        decode_mir_document(pooled)
        self.assertEqual(expand_document(pooled), expanded)
        self.assertEqual(document, before, "inspection or pooling mutated the wire identities")
        self.assertFalse({"layouts", "fn_abis", "compiler_facts", "boolean_queries"} & pooled.keys())
        self.assertEqual(pooled["byte_images"], document["byte_images"])
        self.assertEqual(pooled["types"], document["types"])
        self.assertEqual(pooled["source_trait_material"], document["source_trait_material"])
        self.assertEqual(pooled["source_vtables"], document["source_vtables"])

    def test_complete_payload_dedup_preserves_source_and_allocation_identities(self):
        source = {
            "schema_version": 17,
            "byte_images": ["00"],
            "types": [{"type_id": 0, "source_layout": {"normalized_type": 0}}],
            "allocations": [
                {"allocation_id": 0, "source_alloc_id": 17, "byte_image_id": 0,
                 "initialization_ranges": [[0, 1]], "relocations": []},
                {"allocation_id": 1, "source_alloc_id": 29, "byte_image_id": 0,
                 "initialization_ranges": [], "relocations": []}],
            "bodies": [{"basic_blocks": [{"statements": [
                {"source_info": {"span": 0, "scope": 0}, "kind": {"variant": "Nop"}},
                {"source_info": {"span": 0, "scope": 0}, "kind": {"variant": "Nop"}},
                {"source_info": {"span": 0, "scope": 1}, "kind": {"variant": "StorageLive", "local": 0}},
                {"source_info": {"span": 0, "scope": 1}, "kind": {"variant": "StorageLive", "local": 1}},
            ]}]}],
        }
        pooled = pool_document(source)
        self.assertEqual(len(pooled["source_infos"]), 2)
        self.assertEqual(len(pooled["statement_kinds"]), 3)
        statements = pooled["bodies"][0]["basic_blocks"][0]["statements"]
        self.assertEqual(statements[0], statements[1])
        self.assertNotEqual(statements[2]["kind"], statements[3]["kind"])
        self.assertEqual(pooled["allocations"][0]["relocations"], pooled["allocations"][1]["relocations"])
        self.assertNotEqual(pooled["allocations"][0]["initialization_ranges"],
                            pooled["allocations"][1]["initialization_ranges"])
        self.assertEqual([row["source_alloc_id"] for row in pooled["allocations"]], [17, 29])
        self.assertEqual(expand_document(pooled), source)

    def test_invalid_shared_references_fail(self):
        for field, pool in [("source_info", "source_infos"), ("relocations", "relocations"),
                            ("initialization_ranges", "initialization_ranges")]:
            for invalid in (-1, 1, True, 0.0, None):
                with self.subTest(field=field, reference=invalid), self.assertRaisesRegex(ValueError, "out of range"):
                    expand_document({pool: [{}], "payload": {field: invalid}})
        for invalid in (-1, 1, True, 0.0, None):
            with self.subTest(statement=invalid), self.assertRaisesRegex(ValueError, "out of range"):
                expand_document({"statement_kinds": [{}], "statements": [{"kind": invalid}]})

    def test_pooling_rejects_historical_and_malformed_schema(self):
        for version in (8, 11, 12, 13, 14, 15, 16, True, "17", 17.0, None):
            with self.subTest(version=version), self.assertRaisesRegex(ValueError, "requires schema 17"):
                pool_document({"schema_version": version})
        self.assertEqual(set(SHARED_POOLS), {"initialization_ranges", "relocations",
                                           "statement_kinds", "source_infos"})


if __name__ == "__main__":
    unittest.main()
