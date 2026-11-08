"""Historical conversion is explicit and never weakens active input validation."""
import copy
import hashlib
import json
from pathlib import Path
import sys
import tempfile
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
from mir_fixture import convert_evidence, prepare_schema3_replay
from mir_json import MirJSONError, decode_mir_document


class FixtureConversionTests(unittest.TestCase):
    def test_saved_replay_keeps_source_reference_identity_separate(self):
        source = {"schema": "lean-miri-rustc-mir", "schema_version": 3,
                  "body": {"type": {"type_id": 7}}}
        with tempfile.TemporaryDirectory() as directory:
            original = Path(directory) / "original.json"
            execution = Path(directory) / "execution.schema4.json"
            reference = Path(directory) / "original.reference.json"
            raw = json.dumps(source, indent=2).encode()
            original.write_bytes(raw)
            reference.write_bytes(b"immutable reference to original bytes")
            manifest = prepare_schema3_replay(original, execution)
            self.assertEqual(original.read_bytes(), raw)
            self.assertEqual(reference.read_bytes(), b"immutable reference to original bytes")
            self.assertEqual(manifest["reference_identity"], "original_source_bytes_only")
            self.assertFalse(manifest["compiler_reexecuted"])
            self.assertEqual(manifest["source_sha256"], hashlib.sha256(raw).hexdigest())
            self.assertEqual(manifest["execution_sha256"], hashlib.sha256(execution.read_bytes()).hexdigest())
            self.assertEqual(decode_mir_document(json.loads(execution.read_bytes()))["body"]["type"], 7)
            with self.assertRaises(FileExistsError):
                prepare_schema3_replay(original, original)
            self.assertEqual(original.read_bytes(), raw)

    def test_saved_replay_preparation_does_not_supply_an_active_version_fallback(self):
        with tempfile.TemporaryDirectory() as directory:
            source = Path(directory) / "input.json"
            for version in (2, 4):
                source.write_text(json.dumps({"schema": "lean-miri-rustc-mir", "schema_version": version}))
                with self.subTest(version=version), self.assertRaisesRegex(MirJSONError, "requires schema_version 3"):
                    prepare_schema3_replay(source, Path(directory) / "output.json")
    def test_historical_graph_converts_without_mutating_source(self):
        archived = {"schema": "lean-miri-rustc-mir", "schema_version": 3,
                    "bodies": [{"type": {"type_id": 7}, "span": {"$lean_miri_shared_ref": 0}}],
                    "shared_payloads": {"schema_version": 2, "nodes": [{"lo": 3, "hi": 8}]}}
        original = copy.deepcopy(archived)
        with self.assertRaises(MirJSONError):
            decode_mir_document(archived)
        decoded = decode_mir_document(convert_evidence(archived))
        self.assertEqual(decoded["schema_version"], 4)
        self.assertEqual(decoded["bodies"], [{"type": 7, "span": {"lo": 3, "hi": 8}}])
        self.assertEqual(archived, original)

    def test_tls_initializer_image_stays_inline_template(self):
        image = {"size_bytes": 1, "align_bytes": 1, "mutability": "mutable",
                 "bytes_hex": "00", "initialization_ranges": [], "relocations": []}
        tls = {"kind": "ThreadLocalRef", "status": "supported",
               "initializer": {"status": "supported", "allocation": image}}
        archived = {"schema": "lean-miri-rustc-mir", "schema_version": 3,
                    "tls_a": tls, "tls_b": copy.deepcopy(tls),
                    "pointer": {"allocation": {"allocation_id": 3}}}
        original = copy.deepcopy(archived)
        encoded = convert_evidence(archived)
        for key in ("tls_a", "tls_b"):
            initializer = encoded[key]["initializer"]
            self.assertNotIn("allocation", initializer)
            self.assertEqual(initializer["allocation_template"], image)
            self.assertIsInstance(initializer["allocation_template"], dict)
        self.assertEqual(encoded["pointer"]["allocation"], 3)
        self.assertEqual(archived, original)
        self.assertEqual(decode_mir_document(encoded)["tls_a"]["initializer"]["allocation_template"], image)

    def test_ambiguous_tls_template_fields_are_rejected(self):
        archived = {"schema": "lean-miri-rustc-mir", "schema_version": 3,
                    "tls": {"kind": "ThreadLocalRef", "initializer": {
                        "allocation": {}, "allocation_template": {}}}}
        with self.assertRaisesRegex(MirJSONError, "both allocation and allocation_template"):
            convert_evidence(archived)

    def test_selected_static_allocation_query_has_explicit_role(self):
        archived = {"schema": "lean-miri-rustc-mir", "schema_version": 3,
                    "selected": {"kind": "static", "symbol": "EXPORTED", "declaration": {},
                                 "allocation": {"status": "supported", "value": {"allocation_id": 3}}},
                    "pointer": {"allocation": {"allocation_id": 3}}}
        encoded = convert_evidence(archived)
        self.assertNotIn("allocation", encoded["selected"])
        self.assertEqual(encoded["selected"]["allocation_query"], {"status": "supported", "value": 3})
        self.assertEqual(encoded["pointer"]["allocation"], 3)

    def test_malformed_historical_reference_is_rejected(self):
        archived = {"schema": "lean-miri-rustc-mir", "schema_version": 3,
                    "body": {"$lean_miri_shared_ref": -1},
                    "shared_payloads": {"schema_version": 2, "nodes": []}}
        with self.assertRaisesRegex(MirJSONError, "outside catalog"):
            convert_evidence(archived)

    def test_fail_closed_static_query_preserves_direct_allocation_identity(self):
        archived = {"schema": "lean-miri-rustc-mir", "schema_version": 3,
                    "selected": {"kind": "static", "symbol": "EXPORTED", "declaration": {},
                                 "allocation": {"allocation_id": 3}},
                    "pointer": {"allocation": {"allocation_id": 3}}}
        original = copy.deepcopy(archived)
        encoded = convert_evidence(archived)
        self.assertNotIn("allocation", encoded["selected"])
        self.assertEqual(encoded["selected"]["allocation_query"], 3)
        self.assertEqual(encoded["pointer"]["allocation"], 3)
        self.assertEqual(archived, original)
        self.assertEqual(decode_mir_document(encoded)["selected"]["allocation_query"], 3)

    def test_fail_closed_static_query_rejects_ambiguous_allocation_roles(self):
        archived = {"schema": "lean-miri-rustc-mir", "schema_version": 3,
                    "selected": {"kind": "static", "symbol": "EXPORTED", "declaration": {},
                                 "allocation": {"allocation_id": 3},
                                 "allocation_query": {"allocation_id": 4}}}
        with self.assertRaisesRegex(MirJSONError, "both allocation and allocation_query"):
            convert_evidence(archived)


if __name__ == "__main__":
    unittest.main()
