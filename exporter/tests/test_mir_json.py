import gzip
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "tools"))
from mir_json import MirJSONError, decode_mir_document, load_mir_document


REF = "$lean_miri_shared_ref"


def document(nodes, payload, **root):
    return {
        "schema": "lean-miri-rustc-mir",
        "schema_version": 3,
        **root,
        "payload": payload,
        "shared_payloads": {"schema_version": 2, "nodes": nodes},
    }


class MirJSONTests(unittest.TestCase):
    def test_expands_nested_and_repeated_backward_references(self):
        encoded = document(
            [
                {"values": [1, 2, 3]},
                {"row": {REF: 0}, "name": "node"},
            ],
            [{REF: 1}, {REF: 1}],
            producer={"name": "rustc"},
        )

        decoded = decode_mir_document(encoded)

        self.assertNotIn("shared_payloads", decoded)
        self.assertEqual(decoded["schema_version"], 3)
        self.assertEqual(decoded["producer"], {"name": "rustc"})
        self.assertEqual(
            decoded["payload"],
            [
                {"row": {"values": [1, 2, 3]}, "name": "node"},
                {"row": {"values": [1, 2, 3]}, "name": "node"},
            ],
        )
        self.assertIs(decoded["payload"][0], decoded["payload"][1])

    def test_old_unshared_documents_are_not_accepted_for_active_imports(self):
        old = {"schema": "lean-miri-rustc-mir", "schema_version": 2, "payload": []}
        with self.assertRaisesRegex(MirJSONError, "schema_version must be 3"):
            decode_mir_document(old)

        current_header_without_graph = {**old, "schema_version": 3}
        with self.assertRaisesRegex(MirJSONError, "must contain a shared_payloads graph"):
            decode_mir_document(current_header_without_graph)

    def test_catalog_shape_and_version_are_strict(self):
        wrong_version = document([], None)
        wrong_version["shared_payloads"]["schema_version"] = 3
        with self.assertRaisesRegex(MirJSONError, "schema_version must be 2"):
            decode_mir_document(wrong_version)

        extra_field = document([], None)
        extra_field["shared_payloads"]["unused"] = True
        with self.assertRaisesRegex(MirJSONError, "only schema_version and nodes"):
            decode_mir_document(extra_field)

    def test_rejects_out_of_range_forward_and_cyclic_references(self):
        cases = [
            (["not a node"], {REF: 1}, "reference 1 is out of range"),
            ([{REF: 1}, "later"], None, "forward reference to node 1"),
            ([{REF: 0}], None, "cycle in shared_payloads graph at node 0"),
        ]
        for nodes, payload, message in cases:
            with self.subTest(nodes=nodes):
                with self.assertRaisesRegex(MirJSONError, message):
                    decode_mir_document(document(nodes, payload))

    def test_reserved_markers_must_be_exact_numeric_references(self):
        for marker in (
            {REF: 0, "extra": True},
            {REF: True},
            {REF: -1},
            {REF: 0.0},
        ):
            with self.subTest(marker=marker):
                with self.assertRaises(MirJSONError):
                    decode_mir_document(document([], marker))

        with self.assertRaisesRegex(MirJSONError, "reserved.*one-key"):
            decode_mir_document(document([{REF: 0, "extra": True}], None))

    def test_rejects_root_reference_marker_and_unused_malformed_nodes(self):
        root_marker = document([], None)
        root_marker[REF] = 0
        with self.assertRaisesRegex(MirJSONError, "not valid at the document root"):
            decode_mir_document(root_marker)

        with self.assertRaisesRegex(MirJSONError, "reserved.*one-key"):
            decode_mir_document(document([{"unused": {REF: 0, "extra": 1}}], None))

    def test_loads_gzip_archives(self):
        encoded = document([], {"value": "from gzip"})
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "export.json.gz"
            with gzip.open(path, "wt", encoding="utf-8") as stream:
                json.dump(encoded, stream)
            self.assertEqual(load_mir_document(path)["payload"], {"value": "from gzip"})


if __name__ == "__main__":
    unittest.main()
