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
    def test_typed_abi_headers_preserve_business_document_and_validate_ids(self):
        arg = {"type": {"type_id": 7}, "layout": {"status": "unsupported"}, "mode": {"kind": "Ignore"}}
        abi = {"arguments": {REF: 1}, "return": {REF: 0}, "calling_convention": {"kind": "Rust"},
               "can_unwind": False, "c_variadic": False, "fixed_count": 1}
        ordinary = document([arg, [{REF: 0}], abi], {REF: 2})
        typed = document([{"$lean_miri_abi_arg": [7, arg["layout"], arg["mode"]]},
                          [{REF: 0}], {"$lean_miri_fn_abi": [1, 0, abi["calling_convention"], False, False, 1]}], {REF: 2})
        typed["shared_payloads"]["typed_abi_version"] = 1
        self.assertEqual(decode_mir_document(ordinary), decode_mir_document(typed))
        typed["shared_payloads"]["scan_flags"] = [1, 1, 5]
        self.assertEqual(decode_mir_document(ordinary), decode_mir_document(typed))
        for slot, value in [(0, 2), (1, 1), (1, -1), (3, 0), (4, "false"), (5, True)]:
            import copy
            bad = copy.deepcopy(typed)
            bad["shared_payloads"]["nodes"][2]["$lean_miri_fn_abi"][slot] = value
            with self.assertRaisesRegex(MirJSONError, "typed ABI"):
                decode_mir_document(bad)
        typed["shared_payloads"].pop("typed_abi_version")
        with self.assertRaisesRegex(MirJSONError, "typed ABI"):
            decode_mir_document(typed)

    def test_prepared_scan_flags_are_checked_against_all_nodes(self):
        encoded = document([{"type_id": 7}, [{REF: 0}], {"locals": []}], {REF: 1})
        expected = decode_mir_document(encoded)
        encoded["shared_payloads"]["scan_flags"] = [1, 1, 2]
        self.assertEqual(decode_mir_document(encoded), expected)
        for flags in ([0, 1, 2], [1, 15, 2], [1], [1, True, 2], [1, 16, 2], None):
            encoded["shared_payloads"]["scan_flags"] = flags
            with self.assertRaisesRegex(MirJSONError, "scan_flags"):
                decode_mir_document(encoded)

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
