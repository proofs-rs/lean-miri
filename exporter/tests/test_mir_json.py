import copy
import gzip
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "tools"))
from mir_json import (MirJSONError, SEMANTIC_KINDS, core_references, decode_mir_document,
                      encode_mir_document, load_mir_document)


def document(**root):
    return {"schema": "lean-miri-rustc-mir", "schema_version": 4,
            "semantic_tables": {"schema_version": 1, **{kind: [] for kind in SEMANTIC_KINDS}}, **root}


class MirJSONTests(unittest.TestCase):
    def test_direct_query_reference_inventory_keeps_optional_and_scalar_answers(self):
        view = {"compiler_runtime_primitives": {"u8": 2, "ordering_enum": 3},
                "compiler_named_types": {"pid_t": 4, "absent": None},
                "compiler_libc_type_layouts": {"entries": {"size_t": 5}},
                "runtime": [{"input_type_id": 1, "drop_glue": 2, "mut_pointer_type": 6}],
                "virtual": {"original_instance_id": 3, "method_definition": {}, "resolved": 4},
                "selected": {"allocation_query": 7},
                "cast": {"query_kind": "supertrait_slot", "value": 999},
                "local": 2, "scope": 2, "target": 2}
        self.assertCountEqual(core_references(view),
                              [("type_id", 2), ("type_id", 3), ("type_id", 4), ("type_id", 5),
                               ("type_id", 1), ("instance_id", 2), ("type_id", 6),
                               ("instance_id", 3), ("instance_id", 4), ("allocation_id", 7)])

    def test_core_query_reference_inventory_keeps_scalar_spaces_separate(self):
        view = {"compiler_runtime_primitives": {"u8": 2, "ordering_enum": {"value": 3}},
                "compiler_named_types": {"pid_t": {"value": 4}},
                "runtime": [{"input_type_id": 1, "drop_glue": {"value": 2}}],
                "cast": [{"query_kind": "box_type", "value": 5},
                         {"query_kind": "resolve_fn_ptr", "value": 6},
                         {"query_kind": "supertrait_slot", "value": 999}],
                "allocation_query": {"value": 7},
                "relocation": {"storage_offset_bytes": 2, "target": 8},
                "existing_allocation": 9, "covered_allocation_ids": [10],
                "local": 2, "target": 2, "scope": 2}
        self.assertCountEqual(core_references(view),
                              [("type_id", 2), ("type_id", 3), ("type_id", 4),
                               ("type_id", 1), ("instance_id", 2), ("type_id", 5),
                               ("instance_id", 6), ("allocation_id", 7), ("allocation_id", 8),
                               ("allocation_id", 9), ("allocation_id", 10)])

    def test_pattern_and_hoisted_definition_references_have_explicit_roles(self):
        wire = document(types=[{"type_id": 2, "shape": {"kind": "pattern_type", "pattern": 1}}],
                        binding={"hoisted_from": 0})
        wire["semantic_tables"]["patterns"] = [{"kind": "range", "start": 0, "end": 0},
                                               {"kind": "or", "patterns": [0, 0]}]
        wire["semantic_tables"]["constants"] = [{"kind": "value", "type": 2, "value": {"kind": "leaf", "bits_unsigned": "1"}}]
        wire["semantic_tables"]["definitions"] = [{"crate": 2, "index": 7}]
        decoded = decode_mir_document(wire)
        patterns = decoded["types"][0]["shape"]["pattern"]["patterns"]
        self.assertEqual(patterns[0]["start"]["type"], 2)
        self.assertIs(patterns[0], patterns[1])
        self.assertEqual(decoded["binding"]["hoisted_from"], {"crate": 2, "index": 7})
        self.assertEqual(decode_mir_document(encode_mir_document(decoded)), decoded)

    def test_same_number_has_independent_kind_and_identity(self):
        wire = document(types=[{"type_id": 0, "layout": 0}],
                        bodies=[{"span": 0, "type": 0, "local": 0, "scope": 0, "target": 0}])
        wire["semantic_tables"]["spans"] = [{"lo": 7, "hi": 9}]
        wire["semantic_tables"]["layouts"] = [{"size_bytes": 4}]
        decoded = decode_mir_document(wire)
        self.assertEqual(decoded["types"][0]["layout"], {"size_bytes": 4})
        self.assertEqual(decoded["bodies"][0], {"span": {"lo": 7, "hi": 9}, "type": 0,
                                              "local": 0, "scope": 0, "target": 0})
        self.assertNotIn("semantic_tables", decoded)

    def test_expands_shared_nested_metadata_without_copying(self):
        wire = document(bodies=[{"generic_args": 0}, {"generic_args": 0}])
        wire["semantic_tables"]["generic_args"] = [[{"kind": "lifetime", "value": 0}]]
        wire["semantic_tables"]["regions"] = [{"kind": "erased"}]
        decoded = decode_mir_document(wire)
        self.assertEqual(decoded["bodies"][0]["generic_args"], [{"kind": "lifetime", "value": {"kind": "erased"}}])
        self.assertIs(decoded["bodies"][0]["generic_args"], decoded["bodies"][1]["generic_args"])

    def test_predicates_use_explicit_sparse_identities(self):
        wire = document(input_predicates=[19])
        wire["semantic_tables"]["predicates"] = [{"predicate_id": 19, "kind": "trait"}]
        self.assertEqual(decode_mir_document(wire)["input_predicates"][0]["predicate_id"], 19)
        bad = copy.deepcopy(wire)
        bad["input_predicates"] = [0]
        with self.assertRaisesRegex(MirJSONError, "dangling predicates reference 0"):
            decode_mir_document(bad)
        bad = copy.deepcopy(wire)
        bad["semantic_tables"]["predicates"] *= 2
        with self.assertRaisesRegex(MirJSONError, "duplicate predicate identity"):
            decode_mir_document(bad)

    def test_expands_abi_query_values_and_nested_components(self):
        wire = document(abi_query=0)
        tables = wire["semantic_tables"]
        tables["function_abis"] = [{"arguments": [0], "return": 0, "fixed_count": 1,
                                    "calling_convention": {"kind": "c"}}]
        tables["argument_abis"] = [{"type": 3, "layout": 0,
                                    "mode": {"kind": "Direct", "attributes": 0}}]
        tables["layouts"] = [{"size_bytes": 8}]
        tables["abi_attributes"] = [{"regular_bits": 7}]
        abi = decode_mir_document(wire)["abi_query"]
        self.assertEqual(abi["arguments"][0]["mode"]["attributes"], {"regular_bits": 7})
        self.assertIs(abi["arguments"][0], abi["return"])

    def test_direct_query_results_use_kind_specific_ids_without_success_envelopes(self):
        wire = document(queries={"abi_query": 0, "signature_query": 0, "function_kind": "function_definition"},
                        entry={"signature_query": {"compiler_selected_entry": False, "return_type": 3}},
                        scalar_query={"query_kind": "supertrait_slot", "value": 0})
        tables = wire["semantic_tables"]
        tables["function_abis"] = [{"arguments": [], "return": 0, "fixed_count": 0}]
        tables["argument_abis"] = [{"type": 3, "layout": 0, "mode": {"kind": "Ignore"}}]
        tables["layouts"] = [{"size_bytes": 0}]
        tables["signatures"] = [{"inputs": [], "output": 3, "c_variadic": False}]
        decoded = decode_mir_document(wire)
        self.assertEqual(decoded["queries"]["abi_query"]["return"]["type"], 3)
        self.assertEqual(decoded["queries"]["signature_query"]["output"], 3)
        self.assertEqual(decoded["entry"]["signature_query"],
                         {"compiler_selected_entry": False, "return_type": 3})
        self.assertEqual(decoded["scalar_query"]["value"], 0)
        self.assertNotIn("status", decoded["queries"]["abi_query"])
        self.assertEqual(decode_mir_document(encode_mir_document(decoded)), decoded)

    def test_active_abi_and_signature_fields_reject_old_success_envelopes(self):
        for key in ("fn_abi", "abi_query", "signature_query"):
            wire = document(record={"function_kind": "function_definition",
                                    key: {"status": "supported", "value": 0}})
            with self.subTest(field=key), self.assertRaisesRegex(MirJSONError, "non-negative integer ID"):
                decode_mir_document(wire)

    def test_active_instance_edges_reject_old_failure_records(self):
        for key in ("entry_instance", "fallback_instance", "instance"):
            for status in ("unsupported", "incomplete", "supported"):
                with self.subTest(field=key, status=status), self.assertRaisesRegex(MirJSONError, "non-negative integer ID"):
                    decode_mir_document(document(body={key: {"status": status}}))

    def test_cast_abi_registers_and_attributes_use_their_own_spaces(self):
        wire = document(abi_query=0)
        tables = wire["semantic_tables"]
        tables["function_abis"] = [{"arguments": [], "return": 0, "fixed_count": 0}]
        tables["argument_abis"] = [{"type": 0, "layout": 0,
                                    "mode": {"kind": "Cast", "target": 0}}]
        tables["layouts"] = [{"size_bytes": 8}]
        tables["cast_targets"] = [{"prefix_registers": [0], "rest_register": 0, "attributes": 0}]
        tables["abi_registers"] = [{"kind": {"kind": "integer"}, "size_bits": 64}]
        tables["abi_attributes"] = [{"regular_bits": 0}]
        cast = decode_mir_document(wire)["abi_query"]["return"]["mode"]["target"]
        self.assertEqual(cast["rest_register"]["size_bits"], 64)
        self.assertIs(cast["prefix_registers"][0], cast["rest_register"])
        self.assertEqual(cast["attributes"], {"regular_bits": 0})

    def test_old_graph_and_wrong_versions_are_rejected(self):
        for version in (2, 3, True, 4.0):
            wire = document(schema_version=version)
            with self.assertRaisesRegex(MirJSONError, "schema_version must be 4"):
                decode_mir_document(wire)
        wire = document(shared_payloads={"schema_version": 2, "nodes": []})
        with self.assertRaisesRegex(MirJSONError, "obsolete shared_payloads"):
            decode_mir_document(wire)
        wire = document()
        wire["semantic_tables"]["schema_version"] = 2
        with self.assertRaisesRegex(MirJSONError, "schema_version must be 1"):
            decode_mir_document(wire)

    def test_catalog_shape_and_unused_nodes_are_checked(self):
        for mutation in (lambda c: c.pop("spans"), lambda c: c.update(extra=[]),
                         lambda c: c.update(layouts={})):
            wire = document()
            mutation(wire["semantic_tables"])
            with self.assertRaises(MirJSONError):
                decode_mir_document(wire)
        wire = document()
        wire["semantic_tables"]["layouts"] = [{"layout": 17}]
        with self.assertRaisesRegex(MirJSONError, "dangling layouts reference 17"):
            decode_mir_document(wire)
        wire["semantic_tables"]["layouts"] = [{"layout": 0}]
        with self.assertRaisesRegex(MirJSONError, "cycle in semantic_tables"):
            decode_mir_document(wire)

    def test_bare_references_must_be_nonnegative_integer_ids(self):
        for identity in (-1, True, 0.0, "0", {"lo": 7}, {"$lean_miri_shared_ref": 0}):
            with self.subTest(identity=identity), self.assertRaises(MirJSONError):
                decode_mir_document(document(body={"span": identity}))
        with self.assertRaisesRegex(MirJSONError, "obsolete.*marker"):
            decode_mir_document(document(payload={"$lean_miri_shared_ref": 0}))

    def test_legacy_identity_wrappers_are_rejected(self):
        with self.assertRaisesRegex(MirJSONError, "object-shaped compiler identity"):
            decode_mir_document(document(body={"type": {"type_id": 0}}))

    def test_fixture_encoder_preserves_numeric_identities_and_roles(self):
        original = {"schema": "lean-miri-rustc-mir", "schema_version": 4,
                    "types": [{"type_id": 5, "layout": {"size_bytes": 4}}],
                    "body": {"type": {"type_id": 5}, "span": {"lo": 1, "hi": 3}, "local": 5},
                    "other": {"span": {"lo": 1, "hi": 3}}}
        encoded = encode_mir_document(original)
        self.assertEqual(encoded["body"]["type"], 5)
        self.assertEqual(encoded["body"]["span"], encoded["other"]["span"])
        self.assertEqual(encoded["body"]["local"], 5)
        decoded = decode_mir_document(encoded)
        self.assertEqual(decoded["body"]["type"], 5)
        self.assertEqual(decoded["body"]["span"], original["body"]["span"])
        self.assertEqual(decoded["types"], original["types"])

    def test_pure_instance_edges_are_numeric_and_checked_against_authoritative_rows(self):
        identity = {"instance_id": 0, "instance_kind": {"kind": "item"}, "generic_args": []}
        source = {"schema": "lean-miri-rustc-mir", "schema_version": 4,
                  "instances": [identity], "body": {"entry_instance": copy.deepcopy(identity)}}
        wire = encode_mir_document(source)
        self.assertIsInstance(wire["instances"][0], dict)
        self.assertEqual(wire["body"]["entry_instance"], 0)
        source["body"]["entry_instance"]["generic_args"] = [7]
        with self.assertRaisesRegex(MirJSONError, "differs from canonical identity"):
            encode_mir_document(source)

    def test_loads_gzip_archives(self):
        wire = document(payload={"value": "gzip"})
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "export.json.gz"
            with gzip.open(path, "wt", encoding="utf-8") as stream:
                json.dump(wire, stream)
            self.assertEqual(load_mir_document(path)["payload"], {"value": "gzip"})


if __name__ == "__main__":
    unittest.main()
