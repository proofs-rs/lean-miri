"""Historical fixture adapters are explicit, bounded component-test inputs."""
import copy
from pathlib import Path
import sys
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
from legacy_fixture_schema import adapt_legacy_fixture


class LegacyFixtureSchemaTests(unittest.TestCase):
    def test_preserves_source_and_historical_unwind_answer(self):
        for answer in (False, True):
            source = {"schema_version": 11, "bodies": [{}], "fn_abis": [
                {"can_unwind": answer, "arguments": [3], "return": 2}]}
            frozen = copy.deepcopy(source)
            projected = adapt_legacy_fixture(source)
            self.assertEqual(source, frozen)
            self.assertEqual(projected["compiler_coroutine_coverage"]["body_coroutines"], [False])
            abi = projected["fn_abis"][0]
            self.assertEqual(abi["arguments"], [3])
            self.assertEqual(abi["return"], 2)
            self.assertEqual(abi["unwind_seed"]["panic_unwinds"], answer)
            self.assertNotIn("can_unwind", abi)
            self.assertEqual(projected["instance_abis"], [])

    def test_current_body_schema_missing_abi_material_is_not_adapted(self):
        source = {"schema_version": 13, "mir_templates": [],
                  "bodies": [{"body_kind": "material"}]}
        self.assertEqual(adapt_legacy_fixture(source), source)
        self.assertNotIn("instance_abis", adapt_legacy_fixture(source))

    def test_conflicting_instance_oracles_fail(self):
        source = {"schema_version": 11, "definitions": [{}], "instances": [
            {"instance_kind": {"kind": "item", "def_id": 0}},
            {"instance_kind": {"kind": "virtual", "def_id": 0}}],
            "compiler_runtime_queries": {"instances": [
                {"instance_id": 0, "requires_caller_location": True},
                {"instance_id": 1, "requires_caller_location": False}]}}
        with self.assertRaisesRegex(ValueError, "conflict"):
            adapt_legacy_fixture(source)

    def test_unknown_and_current_schemas_are_not_reinterpreted(self):
        for version in (3, 8, 13, 999):
            source = {"schema_version": version, "fn_abis": [{"can_unwind": True}]}
            self.assertEqual(adapt_legacy_fixture(source), source)

    def test_invalid_virtual_oracle_does_not_acquire_material(self):
        source = {"schema_version": 12, "instances": [{"generic_args": [
            {"kind": "type", "value": 3}, {"kind": "type", "value": 4}]}],
            "compiler_runtime_queries": {"virtual": [{"original_instance_id": 0,
                "concrete_type": 7, "rebased_args": [
                    {"kind": "type", "value": 7}, {"kind": "type", "value": 99}]}]}}
        row = adapt_legacy_fixture(source)["compiler_runtime_queries"]["virtual"][0]
        self.assertNotIn("parent_generic_count", row)
