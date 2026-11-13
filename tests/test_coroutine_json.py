"""Strict raw coroutine catalog wire controls; no compiler authenticity claim."""
import copy
from pathlib import Path
import sys
import unittest
sys.path.insert(0, str(Path(__file__).resolve().parents[1] / "tools"))
from coroutine_json import validate_catalog


def fixture():
    unit = {"kind": "node", "sort": "type", "tag": "tuple", "payload": "", "children": []}
    owner = {"crate": 0, "index": 7}
    source = {"owner": owner, "physical_owner": owner, "typeck_owner": {"crate": 0, "index": 6},
              "parent_count": 1, "parameters": ["type"] * 6, "witness_parameters": ["type"],
              "identity_kind": unit, "by_move_owner": None,
              "type_expression": {"kind": "definition", "sort": "type", "tag": "coroutine", "definition": owner,
                                  "children": [{"kind": "parameter", "sort": "type", "index": 0}] + [unit] * 5},
              "layout": {"field_tys": [{"type": {"kind": "parameter", "sort": "type", "index": 0},
                                        "source_info": 0, "ignore_for_traits": False, "debuginfo_name": None}],
                         "variant_fields": [[], [], [], [0]],
                         "variant_source_info": [{"span": 0, "scope": 0}] * 4,
                         "storage_conflicts": [[0]]}}
    return copy.deepcopy({"bodies": [], "types": [], "definitions": [{"crate": 0, "index": 6}, {"crate": 0, "index": 7}],
                          "spans": [{}], "source_infos": [{"span": 0, "scope": 0}],
                          "compiler_coroutine_coverage": {"body_coroutines": [], "coroutines": [], "auxiliary_bodies": [], "generic_sources": [source]}})


class CoroutineCatalogTests(unittest.TestCase):
    def test_valid_generic_catalog(self):
        validate_catalog(fixture())

    def test_missing_required_catalog_members(self):
        for key in fixture()["compiler_coroutine_coverage"]:
            with self.subTest(key=key):
                document = fixture()
                del document["compiler_coroutine_coverage"][key]
                with self.assertRaises(ValueError):
                    validate_catalog(document)

    def test_missing_and_unknown_raw_source_members(self):
        for key in fixture()["compiler_coroutine_coverage"]["generic_sources"][0]:
            with self.subTest(key=key):
                document = fixture()
                del document["compiler_coroutine_coverage"]["generic_sources"][0][key]
                with self.assertRaises(ValueError):
                    validate_catalog(document)
        document = fixture()
        document["compiler_coroutine_coverage"]["generic_sources"][0]["layout_answer"] = {}
        with self.assertRaises(ValueError):
            validate_catalog(document)

    def test_malformed_raw_source_controls(self):
        changes = [
            lambda s: s.update(parameters=[]),
            lambda s: s.update(witness_parameters=["constant"]),
            lambda s: s.update(parent_count=True),
            lambda s: s.update(physical_owner={"crate": 0, "index": 6}),
            lambda s: s.update(typeck_owner={"crate": 0, "index": 999}),
            lambda s: s.update(by_move_owner=s["owner"]),
            lambda s: s.update(identity_kind={"kind": "atom", "sort": "type", "tag": "int", "payload": "i64"}),
            lambda s: s["layout"].update(storage_conflicts=[]),
            lambda s: s["layout"].update(storage_conflicts=[[0, 0]]),
            lambda s: s["layout"].update(variant_fields=[[], [], [], [1]]),
            lambda s: s["layout"]["field_tys"][0].update(source_info={"span": 0, "scope": 0}),
            lambda s: s["layout"]["field_tys"][0].update(type={"kind": "parameter", "sort": "type", "index": 99}),
            lambda s: s["layout"]["field_tys"][0]["type"].update(unexpected=True),
        ]
        for index, change in enumerate(changes):
            with self.subTest(index=index):
                document = fixture()
                change(document["compiler_coroutine_coverage"]["generic_sources"][0])
                with self.assertRaises(ValueError):
                    validate_catalog(document)

    def test_duplicate_raw_physical_owner(self):
        document = fixture()
        rows = document["compiler_coroutine_coverage"]["generic_sources"]
        rows.append(copy.deepcopy(rows[0]))
        with self.assertRaisesRegex(ValueError, "duplicate physical owner"):
            validate_catalog(document)

    def test_generated_owner_requires_both_consistent_declarations(self):
        document = fixture()
        rows = document["compiler_coroutine_coverage"]["generic_sources"]
        source = rows[0]
        kind = {"kind": "atom", "sort": "type", "tag": "int", "payload": "i16"}
        source["identity_kind"] = kind
        source["type_expression"]["children"][1] = kind
        source["by_move_owner"] = {"crate": 0, "index": 8}
        document["definitions"].append({"crate": 0, "index": 8})
        with self.assertRaisesRegex(ValueError, "physical owner missing"):
            validate_catalog(document)
        generated = copy.deepcopy(source)
        generated["physical_owner"] = source["by_move_owner"]
        rows.append(generated)
        validate_catalog(document)
        generated["typeck_owner"] = source["owner"]
        with self.assertRaisesRegex(ValueError, "inconsistent logical owner"):
            validate_catalog(document)


if __name__ == "__main__":
    unittest.main()
