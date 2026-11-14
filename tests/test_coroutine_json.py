"""Strict raw coroutine catalog wire controls; no compiler authenticity claim."""
import copy
import json
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


def template_fixture():
    document = fixture()
    arguments = [{"kind": "type", "value": 0}] * 6
    document["types"] = [{"shape": {"kind": "coroutine", "def_id": 1, "generic_args": arguments}}]
    document["instances"] = [{"instance_id": 0, "instance_kind": {"kind": "item", "def_id": 1}, "generic_args": arguments}]
    document["bodies"] = [{"body_kind": "copy_template", "template_id": 0, "instance_id": 0,
                           "generic_args": arguments, "promoted_bodies": []}]
    document["mir_templates"] = [{"source_role": "runtime", "source_promoted": None,
        "source_def_id": 1, "def_path": "owner", "span": 0, "preamble_def_span": 0,
        "injection_phase": None, "local_sources": [], "source_scopes": [{}], "backtrace_spans": [],
        "template": json.dumps({"parameters": ["type"] * 6, "types": [], "skeleton": {
            "phase": "runtime_optimized", "argument_count": 0, "spread_argument": None,
            "locals": [], "blocks": []}})}]
    catalog = document["compiler_coroutine_coverage"]
    catalog["body_coroutines"] = [True]
    catalog["coroutines"] = [{"owner_body": 0, "coroutine_type": 0,
        "coroutine_kind": {"kind": "coroutine", "movability": "movable"},
        "yield_type": None, "resume_type": None, "drop_sync": 0, "drop_async": None, "drop_proxy_async": 1,
        "layout": {"field_tys": [], "variant_fields": [[], [], []],
                   "variant_source_info": [{"span": 0, "scope": 0}] * 3, "storage_conflicts": []}}]
    catalog["auxiliary_bodies"] = [{"owner_body": 0, "role": role, "source_kind": kind,
        "body": {"instance_id": 0, "source_def_id": 1, "phase": {"kind": "runtime", "phase": "initial"}}}
        for role, kind in [("sync", {"kind": "shim", "shim_kind": "drop_glue", "def_id": 1, "drop_type": 0}),
                           ("proxy_async", {"kind": "item", "def_id": 1})]]
    return document


class CoroutineCatalogTests(unittest.TestCase):
    def test_valid_raw_runtime_template_owner(self):
        validate_catalog(template_fixture())

    def test_raw_template_owner_header_controls(self):
        changes = [
            lambda d: d["bodies"][0].update(template_id=1),
            lambda d: d["mir_templates"][0].update(source_role="ctfe"),
            lambda d: d["mir_templates"][0].update(source_promoted=0),
            lambda d: d["mir_templates"][0].update(source_def_id=0),
            lambda d: d["mir_templates"][0].update(template="{"),
            lambda d: d["mir_templates"][0].update(template='{"parameters":[],"parameters":[]}'),
            lambda d: d["mir_templates"][0].update(source_scopes=[]),
            lambda d: d["bodies"][0].update(generic_args=[]),
            lambda d: d["instances"][0].update(instance_kind={"kind": "item", "def_id": 0}),
            lambda d: d["instances"][0].update(instance_id=1),
            lambda d: d["types"][0]["shape"].update(generic_args=[]),
            lambda d: d["bodies"][0].update(instance_id=1),
        ]
        for index, change in enumerate(changes):
            with self.subTest(index=index):
                document = template_fixture()
                change(document)
                with self.assertRaises(ValueError):
                    validate_catalog(document)
        for key, value in [("phase", "analysis"), ("parameters", ["constant"] * 6)]:
            document = template_fixture()
            source = document["mir_templates"][0]
            template = json.loads(source["template"])
            if key == "phase":
                template["skeleton"][key] = value
            else:
                template[key] = value
            source["template"] = json.dumps(template)
            with self.assertRaises(ValueError):
                validate_catalog(document)

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
