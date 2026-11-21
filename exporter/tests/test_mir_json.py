import copy
import gzip
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "tools"))
from shared_json_pools import SHARED_POOLS, pool_document, expand_document
from mir_json import MirJSONError, POOL_NAMES, decode_mir_document, load_mir_document, pool_entry


def document(**fields):
    value = {"schema": "lean-miri-rustc-mir", "schema_version": 17,
             **{name: [] for name in POOL_NAMES}, **{name: [] for name in SHARED_POOLS},
             "files": [], "byte_images": [], "source_trait_material": {},
             "source_vtables": {}, "source_abi": {}, "source_cast_targets": [],
             "root_declarations": [], **fields}
    value.setdefault("compiler_coroutine_coverage", {
        "body_coroutines": [False] * (len(value["bodies"]) if isinstance(value["bodies"], list) else 0),
        "coroutines": [], "auxiliary_bodies": []})
    return value


class MirJSONTests(unittest.TestCase):
    def test_preserves_recursive_references(self):
        encoded = document(types=[{"shape": {"pointee": 0}, "source_layout": {"normalized_type": 0}}],
                           payload={"type": 0})
        self.assertIs(decode_mir_document(encoded), encoded)
        self.assertEqual(encoded["payload"], {"type": 0})
        self.assertEqual(pool_entry(encoded, "types", 0)["shape"]["pointee"], 0)

    def test_pool_spaces_and_allocation_identity(self):
        encoded = document(types=[{"kind": "type"}], instances=[{"kind": "instance"}],
                           allocations=[{"allocation_id": 0, "byte_image_id": 0}, {"allocation_id": 1, "byte_image_id": 0}],
                           byte_images=[""])
        self.assertEqual(pool_entry(encoded, "types", 0)["kind"], "type")
        self.assertEqual(pool_entry(encoded, "instances", 0)["kind"], "instance")
        self.assertIsNot(pool_entry(encoded, "allocations", 0), pool_entry(encoded, "allocations", 1))

    def test_grouped_functions_keep_exact_graph_and_source_ids(self):
        encoded = document(allocations=[
            {"allocation_id": 1, "kind": "memory", "byte_image_id": 0},
            {"kind": "function", "instance_id": 7, "identities": [[0, 11], [2, 29]]}],
            byte_images=[""])
        self.assertEqual(pool_entry(encoded, "allocations", 2), {
            "kind": "function", "instance_id": 7, "allocation_id": 2, "source_alloc_id": 29})
        self.assertEqual(pool_entry(encoded, "allocations", 1)["kind"], "memory")
        with self.assertRaises(MirJSONError):
            pool_entry(encoded, "allocations", 3)

    def test_rejects_invalid_pool_access(self):
        encoded = document(types=[{}])
        for index in (-1, 1, True, 0.0, {"type_id": 0}):
            with self.subTest(index=index), self.assertRaises(MirJSONError):
                pool_entry(encoded, "types", index)
        with self.assertRaises(MirJSONError):
            pool_entry(encoded, "generic_args", 0)

    def test_requires_pool_arrays_and_object_definitions(self):
        for name in POOL_NAMES:
            for value in (None, {}, [0]):
                with self.subTest(name=name, value=value), self.assertRaises(MirJSONError):
                    decode_mir_document(document(**{name: value}))

    def test_requires_current_schema_version(self):
        for version in (4, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, True, "17", 17.0):
            with self.subTest(version=version), self.assertRaisesRegex(MirJSONError, "schema_version must be 17"):
                decode_mir_document(document(schema_version=version))

    def test_current_schema_requires_exact_coroutine_catalog_and_preserves_version(self):
        catalog = {"body_coroutines": [], "coroutines": [], "auxiliary_bodies": []}
        current = document(schema_version=17, compiler_coroutine_coverage=catalog)
        self.assertIs(decode_mir_document(current), current)
        self.assertEqual(expand_document(current)["schema_version"], 17)
        for invalid in (None, {}, {**catalog, "unknown_witness": True},
                        {**catalog, "body_coroutines": [False]},
                        {**catalog, "body_coroutines": [0]}):
            with self.subTest(catalog=invalid), self.assertRaises(MirJSONError):
                decode_mir_document(document(schema_version=17, compiler_coroutine_coverage=invalid))
        with self.assertRaises(MirJSONError):
            missing = document()
            del missing["compiler_coroutine_coverage"]
            decode_mir_document(missing)

    def test_coroutine_auxiliary_roles_and_source_pool_round_trip(self):
        body = {"instance_id": 0, "source_def_id": 0,
                "phase": {"kind": "runtime", "phase": "optimized"}, "source_scopes": [{}]}
        auxiliary = {"owner_body": 0, "role": "async", "source_kind": {"kind": "item", "def_id": 0},
                     "body": {**body, "phase": {"kind": "analysis", "phase": "post_cleanup"}}}
        witness = {"owner_body": 0, "coroutine_type": 0,
                   "coroutine_kind": {"kind": "coroutine", "movability": "movable"},
                   "yield_type": None, "resume_type": None,
                   "layout": {"field_tys": [{"type": 0, "source_info": 0,
                                             "ignore_for_traits": False, "debuginfo_name": None}],
                              "variant_fields": [[], [], []],
                              "variant_source_info": [{"span": 0, "scope": 0}] * 3,
                              "storage_conflicts": [[]]},
                   "drop_sync": None, "drop_async": 0, "drop_proxy_async": None}
        catalog = {"body_coroutines": [True], "coroutines": [witness], "auxiliary_bodies": [auxiliary]}
        current = document(schema_version=17, bodies=[body], types=[{}], instances=[{}], definitions=[{}], spans=[{}],
                           source_infos=[{"span": 0, "scope": 0}], compiler_coroutine_coverage=catalog)
        self.assertIs(decode_mir_document(current), current)
        expanded = expand_document(current)
        self.assertEqual(expanded["compiler_coroutine_coverage"]["coroutines"][0]["layout"]["field_tys"][0]["source_info"],
                         {"span": 0, "scope": 0})
        self.assertEqual(current["compiler_coroutine_coverage"]["coroutines"][0]["layout"]["field_tys"][0]["source_info"], 0)
        mutations = [
            lambda d: d["compiler_coroutine_coverage"]["coroutines"][0]["coroutine_kind"].update(unknown_witness=True),
            lambda d: d["compiler_coroutine_coverage"]["auxiliary_bodies"][0].update(role="callable"),
            lambda d: d["compiler_coroutine_coverage"]["auxiliary_bodies"][0]["source_kind"].update(unknown_witness=True),
            lambda d: d["compiler_coroutine_coverage"]["coroutines"][0]["layout"]["field_tys"][0].update(source_info=True),
            lambda d: d["compiler_coroutine_coverage"]["coroutines"][0].update(drop_async=True),
        ]
        for mutate in mutations:
            invalid = copy.deepcopy(current)
            mutate(invalid)
            with self.assertRaises(MirJSONError):
                decode_mir_document(invalid)

    def test_source_material_keeps_its_typed_reference_graph(self):
        current = document(types=[{"source_layout": {"normalized_type": 0},
                                   "shape": {"kind": "raw_pointer", "pointee": 0}}],
                           root_declarations=[{"definition": 0, "def_path": "generic", "generic_parameters": ["type"]}])
        self.assertIs(decode_mir_document(current), current)
        self.assertEqual(pool_entry(current, "types", 0)["shape"]["pointee"], 0)
        for name in ("source_trait_material", "source_vtables", "source_abi"):
            with self.subTest(name=name), self.assertRaises(MirJSONError):
                decode_mir_document(document(**{name: []}))

    def test_filename_ids_stay_shared_and_unexpanded(self):
        encoded = document(files=["src/a.rs", "src/b.rs"],
                           spans=[{"file": 0, "runtime_file": 1}, {"file": 1, "runtime_file": 0}])
        self.assertIs(decode_mir_document(encoded), encoded)
        self.assertEqual([row["file"] for row in encoded["spans"]], [0, 1])
        self.assertEqual([row["runtime_file"] for row in encoded["spans"]], [1, 0])
        for invalid in (None, {}, [0], ["src/a.rs", False]):
            with self.subTest(invalid=invalid), self.assertRaises(MirJSONError):
                decode_mir_document(document(files=invalid))

    def test_lossless_pool_projection_preserves_identity_and_defaults(self):
        raw = document(types=[{"source_layout": {"normalized_type": 0, "is_box": False,
                                                "simd": None, "variant_discriminants": []}}],
            bodies=[{"locals": [{"source_info": {"span": 0, "scope": 0}}],
                     "basic_blocks": [{"statements": [{"source_info": {"span": 0, "scope": 0},
                        "kind": {"variant": "Nop"}}], "terminator": {"source_info": {"span": 0, "scope": 0},
                        "kind": {"variant": "Return"}}}]}],
            allocations=[{"allocation_id": 0, "initialization_ranges": [], "relocations": []},
                         {"allocation_id": 1, "initialization_ranges": [], "relocations": []}])
        for name in SHARED_POOLS:
            raw.pop(name, None)
        pooled = pool_document(raw)
        self.assertEqual(expand_document(pooled), raw)
        self.assertEqual(len(pooled["source_infos"]), 1)
        statement = pooled["bodies"][0]["basic_blocks"][0]["statements"][0]
        self.assertIs(type(statement["source_info"]), int)
        self.assertIs(type(statement["kind"]), int)
        self.assertIs(type(pooled["bodies"][0]["locals"][0]["source_info"]), int)
        self.assertIs(type(pooled["bodies"][0]["basic_blocks"][0]["terminator"]["source_info"]), int)
        self.assertIsInstance(pooled["bodies"][0]["basic_blocks"][0]["terminator"]["kind"], dict)
        self.assertIsNone(pooled["types"][0]["source_layout"]["simd"])
        self.assertIs(pooled["types"][0]["source_layout"]["is_box"], False)
        self.assertEqual(pooled["relocations"], [[]])
        self.assertEqual([node["allocation_id"] for node in pooled["allocations"]], [0, 1])

    def test_shared_pool_shape_and_reference_bounds(self):
        encoded = document(source_infos=[{"span": 0, "scope": 0}])
        self.assertEqual(pool_entry(encoded, "source_infos", 0), {"span": 0, "scope": 0})
        for invalid in (-1, 1, True, "0"):
            with self.subTest(index=invalid), self.assertRaises(MirJSONError):
                pool_entry(encoded, "source_infos", invalid)
        for name, row_type in SHARED_POOLS.items():
            for invalid in (None, {}, [0]):
                with self.subTest(pool=name, value=invalid), self.assertRaises(MirJSONError):
                    decode_mir_document(document(**{name: invalid}))

    def test_loads_gzip_archives(self):
        encoded = document(payload={"type": 0}, types=[{}])
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "export.json.gz"
            with gzip.open(path, "wt", encoding="utf-8") as stream:
                json.dump(encoded, stream)
            self.assertEqual(load_mir_document(path), encoded)


if __name__ == "__main__":
    unittest.main()
