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
    return {"schema": "lean-miri-rustc-mir", "schema_version": 9,
            **{name: [] for name in POOL_NAMES}, **{name: [] for name in SHARED_POOLS}, "layouts": [], "files": [], "byte_images": [], **fields}


class MirJSONTests(unittest.TestCase):
    def test_preserves_recursive_references(self):
        encoded = document(types=[{"shape": {"pointee": 0}, "layout": 0}],
                           layouts=[0], layout_values=[{"size_bytes": 8}], payload={"type": 0})
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
        for version in (4, 6, 7, 8, True, "9", 9.0):
            with self.subTest(version=version), self.assertRaisesRegex(MirJSONError, "schema_version must be 9"):
                decode_mir_document(document(schema_version=version))

    def test_filename_ids_stay_shared_and_unexpanded(self):
        encoded = document(files=["src/a.rs", "src/b.rs"],
                           spans=[{"file": 0}, {"file": 1}, {"file": 0}],
                           bodies=[{"backtrace_spans": 0}],
                           backtrace_spans=[[{"source_position": {"filename": 0}}]])
        self.assertIs(decode_mir_document(encoded), encoded)
        self.assertEqual([row["file"] for row in encoded["spans"]], [0, 1, 0])
        self.assertEqual(encoded["backtrace_spans"][0][0]["source_position"]["filename"], 0)
        for invalid in (None, {}, [0], ["src/a.rs", False]):
            with self.subTest(invalid=invalid), self.assertRaises(MirJSONError):
                decode_mir_document(document(files=invalid))

    def test_lossless_pool_projection_preserves_identity_and_defaults(self):
        raw = document(schema_version=8, layouts=[{"size_bytes": 0}, {"size_bytes": 0}],
            types=[{"compiler_facts": {"boolean_queries": {"is_dynamic": False},
                    "discriminants": {"has_discriminants": False, "values": [], "adt_variant_count": None}}}],
            bodies=[{"backtrace_spans": [], "locals": [{"source_info": {"span": 0, "scope": 0}}],
                     "basic_blocks": [{"statements": [{"source_info": {"span": 0, "scope": 0},
                        "kind": {"variant": "Nop"}}], "terminator": {"source_info": {"span": 0, "scope": 0},
                        "kind": {"variant": "Return"}}}]}],
            allocations=[{"allocation_id": 0, "initialization_ranges": [], "relocations": []},
                         {"allocation_id": 1, "initialization_ranges": [], "relocations": []}])
        for name in SHARED_POOLS:
            raw.pop(name, None)
        pooled = pool_document(raw)
        self.assertEqual(expand_document(pooled, schema_version=8), raw)
        self.assertEqual(pooled["layouts"], [0, 0])
        self.assertEqual(len(pooled["layout_values"]), 1)
        self.assertEqual(len(pooled["source_infos"]), 1)
        statement = pooled["bodies"][0]["basic_blocks"][0]["statements"][0]
        self.assertIs(type(statement["source_info"]), int)
        self.assertIs(type(statement["kind"]), int)
        self.assertIs(type(pooled["bodies"][0]["locals"][0]["source_info"]), int)
        self.assertIs(type(pooled["bodies"][0]["basic_blocks"][0]["terminator"]["source_info"]), int)
        self.assertIsInstance(pooled["bodies"][0]["basic_blocks"][0]["terminator"]["kind"], dict)
        self.assertEqual(pooled["discriminants"][0]["adt_variant_count"], None)
        self.assertIs(pooled["boolean_queries"][0]["is_dynamic"], False)
        self.assertEqual(pooled["relocations"], [[]])
        self.assertEqual([node["allocation_id"] for node in pooled["allocations"]], [0, 1])

    def test_shared_pool_shape_and_reference_bounds(self):
        encoded = document(layouts=[0], layout_values=[{"size_bytes": 8}],
                           source_infos=[{"span": 0, "scope": 0}])
        self.assertEqual(pool_entry(encoded, "layouts", 0), {"size_bytes": 8})
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
