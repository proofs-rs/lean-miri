import gzip
import json
from pathlib import Path
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parents[2] / "tools"))
from mir_json import MirJSONError, POOL_NAMES, decode_mir_document, load_mir_document, pool_entry


def document(**fields):
    return {"schema": "lean-miri-rustc-mir", "schema_version": 5,
            **{name: [] for name in POOL_NAMES}, "files": [], **fields}


class MirJSONTests(unittest.TestCase):
    def test_preserves_recursive_references(self):
        encoded = document(types=[{"shape": {"pointee": 0}, "layout": 0}],
                           layouts=[{"size_bytes": 8}], payload={"type": 0})
        self.assertIs(decode_mir_document(encoded), encoded)
        self.assertEqual(encoded["payload"], {"type": 0})
        self.assertEqual(pool_entry(encoded, "types", 0)["shape"]["pointee"], 0)

    def test_pool_spaces_and_allocation_identity(self):
        encoded = document(types=[{"kind": "type"}], instances=[{"kind": "instance"}],
                           allocations=[{"bytes": []}, {"bytes": []}])
        self.assertEqual(pool_entry(encoded, "types", 0)["kind"], "type")
        self.assertEqual(pool_entry(encoded, "instances", 0)["kind"], "instance")
        self.assertIsNot(pool_entry(encoded, "allocations", 0), pool_entry(encoded, "allocations", 1))

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
        with self.assertRaisesRegex(MirJSONError, "schema_version must be 5"):
            decode_mir_document(document(schema_version=4))

    def test_filename_ids_stay_shared_and_unexpanded(self):
        encoded = document(files=["src/a.rs", "src/b.rs"],
                           spans=[{"file": 0}, {"file": 1}, {"file": 0}],
                           bodies=[{"backtrace_spans": [{"source_position": {"filename": 0}}]}])
        self.assertIs(decode_mir_document(encoded), encoded)
        self.assertEqual([row["file"] for row in encoded["spans"]], [0, 1, 0])
        self.assertEqual(encoded["bodies"][0]["backtrace_spans"][0]["source_position"]["filename"], 0)
        for invalid in (None, {}, [0], ["src/a.rs", False]):
            with self.subTest(invalid=invalid), self.assertRaises(MirJSONError):
                decode_mir_document(document(files=invalid))

    def test_loads_gzip_archives(self):
        encoded = document(payload={"type": 0}, types=[{}])
        with tempfile.TemporaryDirectory() as directory:
            path = Path(directory) / "export.json.gz"
            with gzip.open(path, "wt", encoding="utf-8") as stream:
                json.dump(encoded, stream)
            self.assertEqual(load_mir_document(path), encoded)


if __name__ == "__main__":
    unittest.main()
