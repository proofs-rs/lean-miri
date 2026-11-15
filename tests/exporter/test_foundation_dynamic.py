#!/usr/bin/env python3
"""Finite existential syntax against the existing pinned compiler capture."""
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
ROOT = Path(__file__).resolve().parents[2]

class FoundationDynamic(unittest.TestCase):
    def test_source_predicates_match_compiler_capture(self):
        with tempfile.TemporaryDirectory(prefix="foundation-dynamic-") as directory:
            documents = []
            for mode in ("foundation", "schema12"):
                output = Path(directory) / f"{mode}.json"
                result = subprocess.run([
                    "bash", "tools/export-mir.sh", "--output", str(output),
                    *(["--foundation"] if mode == "foundation" else []),
                    "--root", "dynamic_input", "--", "exporter/fixtures/foundation_dynamic.rs",
                    "--crate-type=lib", "--crate-name", "foundation_dynamic",
                ], cwd=ROOT, capture_output=True, text=True)
                self.assertEqual(result.returncode, 0, result.stderr)
                documents.append(json.loads(output.read_text()))
            source, compiler = documents
            actual = [t["shape"] for t in source["types"] if t["shape"]["kind"] == "dynamic"]
            expected = [t["shape"] for t in compiler["types"] if t["shape"]["kind"] == "dynamic_trait_object"]
            self.assertEqual({t["region"] for t in actual}, {"erased", "static"})
            def identity(doc, definition, finite):
                row = doc["definitions"][definition]
                return (row["crate_index" if finite else "crate"], row["index"])
            def type_shape(doc, index):
                shape = doc["types"][index]["shape"]
                if shape["kind"] == "tuple":
                    return ("tuple", tuple(type_shape(doc, t) for t in shape["elements"]))
                return (shape["kind"], shape.get("name", shape.get("signed_kind")))
            for shape in actual:
                counterpart = next(t for t in expected if t["region"]["kind"] == shape["region"])
                predicates = [compiler["predicates"][i] for i in counterpart["predicates"]]
                self.assertEqual(len(shape["predicates"]), len(predicates))
                for got, want in zip(shape["predicates"], predicates):
                    self.assertEqual(got["kind"], want["kind"])
                    self.assertEqual(identity(source, got["definition"], True), identity(compiler, want["def_id"], False))
                    self.assertEqual(got["bound_variables"], want["bound_variables"])
                    if got["kind"] != "auto_trait":
                        self.assertEqual([type_shape(source,a["type"]) for a in got["arguments"]],
                                         [type_shape(compiler,a["value"]) for a in want["generic_args"]])
                    if got["kind"] == "projection":
                        self.assertEqual(got["term"]["kind"], "type")
                        self.assertEqual(type_shape(source,got["term"]["type"]), type_shape(compiler,want["term"]["value"]))
                        self.assertTrue(want["def_path"].startswith(source["definitions"][got["parent_trait"]]["path"] + "::"))
            self.assertNotIn("compiler_vtable_queries", source)

    def test_higher_ranked_source_predicate_rejects(self):
        with tempfile.TemporaryDirectory(prefix="foundation-dynamic-bound-") as directory:
            source = Path(directory) / "bound.rs"
            source.write_text("pub fn input(_: &'static (dyn for<'a> Fn(&'a u8) -> i32 + Sync)) {}\n")
            output = Path(directory) / "bound.json"
            result = subprocess.run([
                "bash", "tools/export-mir.sh", "--output", str(output), "--foundation", "--root", "input", "--",
                str(source), "--crate-type=lib", "--crate-name", "bound_dynamic",
            ], cwd=ROOT, capture_output=True, text=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("bound existential predicate", result.stderr)
            self.assertFalse(output.exists())

if __name__ == "__main__":
    unittest.main()
