#!/usr/bin/env python3
"""Fresh compiler captures for the finite foundation format (pinned toolchain required)."""
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]

class FoundationExport(unittest.TestCase):
    def export(self, root, destination):
        return subprocess.run([
            "bash", "tools/export-mir.sh", "--output", str(destination),
            "--foundation", "--root", root, "--", "exporter/fixtures/foundation.rs",
            "--crate-type=lib", "--crate-name", "foundation",
        ], cwd=ROOT, capture_output=True, text=True)

    def test_generic_templates_and_concrete_array(self):
        with tempfile.TemporaryDirectory(prefix="foundation-") as directory:
            for root in ("identity", "array_identity", "concrete", "link_identity"):
                output = Path(directory) / f"{root}.json"
                result = self.export(root, output)
                self.assertEqual(result.returncode, 0, result.stderr)
                doc = json.loads(output.read_text())
                self.assertEqual((doc["schema"], doc["schema_version"]), ("lean-miri-foundation", 1))
                self.assertEqual(doc["target"]["architecture"], "x86_64")
                root_span = doc["session"]["root_span"]
                self.assertEqual((root_span["is_dummy"], root_span["lo"], root_span["hi"], root_span["ctxt"]), (True, 0, 0, "#0"))
                self.assertEqual(len(doc["bodies"]), 1)
                self.assertEqual(doc["bodies"][0]["required_consts"], [])
                self.assertEqual(doc["bodies"][0]["promoted_count"], 0)
                self.assertEqual(doc["definitions"][doc["bodies"][0]["definition"]]["kind"], "fn")
                self.assertFalse(any(key.startswith("compiler_") for key in doc))
                shapes = [node["shape"] for node in doc["types"]]
                if root == "identity":
                    self.assertIn({"kind":"param", "index":0, "name":"T"}, shapes)
                if root == "array_identity":
                    array = next(s for s in shapes if s["kind"] == "array")
                    self.assertEqual(array["length"], {"kind":"param", "index":1, "name":"N"})
                    params = doc["bodies"][0]["environment"]["parameters"]
                    self.assertEqual([(p["kind"], p["index"]) for p in params], [("type",0),("const",1)])
                if root == "concrete":
                    array = next(s for s in shapes if s["kind"] == "array")
                    self.assertEqual(array["length"]["bits"], "3")
                value = doc["bodies"][0]["blocks"][0]["statements"][0]["value"]
                self.assertTrue(value["retag"])
                if root == "link_identity":
                    definitions = [d for d in doc["definitions"] if "adt" in d]
                    self.assertEqual(len(definitions), 1)
                    self.assertEqual(len(definitions[0]["adt"]["variants"][0]["fields"]), 2)
                    self.assertLess(len(doc["types"]), 10)
                    self.assertNotIn(None, doc["types"])

    def test_source_entry_selection_preserves_library_absence_and_rustc_main(self):
        with tempfile.TemporaryDirectory(prefix="foundation-entry-") as directory:
            output = Path(directory) / "library.json"
            result = self.export("identity", output)
            self.assertEqual(result.returncode, 0, result.stderr)
            library = json.loads(output.read_text())
            self.assertIsNone(library["entry_selection"]["compiler_entry"])
            source = Path(directory) / "main.rs"
            source.write_text("fn main() {}\n")
            output = Path(directory) / "binary.json"
            result = subprocess.run([
                "bash", "tools/export-mir.sh", "--output", str(output),
                "--foundation", "--root", "main", "--", str(source),
                "--crate-name", "entry_source",
            ], cwd=ROOT, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            binary = json.loads(output.read_text())
            entry = binary["entry_selection"]["compiler_entry"]
            self.assertEqual(entry, {"definition":binary["bodies"][0]["definition"],"kind":"rustc_main","sigpipe":0})
            self.assertIsNotNone(binary["entry_selection"]["start_lang_item"])
            self.assertNotIn("allocations", binary)

    def test_backtraces_match_schema12_body_hygiene_collapse(self):
        with tempfile.TemporaryDirectory(prefix="foundation-backtrace-") as directory:
            source = Path(directory) / "macro.rs"
            source.write_text('macro_rules! value { () => {{ 7_u32 }} }\npub fn item() -> u32 { value!() }\n')
            documents = []
            for mode in ("foundation", "schema12"):
                output = Path(directory) / f"{mode}.json"
                result = subprocess.run([
                    "bash", "tools/export-mir.sh", "--output", str(output),
                    *(["--foundation"] if mode == "foundation" else []),
                    "--root", "item", "--", str(source),
                    "--crate-type=lib", "--crate-name", "macro_source",
                ], cwd=ROOT, capture_output=True, text=True)
                self.assertEqual(result.returncode, 0, result.stderr)
                documents.append(json.loads(output.read_text()))
            foundation, legacy = documents
            expected = []
            for record in legacy["backtrace_spans"][legacy["bodies"][0]["backtrace_spans"]]:
                raw = dict(legacy["spans"][record["span"]])
                raw["file"] = legacy["files"][raw["file"]]
                position = dict(record["source_position"])
                position["filename"] = legacy["files"][position["filename"]]
                expected.append({"span":raw,"source_position":position})
            actual = foundation["bodies"][0]["source_metadata"]["backtrace_spans"]
            comparable = [{"span":{k:v for k,v in row["span"].items() if k not in ("span_id", "parent_local_definition")}, "source_position":row["source_position"]} for row in actual]
            self.assertEqual(comparable, expected)
            self.assertTrue(any(row["span"]["ctxt"] != "#0" for row in actual))

    def test_source_signatures_preserve_generic_safety_and_abi(self):
        with tempfile.TemporaryDirectory(prefix="foundation-signature-") as directory:
            source = Path(directory) / "signatures.rs"
            source.write_text('pub fn generic<T: Copy>(x: T) -> T { x }\npub unsafe extern "C" fn c_unsafe(x: u32) -> u32 { x }\npub extern "C-unwind" fn c_unwind(x: u32) -> u32 { x }\n')
            for root, safety, abi, unwind in (
                ("generic", "safe", "rust", None),
                ("c_unsafe", "unsafe", "c", False),
                ("c_unwind", "safe", "c", True),
            ):
                output = Path(directory) / f"{root}.json"
                result = subprocess.run([
                    "bash", "tools/export-mir.sh", "--output", str(output),
                    "--foundation", "--root", root, "--", str(source),
                    "--crate-type=lib", "--crate-name", "signatures",
                ], cwd=ROOT, capture_output=True, text=True)
                self.assertEqual(result.returncode, 0, result.stderr)
                doc = json.loads(output.read_text())
                self.assertEqual(doc["compilation"], {"panic_strategy":"unwind","panic_in_drop":"unwind","opt_level":"No"})
                body = doc["bodies"][0]
                metadata = body["source_metadata"]
                self.assertEqual(len(metadata["locals"]), len(body["locals"]))
                self.assertTrue(metadata["scopes"])
                self.assertEqual(len(metadata["blocks"]), len(body["blocks"]))
                for source_block, block in zip(metadata["blocks"], body["blocks"]):
                    self.assertEqual(len(source_block["statements"]), len(block["statements"]))
                    self.assertLess(source_block["terminator"]["scope"], len(metadata["scopes"]))
                signature = body["signature"]
                self.assertEqual(signature["safety"], safety)
                self.assertEqual(signature["abi"], {"kind":abi,"unwind":unwind})
                self.assertFalse(signature["c_variadic"])
                self.assertEqual(signature["inputs"], [signature["output"]])
                self.assertEqual(signature["inputs"], body["locals"][1:2])
                self.assertEqual(body["function_attributes"], {
                    "never_unwind":False,"track_caller":False,
                    "is_foreign":False,"is_drop_glue":False,
                })
                shape = doc["types"][signature["output"]]["shape"]
                self.assertEqual(shape, {"kind":"param","index":0,"name":"T"}
                                 if root == "generic" else {"kind":"uint","name":"u32"})

    def test_promoted_tables_and_inherited_associated_environment_abort(self):
        with tempfile.TemporaryDirectory(prefix="foundation-promoted-") as directory:
            source = Path(directory) / "promoted.rs"
            source.write_text('pub struct S; impl S { pub fn identity(x: u8) -> u8 { x } }\n'
                              'pub fn promoted() -> *const u8 { &42u8 as *const u8 }\n')
            for root in ("S::identity", "promoted"):
                output = Path(directory) / f"{root.replace('::', '_')}.json"
                result = subprocess.run([
                    "bash", "tools/export-mir.sh", "--output", str(output),
                    "--foundation", "--root", root, "--", str(source),
                    "--crate-type=lib", "--crate-name", "promoted",
                ], cwd=ROOT, capture_output=True, text=True)
                if root == "promoted":
                    self.assertNotEqual(result.returncode, 0)
                    self.assertIn("unsupported promoted bodies: 1", result.stderr)
                    self.assertFalse(output.exists())
                else:
                    self.assertNotEqual(result.returncode, 0)
                    self.assertIn("unsupported inherited generic environment", result.stderr)
                    self.assertFalse(output.exists())

    def test_variadic_frame_remains_fail_closed(self):
        with tempfile.TemporaryDirectory(prefix="foundation-variadic-") as directory:
            source = Path(directory) / "variadic.rs"
            source.write_text('pub unsafe extern "C" fn variadic(x: u32, _: ...) -> u32 { x }\n')
            output = Path(directory) / "variadic.json"
            result = subprocess.run([
                "bash", "tools/export-mir.sh", "--output", str(output),
                "--foundation", "--root", "variadic", "--", str(source),
                "--crate-type=lib", "--crate-name", "variadic",
            ], cwd=ROOT, capture_output=True, text=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("unsupported generic parameter", result.stderr)
            self.assertIn("VaList", result.stderr)
            self.assertFalse(output.exists())

    def test_bound_signature_aborts_without_erasing_regions(self):
        with tempfile.TemporaryDirectory(prefix="foundation-bound-signature-") as directory:
            source = Path(directory) / "bound.rs"
            source.write_text("pub fn borrowed(x: &u8) -> &u8 { x }\n")
            output = Path(directory) / "bound.json"
            result = subprocess.run([
                "bash", "tools/export-mir.sh", "--output", str(output),
                "--foundation", "--root", "borrowed", "--", str(source),
                "--crate-type=lib", "--crate-name", "bound",
            ], cwd=ROOT, capture_output=True, text=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("unsupported bound function signature", result.stderr)
            self.assertFalse(output.exists())

    def test_unsupported_source_and_missing_root_abort(self):
        with tempfile.TemporaryDirectory(prefix="foundation-") as directory:
            for root, diagnostic in (("missing", "missing MIR root"),
                                     ("requires_const", "unsupported generic or promoted const definition"),
                                     ("tracked", "unsupported caller location prerequisite"),
                                     ("feature_identity", "unsupported function target features")):
                output = Path(directory) / f"{root}.json"
                result = self.export(root, output)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn(diagnostic, result.stderr)
                self.assertFalse(output.exists())

if __name__ == "__main__":
    unittest.main()
