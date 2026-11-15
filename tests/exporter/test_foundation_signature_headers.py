#!/usr/bin/env python3
"""Explicit generic header demands must not contaminate unrelated material."""
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]


class FoundationSignatureHeaders(unittest.TestCase):
    def export(self, output, source, root, extra=(), foundation=True):
        return subprocess.run(["bash", "tools/export-mir.sh", "--output", str(output),
            *(["--foundation"] if foundation else []), *extra, "--root", root, "--", str(source),
            "--crate-type=lib", "--crate-name=signature_header_scope"], cwd=ROOT,
            capture_output=True, text=True)

    def test_tiny_and_typed_fn_pointer_leave_header_and_dyn_capability_absent(self):
        with tempfile.TemporaryDirectory(prefix="signature-scope-") as directory:
            for name, text in [("tiny", "pub fn identity(x:u8)->u8{x}"),
                ("pointer", "pub fn identity(x:fn()->())->fn()->(){x}")]:
                source = Path(directory) / f"{name}.rs"
                source.write_text(text)
                output = Path(directory) / f"{name}.json"
                result = self.export(output, source, "identity")
                self.assertEqual(result.returncode, 0, result.stderr)
                document = json.loads(output.read_text())
                self.assertEqual(document["source_signature_roots"], [])
                self.assertEqual(document["source_function_signatures"], [])
                self.assertIsNone(document["dyn_metadata_source"])
                self.assertFalse(any(row["shape"]["kind"] == "dynamic" for row in document["types"]))

    def test_track_caller_retains_raw_attribute_for_body_and_header(self):
        with tempfile.TemporaryDirectory(prefix="caller-source-attribute-") as directory:
            for tracked in [False, True]:
                source = Path(directory) / f"caller_{tracked}.rs"
                source.write_text(("#[track_caller]\n" if tracked else "") +
                                  "pub fn reference(value: u8) -> u8 { value }\n")
                output = Path(directory) / f"caller_{tracked}.json"
                result = self.export(output, source, "reference",
                                     ["--foundation-signature-root", "reference"])
                self.assertEqual(result.returncode, 0, result.stderr)
                document = json.loads(output.read_text())
                self.assertEqual(document["bodies"][0]["function_attributes"]["track_caller"], tracked)
                self.assertEqual(document["source_function_signatures"][0]["function_attributes"]["track_caller"], tracked)

    def test_explicit_std_header_has_no_executable_std_body(self):
        with tempfile.TemporaryDirectory(prefix="signature-demand-") as directory:
            output = Path(directory) / "source.json"
            result = self.export(output, "exporter/fixtures/foundation_signature_main.rs", "main",
                ["--foundation-signature-root", "std::rt::lang_start_internal"])
            self.assertEqual(result.returncode, 0, result.stderr)
            document = json.loads(output.read_text())
            self.assertEqual(document["source_signature_roots"], ["std::rt::lang_start_internal"])
            self.assertEqual(len(document["source_function_signatures"]), 1)
            header = document["source_function_signatures"][0]
            self.assertEqual(document["definitions"][header["definition"]]["path"], "std::rt::lang_start_internal")
            self.assertEqual(len(header["signature"]["inputs"]), 4)
            self.assertTrue(header["signature"]["bound_variables"])
            self.assertFalse(any(row["definition"] == header["definition"] for row in document["bodies"]))
            self.assertNotIn("locals", header)
            self.assertNotIn("blocks", header)
            self.assertNotIn("abi_query", header)
            self.assertIsNotNone(document["dyn_metadata_source"])

    def test_inherent_header_requires_selected_source_closure(self):
        with tempfile.TemporaryDirectory(prefix="inherent-signature-") as directory:
            output = Path(directory) / "source.json"
            requested = ["--foundation-signature-root", "std::process::ExitCode::to_i32"]
            result = self.export(output, "exporter/fixtures/foundation_signature_main.rs", "main", requested)
            self.assertNotEqual(result.returncode, 0)
            self.assertFalse(output.exists())
            result = self.export(output, "exporter/fixtures/foundation_signature_main.rs",
                "std::rt::lang_start::{closure#0}", requested)
            self.assertEqual(result.returncode, 0, result.stderr)
            document = json.loads(output.read_text())
            headers = document["source_function_signatures"]
            requested_headers = [row for row in headers if document["definitions"][row["definition"]]["path"] ==
                                 "std::process::ExitCode::to_i32"]
            self.assertEqual(len(requested_headers), 1)
            header = requested_headers[0]
            self.assertEqual(len({row["definition"] for row in headers}), len(headers))
            direct_calls = set()
            for body in document["bodies"] + document["closure_templates"]:
                for block in body["blocks"]:
                    term = block["terminator"]
                    if term["kind"] == "call" and term["function"]["kind"] == "constant":
                        shape = document["types"][term["function"]["type"]]["shape"]
                        if shape["kind"] == "function_definition":
                            direct_calls.add(shape["definition"])
            self.assertEqual({row["definition"] for row in headers}, direct_calls | {header["definition"]})
            owner = header["owner_declaration"]
            self.assertEqual(owner["kind"], "inherent_method")
            implementation = document["definitions"][owner["impl_definition"]]
            self.assertEqual(implementation["generic_declaration"]["self_type"], owner["self_type"])
            self.assertEqual(document["definitions"][header["definition"]]["kind"], "assoc_fn")
            self.assertFalse(any(row["definition"] == header["definition"] for row in document["bodies"]))
            self.assertNotIn("locals", header)
            self.assertNotIn("abi_query", header)

    def test_unsupported_or_wrong_mode_signature_demand_rejects(self):
        with tempfile.TemporaryDirectory(prefix="signature-reject-") as directory:
            for foundation, requested, expected in [(False, "std::rt::lang_start_internal", "requires --foundation"),
                (True, "unknown::function", "missing source definition")]:
                output = Path(directory) / f"{foundation}.json"
                result = self.export(output, "exporter/fixtures/foundation_signature_main.rs", "main",
                    ["--foundation-signature-root", requested], foundation)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn(expected, result.stderr)
                self.assertFalse(output.exists())


if __name__ == "__main__":
    unittest.main()
