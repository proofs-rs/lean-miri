#!/usr/bin/env python3
"""Pinned compiler oracle for the supported optNo shared thin return domain."""
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]


class FoundationThinReferences(unittest.TestCase):
    def test_exact_erasure_leaves_and_return_attributes(self):
        with tempfile.TemporaryDirectory(prefix="foundation-thin-reference-") as directory:
            documents = []
            for foundation in [True, False]:
                output = Path(directory) / f"reference-{foundation}.json"
                result = subprocess.run(["bash", "tools/export-mir.sh", "--output", str(output),
                    *(["--foundation"] if foundation else []), "--root", "bytes", "--",
                    "exporter/fixtures/foundation_allocations.rs", "--crate-type=lib",
                    "--crate-name=foundation_allocations"], cwd=ROOT, capture_output=True, text=True)
                self.assertEqual(result.returncode, 0, result.stderr)
                documents.append(json.loads(output.read_text()))
            source, reference = documents
            self.assertEqual(source["compilation"]["opt_level"], "No")
            body = source["bodies"][0]
            source_return = source["types"][body["signature"]["output"]]["shape"]
            mir_return = source["types"][body["locals"][0]]["shape"]
            self.assertEqual((source_return["region"], mir_return["region"]), ("static", "erased"))
            self.assertEqual(source_return["pointee"], mir_return["pointee"])
            root = reference["body_roots"][0]["entry_instance"]
            query = next(row for row in reference["compiler_instance_abis"]
                if row["instance_id"] == root and row["extra_argument_types"] == [])
            abi = reference["fn_abis"][query["abi_query"]]
            result = reference["abi_arguments"][abi["return"]]
            self.assertEqual(result["mode"], {"kind": "Direct", "attributes": {
                "regular_bits": 144, "arg_extension": {"kind": "none"},
                "pointee_size_bytes": 0, "pointee_align_bytes": None}})
            erased = reference["types"][result["type"]]
            self.assertEqual(erased["shape"]["region"]["kind"], "erased")
            static = next(row for row in reference["types"] if row["shape"]["kind"] == "reference"
                and row["shape"]["region"]["kind"] == "static"
                and row["shape"]["pointee"] == erased["shape"]["pointee"])
            for row, erasable in [(static, True), (erased, False)]:
                facts = row["compiler_facts"]
                self.assertEqual(reference["boolean_queries"][facts["boolean_queries"]]["has_erasable_regions"], erasable)
                queries = facts["type_queries"]
                self.assertEqual(queries["normalized"], erased["type_id"])
                self.assertEqual(queries["metadata_tail"], erased["type_id"])
                self.assertEqual(queries["builtin_deref_explicit"], erased["shape"]["pointee"])
                self.assertEqual(queries["builtin_deref_implicit"], erased["shape"]["pointee"])


if __name__ == "__main__":
    unittest.main()
