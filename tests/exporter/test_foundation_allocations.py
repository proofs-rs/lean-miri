#!/usr/bin/env python3
"""Fresh source allocation images, compared with the existing compiler exporter.
The reference document is a comparison oracle, never foundation execution input.
"""
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
FIXTURE = "exporter/fixtures/foundation_allocations.rs"


class FoundationAllocations(unittest.TestCase):
    def export(self, output, foundation, root):
        return subprocess.run([
            "bash", "tools/export-mir.sh", "--output", str(output),
            *(["--foundation"] if foundation else []), "--root", root, "--",
            FIXTURE, "--crate-type=lib", "--crate-name=foundation_allocations",
        ], cwd=ROOT, capture_output=True, text=True)

    def test_genuine_images_match_compiler_reference(self):
        with tempfile.TemporaryDirectory(prefix="foundation-allocations-") as directory:
            for root, expected in [("literal", b"foundation-bytes"), ("bytes", b"Miri")]:
                documents = []
                for foundation in [True, False]:
                    output = Path(directory) / f"{root}-{foundation}.json"
                    result = self.export(output, foundation, root)
                    self.assertEqual(result.returncode, 0, result.stderr)
                    documents.append(json.loads(output.read_text()))
                source, reference = documents
                rows = source["source_allocations"]
                self.assertEqual(len(rows), 1)
                image = rows[0]
                self.assertEqual(image["allocation_id"], 0)
                self.assertGreater(image["source_alloc_id"], 0)
                self.assertEqual(bytes.fromhex(image["bytes_hex"]), expected)
                self.assertEqual(image["size_bytes"], len(expected))
                candidates = [row for row in reference["allocations"]
                    if row["kind"] == "memory" and
                    reference["byte_images"][row["byte_image_id"]] == image["bytes_hex"]]
                self.assertTrue(candidates)
                compared = candidates[0]
                self.assertEqual(compared["size_bytes"], image["size_bytes"])
                self.assertEqual(compared["align_bytes"], image["align_bytes"])
                self.assertEqual(compared["mutability"] == "mutable", image["mutable"])
                ranges = reference["initialization_ranges"][compared["initialization_ranges"]]
                self.assertEqual(image["initialization_ranges"], [dict(
                    initialized=row["state"] == "initialized",
                    start_bytes=row["start_bytes"], end_bytes_exclusive=row["end_bytes_exclusive"])
                    for row in ranges])
                self.assertEqual(image["relocations"], [])
                constant = source["bodies"][0]["blocks"][0]["statements"][0]["value"]["operand"]["value"]
                self.assertEqual(constant["allocation"], 0)
                self.assertEqual(constant["kind"], "allocation_slice" if root == "literal" else "allocation_pointer")

    def test_static_global_requires_source_initializer_semantics(self):
        with tempfile.TemporaryDirectory(prefix="foundation-static-") as directory:
            source = Path(directory) / "unsupported.rs"
            source.write_text('pub static VALUE:u8=7; pub fn pointer()->*const u8 { &VALUE }')
            output = Path(directory) / "unsupported.json"
            result = subprocess.run(["bash", "tools/export-mir.sh", "--output", str(output),
                "--foundation", "--root", "pointer", "--", str(source), "--crate-type=lib",
                "--crate-name=unsupported_static"], cwd=ROOT, capture_output=True, text=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("unsupported source allocation kind or unavailable image", result.stderr)
            self.assertFalse(output.exists())


if __name__ == "__main__":
    unittest.main()
