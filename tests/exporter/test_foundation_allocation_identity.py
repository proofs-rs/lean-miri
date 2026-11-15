#!/usr/bin/env python3
"""Raw allocation identity is compiler construction state, not byte content.
Reference documents below are inspected only, never used as foundation input.
"""
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]


class FoundationAllocationIdentity(unittest.TestCase):
    def test_same_images_have_distinct_compiler_identities(self):
        with tempfile.TemporaryDirectory(prefix="allocation-identity-") as directory:
            output = Path(directory) / "reference.json"
            result = subprocess.run(["bash", "tools/export-mir.sh", "--output", str(output),
                "--root", "literal", "--root", "evaluated", "--",
                "exporter/fixtures/foundation_allocation_identity.rs", "--crate-type=lib",
                "--crate-name=foundation_allocation_identity"], cwd=ROOT, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            document = json.loads(output.read_text())
            rows = [row for row in document["allocations"] if row["kind"] == "memory" and
                document["byte_images"][row["byte_image_id"]] == b"same".hex()]
            self.assertGreaterEqual(len(rows), 2)
            self.assertEqual(len({row["source_alloc_id"] for row in rows}), len(rows))
            images = [(row["size_bytes"], row["align_bytes"], row["mutability"],
                document["initialization_ranges"][row["initialization_ranges"]],
                document["relocations"][row["relocations"]]) for row in rows]
            self.assertTrue(all(image == images[0] for image in images))

    def test_unrelated_source_allocation_changes_raw_identity(self):
        with tempfile.TemporaryDirectory(prefix="allocation-history-") as directory:
            ids = []
            for noise in [False, True]:
                source = Path(directory) / f"source-{noise}.rs"
                source.write_text(("pub fn before()->&'static [u8;5] { b\"noise\" }\n" if noise else "") +
                    "pub fn target()->&'static [u8;4] { b\"same\" }")
                output = Path(directory) / f"source-{noise}.json"
                result = subprocess.run(["bash", "tools/export-mir.sh", "--output", str(output),
                    "--foundation", *(["--root", "before"] if noise else []), "--root", "target",
                    "--", str(source), "--crate-type=lib", "--crate-name=allocation_history"],
                    cwd=ROOT, capture_output=True, text=True)
                self.assertEqual(result.returncode, 0, result.stderr)
                document = json.loads(output.read_text())
                rows = [row for row in document["source_allocations"] if row["bytes_hex"] == b"same".hex()]
                self.assertEqual(len(rows), 1)
                ids.append(rows[0]["source_alloc_id"])
            self.assertNotEqual(*ids)


if __name__ == "__main__":
    unittest.main()
