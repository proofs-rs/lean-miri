#!/usr/bin/env python3
"""Canonical generic array impl source with genuine compiler obligations."""
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
RUSTC = ROOT / ".rustup/toolchains/miri-exporter-8144389c895d/bin/rustc"
FIXTURE = ROOT / "exporter/fixtures/foundation_trait_blanket.rs"

class FoundationTraitBlanket(unittest.TestCase):
    def compile(self, source, output):
        return subprocess.run([
            str(RUSTC), str(source), "--crate-type=lib", "--emit=metadata",
            "--cfg=miri", "--sysroot", str(ROOT / "scratch/miri-sysroot"), "-o", str(output),
        ], cwd=ROOT, capture_output=True, text=True)

    def test_generic_header_preserved_and_compiler_demands(self):
        with tempfile.TemporaryDirectory(prefix="foundation-blanket-") as directory:
            output = Path(directory) / "blanket.json"
            result = subprocess.run([
                "bash", "tools/export-mir.sh", "--output", str(output),
                "--foundation", "--root", "marked", "--", str(FIXTURE),
                "--crate-type=lib", "--crate-name", "foundation_blanket",
            ], cwd=ROOT, capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stderr)
            doc = json.loads(output.read_text())
            trait = next(d["local_trait"] for d in doc["definitions"] if "local_trait" in d)
            self.assertEqual(len(trait["implementations"]), 1)
            header = trait["implementations"][0]
            self.assertEqual(header["parameters"], [{"kind":"type","index":0}])
            self.assertEqual(header["self_type"], {"kind":"array_pattern","element_parameter":0,"length":"3"})
            self.assertEqual({c["lang_item"] for c in header["clauses"]}, {"sized", "copy"})
            for index, (ty, accepted) in enumerate((
                ("[u8;3]", True), ("[u32;3]", True), ("[&'static u8;3]", True),
                ("[u8;4]", False), ("[&'static mut u8;3]", False),
            )):
                source = Path(directory) / f"demand_{index}.rs"
                source.write_text(FIXTURE.read_text() + f"\npub fn demand(x: {ty}) -> {ty} {{ marked(x) }}\n")
                result = self.compile(source, Path(directory) / f"demand_{index}.rmeta")
                self.assertEqual(result.returncode == 0, accepted, result.stderr)
                if not accepted:
                    self.assertIn("E0277", result.stderr)
            source = Path(directory) / "overlap.rs"
            source.write_text(FIXTURE.read_text() + "\nimpl Marker for [u8;3] {}\n")
            result = self.compile(source, Path(directory) / "overlap.rmeta")
            self.assertNotEqual(result.returncode, 0)
            self.assertIn("E0119", result.stderr)

    def test_valid_but_unsupported_bounds_and_supertrait_abort(self):
        with tempfile.TemporaryDirectory(prefix="foundation-blanket-reject-") as directory:
            cases = (
                (FIXTURE.read_text().replace("T: Copy", "T: Clone"), "conditional impl clause"),
                (FIXTURE.read_text().replace("trait Marker {}", "trait Marker: Copy {}"), "super clauses"),
                ((ROOT / "exporter/fixtures/fail_closed/no_core.rs").read_text() +
                 FIXTURE.read_text(), "non-core Copy implementation source"),
            )
            for index, (text, diagnostic) in enumerate(cases):
                source = Path(directory) / f"unsupported_{index}.rs"
                source.write_text(text)
                compiler = self.compile(source, Path(directory) / f"{index}.rmeta")
                self.assertEqual(compiler.returncode, 0, compiler.stderr)
                output = Path(directory) / f"unsupported_{index}.json"
                result = subprocess.run([
                    "bash", "tools/export-mir.sh", "--output", str(output),
                    "--foundation", "--root", "marked", "--", str(source),
                    "--crate-type=lib", "--crate-name", "unsupported_blanket",
                ], cwd=ROOT, capture_output=True, text=True)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn(diagnostic, result.stderr)
                self.assertFalse(output.exists())

if __name__ == "__main__":
    unittest.main()
