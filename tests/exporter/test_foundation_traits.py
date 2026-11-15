#!/usr/bin/env python3
"""Local trait source headers and pinned compiler acceptance controls."""
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
RUSTC = ROOT / ".rustup/toolchains/miri-exporter-8144389c895d/bin/rustc"
FIXTURE = ROOT / "exporter/fixtures/foundation_traits.rs"

class FoundationTraits(unittest.TestCase):
    def export(self, source, output):
        return subprocess.run([
            "bash", "tools/export-mir.sh", "--output", str(output),
            "--foundation", "--root", "marked", "--", str(source),
            "--crate-type=lib", "--crate-name", "foundation_traits",
        ], cwd=ROOT, capture_output=True, text=True)

    def test_complete_headers_and_compiler_obligations(self):
        with tempfile.TemporaryDirectory(prefix="foundation-traits-") as directory:
            output = Path(directory) / "traits.json"
            result = self.export(FIXTURE, output)
            self.assertEqual(result.returncode, 0, result.stderr)
            doc = json.loads(output.read_text())
            trait = next(d["local_trait"] for d in doc["definitions"] if "local_trait" in d)
            self.assertTrue(trait["complete_impl_headers"])
            self.assertEqual(sorted(h["self_type"]["name"] for h in trait["implementations"]), ["u32", "u8"])
            self.assertEqual(len(trait["implementations"]), 2)
            self.assertFalse(any(key.startswith("compiler_") for key in doc))
            for ty, accepted in (("u8", True), ("u32", True), ("u16", False)):
                source = Path(directory) / f"demand_{ty}.rs"
                source.write_text(FIXTURE.read_text() + f"\npub fn demand(x: {ty}) -> {ty} {{ marked(x) }}\n")
                result = subprocess.run([
                    str(RUSTC), str(source), "--crate-type=lib", "--emit=metadata",
                    "--cfg=miri", "--sysroot", str(ROOT / "scratch/miri-sysroot"), "-o", str(Path(directory) / f"{ty}.rmeta"),
                ], cwd=ROOT, capture_output=True, text=True)
                self.assertEqual(result.returncode == 0, accepted, result.stderr)
                if not accepted:
                    self.assertIn("u16: Marker", result.stderr)

    def test_unsupported_source_impl_or_declaration_aborts(self):
        with tempfile.TemporaryDirectory(prefix="foundation-traits-reject-") as directory:
            cases = (
                ("pub trait Marker {} impl<T> Marker for T {}", "generic or conditional impl"),
                ("pub trait Marker: Copy {} impl Marker for u8 {}", "super clauses"),
                ("pub trait Marker {} impl Marker for u8 {} impl Marker for [u8; 3] {}", "non-primitive impl self type"),
                ("#![feature(negative_impls)]\npub trait Marker {} impl Marker for u8 {} impl !Marker for u16 {}", "negative impl"),
            )
            for index, (declarations, diagnostic) in enumerate(cases):
                source = Path(directory) / f"unsupported_{index}.rs"
                source.write_text(declarations + "\npub fn marked<T: Marker>(x:T)->T{x}\n")
                output = Path(directory) / f"unsupported_{index}.json"
                result = self.export(source, output)
                self.assertNotEqual(result.returncode, 0)
                self.assertIn(diagnostic, result.stderr)
                self.assertFalse(output.exists())

if __name__ == "__main__":
    unittest.main()
