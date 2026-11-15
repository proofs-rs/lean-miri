#!/usr/bin/env python3
"""Pinned compiler auto obligations for ordinary function-pointer captures."""
from pathlib import Path
import subprocess
import tempfile
import unittest
ROOT = Path(__file__).resolve().parents[2]
RUSTC = ROOT / ".rustup/toolchains/miri-exporter-8144389c895d/bin/rustc"

class FoundationClosureAuto(unittest.TestCase):
    def test_compiler_capture_auto_obligations(self):
        cases = (
            ("fn output() -> std::cell::Cell<u8> { std::cell::Cell::new(0) }\n"
             "pub fn test() { let f: fn() -> std::cell::Cell<u8> = output; let closure = move || f(); needs_both(&closure); }", None),
            ("pub fn test() { let pointer = std::ptr::null::<u8>(); let closure = move || pointer; needs_sync(&closure); }", "E0277"),
            ("pub fn test() { let cell = std::cell::Cell::new(0_u8); let closure = move || cell.get(); needs_unwind(&closure); }", "E0277"),
        )
        declarations = """
fn needs_sync<T: Sync>(_: &T) {}
fn needs_unwind<T: std::panic::RefUnwindSafe>(_: &T) {}
fn needs_both<T: Sync + std::panic::RefUnwindSafe>(_: &T) {}
"""
        with tempfile.TemporaryDirectory(prefix="closure-auto-compiler-") as directory:
            for index, (body, diagnostic) in enumerate(cases):
                source = Path(directory) / f"case_{index}.rs"
                source.write_text(declarations + body)
                result = subprocess.run([
                    str(RUSTC), str(source), "--crate-type=lib", "--emit=metadata", "--cfg=miri",
                    "--sysroot", str(ROOT / "scratch/miri-sysroot"), "-o", str(Path(directory) / f"{index}.rmeta"),
                ], cwd=ROOT, capture_output=True, text=True)
                self.assertEqual(result.returncode == 0, diagnostic is None, result.stderr)
                if diagnostic:
                    self.assertIn(diagnostic, result.stderr)
                    self.assertIn("Sync" if index == 1 else "RefUnwindSafe", result.stderr)

if __name__ == "__main__":
    unittest.main()
