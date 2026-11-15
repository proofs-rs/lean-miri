#!/usr/bin/env python3
"""Genuine pinned compiler obligations for the finite Fn declaration joins."""
from pathlib import Path
import subprocess
import tempfile
import unittest
ROOT = Path(__file__).resolve().parents[2]
RUSTC = ROOT / ".rustup/toolchains/miri-exporter-8144389c895d/bin/rustc"

DECLARATIONS = """
fn needs_fn<T: ?Sized + Fn() -> i32>(_: &T) {}
fn needs_mut<T: ?Sized + FnMut() -> i32>(_: &T) {}
fn needs_once<T: ?Sized + FnOnce() -> i32>(_: &T) {}
fn needs_wrong_output<T: ?Sized + FnOnce() -> i64>(_: &T) {}
fn needs_sync<T: ?Sized + Sync>(_: &T) {}
fn needs_unwind<T: ?Sized + std::panic::RefUnwindSafe>(_: &T) {}
"""

class FoundationFnSupertraits(unittest.TestCase):
    def test_compiler_entailment_projection_and_auto_bounds(self):
        cases = (
            ("dyn Fn() -> i32 + Sync + std::panic::RefUnwindSafe",
             "needs_mut(value); needs_once(value); needs_sync(value); needs_unwind(value);", None),
            ("dyn FnOnce() -> i32 + Sync + std::panic::RefUnwindSafe", "needs_once(value);", None),
            ("dyn FnOnce() -> i32 + Sync + std::panic::RefUnwindSafe", "needs_fn(value);", "E0277"),
            ("dyn Fn() -> i32 + Sync + std::panic::RefUnwindSafe", "needs_wrong_output(value);", "E0271"),
            ("dyn Fn() -> i32 + std::panic::RefUnwindSafe", "needs_sync(value);", "E0277"),
        )
        with tempfile.TemporaryDirectory(prefix="fn-supertrait-compiler-") as directory:
            for index, (object_type, effects, diagnostic) in enumerate(cases):
                source = Path(directory) / f"case_{index}.rs"
                source.write_text(DECLARATIONS + f"\npub fn test(value: &'static ({object_type})) {{ {effects} }}\n")
                result = subprocess.run([
                    str(RUSTC), str(source), "--crate-type=lib", "--emit=metadata", "--cfg=miri",
                    "--sysroot", str(ROOT / "scratch/miri-sysroot"), "-o", str(Path(directory) / f"{index}.rmeta"),
                ], cwd=ROOT, capture_output=True, text=True)
                self.assertEqual(result.returncode == 0, diagnostic is None, result.stderr)
                if diagnostic:
                    self.assertIn(diagnostic, result.stderr)

if __name__ == "__main__":
    unittest.main()
