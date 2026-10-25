"""Finite comparison against pinned Miri's Eq and CAS-choice expressions.

Extracts two actual expressions, not the interpreter. Rust harness values model
thin-pointer (address, zero) pairs; the explicit spurious Boolean substitutes
only the RNG result. Lean assertions exercise real component allocation,
provenance, pending hooks and error-state mutation. This does not discharge
atomic_access_check, borrow/sync hooks, GenMC or whole-program safety.
"""
from pathlib import Path
import os
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
operator = (ROOT / 'upstream/miri-source/src/operator.rs').read_text()
cas = (ROOT / 'upstream/miri-source/src/concurrency/data_race.rs').read_text()
eq = re.search(r'Eq => (left == right),', operator)
choice = re.search(r'let cmpxchg_success = (eq.to_scalar\(\).to_bool\(\)\?\s*&& if can_fail_spuriously \{\s*this.machine.rng.get_mut\(\).random_bool\(success_rate\)\s*\} else \{\s*true\s*\});', cas)
if eq is None or choice is None:
    raise SystemExit('pinned pointer Eq / CAS expression changed; review adapter')
expression = choice.group(1).replace('eq.to_scalar().to_bool()?', 'eq').replace(
    'this.machine.rng.get_mut().random_bool(success_rate)', '!spurious')
rust = r'''
fn main() {
 for _width in [32, 64] { for _endian in [0, 1] { for _weak_memory in [false, true] {
 for address in [0u64, 4096] { for expected in [0u64, 4096, 4097] {
 for _old_pointer in [false, true] { for _expected_style in [0, 1, 2] { for can_fail_spuriously in [false, true] {
 for spurious in [false, true] {
   let left = (address, 0u64); let right = (expected, 0u64);
   let eq = EQUALITY;
   let succeeded = CHOICE;
   println!("{succeeded}");
 }}}}}}}}}
}
'''.replace('EQUALITY', eq.group(1)).replace('CHOICE', expression)
elan = Path(os.environ.get('LEAN_MIRI_ELAN_HOME', str(ROOT / '.elan')))
rustup = Path(os.environ.get('RUSTUP_HOME', str(ROOT / '.rustup')))
rustc = rustup / 'toolchains/miri-exporter-8144389c895d/bin/rustc'
with tempfile.TemporaryDirectory(prefix='lean-miri-pointer-cas-') as directory:
    directory = Path(directory)
    source = directory / 'compare.rs'
    executable = directory / 'compare'
    source.write_text(rust)
    subprocess.run([str(rustc), '--edition=2024', str(source), '-o', str(executable)], check=True)
    expected = subprocess.check_output([str(executable)], text=True)
    actual = subprocess.check_output([str(elan / 'bin/lake'), 'env', 'lean', '--run',
        'tests/atomic_scalar/PointerCompareExchange.lean'], cwd=ROOT, text=True,
        env=dict(os.environ, ELAN_HOME=str(elan)))
if actual != expected:
    expected_lines, actual_lines = expected.splitlines(), actual.splitlines()
    for index, (want, got) in enumerate(zip(expected_lines, actual_lines)):
        if want != got:
            raise SystemExit(f'case {index}: Lean={got}, source-expression reference={want}')
    raise SystemExit(f'output length: Lean={len(actual_lines)}, reference={len(expected_lines)}')
print(f'{len(actual.splitlines())} pointer CAS outcomes matched pinned Eq/weak-choice expressions; allocation/provenance/error assertions passed')
