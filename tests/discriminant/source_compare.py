"""Finite source-expression comparison, not a full discriminant equivalence proof.

Extracts the actual niche membership comparison and checked absolute-index
expression from pinned discriminant.rs. The surrounding standalone Rust model,
width arithmetic, declared-discriminant lookup and fixture are explicit harness
code. No claim that all source semantics are automatically extracted.
"""
from pathlib import Path
import re
import subprocess
import os

root = Path(__file__).resolve().parents[2]
source = (root / 'upstream/rustc-source/compiler/rustc_const_eval/src/interpret/discriminant.rs').read_text()
condition = re.search(r'if (variant_index_relative <= u128::from\(variants_last - variants_start\))', source)
absolute = re.search(r'variants_start\s*\.checked_add\(variant_index_relative\)', source)
if condition is None or absolute is None:
    raise SystemExit('pinned source expression changed; extraction needs review')
condition = condition.group(1)
absolute = re.sub(r'\s+', '', absolute.group())
rust = r'''
fn niche(tag: u8) -> u32 {
    let variants_start = 0u32;
    let variants_last = 1u32;
    let variant_index_relative = tag.wrapping_sub(255) as u128;
    if CONDITION {
        let variant_index_relative = u32::try_from(variant_index_relative).unwrap();
        ABSOLUTE.expect("checked absolute variant index")
    } else { 2 }
}
fn main() {
    for tag in 0..256 {
        match tag { 0 => println!("ok:0"), 2 => println!("ok:1"), 4 => println!("ok:2"), _ => println!("invalid") }
    }
    for tag in 0..256 { println!("ok:{}", niche(tag as u8)); }
}
'''.replace('CONDITION', condition).replace('ABSOLUTE', absolute)
rust_path = Path('/tmp/lean-miri-discriminant-source.rs')
rust_path.write_text(rust)
rustc = root / '.rustup/toolchains/stable-x86_64-unknown-linux-gnu/bin/rustc'
subprocess.run([str(rustc), '--edition=2021', str(rust_path), '-o', '/tmp/lean-miri-discriminant-source'], check=True)
expected = subprocess.check_output(['/tmp/lean-miri-discriminant-source'], text=True)
env = dict(os.environ, ELAN_HOME=str(root / '.elan'))
actual = subprocess.check_output([str(root / '.elan/bin/lake'), 'env', 'lean', '--run', 'tests/discriminant/Discriminant.lean'], cwd=root, env=env, text=True)
if actual != expected:
    for index, (a, b) in enumerate(zip(actual.splitlines(), expected.splitlines())):
        if a != b:
            raise SystemExit(f'case {index}: Lean={a} Rust={b}')
    raise SystemExit('source comparison output length mismatch')
print('512 direct/niche read cases matched; two source expressions extracted')
