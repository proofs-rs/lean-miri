"""Compare actual Lean sizing with two selected expressions extracted from rustc.

The tiny Rust Size wrapper, target fixture, loops and formatting are explicit
harness code. This is neither extraction of the complete interpreter nor a
semantic equivalence proof of compiler metadata or memory access.
"""
from pathlib import Path
import re
import subprocess
import os
root = Path(__file__).resolve().parents[2]
source = (root / 'upstream/rustc-source/compiler/rustc_const_eval/src/interpret/eval_context.rs').read_text()
slice_expr = re.search(r'let size = (elem\.size\.bytes\(\)\.saturating_mul\(len\))', source)
struct_expr = re.search(r'let full_size = (\(unsized_offset_adjusted \+ unsized_size\)\.align_to\(full_align\))', source)
if slice_expr is None or struct_expr is None:
    raise SystemExit('pinned source sizing expression changed; review extraction')
rust = r'''
use std::ops::Add;
#[derive(Clone, Copy)] struct Size(u64);
impl Size {
    fn bytes(self) -> u64 { self.0 }
    fn align_to(self, align: u64) -> Self { Size((self.0 + align - 1) & !(align - 1)) }
}
impl Add for Size { type Output = Size; fn add(self, other: Size) -> Size { Size(self.0.checked_add(other.0).unwrap()) } }
struct Elem { size: Size }
fn slice(len: u64) -> Option<u64> {
    let elem = Elem { size: Size(4) };
    let size = SLICE_EXPR;
    if size > i64::MAX as u64 { None } else { Some(size) }
}
fn aggregate(len: u64) -> u64 {
    let unsized_offset_adjusted = Size(1).align_to(4);
    let unsized_size = Size(slice(len).unwrap());
    let full_align = 4;
    let full_size = STRUCT_EXPR;
    full_size.bytes()
}
fn main() {
    for n in 0..65 { println!("{}:2", slice(n).unwrap()); }
    for n in 0..65 { println!("{}:2", aggregate(n)); }
    for n in [0, 1, 2305843009213693951, 2305843009213693952, u64::MAX] {
        match slice(n) { Some(size) => println!("{size}:2"), None => println!("too-big") }
    }
}
'''.replace('SLICE_EXPR', slice_expr.group(1)).replace('STRUCT_EXPR', struct_expr.group(1))
path = Path('/tmp/lean-miri-dynamic-source.rs')
path.write_text(rust)
subprocess.run([str(root / '.rustup/toolchains/stable-x86_64-unknown-linux-gnu/bin/rustc'), '--edition=2021', str(path), '-o', '/tmp/lean-miri-dynamic-source'], check=True)
expected = subprocess.check_output(['/tmp/lean-miri-dynamic-source'], text=True)
actual = subprocess.check_output([str(root / '.elan/bin/lake'), 'env', 'lean', '--run', 'tests/dynamic_layout/DynamicLayout.lean'], cwd=root, env=dict(os.environ, ELAN_HOME=str(root / '.elan')), text=True)
if actual != expected:
    for i, (a, b) in enumerate(zip(actual.splitlines(), expected.splitlines())):
        if a != b:
            raise SystemExit(f'case {i}: Lean={a} Rust={b}')
    raise SystemExit('output count mismatch')
print('135 slice/struct sizing cases matched; two pinned source expressions extracted')
