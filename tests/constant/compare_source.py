#!/usr/bin/env python3
"""Execute extracted pinned const_val_to_op control flow with explicit leaf stubs.
The stubs model layout query/global root adjustment as observable boundaries;
this compares the five conversion branches, not the machine leaves themselves.
"""
import os
from pathlib import Path
import subprocess
import sys
import tempfile
root = Path(__file__).resolve().parents[2]
source = (root / 'upstream/rustc-source/compiler/rustc_const_eval/src/interpret/operand.rs').read_text()
start = source.index('    pub(crate) fn const_val_to_op(')
brace = source.index('{', start)
depth = 1
end = brace + 1
while depth:
    depth += (source[end] == '{') - (source[end] == '}')
    end += 1
body = source[brace:end]
method = "fn const_val_to_op(&self,val_val:mir::ConstValue,ty:u8,layout:Option<Layout>)->InterpResult<'tcx,OpTy> " + body
probe = (root / 'tests/constant/source_probe.rs.in').read_text().replace('__SOURCE_METHOD__', method)
env = os.environ.copy()
env.setdefault('RUSTUP_HOME', str(root / '.rustup'))
env.setdefault('ELAN_HOME', str(root / '.elan'))
with tempfile.TemporaryDirectory(prefix='lean-miri-constant-source-') as tmp:
    rust = Path(tmp) / 'probe.rs'
    exe = Path(tmp) / 'probe'
    rust.write_text(probe)
    subprocess.run([str(root / '.cargo/bin/rustup'), 'run', 'miri-exporter-8144389c895d', 'rustc', '--edition=2024', '-Awarnings', str(rust), '-o', str(exe)], check=True, env=env)
    expected = subprocess.check_output([str(exe)], text=True, env=env)
    actual = subprocess.check_output([str(root / '.elan/bin/lake'), 'env', 'lean', '--run', 'tests/constant/SourceObservations.lean', sys.argv[1]], text=True, cwd=root, env=env)
    if actual != expected:
        raise SystemExit(f'source observations differ\nRust:\n{expected}\nLean:\n{actual}')
print('matched all five const_val_to_op conversion branches and root-pointer effects against extracted pinned source')
