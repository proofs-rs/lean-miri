"""Compare exact Lean float execution directly with pinned rustc_apfloat.

The oracle executes the local pinned crate. Its Miri NaN candidate enumerator
is an explicitly handwritten transcription of operator.rs::generate_nan; it
uses the actual crate's conversion, signaling tests and bit encodings. Finite
corpus agreement is not a proof of semantic equivalence.
"""
from pathlib import Path
import os
import subprocess
root = Path(__file__).resolve().parents[2]
env = dict(os.environ,
    CARGO_HOME=str(root / '.cargo'),
    CARGO_TARGET_DIR='/tmp/lean-miri-float-oracle-target',
    RUSTC=str(root / '.rustup/toolchains/stable-x86_64-unknown-linux-gnu/bin/rustc'),
    RUSTFLAGS='--cap-lints allow',
    ELAN_HOME=str(root / '.elan'))
# The newer local rustc deprecates i32::max_value used by the pinned crate,
# which has deny(warnings). Cap lints without changing its source or arithmetic.
expected = subprocess.check_output([
    str(root / '.rustup/toolchains/stable-x86_64-unknown-linux-gnu/bin/cargo'),
    'run', '--quiet', '--offline', '--locked', '--manifest-path',
    'tests/float_ops/source_oracle/Cargo.toml'], cwd=root, env=env, text=True)
actual = subprocess.check_output([str(root / '.elan/bin/lake'), 'env', 'lean', '--run',
    'tests/float_ops/Float.lean'], cwd=root, env=env, text=True)
a, b = actual.splitlines(), expected.splitlines()
if a != b:
    for index, (lean, rust) in enumerate(zip(a,b)):
        if lean != rust:
            raise SystemExit(f'output {index}: Lean={lean}, pinned apfloat={rust}')
    raise SystemExit(f'output count differs: Lean={len(a)}, apfloat={len(b)}')
if len(a) != 36472:
    raise SystemExit(f'unexpected corpus count: {len(a)}; update coverage description explicitly')
print(f'{len(a)} outputs matched pinned rustc_apfloat and source NaN choices; four IEEE widths')
