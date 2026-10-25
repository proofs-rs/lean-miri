"""Direct pinned APFloat oracle comparison for the actual IntrinsicFloat helpers.
NaN adjustment is deterministic (preferred NaN); both permitted equal-number
choices are tested. This does not cover all Intrinsics dispatcher hooks.
"""
from pathlib import Path
import hashlib,json,os,subprocess
ROOT=Path(__file__).resolve().parents[2]
lock=json.loads((ROOT/'upstream/source-lock.json').read_text())
for entry in lock['files']:
    if entry['path'].startswith('upstream/rustc-apfloat-source/') or entry['path']=='upstream/rustc-source/compiler/rustc_const_eval/src/interpret/intrinsics.rs':
        assert hashlib.sha256((ROOT/entry['path']).read_bytes()).hexdigest()==entry['sha256'],entry['path']
env={**os.environ,'ELAN_HOME':str(ROOT/'.elan'),'CARGO_HOME':str(ROOT/'.cargo'),'CARGO_TARGET_DIR':str(ROOT/'scratch/intrinsic-float-oracle-target'),'RUSTC':str(ROOT/'.rustup/toolchains/stable-x86_64-unknown-linux-gnu/bin/rustc'),'RUSTFLAGS':'--cap-lints allow'}
expected=subprocess.check_output([str(ROOT/'.rustup/toolchains/stable-x86_64-unknown-linux-gnu/bin/cargo'),'run','--quiet','--offline','--locked','--manifest-path','tests/intrinsic_float/source_oracle/Cargo.toml'],cwd=ROOT,env=env,text=True).splitlines()
actual=subprocess.check_output(['.elan/bin/lake','env','lean','--run','tests/intrinsic_float/IntrinsicFloat.lean'],cwd=ROOT,env=env,text=True).splitlines()
if expected!=actual:
 for i,(a,b) in enumerate(zip(expected,actual)):
  if a!=b:raise SystemExit(f'intrinsic output {i}: APFloat={a}; Lean={b}')
 raise SystemExit(f'count differs: APFloat={len(expected)}; Lean={len(actual)}')
assert len(actual)==4*(17*5+17*17*8+17**3),len(actual)
print(f'{len(actual)} exact FMA, integral-rounding and min/max observations matched pinned APFloat across four IEEE widths')
