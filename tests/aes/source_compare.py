"""Compare actual pinned AES fixslice u32/u64 generic bodies with Lean.
Only visibility is changed in a scratch copy; no upstream source is edited.
"""
from pathlib import Path
import hashlib,json,os,shutil,subprocess,tomllib
ROOT=Path(__file__).resolve().parents[2]
source=ROOT/'upstream/crates/aes-0.9.3'
lock=json.loads((ROOT/'upstream/source-lock.json').read_text())
locked_aes=[entry for entry in lock['files'] if entry['path'].startswith('upstream/crates/aes-0.9.3/')]
assert locked_aes, 'AES source inventory must be locked'
for entry in locked_aes:
 if entry['path'].startswith('upstream/crates/aes-0.9.3/'):
  assert hashlib.sha256((ROOT/entry['path']).read_bytes()).hexdigest()==entry['sha256'],entry['path']
work=ROOT/'scratch/aes-source-qa';copy=work/'aes';oracle=work/'oracle'
if copy.exists():shutil.rmtree(copy)
shutil.copytree(source,copy);(oracle/'src').mkdir(parents=True,exist_ok=True)
hazmat=copy/'src/backends/fixslice/hazmat.rs';text=hazmat.read_text()
for name in ['cipher_round_generic','equiv_inv_cipher_round_generic','mix_columns_generic','inv_mix_columns_generic']:
 old='fn '+name+'<';assert text.count(old)==1;text=text.replace(old,'pub(crate) fn '+name+'<',1)
hazmat.write_text(text)
wrapper='\n'
for width in [32,64]:
 wrapper+=f'pub fn qa_round{width}(block:&mut Block,key:&Block,inverse:bool){{if inverse{{backends::soft::hazmat::equiv_inv_cipher_round_generic::<u{width}>(block,key)}}else{{backends::soft::hazmat::cipher_round_generic::<u{width}>(block,key)}}}}\n'
 wrapper+=f'pub fn qa_mix{width}(block:&mut Block,inverse:bool){{if inverse{{backends::soft::hazmat::inv_mix_columns_generic::<u{width}>(block)}}else{{backends::soft::hazmat::mix_columns_generic::<u{width}>(block)}}}}\n'
with (copy/'src/lib.rs').open('a') as f:f.write(wrapper)
(oracle/'Cargo.toml').write_text('[package]\nname="lean-miri-aes-source-oracle"\nversion="0.1.0"\nedition="2024"\n[dependencies]\naes={path="../aes",features=["hazmat"]}\nlibc="=0.2.189"\n')
shutil.copyfile(ROOT/'tests/aes/Oracle.rs',oracle/'src/main.rs')
env={**os.environ,'ELAN_HOME':str(ROOT/'.elan'),'CARGO_HOME':str(ROOT/'.cargo'),'CARGO_TARGET_DIR':str(work/'target'),'RUSTC':str(ROOT/'.rustup/toolchains/stable-x86_64-unknown-linux-gnu/bin/rustc'),'RUSTFLAGS':'--cfg aes_backend="soft" --cap-lints allow'}
cargo=str(ROOT/'.rustup/toolchains/stable-x86_64-unknown-linux-gnu/bin/cargo')
cargo_command=[cargo,'--config',str(ROOT/'scratch/cargo-vendor.toml')]
subprocess.run(cargo_command+['generate-lockfile','--offline','--manifest-path',str(oracle/'Cargo.toml')],env=env,cwd=ROOT,check=True)
pinned=tomllib.loads((ROOT/'upstream/miri-source/Cargo.lock').read_text())
versions={(p['name'],p['version']):p.get('checksum') for p in pinned['package']}
actual=tomllib.loads((oracle/'Cargo.lock').read_text())
# The shared offline vendor directory may contain versions from other tasks.
# Resolve every registry package back to the immutable Miri lock, not latest.
for package in actual['package']:
 if 'checksum' in package and versions.get((package['name'],package['version']))!=package['checksum']:
  candidates=[p for p in pinned['package'] if p['name']==package['name']]
  assert len(candidates)==1, package
  subprocess.run(cargo_command+['update','--offline','--manifest-path',str(oracle/'Cargo.toml'),'-p',package['name']+'@'+package['version'],'--precise',candidates[0]['version']],env=env,cwd=ROOT,check=True)
actual=tomllib.loads((oracle/'Cargo.lock').read_text())
for package in actual['package']:
 if 'checksum' in package:assert versions.get((package['name'],package['version']))==package['checksum'],package
expected=subprocess.check_output(cargo_command+['run','--quiet','--locked','--offline','--manifest-path',str(oracle/'Cargo.toml')],env=env,cwd=ROOT,text=True).splitlines()
actual=subprocess.check_output(['.elan/bin/lake','env','lean','--run','tests/aes/Aes.lean'],env=env,cwd=ROOT,text=True).splitlines()
(work/'rust-output.txt').write_text('\n'.join(expected)+'\n')
(work/'lean-output.txt').write_text('\n'.join(actual)+'\n')
if expected!=actual:
 for i,(a,b) in enumerate(zip(expected,actual)):
  if a!=b:raise SystemExit(f'AES case{i}: pinned32/64={a}; Lean={b}')
 raise SystemExit(f'AES counts differ: source={len(expected)}, Lean={len(actual)}')
assert len(actual)==924,len(actual)
print('924 pinned AES u32/u64 round+inverse/mix observations agree with Lean; visibility-only source adaptation')
