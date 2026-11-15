#!/usr/bin/env python3
"""Build the normal exporter against a pinned, observation-patched compiler.

The compiler is built separately using rustc-patches/allocation-identity-snapshot.patch.
No installed toolchain or normal exporter artifact is replaced.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
PIN = '8144389c895da997dbdecaa635e41d6a50be6ffd'
p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--compiler-build', type=Path, required=True, help='rustc build/<host> directory')
p.add_argument('--driver', type=Path, required=True, help='patched stage1 librustc_driver-<hash>.so')
p.add_argument('--target-dir', type=Path, default=ROOT / 'scratch/snapshot-exporter-target')
a = p.parse_args()
build = a.compiler_build.resolve()
driver = a.driver.resolve()
host = ROOT / '.rustup/toolchains/miri-exporter-8144389c895d'
rustc = host / 'bin/rustc'
version = subprocess.check_output([rustc, '-vV'], text=True)
if f'commit-hash: {PIN}\n' not in version:
    p.error('host compiler does not match pinned commit')
private = build / 'stage0-sysroot'
triple = re.search(r'^host: (.+)$', version, re.M).group(1)
metadata = private / 'lib/rustlib' / triple / 'lib'
driver_metadata = metadata / (driver.stem + '.rmeta')
listing = subprocess.check_output([rustc, '-Zls=all', driver_metadata], text=True)
dependencies = dict(re.findall(r'^\d+ (\w+)-([0-9a-f]+) hash ', listing, re.M))
std = host / 'lib/rustlib' / triple / 'lib' / ('libstd-' + dependencies['std'])
flags = ['--sysroot', str(private), '-L', 'dependency=' + str(metadata), '-Cprefer-dynamic',
         '--extern', 'std=' + str(std) + '.rmeta', '--extern', 'std=' + str(std) + '.so']
for name in re.findall(r'^extern crate (rustc_\w+);', (ROOT / 'exporter/src/main.rs').read_text(), re.M):
    artifact = driver_metadata if name == 'rustc_driver' else metadata / f'lib{name}-{dependencies[name]}.rmeta'
    if not artifact.is_file():
        p.error(f'matching private metadata absent: {artifact}')
    flags += ['--extern', f'{name}={artifact}']
# Preserve the normal producer check: the loaded compiler must reside inside
# the sysroot checked by build.rs. Hardlink the exact driver; never bypass it.
installed = private / 'lib' / driver.name
if installed.exists():
    if not os.path.samefile(installed, driver):
        p.error(f'conflicting compiler artifact: {installed}')
else:
    os.link(driver, installed)
flags += ['--extern', 'rustc_driver=' + str(installed)]
env = os.environ.copy()
env.pop('LEAN_MIRI_OBSERVE_CTFE_ROOT', None)
env.update(RUSTUP_HOME=str(ROOT / '.rustup'), CARGO_HOME=str(ROOT / '.cargo'),
           CARGO_TARGET_DIR=str(a.target_dir.resolve()), CARGO_ENCODED_RUSTFLAGS='\x1f'.join(flags),
           PATH=f'{host}/bin:{ROOT}/.cargo/bin:' + env['PATH'],
           LD_LIBRARY_PATH=f'{private}/lib:{build}/stage1/lib:{metadata}:{host}/lib')
subprocess.run([ROOT / '.cargo/bin/cargo', '+miri-exporter-8144389c895d', 'build', '--release',
                '--locked', '--offline', '--features', 'allocation-identity-snapshot',
                '--manifest-path', ROOT / 'exporter/Cargo.toml'], env=env, check=True)
manifest = dict(pin=PIN, compiler_build=str(build), driver=str(driver),
                driver_sha256=hashlib.file_digest(driver.open("rb"), "sha256").hexdigest(), flags=flags,
                binary=str(a.target_dir.resolve() / 'release/lean-miri-mir-exporter'),
                environment={k: env[k] for k in ['PATH', 'LD_LIBRARY_PATH']},
                target_sysroot=str(build / 'stage1'))
(a.target_dir / 'snapshot-build.json').write_text(json.dumps(manifest, indent=2) + '\n')
print(f'Build manifest: {a.target_dir / "snapshot-build.json"}')
