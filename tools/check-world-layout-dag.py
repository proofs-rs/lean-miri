#!/usr/bin/env python3
"""Check Rust's successful tuple size and exclusive object bound, then Lean DAG demands.

The 64-level Lean demand must return an actual size-overflow error within the
process deadline. A timeout is always failure, never an expected overflow.
"""
import argparse
import json
import os
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('material', type=Path)
    parser.add_argument('output', type=Path, help='new directory under scratch/')
    parser.add_argument('--timeout', type=float, default=30)
    args = parser.parse_args()
    material = args.material.resolve()
    output = args.output.resolve()
    if output.exists() or not output.is_relative_to(ROOT / 'scratch'):
        parser.error('output must be a new directory under scratch/')
    output.mkdir(parents=True)
    raw = json.loads(material.read_bytes())
    if raw['runtime_target_data_layout']['pointer_width_bits'] != 64:
        parser.error('this regression compares the pinned 64-bit target')
    bound = raw['runtime_target_data_layout']['object_size_bound_bytes']
    triple = raw['producer']['target_triple']
    env = os.environ.copy()
    rustup = Path(env.get('RUSTUP_HOME', ROOT / '.rustup'))
    toolchain = rustup / 'toolchains/miri-exporter-8144389c895d'
    rustc = toolchain / 'bin/rustc'
    env['LD_LIBRARY_PATH'] = str(toolchain / 'lib') + ':' + env.get('LD_LIBRARY_PATH', '')
    env['LEAN_NUM_THREADS'] = '1'
    sysroot = Path(env.get('MIRI_SYSROOT', ROOT / 'scratch/miri-sysroot'))
    version = subprocess.run([str(rustc), '-vV'], env=env, text=True,
                             capture_output=True, check=True, timeout=args.timeout).stdout
    lock = json.loads((ROOT / 'upstream/source-lock.json').read_text())
    if f"commit-hash: {lock['pins']['rustc']['commit']}" not in version:
        raise SystemExit('Rust oracle does not match the pinned compiler')
    target = json.loads(subprocess.run([str(rustc), '--target', triple,
        '-Zunstable-options', '--print', 'target-spec-json'], env=env, text=True,
        capture_output=True, check=True, timeout=args.timeout).stdout)
    if target['data-layout'] != raw['runtime_target_data_layout']['llvm_data_layout']:
        raise SystemExit('Rust oracle and material target data layouts differ')
    prefix = '#![no_std]\ntype T0=bool;\n'
    prefix += ''.join(f'type T{i}=(T{i-1},T{i-1});\n' for i in range(1, 17))
    cases = {
        'size16': prefix + '#[unsafe(no_mangle)] pub extern "C" fn dag_size()->usize { core::mem::size_of::<T16>() }\n',
        'bound': f'#![no_std]\ntype Limit=[bool;{bound}];\n#[unsafe(no_mangle)] pub extern "C" fn bound_size()->usize {{ core::mem::size_of::<Limit>() }}\n',
    }
    for name, source in cases.items():
        path = output / f'{name}.rs'
        path.write_text(source)
        command = [str(rustc), '--sysroot', str(sysroot), '--target', triple,
                   '--crate-type', 'lib', '--crate-name', f'layout_dag_{name}',
                   '--edition', '2024', '-Cpanic=abort', '--emit=llvm-ir', str(path),
                   '-o', str(output / f'{name}.ll')]
        result = subprocess.run(command, cwd=ROOT, env=env, text=True,
                                capture_output=True, timeout=args.timeout)
        (output / f'{name}.log').write_text(result.stdout + result.stderr)
        if name == 'size16':
            if result.returncode != 0 or not re.search(r'ret i64 65536\b', (output / 'size16.ll').read_text()):
                raise SystemExit('pinned Rust did not return the exact successful tuple size')
        elif result.returncode == 0 or 'are too big for the target architecture' not in result.stderr:
            raise SystemExit('pinned Rust did not reject the exact exclusive object-size bound')
    with (output / 'lean.log').open('x') as log:
        subprocess.run(['lake', 'env', 'lean', '--run', 'tests/compiler_queries/WorldLayoutDAG.lean', str(material)],
                       cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT,
                       check=True, timeout=args.timeout)
    print('PASS pinned Rust size16/exclusive-bound oracles and Lean 16/64-node shared DAG actual results')


if __name__ == '__main__':
    main()
