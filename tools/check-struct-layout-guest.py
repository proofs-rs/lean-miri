#!/usr/bin/env python3
"""Fresh struct reads through prepared pinned Miri and the native Lean runner."""
import argparse
import json
import os
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path, help='new output under scratch/')
    parser.add_argument('--timeout', type=float, default=600)
    args = parser.parse_args()
    output = args.output.resolve()
    if not output.is_relative_to(ROOT / 'scratch') or output.exists():
        parser.error('output must be a new file under scratch/')
    output.parent.mkdir(parents=True, exist_ok=True)
    env = os.environ.copy()
    toolchain = Path(env.get('RUSTUP_HOME', ROOT / '.rustup')) / 'toolchains/miri-exporter-8144389c895d'
    sysroot = Path(env.get('MIRI_SYSROOT', ROOT / 'scratch/miri-sysroot'))
    env['PATH'] = f"{toolchain / 'bin'}:{env.get('PATH', '')}"
    env['LD_LIBRARY_PATH'] = str(toolchain / 'lib') + ':' + env.get('LD_LIBRARY_PATH', '')
    env['LEAN_MIRI_PREPARED_ALLOC_ID_WORLD'] = '1'
    env['LEAN_MIRI_RUN_PREPARED_MIRI'] = '1'
    env['LEAN_NUM_THREADS'] = '1'
    env.pop('LEAN_MIRI_REFERENCE_ARGS_JSON', None)
    command = [str(ROOT / 'exporter/target/release/lean-miri-mir-exporter'),
               '--output', str(output), '--root', 'miri_start', '--',
               str(ROOT / 'tests/repro/compiler-queries/struct-layout-guest.rs'),
               '--crate-type=bin', '--crate-name=struct_layout_guest', '--edition=2024',
               '-Cpanic=abort', '-Zmir-opt-level=0', '-Zalways-encode-mir',
               '--cfg=miri', '--sysroot', str(sysroot)]
    with output.with_suffix('.export.log').open('x') as log:
        subprocess.run(command, cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT,
                       check=True, timeout=args.timeout)
    raw = output.read_bytes()
    reference = json.loads(Path(str(output) + '.miri-reference.json').read_text())
    digest = 0xcbf29ce484222325
    for byte in raw:
        digest = ((digest ^ byte) * 0x100000001b3) & ((1 << 64) - 1)
    lock = json.loads((ROOT / 'upstream/source-lock.json').read_text())
    if not (reference.get('status') == 'completed'
            and reference.get('rustc_commit') == lock['pins']['rustc']['commit']
            and reference.get('miri_commit') == lock['pins']['miri']['commit']
            and reference.get('reference', {}).get('outcome') == {'kind': 'exit_zero'}
            and reference.get('reference', {}).get('config', {}).get('same_tcx') is True
            and reference.get('snapshot_byte_length') == len(raw)
            and reference.get('snapshot_fnv1a64') == f'{digest:016x}'):
        raise SystemExit('prepared Miri did not establish same-TyCtxt exit-zero on these bytes')
    document = json.loads(raw)
    if sum('struct_type' in row for row in document['layout_values']) < 5:
        raise SystemExit('fresh guest lost its five struct layout material recipes')
    with output.with_suffix('.lean.log').open('x') as log:
        subprocess.run([str(ROOT / '.lake/build/bin/native_runner'), str(output),
                        '--ui-source', str(ROOT / 'tests/repro/compiler-queries/struct-layout-guest.rs'),
                        '--ui-flags', '[]'],
                       cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT,
                       check=True, timeout=args.timeout)
    result = output.with_suffix('.lean.log').read_text()
    if not re.search(r'^run: finalized_exit code=0;', result, re.MULTILINE):
        raise SystemExit('Lean guest did not finalize with exit-zero; inspect the retained log')
    if output.read_bytes() != raw:
        raise SystemExit('input bytes changed during consumer execution')
    print('PASS five genuine struct field reads: prepared same-TyCtxt Miri and Lean exit-zero')


if __name__ == '__main__':
    main()
