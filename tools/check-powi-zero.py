#!/usr/bin/env python3
"""Compare fresh f32/f64 powi(0) guest bit assertions with prepared Miri.

The 16 non-signaling bases must produce exact positive-one bits. This finite
check excludes the signaling-NaN nondeterministic policy and std main.
"""
import argparse
import json
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
from mir_json import decode_mir_document


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path, help='new output under scratch/')
    parser.add_argument('--timeout', type=float, default=600)
    parser.add_argument('--exporter', type=Path, default=ROOT / 'exporter/target/debug/lean-miri-mir-exporter')
    args = parser.parse_args()
    output = args.output.resolve()
    if not output.is_relative_to(ROOT / 'scratch') or output.exists():
        parser.error('output must be a new file under scratch/')
    output.parent.mkdir(parents=True, exist_ok=True)
    env = os.environ.copy()
    toolchain = Path(env.get('RUSTUP_HOME', ROOT / '.rustup')) / 'toolchains/miri-exporter-8144389c895d'
    sysroot = Path(env.get('MIRI_SYSROOT', ROOT / 'scratch/miri-sysroot'))
    elan = Path(env.get('ELAN_HOME', ROOT / '.elan'))
    env['ELAN_HOME'] = str(elan)
    env['PATH'] = f"{toolchain / 'bin'}:{env.get('PATH', '')}"
    env['LD_LIBRARY_PATH'] = str(toolchain / 'lib') + ':' + env.get('LD_LIBRARY_PATH', '')
    env['LEAN_MIRI_PREPARED_ALLOC_ID_WORLD'] = '1'
    env['LEAN_MIRI_RUN_PREPARED_MIRI'] = '1'
    env.pop('LEAN_MIRI_REFERENCE_ARGS_JSON', None)
    env['LEAN_NUM_THREADS'] = '1'
    cmd = [str(args.exporter.resolve()), '--output', str(output), '--root', 'miri_start', '--',
           str(ROOT / 'tests/repro/math-host/miri_start_powi_zero.rs'), '--crate-type=bin', '--crate-name=powi_zero',
           '--edition=2024', '-Cpanic=abort', '-Zmir-opt-level=0', '-Zalways-encode-mir',
           '--cfg=miri', '--sysroot', str(sysroot)]
    with output.with_suffix('.export.log').open('x') as log:
        subprocess.run(cmd, cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT,
                       check=True, timeout=args.timeout)
    reference = json.loads(Path(str(output) + '.miri-reference.json').read_text())
    raw = output.read_bytes()
    digest = 0xcbf29ce484222325
    for byte in raw:
        digest = ((digest ^ byte) * 0x100000001b3) & ((1 << 64) - 1)
    if (reference.get('status') != 'completed' or
            reference.get('rustc_commit') != (ROOT / 'upstream/.pins/rustc.commit').read_text().strip() or
            reference.get('miri_commit') != (ROOT / 'upstream/.pins/miri.commit').read_text().strip() or
            reference.get('reference', {}).get('status') != 'completed' or
            reference['reference'].get('outcome') != {'kind': 'exit_zero'} or
            reference['reference'].get('config', {}).get('same_tcx') is not True or
            reference.get('snapshot_byte_length') != len(raw) or
            reference.get('snapshot_fnv1a64') != f'{digest:016x}'):
        raise SystemExit('reference did not establish same-TyCtxt exit_zero for these exact bytes')
    # Check that the fresh compiler output retained both real intrinsic calls.
    # A source-level powi spelling alone is insufficient coverage evidence.
    snapshot = decode_mir_document(json.loads(raw))
    records = snapshot['compiler_runtime_queries']['instances']
    intrinsics = {record['instance_id']: record.get('item_name', {}).get('value')
                  for record in records
                  if record.get('intrinsic_metadata', {}).get('status') == 'supported'
                  and record['intrinsic_metadata'].get('value') is not None}
    retained = set()
    for body in snapshot['bodies']:
        if body.get('def_path') != 'miri_start':
            continue
        for block in body['basic_blocks']:
            call = block.get('terminator', {}).get('kind', {})
            name = intrinsics.get(call.get('resolution', {}).get('instance_id'))
            if name not in {'powif32', 'powif64'}:
                continue
            base, power = [arg['operand'] for arg in call['args']]
            if (base['kind'] not in {'Copy', 'Move'} or power['kind'] != 'Constant' or
                    power['constant']['constant']['value']['bits_unsigned'] != '0'):
                raise SystemExit(f'{name} lost its runtime base or zero exponent')
            retained.add(name)
    if retained != {'powif32', 'powif64'}:
        raise SystemExit(f'fresh MIR lost powi intrinsic calls: {retained}')
    subprocess.run([str(elan / 'bin/lake'), 'env', 'lean', '--run',
                    'tests/connected/203-upcast-a-prefix.lean', str(output)],
                   cwd=ROOT, env=env, check=True, timeout=args.timeout)
    if output.read_bytes() != raw:
        raise SystemExit('input bytes changed during consumer validation')
    print('powi-zero: 16 exact positive-one bit assertions; prepared Miri + connected exit_zero')


if __name__ == '__main__':
    main()
