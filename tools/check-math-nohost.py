#!/usr/bin/env python3
"""Compare real MIR host-demand and fixed-value math capability boundaries.

sin(1) has only a coarse source range assertion: pinned Miri permits host error
and this check does not claim bitwise numerical equivalence. The fixed cos(0)
control asserts exact 1.0 bits. Both use the canonical no_std source route.
"""
import argparse
import json
import os
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def expand_shared(document, value):
    # Schema3 may share complete tables and nested instance metadata. This is
    # only a coverage assertion; the Lean consumer decodes the original bytes.
    if isinstance(value, dict) and set(value) == {'$lean_miri_shared_ref'}:
        return expand_shared(document, document['shared_payloads']['nodes'][value['$lean_miri_shared_ref']])
    if isinstance(value, list):
        return [expand_shared(document, item) for item in value]
    if isinstance(value, dict):
        return {key: expand_shared(document, item) for key, item in value.items()}
    return value


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path, help='new output directory under scratch/')
    parser.add_argument('--timeout', type=float, default=600)
    parser.add_argument('--exporter', type=Path, default=ROOT / 'exporter/target/debug/lean-miri-mir-exporter')
    args = parser.parse_args()
    output = args.output.resolve()
    if not output.is_relative_to(ROOT / 'scratch') or output.exists():
        parser.error('output must be a new directory under scratch/')
    output.mkdir(parents=True)
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
    for fixed in [False, True]:
        check_case(args, output / ('fixed.json' if fixed else 'demand.json'), env, elan, sysroot, fixed)
    print('math-nohost: same-TyCtxt references exit_zero; host-enabled guests exit_zero; '
          'sin(1) host-absent Unsupported; cos(0) host-absent exit_zero')


def check_case(args, output, env, elan, sysroot, fixed):
    source = ROOT / 'tests/repro/math-host/miri_start_nohost.rs'
    cmd = [str(args.exporter.resolve()), '--output', str(output), '--root', 'miri_start', '--',
           str(source), '--crate-type=bin', '--crate-name=math_nohost',
           '--edition=2024', '-Cpanic=abort', '-Zmir-opt-level=0', '-Zalways-encode-mir',
           '--cfg=miri', '--sysroot', str(sysroot)]
    if fixed:
        cmd += ['--cfg=fixed_control']
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
    snapshot = json.loads(raw)
    records = expand_shared(snapshot, snapshot['compiler_runtime_queries'])['instances']
    names = {record.get('item_name', {}).get('value') for record in records
             if record.get('intrinsic_metadata', {}).get('status') == 'supported'
             and record['intrinsic_metadata'].get('value') is not None}
    expected_intrinsic = 'cos' if fixed else 'sin'
    if expected_intrinsic not in names:
        raise SystemExit(f'fresh MIR lost {expected_intrinsic} intrinsic: {names}')
    for mode in [[], ['--without-math-host' if fixed else '--expect-no-math-host']]:
        log_path = output.with_suffix('.host.log' if not mode else '.nohost.log')
        with log_path.open('x') as log:
            subprocess.run([str(elan / 'bin/lake'), 'env', 'lean', '--run',
                            'tests/connected/203-upcast-a-prefix.lean', str(output), *mode],
                           cwd=ROOT, env=env, check=True, timeout=args.timeout,
                           stdout=log, stderr=subprocess.STDOUT)
        text = log_path.read_text()
        expected = ('math_boundary=expected_unary_unsupported; guest_success=false'
                    if mode and not fixed else 'trait_upcast_result=exit_zero; leak_check=true')
        if expected not in text:
            raise SystemExit(f'missing exact terminal classification in {log_path}')
    # The QA expectation must not silently accept either the wrong terminal or
    # Unsupported under the normal success-only invocation.
    negative_mode = '--expect-no-math-host' if fixed else '--without-math-host'
    negative = subprocess.run([str(elan / 'bin/lake'), 'env', 'lean', '--run',
                               'tests/connected/203-upcast-a-prefix.lean', str(output), negative_mode],
                              cwd=ROOT, env=env, timeout=args.timeout, capture_output=True, text=True)
    output.with_suffix('.negative.log').write_text(negative.stdout + negative.stderr)
    expected_error = ('math host absence unexpectedly allowed guest exit' if fixed else
                      'stopped at Unsupported, so no pass is counted')
    if negative.returncode == 0 or expected_error not in negative.stdout + negative.stderr:
        raise SystemExit('negative terminal-classification control did not reject')
    if output.read_bytes() != raw:
        raise SystemExit('input bytes changed during consumer validation')


if __name__ == '__main__':
    main()
