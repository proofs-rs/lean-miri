#!/usr/bin/env python3
"""Run one fresh compiler-backed regression, retaining its inputs and diagnostics."""
import argparse
import json
import os
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[2]
EXPORTER = ROOT / 'exporter/target/release/lean-miri-mir-exporter'
FOCUSED = {
    'handoff-acquire': ('atomic-handoff/acquire.rs', 'AtomicHandoff', 'expect-zero'),
    'handoff-relaxed': ('atomic-handoff/relaxed.rs', 'AtomicHandoff', 'expect-race'),
    'fence-positive': ('atomic-fence/positive.rs', 'AtomicFence', 'expect-zero'),
    'fence-negative': ('atomic-fence/negative.rs', 'AtomicFence', 'expect-race'),
    'pthread-race': ('race-negative/pthread-race-miri-start.rs', 'AtomicHandoff', 'expect-race'),
    'backtrace': ('backtrace/source-e6209e72.rs', 'BacktraceSourceRun', None),
}


def environment():
    env = os.environ.copy()
    toolchain = Path(env.get('RUSTUP_HOME', ROOT / '.rustup')) / 'toolchains/miri-exporter-8144389c895d'
    env.update(ELAN_HOME=env.get('ELAN_HOME', str(ROOT / '.elan')),
               MIRI_SYSROOT=env.get('MIRI_SYSROOT', str(ROOT / 'scratch/miri-sysroot')),
               PATH=str(toolchain / 'bin') + ':' + env.get('PATH', ''),
               LD_LIBRARY_PATH=str(toolchain / 'lib') + ':' + env.get('LD_LIBRARY_PATH', ''),
               LEAN_NUM_THREADS='1')
    for key in list(env):
        if key.startswith('LEAN_MIRI_REFERENCE_') or key in (
                'LEAN_MIRI_PREPARED_ALLOC_ID_WORLD', 'LEAN_MIRI_RUN_PREPARED_MIRI'):
            del env[key]
    return env


def run(command, env, *, log=None, expected=0):
    command = [str(item) for item in command]
    print(json.dumps(command), flush=True)
    if log:
        with log.open('x') as stream:
            result = subprocess.run(command, cwd=ROOT, env=env, stdout=stream, stderr=subprocess.STDOUT)
    else:
        result = subprocess.run(command, cwd=ROOT, env=env)
    if result.returncode != expected:
        raise RuntimeError(f'expected process exit {expected}, got {result.returncode}: {command}; log={log}')


def libc():
    record = ROOT / 'scratch/connected-libc-target/libc-rlib.path'
    paths = record.read_text().splitlines()
    if len(paths) != 1 or not Path(paths[0]).is_file():
        raise RuntimeError('missing/invalid Cargo libc artifact; run tools/ci/fresh.sh prepare')
    return paths[0]


def export(source, output, env, *, roots=(), reference=False, expected=0, extra=()):
    command = [EXPORTER, '--output', output]
    for root in roots:
        command += ['--root', root]
    command += ['--', ROOT / source, '--edition=2024', '-Zmir-opt-level=0',
                '-Zalways-encode-mir', '--sysroot', env['MIRI_SYSROOT'], *extra]
    if reference:
        env = dict(env, LEAN_MIRI_PREPARED_ALLOC_ID_WORLD='1', LEAN_MIRI_RUN_PREPARED_MIRI='1')
    run(command, env, log=output.with_suffix('.export.log'), expected=expected)


def reference_check(output, race):
    # A compiler failure is never evidence of expected guest UB.
    import sys
    sys.path.insert(0, str(ROOT / 'tools'))
    import importlib.util
    spec = importlib.util.spec_from_file_location('fresh_vtable', ROOT / 'tools/check-vtable-erasure.py')
    vtable = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(vtable)
    raw = output.read_bytes()
    sidecar = json.loads(Path(str(output) + '.miri-reference.json').read_text())
    for name in ('miri', 'rustc'):
        assert sidecar[name + '_commit'] == (ROOT / f'upstream/.pins/{name}.commit').read_text().strip()
    assert sidecar['snapshot_byte_length'] == len(raw)
    assert sidecar['snapshot_fnv1a64'] == vtable.fingerprint(raw)
    reference = sidecar['reference']
    assert reference['config']['same_tcx'] is True
    if race:
        assert reference['status'] == 'failed'
        assert reference['outcome']['kind'] == 'miri_evaluation_error'
        diagnostic = output.with_suffix('.export.log').read_text()
        marker = 'error: Undefined Behavior:'
        assert marker in diagnostic
        primary = diagnostic.split(marker, 1)[1].split('\n\n', 1)[0]
        assert 'Data race' in primary
    else:
        assert reference['status'] == 'completed'
        assert reference['outcome'] == {'kind': 'exit_zero'}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('case', choices=[*FOCUSED, 'query-demand', 'runtime-type-closure', 'vtable-cross-crate'])
    args = parser.parse_args()
    output = ROOT / 'scratch/ci-fresh' / args.case
    output.mkdir(parents=True, exist_ok=False)
    env = environment()
    lake = Path(env['ELAN_HOME']) / 'bin/lake'
    snapshot = output / 'input.json'
    if args.case in FOCUSED:
        source, harness, expectation = FOCUSED[args.case]
        race = expectation == 'expect-race'
        export('tests/repro/' + source, snapshot, env, roots=['miri_start'], reference=True,
               expected=2 if race else 0, extra=['--crate-type=bin', '--crate-name=focused',
               '-Cpanic=abort', '--cfg=miri', '--extern', 'libc=' + libc()])
        reference_check(snapshot, race)
        run([lake, 'env', 'lean', '--run', f'tests/connected/focused/{harness}.lean', snapshot,
             *([expectation] if expectation else [])], env, log=output / 'lean.log')
    elif args.case == 'runtime-type-closure':
        export('exporter/fixtures/runtime_type_closure.rs', snapshot, env,
               roots=['make_dyn', 'call_dyn'], extra=['--crate-type=lib', '--crate-name=runtime_type_closure'])
        run(['python3', 'exporter/tests/check_runtime_type_closure.py', snapshot], env)
    elif args.case == 'query-demand':
        export('exporter/fixtures/call_transfer.rs', snapshot, env, roots=['call_transfer_root'],
               extra=['--crate-type=lib', '--crate-name=query_demand', '-Cpanic=abort', '--cfg=miri'])
        tls_snapshot = output / 'tls.json'
        export('exporter/fixtures/mir_features.rs', tls_snapshot, env, roots=['read_tls'],
               extra=['--crate-type=lib', '--crate-name=query_demand_tls'])
        run(['python3', 'tests/query_demand/make_cases.py', snapshot, output / 'cases',
             '--tls-base', tls_snapshot], env)
        run([lake, 'env', 'lean', '--run', 'tests/query_demand/CatalogRoles.lean', output / 'cases'], env)
    else:
        library = output / 'libvtable_metadata_producer.rlib'
        run(['rustc', 'tests/repro/vtable/metadata-producer.rs', '--crate-type=rlib',
             '--crate-name=vtable_metadata_producer', '--edition=2024', '-Cpanic=abort',
             '-Zmir-opt-level=0', '-Zalways-encode-mir', '--cfg=miri', '--sysroot',
             env['MIRI_SYSROOT'], '-o', library], env)
        run(['python3', 'tools/check-vtable-erasure.py', 'tests/repro/vtable/metadata-consumer.rs',
             snapshot, '--expect', 'identity', '--extern', 'vtable_metadata_producer=' + str(library),
             '--require-external-constant', 'vtable_metadata_producer::OBJECT',
             '--exporter', EXPORTER], env)
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
