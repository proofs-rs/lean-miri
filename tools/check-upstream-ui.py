#!/usr/bin/env python3
"""Run every compatible pinned upstream pass/fail case, without rewriting Rust.

Inventory includes unsupported profiles. Run output is stored only in scratch.
Exit zero requires every selected compatible case to pass; unsupported profiles
are reported separately, while attempted export/runner/oracle failures fail.
"""
import argparse
from collections import Counter
from concurrent.futures import ThreadPoolExecutor, as_completed
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tests/upstream_ui'))
from suite import SOURCES, compare, discover, reference_oracle
from run_guarded import run as guarded_run


def sha256(path):
    h = hashlib.sha256()
    with path.open('rb') as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b''):
            h.update(chunk)
    return h.hexdigest()


def invoke(command, env, log, timeout):
    try:
        return guarded_run(command, cwd=ROOT, env=env, log=log, timeout=timeout,
                           memory_limit=15_500_000_000).returncode
    except RuntimeError as error:
        return 'timeout' if 'walltime limit' in str(error) else 'resource_limit'


def run_case(case, args, env, output):
    directory = output / hashlib.sha256(case.id.encode()).hexdigest()[:16]
    directory.mkdir()
    record = case.record() | {'directory': str(directory), 'source_sha256': sha256(SOURCES / case.path)}
    snapshot = directory / 'input.json'
    source = SOURCES / case.path
    command = [str(args.exporter), '--output', str(snapshot)]
    entry_root = 'miri_start' if b'#![no_main]' in source.read_bytes() else 'main'
    command += ['--root', entry_root]
    command += ['--', str(source),
               '--edition=' + case.edition, '--crate-name=upstream_ui', '--sysroot', str(args.sysroot),
               '-o', str(directory / 'guest'), *case.flags]
    if case.revision:
        command.extend(['--cfg', case.revision])
    record['command'] = command
    started = time.monotonic()
    export_code = invoke(command, env, directory / 'export.log', args.export_timeout)
    record['export_exit'] = export_code
    record['export_seconds'] = time.monotonic() - started
    sidecar_path = Path(str(snapshot) + '.miri-reference.json')
    if export_code in ('timeout', 'resource_limit'):
        record['status'] = 'export_' + export_code
    elif not snapshot.is_file() or not sidecar_path.is_file():
        record['status'] = 'export_failed'
    else:
        sidecar = json.loads(sidecar_path.read_text())
        if sidecar.get('snapshot_byte_length') != snapshot.stat().st_size:
            raise ValueError('reference snapshot length mismatch')
        for name in ('miri', 'rustc'):
            expected = (ROOT / f'upstream/.pins/{name}.commit').read_text().strip()
            if sidecar.get(name + '_commit') != expected:
                raise ValueError(f'reference {name} pin mismatch')
        if sha256(SOURCES / case.path) != record['source_sha256']:
            raise ValueError('Rust source changed during export')
        record['snapshot_sha256'] = sha256(snapshot)
        record['reference'] = sidecar
        status, category = reference_oracle(case, sidecar, (directory / 'export.log').read_text(errors='replace'))
        record['category'] = category
        # A negative reference normally makes the exporter process exit 1.
        # Reject any other process failure even if a sidecar was written.
        if export_code not in (0, 1) or (not case.fail and export_code != 0):
            status = 'export_failed'
        record['status'] = status
        if status == 'ready':
            started = time.monotonic()
            code = invoke([str(args.runner), str(snapshot), '--ui-source', str(source)], env, directory / 'lean.log', args.timeout)
            record['lean_exit'] = code
            record['lean_seconds'] = time.monotonic() - started
            if code != 0:
                record['status'] = 'lean_' + code if isinstance(code, str) else 'lean_process_failed'
            else:
                terminals = [line.removeprefix('upstream_result: ') for line in
                             (directory / 'lean.log').read_text(errors='replace').splitlines()
                             if line.startswith('upstream_result: ')]
                if len(terminals) != 1:
                    record['status'] = 'lean_missing_outcome'
                else:
                    record['terminal'] = json.loads(terminals[0])
                    record['status'] = compare(case, record['terminal'], category)
    # Full exports are often large. Retain hashes, reference, logs and outcomes;
    # --keep-inputs explicitly retains exported bytes for debugging/replay.
    for temporary in directory.glob('input.json.tmp-*'):
        temporary.unlink()
    if snapshot.is_file() and 'snapshot_sha256' in record and sha256(snapshot) != record['snapshot_sha256']:
        record['status'] = 'input_mutated'
    if not args.keep_inputs:
        snapshot.unlink(missing_ok=True)
        (directory / 'guest').unlink(missing_ok=True)
    (directory / 'result.json').write_text(json.dumps(record, indent=2) + '\n')
    return record


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--inventory', action='store_true', help='list all cases and profile exclusions without building')
    parser.add_argument('--case', action='append', default=[], help='exact case id (repeatable); default: all cases')
    parser.add_argument('--output', type=Path, help='new run directory under scratch/')
    parser.add_argument('--exporter', type=Path, default=ROOT / 'exporter/target/release/lean-miri-mir-exporter')
    parser.add_argument('--sysroot', type=Path, default=ROOT / 'scratch/miri-sysroot')
    parser.add_argument('--runner', type=Path, default=ROOT / '.lake/build/bin/native_runner')
    parser.add_argument('--skip-build', action='store_true')
    parser.add_argument('--timeout', type=float, default=600)
    parser.add_argument('--export-timeout', type=float, default=900)
    parser.add_argument('--shard-index', type=int, default=0)
    parser.add_argument('--shard-count', type=int, default=1)
    parser.add_argument('--jobs', type=int, default=1, help='independent guest processes (default serial; high memory per case)')
    parser.add_argument('--keep-inputs', action='store_true')
    args = parser.parse_args()
    if min(args.timeout, args.export_timeout, args.jobs) <= 0:
        parser.error('timeouts and jobs must be positive')
    cases = list(discover())
    if args.case:
        unknown = set(args.case) - {c.id for c in cases}
        if unknown:
            parser.error(f'unknown case IDs: {sorted(unknown)}')
        cases = [c for c in cases if c.id in args.case]
    if not 0 <= args.shard_index < args.shard_count:
        parser.error('require 0 <= shard-index < shard-count')
    cases = [c for c in cases if int(hashlib.sha256(c.id.encode()).hexdigest(), 16) % args.shard_count == args.shard_index]
    if args.inventory:
        print(json.dumps([c.record() for c in cases], indent=2))
        return 0
    output = args.output or ROOT / 'scratch/upstream-ui' / time.strftime('%Y%m%dT%H%M%S')
    output = output.resolve()
    if not output.is_relative_to(ROOT / 'scratch') or output.exists():
        parser.error('--output must be a new directory under scratch/')
    output.mkdir(parents=True)
    (output / 'inventory.json').write_text(json.dumps([c.record() for c in cases], indent=2) + '\n')
    env = os.environ.copy()
    toolchain = ROOT / '.rustup/toolchains/miri-exporter-8144389c895d'
    env.update(PATH=str(toolchain / 'bin') + ':' + env.get('PATH', ''),
               LD_LIBRARY_PATH=str(toolchain / 'lib') + ':' + env.get('LD_LIBRARY_PATH', ''),
               MIRI_SYSROOT=str(args.sysroot.resolve()), ELAN_HOME=str(ROOT / '.elan'),
               LEAN_MIRI_PREPARED_ALLOC_ID_WORLD='1', LEAN_MIRI_RUN_PREPARED_MIRI='1',
               LEAN_NUM_THREADS='1')
    # No ambient reference args may silently change test conditions.
    for key in list(env):
        if key.startswith('LEAN_MIRI_REFERENCE_'):
            del env[key]
    env['LEAN_MIRI_REFERENCE_EMPTY_ENV'] = '1'
    if not args.skip_build:
        with (output / 'build.log').open('w') as log:
            subprocess.run(['flock', '--no-fork', '/tmp/lean-miri-lake-build.lock',
                            str(ROOT / '.elan/bin/lake'), 'build', 'native_runner'],
                           cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT, check=True)
    for path in (args.exporter, args.runner):
        if not path.is_file():
            parser.error(f'missing executable: {path}')
    exporter_hash, runner_hash = sha256(args.exporter), sha256(args.runner)
    (output / 'provenance.json').write_text(json.dumps({
        'source_lock_sha256': sha256(ROOT / 'upstream/source-lock.json'),
        'exporter_sha256': exporter_hash, 'runner_sha256': runner_hash,
        'timeout': args.timeout, 'export_timeout': args.export_timeout,
        'profile': 'same-prepared-TyCtxt Tree Borrows, precise interior mutability, no implicit writes',
        'claim': 'finite executions only; no whole-machine safety proof',
    }, indent=2) + '\n')
    records = [c.record() | {'status': 'profile_unsupported'} for c in cases if c.reasons]
    with ThreadPoolExecutor(max_workers=args.jobs) as pool, (output / 'results.jsonl').open('w') as stream:
        for record in records:
            stream.write(json.dumps(record) + '\n')
        futures = {pool.submit(run_case, c, args, env, output): c for c in cases if not c.reasons}
        for future in as_completed(futures):
            case = futures[future]
            try:
                record = future.result()
            except Exception as error:
                record = case.record() | {'status': 'harness_error', 'error': str(error)}
            records.append(record)
            stream.write(json.dumps(record) + '\n')
            stream.flush()
            print(f'{record["status"]}: {case.id}', flush=True)
    if sha256(args.exporter) != exporter_hash or sha256(args.runner) != runner_hash:
        raise RuntimeError('exporter or runner changed during comparisons; run is invalid')
    counts = dict(Counter(r['status'] for r in records))
    (output / 'summary.json').write_text(json.dumps(counts, indent=2) + '\n')
    print(json.dumps(counts, sort_keys=True))
    print(f'Results: {output}')
    return int(not counts.get('passed') or any(r['status'] not in ('passed', 'profile_unsupported') for r in records))


if __name__ == '__main__':
    raise SystemExit(main())
