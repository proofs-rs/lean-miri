#!/usr/bin/env python3
"""Replay finite connected fixtures against a freshly built local module closure."""
import argparse
import gzip
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tests/connected'))
from cases import CASES, MIRI_ERRORS
from run_guarded import run as run_guarded, source_closure
FIXTURES = ROOT / 'tests/connected/fixtures'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--case', action='append', help='canonical case ID (default: all twelve)')
    parser.add_argument('--ordering', action='store_true', help='four matched SC/weak controls')
    parser.add_argument('--large-tb', action='store_true', help='same-program Frozen-tag-write UB witness')
    parser.add_argument('--timeout', type=int, default=900, help='per-case seconds; expiration is a failure')
    args = parser.parse_args()
    if sum((bool(args.case), args.ordering, args.large_tb)) > 1:
        parser.error('choose canonical cases, --ordering, or --large-tb separately')
    env = os.environ.copy()
    env.setdefault('ELAN_HOME', str(ROOT / '.elan'))
    env['LEAN_NUM_THREADS'] = '1'
    lake = str(Path(env['ELAN_HOME']) / 'bin/lake')
    out = ROOT / 'scratch/connected-runs'
    out.mkdir(parents=True, exist_ok=True)
    run_dir = Path(tempfile.mkdtemp(prefix='run-', dir=out))
    canonical = {ident: (extra, code, texts, sha) for ident, extra, code, texts, sha, _, _ in CASES}
    if args.case and set(args.case) - canonical.keys():
        parser.error('unknown case: ' + str(set(args.case) - canonical.keys()))
    jobs = []
    if args.case or not (args.ordering or args.large_tb):
        for ident in args.case or canonical:
            extra, code, texts, sha = canonical[ident]
            jobs.append((ident, f'{ident}.lean', extra, code, texts, sha))
    if args.ordering:
        for ident in ('fence-acqrel', 'fence-sc', 'rmw-relaxed', 'rmw-sc'):
            jobs.append((ident, 'ScOrderingControls.lean', ['--tape', str(FIXTURES / f'{ident}.tape.json')], 0,
                         ['sc_ordering_control_fixture=PASS', 'outcome=exit_zero; leak_check=true'], None))
    if args.large_tb:
        jobs.append(('large-tb', 'LargeTreeBorrows.lean', ['Tree Borrows'], 0,
                     ['undefinedBehavior', 'ChildAccessForbidden', 'Frozen'],
                     '32870449acfdc89f8ff86d1519fb562d8ad11b9fc3c92cfc012ea2cb1d39b8a7'))
    # Refuse silently changed retained inputs before invoking any interpreter.
    subprocess.run(['sha256sum', '--quiet', '--check', 'SHA256SUMS'], cwd=FIXTURES, check=True)
    closure_before = source_closure(ROOT)
    ordering_rows = []
    for ident, harness, extra, expected_exit, required, expected_sha in jobs:
        raw = gzip.decompress((FIXTURES / f'{ident}.json.gz').read_bytes())
        if expected_sha and hashlib.sha256(raw).hexdigest() != expected_sha:
            raise SystemExit(f'{ident}: snapshot SHA-256 mismatch')
        reference = json.loads((FIXTURES / f'{ident}.reference.json').read_text())
        if ident in MIRI_ERRORS:
            diagnostic = (FIXTURES / f'{ident}.miri-error.txt').read_text()
            if reference['reference']['status'] != 'failed' or reference['reference']['outcome']['kind'] != 'miri_evaluation_error' or not all(t in diagnostic for t in MIRI_ERRORS[ident]):
                raise SystemExit(f'{ident}: expected reference UB diagnostic is not established')
        elif reference['reference']['status'] != 'completed' or reference['reference']['outcome']['kind'] != 'exit_zero':
            raise SystemExit(f'{ident}: reference did not complete successfully')
        if len(raw) != reference['snapshot_byte_length']:
            raise SystemExit(f'{ident}: reference byte length mismatch')
        fnv = 14695981039346656037
        for byte in raw:
            fnv = ((fnv ^ byte) * 1099511628211) & ((1 << 64) - 1)
        if f'{fnv:016x}' != reference['snapshot_fnv1a64']:
            raise SystemExit(f'{ident}: reference input identity mismatch')
        if reference['reference_contract'] != 'same_prepared_tcx_after_snapshot_capture;not_vanilla_miri_alloc_id_history':
            raise SystemExit(f'{ident}: reference contract changed')
        snapshot = run_dir / f'{ident}.json'
        snapshot.write_bytes(raw)
        cmd = [lake, 'env', 'lean', '--run', str(ROOT / 'tests/connected' / harness), str(snapshot), *extra]
        tracked_inputs = [snapshot, FIXTURES / f'{ident}.reference.json', ROOT / 'tests/connected' / harness, FIXTURES / f'{ident}.rs']
        if args.ordering:
            tracked_inputs.append(FIXTURES / f'{ident}.tape.json')
        def fingerprint():
            return {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in tracked_inputs}
        inputs_before = fingerprint()
        print(f'{ident}: running; log={run_dir / (ident + ".log")}', flush=True)
        try:
            result = run_guarded(cmd, cwd=ROOT, env=env, log=run_dir / f'{ident}.log',
                                 timeout=args.timeout, memory_limit=15_500_000_000)
            text = (run_dir / f'{ident}.log').read_text()
            if result.returncode != expected_exit or any(t not in text for t in required):
                raise SystemExit(f'{ident}: FAIL (exit={result.returncode}); inspect retained log')
            if args.ordering and ident in ('fence-acqrel', 'fence-sc', 'rmw-relaxed', 'rmw-sc'):
                result_path = run_dir / f'{ident}.result.json'
                result_path.write_text(json.dumps({'exit_code': result.returncode, 'guard': None, 'inputs_before': inputs_before, 'inputs_after': fingerprint(), 'log_sha256': hashlib.sha256((run_dir / f'{ident}.log').read_bytes()).hexdigest()}))
                Path(str(snapshot) + '.miri-reference.json').write_bytes((FIXTURES / f'{ident}.reference.json').read_bytes())
                ordering_rows.append({'case': ident, 'snapshot': str(snapshot), 'log': str(run_dir / f'{ident}.log'), 'prefix': str(FIXTURES / f'{ident}.tape.json'), 'result': str(result_path)})
                subprocess.run([sys.executable, str(ROOT / 'tests/connected/validate_guided_choice_replay.py'),
                                str(FIXTURES / f'{ident}.tape.json'), str(run_dir / f'{ident}.log'),
                                str(run_dir / f'{ident}.validation.json')], check=True)
            if ident == 'large-tb':
                subprocess.run([sys.executable, str(ROOT / 'tests/connected/validate_large_tb.py'), str(snapshot), str(run_dir / f'{ident}.log')], check=True)
            if fingerprint() != inputs_before:
                raise SystemExit(f'{ident}: input changed during run')
            print(f'{ident}: PASS (finite fixture assertion)', flush=True)
        finally:
            # Raw MIR is reproducible from the retained archive; retain only the run log.
            if not args.ordering:
                snapshot.unlink(missing_ok=True)
    if args.ordering:
        rows_path = run_dir / 'ordering-cases.json'
        rows_path.write_text(json.dumps(ordering_rows))
        try:
            subprocess.run([sys.executable, str(ROOT / 'tests/connected/validate_ordering_pairs.py'), str(rows_path), str(run_dir / 'ordering-result.json')], check=True)
        finally:
            for row in ordering_rows:
                Path(row['snapshot']).unlink(missing_ok=True)
                Path(row['snapshot'] + '.miri-reference.json').unlink(missing_ok=True)
    if source_closure(ROOT) != closure_before:
        raise SystemExit('project source or compiled module closure changed during replay')
    print(f'Logs: {run_dir}')


if __name__ == '__main__':
    main()
