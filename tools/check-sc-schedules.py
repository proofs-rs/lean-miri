#!/usr/bin/env python3
"""Bounded diagnostic seeds 0..11 with independent atomic-order log validation."""
import gzip
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
from run_guarded import run as run_guarded, source_closure

ROOT = Path(__file__).resolve().parents[1]


def main():
    out = ROOT / 'scratch/sc-schedules'
    out.mkdir(parents=True, exist_ok=True)
    run = Path(tempfile.mkdtemp(prefix='run-', dir=out))
    fixtures = ROOT / 'tests/connected/fixtures'
    subprocess.run(['sha256sum', '--quiet', '--check', 'SHA256SUMS'], cwd=fixtures, check=True)
    raw = run / '198-sc-base.json'
    raw.write_bytes(gzip.decompress((fixtures / '198-sc-base.json.gz').read_bytes()))
    env = os.environ.copy()
    env.setdefault('ELAN_HOME', str(ROOT / '.elan'))
    env['LEAN_NUM_THREADS'] = '1'
    lake = str(Path(env['ELAN_HOME']) / 'bin/lake')
    inputs = [raw, fixtures / '198-sc-base.rs', fixtures / '198-sc-base.reference.json',
              ROOT / 'tests/connected/ScSchedules.lean', ROOT / 'tests/connected/validate_schedule.py']
    def hashes():
        return {str(p.relative_to(ROOT)): hashlib.sha256(p.read_bytes()).hexdigest() for p in inputs}
    before = hashes()
    closure_before = source_closure(ROOT)
    orders = set()
    try:
        # Fixed original budget. No seed search beyond these twelve executions.
        for seed in range(12):
            log = run / f'seed-{seed:02d}.log'
            result = run_guarded([lake, 'env', 'lean', '--run', 'tests/connected/ScSchedules.lean', str(raw), str(seed)],
                                 cwd=ROOT, env=env, log=log, timeout=120, memory_limit=15_000_000_000)
            if result.returncode:
                raise SystemExit(f'seed {seed}: failed (exit {result.returncode}); log={log}')
            report = run / f'seed-{seed:02d}.json'
            subprocess.run([sys.executable, str(ROOT / 'tests/connected/validate_schedule.py'), str(raw), str(log), str(report)], check=True)
            checked = json.loads(report.read_text())
            if int(checked['reported_seed']) != seed:
                raise SystemExit('reported seed differs from requested seed')
            orders.add(tuple(checked['atomic_intrinsic_order']))
        subprocess.run([sys.executable, str(ROOT / 'tests/connected/check_schedule_rejections.py'), str(raw),
                        str(run / 'seed-00.log'), str(run / 'negative-validator')], check=True)
        if hashes() != before or source_closure(ROOT) != closure_before:
            raise SystemExit('SC source/input changed during the run')
        print(f'PASS: seeds 0..11; observed atomic orders={sorted(orders)}; logs={run}')
        print('Sampled execution coverage only; unobserved schedules and all-prefix safety remain open.')
    finally:
        raw.unlink(missing_ok=True)


if __name__ == '__main__':
    main()
