#!/usr/bin/env python3
"""Run bounded, CPU-pinned GI mechanism probes; timeout is explicitly not pass.

These per-process measurements include material decoding. The Lean probe also
reports the isolated ofType/resolveType wall intervals. Shared-host samples do
not establish an arbitrary-program speedup.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import resource
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]


def cpu_steal(core):
    for line in Path('/proc/stat').read_text().splitlines():
        if line.startswith(f'cpu{core} '):
            return int(line.split()[8])
    raise RuntimeError('selected CPU missing from /proc/stat')


def cgroup_cpu():
    try:
        return dict((key, int(value)) for key, value in
                    (line.split() for line in Path('/sys/fs/cgroup/cpu.stat').read_text().splitlines()))
    except OSError:
        return {}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('material', type=Path)
    parser.add_argument('output', type=Path, help='new scratch directory')
    parser.add_argument('--mode', choices=('cert', 'raw'), default='cert')
    parser.add_argument('--case', action='append', choices=('primitive', 'early-reference', 'late-reference'))
    parser.add_argument('--timeout', type=float, default=30)
    parser.add_argument('--cpu', type=int, default=min(os.sched_getaffinity(0)))
    parser.add_argument('--lean', type=Path,
                        default=Path(os.environ.get('ELAN_HOME', ROOT / '.elan')) / 'bin/lean')
    args = parser.parse_args()
    output = args.output.resolve()
    if not output.is_relative_to(ROOT / 'scratch'):
        parser.error('output must be under scratch/')
    output.mkdir(parents=True, exist_ok=False)
    material = args.material.resolve()
    material_hash = hashlib.sha256(material.read_bytes()).hexdigest()
    env = dict(os.environ, LEAN_NUM_THREADS='1', LEAN_PATH=str(ROOT / '.lake/build/lib/lean'))
    results = []
    for case in args.case or ('primitive', 'early-reference', 'late-reference'):
        command = ['taskset', '-c', str(args.cpu), str(args.lean.absolute()), '--run',
                   str(ROOT / 'tools/GenericTypeProbe.lean'), str(material), args.mode, case]
        before = resource.getrusage(resource.RUSAGE_CHILDREN)
        steal_before = cpu_steal(args.cpu)
        group_before = cgroup_cpu()
        start = time.monotonic()
        log = output / f'{args.mode}-{case}.log'
        with log.open('x') as stream:
            try:
                process = subprocess.run(command, cwd=ROOT, env=env, stdout=stream,
                                         stderr=subprocess.STDOUT, timeout=args.timeout)
                status = process.returncode
            except subprocess.TimeoutExpired:
                status = 'timeout-not-pass'
        after = resource.getrusage(resource.RUSAGE_CHILDREN)
        group_after = cgroup_cpu()
        result = {
            'case': case, 'mode': args.mode, 'status': status, 'cpu': args.cpu,
            'material_sha256': material_hash, 'wall_seconds': time.monotonic() - start,
            'user_seconds': after.ru_utime - before.ru_utime,
            'system_seconds': after.ru_stime - before.ru_stime,
            'same_cpu_steal_ticks': cpu_steal(args.cpu) - steal_before,
            'ticks_per_second': os.sysconf('SC_CLK_TCK'),
            'cgroup_cpu_delta': {key: group_after[key] - value
                                 for key, value in group_before.items() if key in group_after},
        }
        results.append(result)
        print(json.dumps(result), flush=True)
    (output / 'measurements.json').write_text(json.dumps(results, indent=2) + '\n')
    if hashlib.sha256(material.read_bytes()).hexdigest() != material_hash:
        raise SystemExit('probe material changed during measurement')
    if any(result['status'] != 0 for result in results):
        raise SystemExit('one or more probes did not finish successfully; inspect retained logs')


if __name__ == '__main__':
    main()
