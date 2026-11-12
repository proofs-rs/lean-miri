#!/usr/bin/env python3
"""Check a fresh material-seed guest against its same-TyCtxt Miri reference.

The exporter must already be built with miri-reference, and native_runner must
already be built. No builds or shared writable artifacts overlap guest execution.
One diagnostic timing is recorded, not a comparative performance claim.
"""
import argparse
import hashlib
import json
import os
import resource
from pathlib import Path
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]


def counters(cpu):
    result = {}
    for line in Path('/proc/stat').read_text().splitlines():
        if line.startswith(f'cpu{cpu} '):
            fields = line.split()
            result['cpu_steal_ticks'] = int(fields[8])
    path = Path('/sys/fs/cgroup/cpu.stat')
    if path.exists():
        result['cgroup_cpu'] = dict(line.split() for line in path.read_text().splitlines())
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path, help='new directory under scratch/')
    parser.add_argument('--timeout', type=float, default=600)
    args = parser.parse_args()
    output = args.output.resolve()
    if not output.is_relative_to(ROOT / 'scratch') or output.exists():
        parser.error('output must be a new directory under scratch/')
    output.mkdir(parents=True)
    document = output / 'guest.json'
    env = os.environ.copy()
    env.update(LEAN_MIRI_PREPARED_ALLOC_ID_WORLD='1', LEAN_MIRI_RUN_PREPARED_MIRI='1',
               LEAN_NUM_THREADS='1')
    with (output / 'export.log').open('x') as log:
        subprocess.run(['bash', 'tools/export-mir.sh', '--output', str(document),
                        '--root', 'miri_start', '--', 'tests/compiler_queries/material-guest.rs',
                        '--crate-name=material_guest', '--edition=2024', '-Cpanic=abort',
                        '-Zmir-opt-level=0', '--cfg=miri'], cwd=ROOT, env=env,
                       stdout=log, stderr=subprocess.STDOUT, check=True, timeout=args.timeout)
    raw = document.read_bytes()
    reference = json.loads(Path(str(document) + '.miri-reference.json').read_text())
    digest = 0xcbf29ce484222325
    for byte in raw:
        digest = ((digest ^ byte) * 0x100000001b3) & ((1 << 64) - 1)
    if not (reference.get('status') == 'completed'
            and reference.get('reference', {}).get('status') == 'completed'
            and reference['reference'].get('config', {}).get('same_tcx') is True
            and reference['reference'].get('outcome') == {'kind': 'exit_zero'}
            and reference.get('snapshot_byte_length') == len(raw)
            and reference.get('snapshot_fnv1a64') == f'{digest:016x}'):
        raise SystemExit('fresh reference did not establish same-TyCtxt exit_zero for these bytes')
    cpu = min(os.sched_getaffinity(0))
    binary = ROOT / '.lake/build/bin/native_runner'
    before = counters(cpu)
    cpu_before = resource.getrusage(resource.RUSAGE_CHILDREN)
    start = time.monotonic()
    with (output / 'lean.log').open('x') as log:
        result = subprocess.run(['taskset', '-c', str(cpu), str(binary), str(document),
                                 '--ui-source', 'tests/compiler_queries/material-guest.rs',
                                 '--ui-flags', '[]', '--profile'], cwd=ROOT, env=env,
                                stdout=log, stderr=subprocess.STDOUT, timeout=args.timeout)
    elapsed = time.monotonic() - start
    after = counters(cpu)
    cpu_after = resource.getrusage(resource.RUSAGE_CHILDREN)
    text = (output / 'lean.log').read_text()
    success = result.returncode == 0 and 'run: finalized_exit code=0;' in text
    manifest = dict(input_sha256=hashlib.sha256(raw).hexdigest(), input_bytes=len(raw),
                    binary_sha256=hashlib.sha256(binary.read_bytes()).hexdigest(),
                    cpu=cpu, lean_threads=1, wall_seconds=elapsed, before=before, after=after,
                    user_cpu_seconds=cpu_after.ru_utime-cpu_before.ru_utime,
                    system_cpu_seconds=cpu_after.ru_stime-cpu_before.ru_stime,
                    all_children_high_water_rss_kib=cpu_after.ru_maxrss,
                    lean_process_exit=result.returncode, terminal_exit_zero=success,
                    scope='one fresh finite guest; no general equivalence or speedup claim')
    (output / 'manifest.json').write_text(json.dumps(manifest, indent=2) + '\n')
    if document.read_bytes() != raw:
        raise SystemExit('input changed during execution')
    if not success:
        raise SystemExit(f'Lean guest did not finalize exit-zero; see {output / "lean.log"}')
    print('PASS fresh material guest: same-TyCtxt Miri and Lean finalized exit zero')


if __name__ == '__main__':
    main()
