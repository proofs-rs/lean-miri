#!/usr/bin/env python3
"""Compare frozen runners on independently hash-bound prepared-Miri inputs.

Each input must come from the same source/configuration. This measures one
finite workload, not compiler equivalence or general verification throughput.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import signal
import statistics
import time


def sha(path):
    with path.open('rb') as stream:
        return hashlib.file_digest(stream, 'sha256').hexdigest()


def reference(path):
    raw = path.read_bytes()
    sidecar = json.loads(Path(str(path) + '.miri-reference.json').read_text())
    digest = 0xcbf29ce484222325
    for byte in raw:
        digest = ((digest ^ byte) * 0x100000001b3) & ((1 << 64) - 1)
    ref = sidecar.get('reference', {})
    if not (sidecar.get('status') == 'completed' and ref.get('status') == 'completed'
            and ref.get('config', {}).get('same_tcx') is True
            and ref.get('outcome') == {'kind': 'exit_zero'}
            and sidecar.get('snapshot_byte_length') == len(raw)
            and sidecar.get('snapshot_fnv1a64') == f'{digest:016x}'):
        raise ValueError(f'{path}: missing hash-bound same-TyCtxt exit-zero reference')
    return dict(bytes=len(raw), sha256=hashlib.sha256(raw).hexdigest(),
                reference_config=ref['config'])


def counters(cpu):
    result = {}
    for line in Path('/proc/stat').read_text().splitlines():
        if line.startswith(f'cpu{cpu} '):
            result['cpu_steal_ticks'] = int(line.split()[8])
    for name in ('cpu.stat', 'memory.events'):
        path = Path('/sys/fs/cgroup') / name
        if path.exists():
            result[name] = {key: int(value) for key, value in
                            (line.split() for line in path.read_text().splitlines())}
    return result


def difference(after, before):
    return {key: difference(value, before[key]) if isinstance(value, dict)
            else value - before[key] for key, value in after.items()}


def trial(binary, document, source, cpu, timeout, log):
    before = counters(cpu)
    start = time.perf_counter()
    child = os.fork()
    if child == 0:
        try:
            os.sched_setaffinity(0, {cpu})
            with log.open('xb', buffering=0) as stream:
                os.dup2(stream.fileno(), 1)
                os.dup2(stream.fileno(), 2)
                env = {**os.environ, 'LEAN_NUM_THREADS': '1'}
                os.execve(str(binary), [str(binary), str(document), '--ui-source',
                                       str(source), '--ui-flags', '[]', '--profile'], env)
        finally:
            os._exit(127)
    timed_out = False
    while True:
        waited, status, usage = os.wait4(child, os.WNOHANG)
        if waited:
            break
        if time.perf_counter() - start > timeout:
            timed_out = True
            os.kill(child, signal.SIGKILL)
            _, status, usage = os.wait4(child, 0)
            break
        time.sleep(0.02)
    wall = time.perf_counter() - start
    after = counters(cpu)
    exit_code = os.waitstatus_to_exitcode(status)
    output = log.read_text(errors='replace')
    passed = not timed_out and exit_code == 0 and 'run: finalized_exit code=0;' in output
    return dict(status='PASS' if passed else 'INCOMPLETE_OR_FAILED_NOTPASS',
                exit_code=exit_code, timed_out=timed_out, wall_seconds=wall,
                user_seconds=usage.ru_utime, system_seconds=usage.ru_stime,
                cpu_seconds=usage.ru_utime + usage.ru_stime, peak_rss_kib=usage.ru_maxrss,
                host_before=before, host_after=after, host_delta=difference(after, before),
                log=str(log))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for version in ('before', 'after'):
        parser.add_argument(f'--{version}-binary', type=Path, required=True)
        parser.add_argument(f'--{version}-input', type=Path, required=True)
    parser.add_argument('--source', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True, help='new directory')
    parser.add_argument('--cpu', type=int, default=min(os.sched_getaffinity(0)))
    parser.add_argument('--trials', type=int, default=5)
    parser.add_argument('--warmups', type=int, default=1)
    parser.add_argument('--timeout', type=float, default=600)
    args = parser.parse_args()
    if args.trials < 2 or args.warmups < 0 or args.cpu not in os.sched_getaffinity(0):
        parser.error('require >=2 trials, >=0 warmups and an available CPU')
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    source = args.source.resolve()
    source_sha = sha(source)
    versions = {}
    for name in ('before', 'after'):
        document = getattr(args, name + '_input').resolve()
        original = getattr(args, name + '_binary').resolve()
        frozen = output / (name + '-runner')
        shutil.copy2(original, frozen)
        frozen.chmod(0o555)
        versions[name] = dict(input=str(document), binary=str(frozen),
                              binary_sha256=sha(frozen), **reference(document))
    if versions['before']['reference_config'] != versions['after']['reference_config']:
        raise ValueError('prepared reference configurations differ; comparison refused')
    manifest = dict(source=str(source), source_sha256=source_sha, cpu=args.cpu,
                    lean_threads=1, clock_ticks_per_second=os.sysconf('SC_CLK_TCK'),
                    versions=versions, trials=[],
                    scope='one workload; no compiler equivalence or general speedup claim')
    manifest_path = output / 'manifest.json'
    for pair in range(args.warmups + args.trials):
        order = ('before', 'after') if pair % 2 == 0 else ('after', 'before')
        for name in order:
            version = versions[name]
            document, binary = Path(version['input']), Path(version['binary'])
            if sha(source) != source_sha or sha(document) != version['sha256'] or sha(binary) != version['binary_sha256']:
                raise ValueError('source/input/frozen binary changed during comparison')
            result = trial(binary, document, source, args.cpu, args.timeout,
                           output / f'{pair:02d}-{name}.log')
            result.update(version=name, pair=pair, warmup=pair < args.warmups)
            manifest['trials'].append(result)
            manifest_path.write_text(json.dumps(manifest, indent=2) + '\n')
            if result['status'] != 'PASS':
                raise SystemExit('non-PASS terminal; raw manifest preserved, no ratio reported')
    for name, version in versions.items():
        if sha(source) != source_sha or sha(Path(version['input'])) != version['sha256'] or sha(Path(version['binary'])) != version['binary_sha256']:
            raise ValueError('source/input/frozen binary changed at final verification')
    manifest['summary'] = {}
    for name in versions:
        rows = [row for row in manifest['trials'] if row['version'] == name and not row['warmup']]
        manifest['summary'][name] = {key: dict(median=statistics.median(values),
            minimum=min(values), maximum=max(values), stdev=statistics.stdev(values))
            for key in ('wall_seconds', 'cpu_seconds', 'peak_rss_kib')
            for values in [[row[key] for row in rows]]}
    manifest['wall_median_before_over_after'] = (manifest['summary']['before']['wall_seconds']['median'] /
                                                manifest['summary']['after']['wall_seconds']['median'])
    manifest_path.write_text(json.dumps(manifest, indent=2) + '\n')
    print(manifest_path)


if __name__ == '__main__':
    main()
