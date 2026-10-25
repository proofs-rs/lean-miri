#!/usr/bin/env python3
"""Run the explicitly maintained CI suites and retain per-suite wall times/logs."""
import argparse
from dataclasses import dataclass
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import platform
import signal
import subprocess
import sys
import time
from time_command import read_steps

ROOT = Path(__file__).resolve().parents[2]
REFERENCE_EXPORTER = 'exporter/target/release/lean-miri-mir-exporter'


@dataclass(frozen=True)
class Suite:
    name: str
    command: tuple[str, ...]
    timeout: int = 3600


def suites(lane):
    if lane == 'regression':
        # check.sh already contains quick's audit/Python/inventory checks.
        # Only the two fixture hash manifests are unique to check-quick.sh.
        return [Suite('connected-fixture-hashes', ('bash', '-c',
                      'cd tests/connected/fixtures && sha256sum --check SHA256SUMS')),
                Suite('input-fixture-hashes', ('bash', '-c',
                      'cd tests/input/fixtures && sha256sum --check SHA256SUMS')),
                Suite('full', ('bash', 'tools/check.sh'), 14400)]
    if lane == 'replay':
        # Freeze the full library closure before immutable-fixture replay.
        return [
            Suite('build', ('bash', 'tools/ci/build.sh'), 7200),
            Suite('canonical12', ('python3', 'tools/check-connected.py'), 14400),
            Suite('ordering', ('python3', 'tools/check-connected.py', '--ordering'), 7200),
            Suite('large-tb', ('python3', 'tools/check-connected.py', '--large-tb', '--timeout', '1800')),
            Suite('sc-seeds', ('python3', 'tools/check-sc-schedules.py')),
        ]
    if lane != 'extended':
        raise ValueError(lane)
    result = [
        Suite('build', ('bash', 'tools/ci/build.sh'), 7200),
        Suite('exporter-build', ('cargo', '+miri-exporter-8144389c895d', 'build', '--locked', '--offline',
                                 '--manifest-path', 'exporter/Cargo.toml')),
        Suite('decoder', ('bash', 'tools/check-decoder.sh')),
        Suite('structural', ('bash', 'tools/check-structural-regressions.sh')),
        Suite('optimization', ('bash', 'tools/check-performance-regressions.sh')),
        Suite('connected-proofs', ('bash', 'tools/check-connected-proofs.sh')),
        Suite('intrinsic-float', ('python3', 'tests/intrinsic_float/source_compare.py')),
        Suite('aes', ('python3', 'tests/aes/source_compare.py')),
        Suite('random-memory', ('python3', 'tests/random_memory/source_compare.py')),
        Suite('scheduler-prefix', ('python3', 'tests/scheduling/test_source_prefix.py')),
        Suite('sc-prefix', ('python3', 'tests/weak_memory/test_sc_prefix.py')),
        Suite('detached-join-order', ('python3', 'tests/step/test_detached_join_source_order.py')),
        Suite('selector', ('python3', 'tests/connected/compare_selector.py')),
        Suite('producer-decoder', ('python3', 'tests/producer/primitive_ranges.py')),
        Suite('native-math', ('lake', 'exe', 'native_math_boundary_qa')),
        Suite('fresh-prepare', ('bash', 'tools/ci/fresh.sh', 'prepare')),
        Suite('powi-zero', ('python3', 'tools/check-powi-zero.py', 'scratch/ci-fresh/powi-zero.json',
                            '--exporter', REFERENCE_EXPORTER)),
        Suite('math-host', ('python3', 'tools/check-math-nohost.py', 'scratch/ci-fresh/math-host',
                            '--exporter', REFERENCE_EXPORTER)),
        Suite('timezone', ('bash', 'tools/ci/fresh.sh', 'timezone')),
    ]
    for name, extra in [
        ('hrtb', ('--require-predicate-contrast',)),
        ('static', ()),
        ('hrtb-upcast', ('--require-predicate-contrast', '--require-trait-vptr')),
    ]:
        result.append(Suite('vtable-' + name, (
            'python3', 'tools/check-vtable-erasure.py', f'tests/repro/vtable/{name}-erasure-control.rs',
            f'scratch/ci-fresh/vtable-{name}.json', '--expect', 'identity',
            '--exporter', REFERENCE_EXPORTER, *extra)))
    return result


def stop(child):
    """Terminate the whole suite, including compiler/interpreter grandchildren."""
    try:
        os.killpg(child.pid, signal.SIGTERM)
    except ProcessLookupError:
        return
    try:
        child.wait(timeout=5)
    except subprocess.TimeoutExpired:
        pass
    # A grandchild can ignore TERM even after its parent exits.
    try:
        os.killpg(child.pid, signal.SIGKILL)
    except ProcessLookupError:
        pass
    if child.returncode is None:
        child.wait()


def execute(suite, output, root=ROOT):
    log = output / (suite.name + '.log')
    timing = (output / (suite.name + '.steps.jsonl')).resolve()
    timing.unlink(missing_ok=True)
    env = dict(os.environ, CI_TIMING_FILE=str(timing))
    start = time.monotonic()
    status, code = 'failed', None
    with log.open('w') as stream:
        stream.write(json.dumps(list(suite.command)) + '\n')
        stream.flush()
        try:
            child = subprocess.Popen(suite.command, cwd=root, stdout=stream,
                                     stderr=subprocess.STDOUT, start_new_session=True, env=env)
            try:
                code = child.wait(timeout=suite.timeout)
                status = 'passed' if code == 0 else 'failed'
            except subprocess.TimeoutExpired:
                status = 'timeout'
                stop(child)
                code = child.returncode
            except BaseException:
                stop(child)
                raise
        except OSError as error:
            stream.write(str(error) + '\n')
    steps, timing_errors = read_steps(timing)
    return dict(name=suite.name, command=list(suite.command), status=status,
                exit_code=code, seconds=round(time.monotonic() - start, 3),
                timeout_seconds=suite.timeout, log=str(log), steps=steps,
                timing_errors=timing_errors)


def run_all(selected, output, metadata, root=ROOT):
    output.mkdir(parents=True, exist_ok=True)
    rows = []
    report = dict(metadata, results=rows, complete=False)
    path = output / 'results.json'
    path.write_text(json.dumps(report, indent=2) + '\n')
    for suite in selected:
        print(f'::group::{suite.name}', flush=True)
        row = execute(suite, output, root)
        rows.append(row)
        # Preserve completed results even if the job is later interrupted.
        path.write_text(json.dumps(report, indent=2) + '\n')
        print(f"{row['status']}: {suite.name} ({row['seconds']}s); {row['log']}", flush=True)
        if row['status'] != 'passed':
            print('\n'.join(Path(row['log']).read_text(errors='replace').splitlines()[-80:]))
        print('::endgroup::', flush=True)
    report['complete'] = True
    path.write_text(json.dumps(report, indent=2) + '\n')
    summary = '| Suite | Result | Seconds |\n| --- | --- | ---: |\n'
    summary += ''.join(f"| {r['name']} | {r['status']} | {r['seconds']} |\n" for r in rows)
    for row in rows:
        if not row['steps']:
            continue
        summary += f"\n<details><summary>{row['name']}: command timings</summary>\n\n"
        summary += '| Command | Result | Wall seconds | CPU seconds |\n| --- | --- | ---: | ---: |\n'
        for step in row['steps']:
            cpu = round(step.get('user_seconds', 0) + step.get('system_seconds', 0), 3)
            summary += f"| {step['label']} | {step['status']} | {step.get('seconds', 'incomplete')} | {cpu} |\n"
        summary += '\n</details>\n'
    (output / 'summary.md').write_text(summary)
    if os.environ.get('GITHUB_STEP_SUMMARY'):
        with open(os.environ['GITHUB_STEP_SUMMARY'], 'a') as stream:
            stream.write(summary)
    return int(any(r['status'] != 'passed' for r in rows))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('lane', choices=['regression', 'extended', 'replay'])
    parser.add_argument('--list', action='store_true')
    args = parser.parse_args()
    selected = suites(args.lane)
    if args.list:
        for suite in selected:
            print(suite.name + ': ' + ' '.join(suite.command))
        return 0
    metadata = dict(lane=args.lane, commit=os.environ.get('GITHUB_SHA'),
                    started_at=datetime.now(timezone.utc).isoformat(),
                    platform=platform.platform(), python=sys.version,
                    cache=dict(exact_hit=os.environ.get('CI_LEAN_CACHE_HIT'),
                               requested_key=os.environ.get('CI_LEAN_CACHE_KEY'),
                               restored_key=os.environ.get('CI_LEAN_CACHE_RESTORED_KEY')),
                    lean_toolchain=(ROOT / 'lean-toolchain').read_text().strip(),
                    rustc_commit=(ROOT / 'upstream/.pins/rustc.commit').read_text().strip(),
                    miri_commit=(ROOT / 'upstream/.pins/miri.commit').read_text().strip())
    setup_steps, setup_errors = read_steps(ROOT / 'scratch/ci/setup.steps.jsonl')
    metadata.update(setup_steps=setup_steps, setup_timing_errors=setup_errors)
    return run_all(selected, ROOT / 'scratch/ci' / args.lane, metadata)


if __name__ == '__main__':
    raise SystemExit(main())
