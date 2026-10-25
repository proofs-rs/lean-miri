#!/usr/bin/env python3
"""Compare fresh Linux localtime_r guest assertions in pinned Miri and Lean.

The standalone reference explicitly disables isolation (required by localtime_r).
It runs the same Rust, compiler flags and MIR-enabled sysroot as the exporter;
this does not compare vanilla Miri's allocation IDs with the prepared catalog.
"""
import argparse
import hashlib
import json
import os
import re
import select
from pathlib import Path
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('output', type=Path, help='new output directory under scratch/')
    parser.add_argument('--libc', type=Path, required=True,
                        help='actual libc rlib built with tools/build-connected-libc.sh')
    parser.add_argument('--miri', type=Path, default=ROOT / 'upstream/miri-source/target/debug/miri')
    parser.add_argument('--miri-build-record', type=Path, default=ROOT / 'scratch/miri-reference-build.json')
    parser.add_argument('--exporter', type=Path, default=ROOT / 'exporter/target/debug/lean-miri-mir-exporter')
    parser.add_argument('--timeout', type=float, default=600)
    args = parser.parse_args()
    output = args.output.resolve()
    if not output.is_relative_to(ROOT / 'scratch') or output.exists():
        parser.error('output must be a new directory under scratch/')
    if not args.libc.is_file():
        parser.error('--libc must name a built rlib')
    build = json.loads(args.miri_build_record.read_text())
    rustc = (ROOT / 'upstream/.pins/rustc.commit').read_text().strip()
    if build['rustc_commit'] != rustc or digest(args.miri) != build['binary_sha256']:
        parser.error('reference binary/build record differs; rerun setup-miri-reference.sh')
    output.mkdir(parents=True)
    env = os.environ.copy()
    toolchain = Path(env.get('RUSTUP_HOME', ROOT / '.rustup')) / 'toolchains/miri-exporter-8144389c895d'
    sysroot = Path(env.get('MIRI_SYSROOT', ROOT / 'scratch/miri-sysroot')).resolve()
    env['PATH'] = str(toolchain / 'bin') + ':' + env.get('PATH', '')
    env['LD_LIBRARY_PATH'] = str(toolchain / 'lib') + ':' + env.get('LD_LIBRARY_PATH', '')
    env['MIRI_SYSROOT'] = str(sysroot)
    env['ELAN_HOME'] = str(Path(env.get('ELAN_HOME', ROOT / '.elan')).resolve())
    env['LEAN_NUM_THREADS'] = '1'
    # Deliberately disagree with UTC fallback: the guest must unset/change TZ.
    env['TZ'] = 'Pacific/Honolulu'
    env['LEAN_MIRI_PREPARED_ALLOC_ID_WORLD'] = '1'
    env['LEAN_MIRI_RUN_PREPARED_MIRI'] = '0'
    source = ROOT / 'tests/repro/timezone/localtime.rs'
    source_digest = digest(source)
    compiler = [str(source), '--crate-type=bin', '--crate-name=timezone_boundary',
                '--edition=2024', '-Cpanic=abort', '-Zmir-opt-level=0', '-Zalways-encode-mir',
                '--cfg=miri', '--sysroot', str(sysroot), '--extern', 'libc=' + str(args.libc.resolve())]
    exported = output / 'input.json'
    commands = [
        ('reference', [str(args.miri.resolve()), '-Zmiri-disable-isolation',
                       '-Zmiri-tree-borrows', '-Zmiri-deterministic-floats', *compiler]),
        ('export', [str(args.exporter.resolve()), '--output', str(exported),
                    '--root', 'miri_start', '--', *compiler]),
        ('connected', [str(Path(env['ELAN_HOME']) / 'bin/lake'), 'env', 'lean', '--run',
                       'tests/connected/203-upcast-a-prefix.lean', str(exported), '--timezone']),
    ]
    snapshot_digest = None
    consumed_polls = None
    for name, command in commands:
        with (output / f'{name}.log').open('x') as log:
            if name == 'connected':
                # A real Linux poll object lives across the complete source run.
                # Capture a bounded sequence of actual empty nonblocking polls.
                # The interpreter checks and consumes one observation per call;
                # registration/blocking/unobserved demands remain Unsupported.
                # This is a finite trace, not a general host poll implementation.
                with select.epoll() as poll:
                    env['LEAN_MIRI_TIMEZONE_POLL_FD'] = str(poll.fileno())
                    # Preserve the source request order: new poll, monotonic
                    # initialization, then the nonblocking poll observations.
                    monotonic = time.monotonic_ns()
                    env['LEAN_MIRI_TIMEZONE_MONOTONIC_NANOS'] = str(monotonic)
                    observations = 512
                    for _ in range(observations):
                        if poll.poll(timeout=0, maxevents=16):
                            raise SystemExit('unexpected event in the unregistered host poll trace')
                    env['LEAN_MIRI_TIMEZONE_POLL_OBSERVATIONS'] = str(observations)
                    subprocess.run(command, cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT,
                                   pass_fds=(poll.fileno(),), check=True, timeout=args.timeout)
            else:
                subprocess.run(command, cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT,
                               check=True, timeout=args.timeout)
        if name == 'connected':
            terminal = (output / 'connected.log').read_text()
            if 'timezone_result=exit_zero; leak_check=true; threads=1;' not in terminal:
                raise SystemExit('connected output lacks the exact exit-zero/leak/thread assertions')
            consumed = re.search(r'observed_host_polls=512; consumed_host_polls=(\d+)', terminal)
            if not consumed or not 0 < int(consumed.group(1)) <= 512:
                raise SystemExit('connected output lacks the bounded host poll consumption count')
            consumed_polls = int(consumed.group(1))
        if name == 'export':
            snapshot_digest = digest(exported)
        if digest(source) != source_digest or (snapshot_digest and digest(exported) != snapshot_digest):
            raise SystemExit('guest source or exported bytes changed during comparison')
    result = {'rustc_commit': rustc, 'miri_commit': (ROOT / 'upstream/.pins/miri.commit').read_text().strip(),
              'reference_binary_sha256': build['binary_sha256'], 'source_sha256': source_digest,
              'input_sha256': snapshot_digest, 'reference': 'standalone exit_zero; isolation explicitly disabled',
              'connected': 'exit_zero with leak check', 'host_TZ': env['TZ'],
              'localtime_assertions': 8, 'consumed_host_polls': consumed_polls,
              'host_monotonic_nanos': monotonic,
              'host_initialization': 'one live epoll, one monotonic timestamp, 512 empty nonblocking polls',
              'commands': {name: cmd for name, cmd in commands}}
    (output / 'result.json').write_text(json.dumps(result, indent=2) + '\n')
    print('timezone: 8 localtime_r assertions PASS in pinned standalone Miri and fresh connected Lean')


if __name__ == '__main__':
    main()
