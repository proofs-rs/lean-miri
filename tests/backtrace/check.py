#!/usr/bin/env python3
"""Compare runtime backtrace observations against the matching prepared Miri."""
import argparse
import importlib.util
import json
import os
from pathlib import Path
import struct
import sys
import subprocess
from types import SimpleNamespace

ROOT = Path(__file__).resolve().parents[2]
sys.path[:0] = [str(ROOT / 'tools'), str(ROOT / 'tests/upstream_ui')]
from suite import Case
SPEC = importlib.util.spec_from_file_location('backtrace_ui', ROOT / 'tools/check-upstream-ui.py')
driver = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(driver)


def events(path):
    payload = path.read_bytes()
    prefix, suffix = b'\0backtrace-event\xff', b'\xffbacktrace-end\0\n'
    result, cursor = [], 0
    while (start := payload.find(prefix, cursor)) >= 0:
        start += len(prefix)
        if start + 64 > len(payload):
            raise RuntimeError('truncated backtrace event header')
        header = struct.unpack_from('<8Q', payload, start)
        name_length, filename_length = header[6:]
        if name_length > 512 or filename_length > 512:
            raise RuntimeError('invalid backtrace string length')
        name_start = start + 64
        filename_start = name_start + name_length
        end = filename_start + filename_length
        if payload[end:end + len(suffix)] != suffix:
            raise RuntimeError('truncated backtrace event payload')
        name, filename = payload[name_start:filename_start], payload[filename_start:end]
        name.decode('utf-8')
        filename.decode('utf-8')
        result.append(header[:6] + (name, filename))
        cursor = end + len(suffix)
    return result


def main():
    parser = argparse.ArgumentParser(__doc__)
    parser.add_argument('--exporter', type=Path, required=True)
    parser.add_argument('--runner', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--sysroot', type=Path, default=ROOT / 'scratch/lake/miri-sysroot')
    args = parser.parse_args()
    output = args.output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    toolchain = ROOT / '.rustup/toolchains/miri-exporter-8eb778d04094'
    env = dict(os.environ, ELAN_HOME=str(ROOT / '.elan'), LEAN_NUM_THREADS='1',
        LEAN_MIRI_PREPARED_ALLOC_ID_WORLD='1', LEAN_MIRI_RUN_PREPARED_MIRI='1')
    env['PATH'] = str(toolchain / 'bin') + ':' + str(ROOT / '.elan/bin') + ':' + env['PATH']
    env['LD_LIBRARY_PATH'] = str(toolchain / 'lib') + ':' + env.get('LD_LIBRARY_PATH', '')
    settings = SimpleNamespace(exporter=args.exporter.resolve(), runner=args.runner.resolve(),
        sysroot=args.sysroot.resolve(), export_timeout=300, timeout=300,
        memory_limit=12 * 1024**3, keep_inputs=True)
    hashes = [driver.sha256(settings.exporter), driver.sha256(settings.runner)]
    driver.SOURCES = ROOT / 'tests/fixtures/backtrace'
    base = ['-Cpanic=abort', '-Zmir-opt-level=0', '-Zalways-encode-mir', '--cfg=miri']
    remap = '--remap-path-prefix=' + str(ROOT) + '=/mapped/π'
    cases = [Case('runtime.rs', revision='ordinary', edition='2024', flags=base),
        Case('runtime.rs', revision='remapped', edition='2024', flags=base + [remap]),
        Case('runtime.rs', revision='diagnostics_remap', edition='2024',
             flags=base + [remap, '-Zunstable-options', '--remap-path-scope=diagnostics'])]
    records = []
    for case in cases:
        record = driver.run_case(case, settings, env, output)
        if record['status'] != 'passed':
            raise RuntimeError(f"{case.id}: {record['status']}; see {record['directory']}")
        directory = Path(record['directory'])
        reference = events(directory / 'export.log')
        native = events(directory / 'lean.log')
        if native != reference or not reference:
            raise RuntimeError(f'{case.id}: exact runtime backtrace event sequences differ')
        rounds = {round for round, *_ in reference}
        if rounds != {0, 1, 2, 3, 4}:
            raise RuntimeError(f'{case.id}: missing macro or deep/body-context observations: {rounds}')
        for round in rounds:
            rows = [row for row in reference if row[0] == round]
            if [row[1] for row in rows] != list(range(len(rows))):
                raise RuntimeError('frame order or count changed')
        if len([row for row in reference if row[0] == 2]) < 14:
            raise RuntimeError('deep-scope fixture did not exercise the intended stack')
        if case.revision != 'ordinary' and not all(row[7].startswith('/mapped/π'.encode()) for row in reference):
            raise RuntimeError('runtime filenames did not preserve unconditional Unicode remapping')
        oracle_input = directory / 'oracle-input.json'
        oracle = directory / 'oracle.json'
        command = list(record['command'])
        command[command.index('--output') + 1] = str(oracle_input)
        command[command.index('--'):command.index('--')] = ['--oracle-output', str(oracle)]
        oracle_env = dict(env)
        oracle_env.pop('LEAN_MIRI_PREPARED_ALLOC_ID_WORLD')
        oracle_env.pop('LEAN_MIRI_RUN_PREPARED_MIRI')
        with (directory / 'oracle-export.log').open('w') as log:
            subprocess.run(command, cwd=ROOT, env=oracle_env, stdout=log, stderr=subprocess.STDOUT, check=True)
        payload = oracle_input.read_bytes()
        expected = json.loads(oracle.read_text())
        fingerprint = 0xcbf29ce484222325
        for byte in payload:
            fingerprint = ((fingerprint ^ byte) * 0x100000001b3) & ((1 << 64) - 1)
        if expected.get('schema') != 'lean-miri-rustc-oracle' or expected.get('snapshot_byte_length') != len(payload) or expected.get('snapshot_fnv1a64') != f'{fingerprint:016x}':
            raise RuntimeError('source hygiene oracle is not bound to these input bytes')
        if expected.get('rustc_commit') != json.loads(payload)['producer']['rustc_commit']:
            raise RuntimeError('source hygiene oracle compiler revision differs')
        with (directory / 'walk-oracle.log').open('w') as log:
            subprocess.run(['lake', 'env', 'lean', '--run', 'tests/backtrace/WalkOracle.lean',
                str(oracle_input), str(oracle)], cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT, check=True)
        record['walks_compared'] = len(expected['backtrace_walks'])
        record['oracle_input_sha256'] = driver.sha256(oracle_input)
        record['oracle_sha256'] = driver.sha256(oracle)
        record['runtime_frames_compared'] = len(reference)
        records.append(record)
        print('PASS', case.id, len(reference), 'exact function raw IDs, BytePos, line/column, names and frame order', flush=True)
    assert hashes == [driver.sha256(settings.exporter), driver.sha256(settings.runner)], 'binaries changed during comparisons'
    (output / 'summary.json').write_text(json.dumps({'cases': records, 'binary_sha256': hashes}, indent=2) + '\n')


if __name__ == '__main__':
    main()
