#!/usr/bin/env python3
"""Compare demanded caller locations with the matching prepared Miri execution."""
import argparse
import importlib.util
import itertools
import json
import os
import re
from pathlib import Path
import subprocess
import sys
from types import SimpleNamespace

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'tests/upstream_ui'))
sys.path.insert(0, str(ROOT / 'tools'))
from suite import Case
SPEC = importlib.util.spec_from_file_location('caller_ui', ROOT / 'tools/check-upstream-ui.py')
driver = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(driver)


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
        LEAN_MIRI_PREPARED_ALLOC_ID_WORLD='1', LEAN_MIRI_RUN_PREPARED_MIRI='1',
        LEAN_MIRI_REFERENCE_ALLOCATION_TRACE='1')
    env['PATH'] = str(toolchain / 'bin') + ':' + str(ROOT / '.elan/bin') + ':' + env['PATH']
    env['LD_LIBRARY_PATH'] = str(toolchain / 'lib') + ':' + env.get('LD_LIBRARY_PATH', '')
    settings = SimpleNamespace(exporter=args.exporter.resolve(), runner=args.runner.resolve(),
        sysroot=args.sysroot.resolve(), export_timeout=300, timeout=300,
        memory_limit=12 * 1024**3, keep_inputs=True)
    hashes = [driver.sha256(settings.exporter), driver.sha256(settings.runner)]
    driver.SOURCES = ROOT / 'tests/fixtures/caller_location'
    cases = []
    for details in itertools.product((False, True), repeat=3):
        selected = [name for name, enabled in zip(('file', 'line', 'column'), details) if enabled]
        flags = ['-Cpanic=abort', '-Zmir-opt-level=0', '-Zalways-encode-mir', '--cfg=miri',
            '-Zlocation-detail=' + (','.join(selected) or 'none')]
        flags += ['--cfg=redact_' + name for name, enabled in zip(('file', 'line', 'column'), details) if not enabled]
        label = 'detail_' + '_'.join(selected or ['none'])
        cases.append(Case('projection.rs', revision=label, edition='2024', flags=flags))
    cases.append(Case('projection.rs', revision='unicode_remap', edition='2024', flags=[
        '-Cpanic=abort', '-Zmir-opt-level=0', '-Zalways-encode-mir', '--cfg=miri',
        '--remap-path-prefix=' + str(ROOT) + '=/mapped/π']))
    records = []
    for case in cases:
        record = driver.run_case(case, settings, env, output)
        if record['status'] != 'passed':
            raise RuntimeError(f"{case.id}: {record['status']}; see {record['directory']}")
        directory = Path(record['directory'])
        pattern = rb'^caller-ids:([0-9a-f]{16}):([0-9a-f]{16})$'
        reference_events = re.findall(pattern, (directory / 'export.log').read_bytes(), re.MULTILINE)
        native_events = re.findall(pattern, (directory / 'lean.log').read_bytes(), re.MULTILINE)
        if len(reference_events) != 3 or native_events != reference_events:
            raise RuntimeError(f"{case.id}: absolute caller root/file event sequence differs: "
                               f"reference={reference_events!r}, native={native_events!r}")
        trace = json.loads((directory / 'input.json.miri-allocations.json').read_text())
        observed = [(int(root, 16), int(file, 16)) for root, file in reference_events]
        allocations = {row['source_alloc_id']: row for row in trace['allocations']}
        for root, file in observed:
            if root <= trace['snapshot_frontier'] or file > trace['snapshot_frontier']:
                raise RuntimeError('guest IDs do not denote a fresh root and existing ordinary filename')
            row = allocations[root]
            if len(row['relocations']) != 1 or row['relocations'][0]['target_source_alloc_id'] != file:
                raise RuntimeError('guest event is not bound to the independently observed CTFE allocation')
        record['absolute_id_events'] = observed
        print('PASS', case.id, 'absolute root/file IDs and event order match', observed, flush=True)
        command = ['lake', 'env', 'lean', '--run', 'tests/caller_location/AllocationOracle.lean',
            str(directory / 'input.json'), str(directory / 'input.json.miri-allocations.json')]
        with (directory / 'allocation-oracle.log').open('w') as log:
            subprocess.run(command, cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT, check=True)
        records.append(record)
        print('PASS', case.id, 'same profile/outcome; 3 allocation payload comparisons', flush=True)
    assert hashes == [driver.sha256(settings.exporter), driver.sha256(settings.runner)], 'binaries changed during comparisons'
    (output / 'summary.json').write_text(json.dumps({'cases': records, 'binary_sha256': hashes}, indent=2) + '\n')


if __name__ == '__main__':
    main()
