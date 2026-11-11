#!/usr/bin/env python3
"""Fresh concrete generic/DST export and native execution regression."""
import argparse
import json
import os
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[3]


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--exporter', required=True, type=Path)
    parser.add_argument('--runner', required=True, type=Path)
    args = parser.parse_args()
    toolchain = Path(os.environ.get('RUSTUP_HOME', ROOT / '.rustup')) / 'toolchains/miri-exporter-8144389c895d'
    sysroot = Path(os.environ.get('MIRI_SYSROOT', ROOT / 'scratch/miri-sysroot'))
    env = os.environ.copy()
    env.update(PATH=str(toolchain / 'bin') + ':' + env.get('PATH', ''),
               LD_LIBRARY_PATH=str(toolchain / 'lib'), LEAN_MIRI_PREPARED_ALLOC_ID_WORLD='1',
               LEAN_MIRI_RUN_PREPARED_MIRI='0', LEAN_NUM_THREADS='1')
    with tempfile.TemporaryDirectory(prefix='resolved-generic-') as tmp:
        snapshot = Path(tmp) / 'input.json'
        subprocess.run([str(args.exporter.resolve()), '--output', str(snapshot), '--root', 'main', '--',
                        str(Path(__file__).with_name('resolved_generic.rs')), '--crate-type=bin',
                        '--crate-name=resolved_generic', '--edition=2024', '-Cpanic=abort', '-Zmir-opt-level=0',
                        '--sysroot', str(sysroot), '--cfg=miri', '-Zalways-encode-mir', '-Zextra-const-ub-checks',
                        '-Zmir-preserve-ub', '-Zmir-enable-passes=-CheckAlignment,-CheckNull,-CheckEnums',
                        '-Zmir-enable-passes=-ReferencePropagation,-GVN', '-Zdeduplicate-diagnostics=no'],
                       cwd=ROOT, env=env, check=True)
        document = json.loads(snapshot.read_text())
        owners = {}
        def record(body_id, owner):
            if owner in owners and owners[owner] != body_id:
                raise SystemExit('duplicate concrete instance/promoted body')
            owners[owner] = body_id
        for root in document['body_roots']:
            record(root['body'], (root['entry_instance'], None))
            for promoted in root['promoted_bodies']:
                record(promoted['body'], (root['entry_instance'], promoted['promoted_index']))
        for instance in document['instances']:
            if instance['kind'] == 'instance_mir':
                record(instance['body'], (instance['instance_id'], None))
                for promoted in instance['promoted_bodies']:
                    record(promoted['body'], (instance['instance_id'], promoted['promoted_index']))
        if set(owners.values()) != set(range(len(document['bodies']))):
            raise SystemExit('body pool contains an unowned concrete body')
        if any('constant_query_context' in body for body in document['bodies']):
            raise SystemExit('obsolete body normalization context')
        result = subprocess.run([str(args.runner.resolve()), str(snapshot)], cwd=ROOT, env=env,
                                text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, timeout=120)
        print(result.stdout, end='')
        if result.returncode or 'run: finalized_exit code=0;' not in result.stdout:
            raise SystemExit('concrete generic/DST guest did not exit zero')
    print('resolved_generic_native=PASS')


if __name__ == '__main__':
    main()
