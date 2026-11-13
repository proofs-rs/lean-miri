#!/usr/bin/env python3
"""Run the pinned source-field controls against caller-supplied artifacts.

Requires a coherent completed Lake build. The full-std tests intentionally check
v26 physical identities; the named-field input is the transparent1 candidate.
These finite controls do not establish a live-runtime CTFE provider or UB freedom.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', required=True, type=Path, help='canonical source3 full-std document')
    parser.add_argument('--oracle', required=True, type=Path, help='independent Sized/pointer JSON')
    parser.add_argument('--named-input', required=True, type=Path, help='transparent1 candidate document')
    parser.add_argument('--log-dir', required=True, type=Path)
    parser.add_argument('--build-oracle', action='store_true')
    parser.add_argument('--rustc', default='rustc', help='pinned base compiler, used only with --build-oracle')
    parser.add_argument('--rustc-cwd', type=Path, help='actual original rustc invocation directory')
    args = parser.parse_args()
    args.input = args.input.resolve()
    args.oracle = args.oracle.resolve()
    args.named_input = args.named_input.resolve()
    args.log_dir.mkdir(parents=True, exist_ok=True)
    env = os.environ.copy()
    env['LEAN_NUM_THREADS'] = '1'
    record = {'scope': 'finite pinned source-field controls', 'runs': []}

    def run(command, name, cwd=ROOT, run_env=env):
        log = args.log_dir / (name + '.log')
        started = time.monotonic()
        with log.open('w') as output:
            result = subprocess.run(command, cwd=cwd, env=run_env, stdout=output, stderr=subprocess.STDOUT)
        record['runs'].append({'argv': list(map(str, command)), 'cwd': str(cwd),
                              'exit': result.returncode, 'seconds': time.monotonic() - started,
                              'log': str(log), 'log_sha256': digest(log)})
        (args.log_dir / 'manifest.json').write_text(json.dumps(record, indent=2) + '\n')
        if result.returncode:
            raise SystemExit(f'{name} failed ({result.returncode}); see {log}')

    if args.build_oracle:
        if args.rustc_cwd is None:
            parser.error('--build-oracle requires the actual --rustc-cwd; it is not inferred')
        invocation = json.loads(args.input.read_text())['invocation']['rustc_args']
        build_env = dict(env, RUSTC_BOOTSTRAP='1')
        with tempfile.TemporaryDirectory(prefix='miri-source-pointer-') as directory:
            binary = Path(directory) / 'oracle'
            source = ROOT / 'tools/source-pointer-sized-oracle.rs'
            run([args.rustc, '--edition=2024', '-Cprefer-dynamic', str(source), '-o', str(binary)],
                'oracle-build', run_env=build_env)
            record['oracle_source_sha256'] = digest(source)
            record['oracle_binary_sha256'] = digest(binary)
            log = args.log_dir / 'oracle-run.log'
            args.oracle.parent.mkdir(parents=True, exist_ok=True)
            with args.oracle.open('w') as output, log.open('w') as error:
                result = subprocess.run([str(binary), *invocation], cwd=args.rustc_cwd,
                                        env=build_env, stdout=output, stderr=error)
            record['oracle_invocation'] = {'rustc_args': invocation, 'cwd': str(args.rustc_cwd),
                                          'exit': result.returncode, 'stderr': str(log)}
            (args.log_dir / 'manifest.json').write_text(json.dumps(record, indent=2) + '\n')
            if result.returncode:
                raise SystemExit(f'oracle run failed ({result.returncode}); see {log}')
    json.loads(args.oracle.read_text())  # A failed/truncated oracle is never a positive result.
    cases = [
        ('field-failure', 'TypeConstantFieldFailure.lean', [args.input]),
        ('pointer-order', 'SourcePointerFieldOrder.lean', [args.input, args.oracle]),
        ('named-field', 'NamedFieldWorld.lean', [args.named_input]),
    ]
    paths = {args.input, args.oracle, args.named_input}
    paths.update(ROOT / 'tests/compiler_queries' / source for _, source, _ in cases)
    for module in ['RuntimeMetadata', 'RuntimeEffectfulLayout', 'WorldTypeMetadata',
                   'CompilerNamedFields', 'CompilerWorldCompatibility', 'EvalProjectionMachine']:
        paths.add(ROOT / 'Miri/Input' / (module + '.lean'))
        paths.add(ROOT / '.lake/build/lib/lean/Miri/Input' / (module + '.olean'))
    record['before'] = {str(path): digest(path) for path in sorted(paths)}
    for name, source, inputs in cases:
        run(['lake', 'env', 'lean', '--run', str(ROOT / 'tests/compiler_queries' / source),
             *map(str, inputs)], name)
    record['after'] = {str(path): digest(path) for path in sorted(paths)}
    record['unchanged'] = record['before'] == record['after']
    (args.log_dir / 'manifest.json').write_text(json.dumps(record, indent=2) + '\n')
    if not record['unchanged']:
        raise SystemExit('source/input/core artifact changed during controls')
    print('source field controls PASS (three finite controls; artifacts unchanged)')


if __name__ == '__main__':
    main()
