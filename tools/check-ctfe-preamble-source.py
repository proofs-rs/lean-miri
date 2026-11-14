#!/usr/bin/env python3
"""Compare ordered generic entry; source candidates never admit compiler queries."""
import argparse
import json
import os
from pathlib import Path
import subprocess


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--oracle', type=Path, required=True)
    parser.add_argument('--sysroot', type=Path, required=True)
    parser.add_argument('--lean', default='lean')
    options = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    out = options.out.resolve()
    out.mkdir(parents=True, exist_ok=True)
    source = out / 'preamble.json'
    for name in ['Good', 'Bad']:
        env = dict(os.environ, CTFE_PREAMBLE_SOURCE=str(source), CTFE_PREAMBLE_TYPE=name)
        actual = subprocess.run([str(options.oracle.resolve()),
            str(root / 'tests/repro/compiler-queries/ctfe-preamble-source.rs'), '--sysroot',
            str(options.sysroot.resolve()), '--crate-name', 'ctfe_preamblecase', '--crate-type',
            'lib', '--edition=2024', '-Cpanic=abort', '-Zmir-opt-level=0'],
            cwd=root, env=env, text=True, capture_output=True)
        (out / (name+'-rust.log')).write_text(actual.stdout)
        (out / (name+'-rust.stderr')).write_text(actual.stderr)
        assert actual.returncode == (0 if name == 'Good' else 101), actual.stderr
        reduced = subprocess.run([options.lean, '--run',
            'tests/compiler_queries/CtfePreambleSource.lean', str(source), name],
            cwd=root, env=env, text=True, capture_output=True)
        (out / (name+'-lean.log')).write_text(reduced.stdout+reduced.stderr)
        assert reduced.returncode == 0, reduced.stdout+reduced.stderr
        if name == 'Good':
            before = [line for line in actual.stdout.splitlines() if line.startswith(('step\t', 'result\t'))]
            after = reduced.stdout.splitlines()[1:]
            assert before[:-1] == after[:-1]
            expected, observed = before[-1].split('\t'), after[-1].split('\t')
            assert expected[:3] == observed[:3] and int(expected[3], 16) == int(observed[3]) == 16
            assert reduced.stdout.startswith('preamble\tok\t2\n')
        else:
            assert 'preamble\terror\tRight(' in actual.stdout and 'AlreadyReported' in actual.stdout
            assert not any(line.startswith('step\t') for line in actual.stdout.splitlines())
            assert reduced.stdout == 'preamble\terror\tpending\t1\n'
        data = json.loads(source.read_text())
        assert all(value['user_type_annotations'] == [] for value in data['sources'])
        assert any('"user_type": 0' in json.dumps(value) for value in data['sources'])
        if name == 'Good':
            malformed = json.loads(source.read_text())
            owner = next(value for value in malformed['sources'] if value['required_consts'])
            assert owner['required_consts'][0]['arguments'][0]['kind'] == 'type_parameter'
            owner['required_consts'][0]['arguments'] = []
            bad_path = out / 'malformed-argument.json'
            bad_path.write_text(json.dumps(malformed))
            rejected = subprocess.run([options.lean, '--run',
                'tests/compiler_queries/CtfePreambleSource.lean', str(bad_path), name],
                cwd=root, env=env, text=True, capture_output=True)
            assert rejected.returncode != 0 and 'exactly one type-parameter argument' in rejected.stdout+rejected.stderr
        print(f'PASS {name}: production wire ordered required constants and pending/PC behavior', flush=True)


if __name__ == '__main__':
    main()
