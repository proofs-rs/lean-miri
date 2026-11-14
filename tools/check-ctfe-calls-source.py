#!/usr/bin/env python3
"""Finite source-frame comparisons; no private-root/query admission claim."""
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
    fixture = (root / 'tests/repro/compiler-queries/ctfe-calls-source.rs').read_text()
    env = dict(os.environ, CTFE_CALLS_SOURCE=str(out / 'source.json'))
    for name, value, tiny, deny in [('zero', 0, 0, 1), ('one', 1, 0, 1),
            ('nine', 9, 0, 1), ('forty', 40, 0, 1), ('tiny-deny', 40, 1, 1),
            ('tiny-allow', 40, 1, 0), ('overflow', 2**32-1, 0, 1)]:
        source = out / 'calls.rs'
        source.write_text(fixture.replace('INPUT:u32=9', 'INPUT:u32='+str(value))
                          .replace('pub const ROOT:u32=arithmetic(INPUT);',
                                   'pub const ROOT:u32=arithmetic(1);'))
        command = [str(options.oracle.resolve()), str(source), '--sysroot',
                   str(options.sysroot.resolve()), '--crate-name', 'ctfe_callcase',
                   '--crate-type', 'lib', '--edition=2024', '-Cpanic=abort', '-Zmir-opt-level=0']
        if tiny:
            command += ['-Ztiny-const-eval-limit']
        if not deny:
            command += ['-A', 'long_running_const_eval']
        actual = subprocess.run(command, cwd=root, env=env, text=True, capture_output=True)
        (out / (name+'-rust.log')).write_text(actual.stdout)
        (out / (name+'-rust.stderr')).write_text(actual.stderr)
        assert actual.returncode == (101 if name == 'tiny-deny' else 0), actual.stderr
        reduced = subprocess.run([options.lean, '--run', 'tests/compiler_queries/CtfeCallsSource.lean',
            env['CTFE_CALLS_SOURCE'], 'root_call', str(tiny), str(deny)], cwd=root,
            env=env, text=True, capture_output=True)
        (out / (name+'-lean.log')).write_text(reduced.stdout+reduced.stderr)
        assert reduced.returncode == 0, reduced.stdout+reduced.stderr
        before = [line for line in actual.stdout.splitlines() if line.startswith(('step\t', 'result\t', 'error\t'))]
        after = reduced.stdout.splitlines()
        assert before[:-1] == after[:-1], (name, 'complete active-frame PC/counter trace mismatch')
        expected, observed = before[-1].split('\t'), after[-1].split('\t')
        assert expected[:3] == observed[:3], (name, expected, observed)
        if expected[0] == 'result':
            assert int(expected[3], 16) == int(observed[3]), (name, expected, observed)
        elif name == 'tiny-deny':
            assert 'AlreadyReported' in expected[3] and observed[3] == 'long_running_const_eval'
        else:
            assert 'Overflow' in expected[3] and observed[3] == 'assertion failed'
        if name == 'tiny-allow':
            assert actual.stderr.count('warning: constant evaluation is taking a long time') == 1
        print(f'PASS {name}: complete production-wire PC trace, {expected[1]} steps/{expected[2]} counters', flush=True)
    data = json.loads((out / 'source.json').read_text())
    assert {source['policy'] for source in data['sources']} == {'scalar_u32', 'scalar_u32_calls_v1'}


if __name__ == '__main__':
    main()
