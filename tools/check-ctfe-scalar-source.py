#!/usr/bin/env python3
"""Compare a bounded source-frame leaf with real CompileTimeMachine steps.

This does not validate root allocations, interning or whole raw query admission.
The oracle uses the public inspection-context factory; see the tool's notes.
"""
import argparse
import copy
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
    source = out / 'source.json'
    fixture = root / 'tests/repro/compiler-queries/ctfe-scalar-source.rs'
    command = [str(options.oracle.resolve()), str(fixture), '--sysroot', str(options.sysroot),
               '--crate-name', 'ctfe_scalar_frame_probe', '--crate-type', 'lib',
               '--edition=2024', '-Cpanic=abort', '-Zmir-opt-level=0']
    capture = subprocess.run(command, cwd=root, env=dict(os.environ,
        LEAN_MIRI_CTFE_SCALAR_SOURCE=str(source)), text=True, capture_output=True)
    (out / 'source-capture.stdout').write_text(capture.stdout)
    (out / 'source-capture.stderr').write_text(capture.stderr)
    assert capture.returncode == 0, capture.stderr
    span_count = source.with_suffix('.span_count').read_text()
    reader = root / 'tests/compiler_queries/CtfeScalarFrame.lean'
    for name, value, tiny, deny in [
        ('zero', 0, 0, 1), ('one', 1, 0, 1), ('nine', 9, 0, 1),
        ('forty', 40, 0, 1), ('tiny-deny', 40, 1, 1),
        ('tiny-allow', 40, 1, 0), ('overflow', 2**32-1, 0, 1),
    ]:
        arguments = command + (['-Ztiny-const-eval-limit'] if tiny else [])
        if not deny:
            arguments += ['-A', 'long_running_const_eval']
        actual = subprocess.run(arguments, cwd=root, env=dict(os.environ,
            LEAN_MIRI_CTFE_SCALAR_INPUT=str(value)), text=True, capture_output=True)
        assert actual.returncode == (101 if name == 'tiny-deny' else 0), (name, actual.stderr)
        reduced = subprocess.run([options.lean, '--run', str(reader), str(source),
            str(value), str(tiny), str(deny), span_count], cwd=root,
            text=True, capture_output=True)
        assert reduced.returncode == 0, (name, reduced.stdout, reduced.stderr)
        (out / (name+'-rust.tsv')).write_text(actual.stdout)
        (out / (name+'-rust.stderr')).write_text(actual.stderr)
        (out / (name+'-lean.tsv')).write_text(reduced.stdout)
        before, after = actual.stdout.splitlines(), reduced.stdout.splitlines()
        assert before[:-1] == after[:-1], (name, 'source PC/counter-marker trace differs')
        expected, observed = before[-1].split('\t'), after[-1].split('\t')
        assert expected[:3] == observed[:3], (name, expected, observed)
        if expected[0] == 'result':
            assert int(expected[3], 16) == int(observed[3]), (name, expected, observed)
        elif name == 'tiny-deny':
            assert 'AlreadyReported' in expected[3] and observed[3] == 'long_running_const_eval'
        elif name == 'overflow':
            assert 'Overflow' in expected[3] and observed[3] == 'assertion failed'
        else:
            raise AssertionError((name, expected, observed))
        if name == 'tiny-allow':
            assert actual.stderr.count('warning: constant evaluation is taking a long time') == 1
        print(f'PASS {name}: complete PC trace, {expected[1]} steps/{expected[2]} counters, {expected[0]}')
    original = json.loads(source.read_text())
    def first_literal(value):
        if isinstance(value, dict):
            if value.get('kind') == 'source_value':
                return value
            for child in value.values():
                if (found := first_literal(child)) is not None:
                    return found
        elif isinstance(value, list):
            for child in value:
                if (found := first_literal(child)) is not None:
                    return found
        return None
    mutations = {}
    for name, field, value in [
        ('unknown-policy', 'policy', 'unknown_future_policy'),
        ('runtime-role', 'source_role', 'runtime'),
        ('runtime-phase', 'phase', 'runtime_optimized'),
    ]:
        changed = copy.deepcopy(original)
        changed[field] = value
        mutations[name] = changed
    changed = copy.deepcopy(original)
    del changed['source_role']
    mutations['missing-role'] = changed
    changed = copy.deepcopy(original)
    changed['environment_recipe']['mode'] = 'codegen'
    mutations['caller-env-as-source-scope'] = changed
    changed = copy.deepcopy(original)
    changed['environment_recipe']['owner']['index'] += 1
    mutations['wrong-environment-owner'] = changed
    changed = copy.deepcopy(original)
    changed['locals'][0]['source']['span'] = int(span_count)
    mutations['missing-span'] = changed
    changed = copy.deepcopy(original)
    literal = first_literal(changed)
    assert literal is not None
    literal['source_class'] = 'evaluated_answer'
    mutations['evaluated-answer-class'] = changed
    changed = copy.deepcopy(original)
    changed['required_consts'] = [copy.deepcopy(first_literal(original))]
    mutations['unevaluated-required-preamble'] = changed
    changed = copy.deepcopy(original)
    changed['blocks'][0]['cleanup'] = True
    mutations['unknown-cleanup-policy'] = changed
    for name, changed in mutations.items():
        path = out / (name+'.json')
        path.write_text(json.dumps(changed))
        negative = subprocess.run([options.lean, '--run', str(reader), str(path),
            '9', '0', '1', span_count], cwd=root, text=True, capture_output=True)
        (out / (name+'.log')).write_text(negative.stdout+negative.stderr)
        assert negative.returncode != 0, (name, 'malformed source was accepted')
        assert 'error:' not in negative.stdout, (name, 'reader compilation failed')
    print('PASS ten source role/policy/recipe/reference/value-class/preamble controls reject')


if __name__ == '__main__':
    main()
