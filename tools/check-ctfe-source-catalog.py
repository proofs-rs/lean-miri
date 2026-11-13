#!/usr/bin/env python3
"""Capture a real raw CTFE dependency closure without claiming root evaluation."""
import argparse
import json
import os
from pathlib import Path
import subprocess


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--exporter', type=Path, required=True)
    parser.add_argument('--sysroot', type=Path, required=True)
    parser.add_argument('--out', type=Path, required=True)
    parser.add_argument('--lean', default='lean')
    args = parser.parse_args()
    root = Path(__file__).resolve().parents[1]
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=True)
    document = out / 'closure.json'
    exported = subprocess.run([str(args.exporter.resolve()), '--output', str(document),
        '--root', 'ROOT', '--', str(root / 'tests/repro/compiler-queries/ctfe-source-closure.rs'),
        '--sysroot', str(args.sysroot.resolve()), '--crate-type', 'lib', '--edition=2024',
        '-Cpanic=abort', '-Zmir-opt-level=0'], cwd=root, text=True, capture_output=True,
        env=dict(os.environ, LEAN_MIRI_TRACE_CTFE_SOURCE='1'))
    (out / 'export.stdout').write_text(exported.stdout)
    (out / 'export.stderr').write_text(exported.stderr)
    assert exported.returncode == 0, exported.stderr
    raw = json.loads(document.read_text())
    sources = raw['ctfe_scalar_sources']
    assert len(sources) >= 2
    assert all(source['source_role'] == 'ctfe' for source in sources)
    assert any(source['policy'] == 'scalar_u32_calls_v1' for source in sources)
    assert all(source['policy'] in ('scalar_u32', 'scalar_u32_calls_v1') for source in sources)
    candidates = [source for source in sources if source['arg_count'] == 1]
    assert len(candidates) == 1, candidates
    source_path = out / 'arithmetic.json'
    source_path.write_text(json.dumps(candidates[0]))
    for test, arguments in [
        ('CtfeSourceCatalogue', [str(document)]),
        ('CtfeScalarFrame', [str(source_path), '9', '0', '1', str(len(raw['spans']))]),
    ]:
        checked = subprocess.run([args.lean, '--run', str(root / 'tests/compiler_queries' / (test+'.lean')),
            *arguments], cwd=root, text=True, capture_output=True)
        (out / (test+'.log')).write_text(checked.stdout+checked.stderr)
        assert checked.returncode == 0, (test, checked.stdout, checked.stderr)
        if test == 'CtfeScalarFrame':
            assert checked.stdout.splitlines()[-1] == 'result\t189\t9\t45'
    print('PASS actual source closure and strict catalogue; captured arithmetic 189 steps/9 counters/45')
    print('ROOT raw Call/cleanup source is retained; compiler root allocation/interner/query admission remains unavailable')


if __name__ == '__main__':
    main()
