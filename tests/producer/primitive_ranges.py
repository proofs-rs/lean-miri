#!/usr/bin/env python3
"""Check Lean decoder boundaries against the exporter's primitive-range fixture."""
from pathlib import Path
import os
import subprocess
import tempfile

ROOT=Path(__file__).resolve().parents[2]
env={**os.environ, 'ELAN_HOME':os.environ.get('ELAN_HOME', str(ROOT/'.elan'))}
with tempfile.TemporaryDirectory(prefix='lean-miri-primitive-ranges-') as tmp:
    output=Path(tmp)/'actual.json'
    subprocess.run(['bash', str(ROOT/'exporter/tests/run-producer.sh'),
                    'primitive_ranges', str(output)], cwd=ROOT, env=env, check=True)
    subprocess.run([str(Path(env['ELAN_HOME'])/'bin/lake'), 'env', 'lean', '--run',
                    'tests/producer/PrimitiveRanges.lean', str(output)],
                   cwd=ROOT, env=env, check=True)
