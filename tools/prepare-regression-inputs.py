#!/usr/bin/env python3
"""Prepare current-wire unit inputs from the pinned eval_core fixtures."""
import gzip
import hashlib
from pathlib import Path
import subprocess
import sys
ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'scratch/regression-inputs'
OUT.mkdir(parents=True, exist_ok=True)
for name, source, expected in [
    ('u32', 'source133-root-u32-001', 'd94a5daaf0ec5c780113a5a74fc751fca6da4d4510fd24f6765f135ae663529a'),
    ('control-flow', 'source133-root-control-flow-001', 'f1590691685cabe1b0d6251f04e80aa1dc89d4ee18cf66b16525c85ee4c2d489')]:
    raw = gzip.decompress((ROOT / 'tests/eval_core/fixtures' / f'{source}.json.gz').read_bytes())
    if hashlib.sha256(raw).hexdigest() != expected:
        raise SystemExit(f'{source}: pinned unit input hash mismatch')
    path = OUT / f'{name}.json'
    path.write_bytes(raw)
    subprocess.run([sys.executable, str(ROOT / 'tests/eval_core/copy_fixture.py'),
                    str(path), str(OUT / f'{name}.checked.json')], check=True)
