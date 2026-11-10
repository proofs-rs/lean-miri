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
    ('u32', 'source133-root-u32-001', '04904a327c4a25a4421cc2c4e019308c1a338d81523a6f6104c368e1980ac07b'),
    ('control-flow', 'source133-root-control-flow-001', 'd9b1ad451c406213f7938a2eb57cdf850bfcadb67d3d240a32be1ae434e8c277')]:
    raw = gzip.decompress((ROOT / 'tests/eval_core/fixtures' / f'{source}.json.gz').read_bytes())
    if hashlib.sha256(raw).hexdigest() != expected:
        raise SystemExit(f'{source}: pinned unit input hash mismatch')
    path = OUT / f'{name}.json'
    path.write_bytes(raw)
    subprocess.run([sys.executable, str(ROOT / 'tests/eval_core/copy_fixture.py'),
                    str(path), str(OUT / f'{name}.checked.json')], check=True)
