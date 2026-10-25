#!/usr/bin/env python3
"""Derive schema3 unit inputs from the pinned schema2 eval_core fixtures."""
import gzip
import hashlib
from pathlib import Path
import subprocess
import sys
ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'scratch/regression-inputs'
OUT.mkdir(parents=True, exist_ok=True)
for name, source, expected in [
    ('u32', 'source133-root-u32-001', 'd6d35a344b68ba036f1d3d0d090294b67b3fa54e211473b7c35a47dbb8857f84'),
    ('control-flow', 'source133-root-control-flow-001', 'ebddbb887fd8f4256b16eab0921071433f0bd7e7d869fc94becdfd463a788660')]:
    raw = gzip.decompress((ROOT / 'tests/eval_core/fixtures' / f'{source}.json.gz').read_bytes())
    if hashlib.sha256(raw).hexdigest() != expected:
        raise SystemExit(f'{source}: pinned unit input hash mismatch')
    path = OUT / f'{name}.json'
    path.write_bytes(raw)
    subprocess.run([sys.executable, str(ROOT / 'tests/eval_core/prepare_schema3_fixture.py'),
                    str(path), str(OUT / f'{name}.schema3.json')], check=True)
