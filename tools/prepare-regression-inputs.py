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
    ('u32', 'source133-root-u32-001', 'c3cb5698f70066a22579f1a15501450f27b4b0880a6870c6a5a23c1d5d7a1246'),
    ('control-flow', 'source133-root-control-flow-001', 'f9cd1fd726d6aa8c071f3f36d4f05823be52cc1a6b8d19859b698b320de81ad2')]:
    raw = gzip.decompress((ROOT / 'tests/eval_core/fixtures' / f'{source}.json.gz').read_bytes())
    if hashlib.sha256(raw).hexdigest() != expected:
        raise SystemExit(f'{source}: pinned unit input hash mismatch')
    path = OUT / f'{name}.json'
    path.write_bytes(raw)
    subprocess.run([sys.executable, str(ROOT / 'tests/eval_core/prepare_schema3_fixture.py'),
                    str(path), str(OUT / f'{name}.schema3.json')], check=True)
