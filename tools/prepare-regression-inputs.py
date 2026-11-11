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
    ('u32', 'source133-root-u32-001', 'c8630afdb41f769593af2d739de929ac8c92c4a9ef410a7d56afa29ee5b9b211'),
    ('control-flow', 'source133-root-control-flow-001', 'de7e4137e2473c11a7206daca0132cbc92b8cbddc5d55999fcdb74fde8f25c6c')]:
    raw = gzip.decompress((ROOT / 'tests/eval_core/fixtures' / f'{source}.json.gz').read_bytes())
    if hashlib.sha256(raw).hexdigest() != expected:
        raise SystemExit(f'{source}: pinned unit input hash mismatch')
    path = OUT / f'{name}.json'
    path.write_bytes(raw)
    subprocess.run([sys.executable, str(ROOT / 'tests/eval_core/copy_fixture.py'),
                    str(path), str(OUT / f'{name}.checked.json')], check=True)
