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
    ('u32', 'source133-root-u32-001', 'e9901b4240b3319b013996de4c20116eae1e134d1f6b93c02e9a75119be799a5'),
    ('control-flow', 'source133-root-control-flow-001', 'd715e9c95aacf889d57a74b52f3562887c3567a909aa93f2e6963e128245ab09')]:
    raw = gzip.decompress((ROOT / 'tests/eval_core/fixtures' / f'{source}.json.gz').read_bytes())
    if hashlib.sha256(raw).hexdigest() != expected:
        raise SystemExit(f'{source}: pinned unit input hash mismatch')
    path = OUT / f'{name}.json'
    path.write_bytes(raw)
    subprocess.run([sys.executable, str(ROOT / 'tests/eval_core/copy_fixture.py'),
                    str(path), str(OUT / f'{name}.checked.json')], check=True)
