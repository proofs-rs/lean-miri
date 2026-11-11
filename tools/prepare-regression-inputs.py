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
    ('u32', 'source133-root-u32-001', '1ef4f7fc734799b89e984a42f93ae2357f88f50a57a495af6cd8076f42b777d6'),
    ('control-flow', 'source133-root-control-flow-001', '2b5c83a8c9ecfb7de63c61377cf78aa057a599846672521b8bc8ff04b423c175')]:
    raw = gzip.decompress((ROOT / 'tests/eval_core/fixtures' / f'{source}.json.gz').read_bytes())
    if hashlib.sha256(raw).hexdigest() != expected:
        raise SystemExit(f'{source}: pinned unit input hash mismatch')
    path = OUT / f'{name}.json'
    path.write_bytes(raw)
    subprocess.run([sys.executable, str(ROOT / 'tests/eval_core/copy_fixture.py'),
                    str(path), str(OUT / f'{name}.checked.json')], check=True)
