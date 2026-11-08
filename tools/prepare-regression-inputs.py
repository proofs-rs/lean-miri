#!/usr/bin/env python3
"""Prepare current-wire unit inputs from the pinned eval_core fixtures."""
import gzip
import hashlib
import json
from pathlib import Path
from mir_json import decode_mir_document
ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'scratch/regression-inputs'
OUT.mkdir(parents=True, exist_ok=True)
for name, source, expected in [
    ('u32', 'source133-root-u32-001', '810f5be842d888bfe0e3366d1711612ec3f8672952d3f8111ac3f58248eaa668'),
    ('control-flow', 'source133-root-control-flow-001', 'e1ae0ff7bab92679fd212e47114a670e09ce29352ef01acf15095d806c12b5de')]:
    raw = gzip.decompress((ROOT / 'tests/eval_core/fixtures' / f'{source}.json.gz').read_bytes())
    if hashlib.sha256(raw).hexdigest() != expected:
        raise SystemExit(f'{source}: pinned unit input hash mismatch')
    decode_mir_document(json.loads(raw))
    path = OUT / f'{name}.json'
    path.write_bytes(raw)
    (OUT / f'{name}.schema4.json').write_bytes(raw)
