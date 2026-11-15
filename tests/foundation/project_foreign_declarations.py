#!/usr/bin/env python3
"""Comparison-only projection; never imported as foundation source material."""
import json
from pathlib import Path
import runpy
import sys

reference = json.load(open(sys.argv[1]))
assert (reference['schema'], reference['schema_version']) == ('lean-miri-rustc-mir', 12)
helper = runpy.run_path(str(Path(__file__).parents[1] / 'exporter/test_foundation_foreign_source.py'))
projected = {
    'schema': reference['schema'], 'schema_version': reference['schema_version'],
    'rustc_commit': reference['producer']['rustc_commit'],
    'candidates': helper['reference_candidates'](reference),
}
with open(sys.argv[2], 'w') as output:
    json.dump(projected, output, separators=(',', ':'))
