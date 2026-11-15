#!/usr/bin/env python3
"""Run the normal exporter built by build-snapshot-exporter.py, without replacing tools."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import subprocess

root = Path(__file__).resolve().parents[1]
p = argparse.ArgumentParser(description=__doc__)
p.add_argument('--build-manifest', type=Path, default=root / 'scratch/snapshot-exporter-target/snapshot-build.json')
p.add_argument('arguments', nargs=argparse.REMAINDER)
a = p.parse_args()
manifest = json.loads(a.build_manifest.read_text())
expected_driver = manifest.get('driver_sha256')
if expected_driver is None:
    p.error('snapshot manifest lacks driver identity; rebuild the snapshot exporter')
try:
    with Path(manifest['driver']).open('rb') as driver:
        actual_driver = hashlib.file_digest(driver, 'sha256').hexdigest()
except FileNotFoundError:
    p.error('snapshot compiler driver is unavailable; finish its build and rebuild the exporter')
if actual_driver != expected_driver:
    p.error('snapshot compiler driver changed; rebuild the exporter against this exact driver')
env = os.environ.copy()
env.update(manifest['environment'])
env['MIRI_SYSROOT'] = manifest['target_sysroot']
env.pop('LEAN_MIRI_OBSERVE_CTFE_ROOT', None)
arguments = a.arguments[1:] if a.arguments[:1] == ['--'] else a.arguments
raise SystemExit(subprocess.run([manifest['binary'], *arguments], env=env).returncode)
