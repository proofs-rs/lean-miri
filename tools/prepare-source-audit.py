#!/usr/bin/env python3
"""Regenerate audit inventories in scratch; keep only reviewed inputs in Git."""
from pathlib import Path
import json
import os
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'scratch/source-audit'


def main():
    OUT.mkdir(parents=True, exist_ok=True)
    # Existing audit tools accept a repository root. Sources stay read-only here;
    # generated inventories have their own directories and never enter Git.
    for name in ('Miri', 'Miri.lean', 'MiriTests', 'MiriTests.lean', 'tests', 'exporter',
                 'native', 'upstream', 'third_party'):
        dest = OUT / name
        if not dest.exists():
            dest.symlink_to(ROOT / name, target_is_directory=(ROOT / name).is_dir())
    # Keep the analyzer directory writable for generated inventory output.
    # Other tools remain linked to the reviewed repository inputs.
    tool_dir = OUT / 'tools'
    if tool_dir.is_symlink():
        tool_dir.unlink()
    tool_dir.mkdir(exist_ok=True)
    for source in (ROOT / 'tools').iterdir():
        if source.name == 'source-analysis':
            continue
        dest = tool_dir / source.name
        if not dest.exists():
            dest.symlink_to(source, target_is_directory=source.is_dir())
    analyzer = tool_dir / 'source-analysis'
    analyzer.mkdir(exist_ok=True)
    for name in ('Cargo.toml', 'Cargo.lock', 'src'):
        dest = analyzer / name
        if not dest.exists():
            dest.symlink_to(ROOT / 'tools/source-analysis' / name)
    tracking = OUT / 'tracking'
    tracking.mkdir(exist_ok=True)
    for name in ('features.json', 'exclusions.json'):
        shutil.copyfile(ROOT / 'tools/audit' / name, tracking / name)
    env = os.environ.copy()
    env.setdefault('CARGO_HOME', str(ROOT / '.cargo'))
    env.setdefault('RUSTUP_HOME', str(ROOT / '.rustup'))
    env['PATH'] = f"{env['CARGO_HOME']}/bin:{env.get('PATH', '')}"
    # Cargo output is also disposable. The analyzer and Cargo.lock are the inputs.
    env['CARGO_TARGET_DIR'] = str(ROOT / 'scratch/source-analysis-target')
    for args in (
        ['tools/coverage.py', 'sync'],
        ['tools/update_features.py', '--refresh-inventory', '--write'],
        ['tools/update_implementation_ledger.py'],
    ):
        subprocess.run([sys.executable, str(ROOT / args[0]), *args[1:], '--root', str(OUT)],
                       cwd=ROOT, env=env, check=True)
    print(f'Audit inventories: {OUT.relative_to(ROOT)} (generated; not semantic completion)')


if __name__ == '__main__':
    main()
