#!/usr/bin/env python3
"""Fresh compiler export/reference for one canonical Rust fixture (not a replay)."""
import argparse
import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tests/connected'))
from cases import CASES, ORDERING_EXPORTS


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('case', choices=[c[0] for c in CASES] + [c[0] for c in ORDERING_EXPORTS])
    parser.add_argument('output', type=Path, help='new JSON path under scratch/')
    parser.add_argument('--libc', type=Path, help='libc rlib built with the pinned Miri sysroot')
    parser.add_argument('--exporter', type=Path, help='reference-only exporter copy; required for fence-acqrel profile')
    args = parser.parse_args()
    output = args.output.resolve()
    if not output.is_relative_to(ROOT / 'scratch') or output.exists():
        parser.error('output must be a new file under scratch/')
    output.parent.mkdir(parents=True, exist_ok=True)
    rustup = Path(os.environ.get('RUSTUP_HOME', ROOT / '.rustup'))
    toolchain = rustup / 'toolchains/miri-exporter-8144389c895d'
    sysroot = Path(os.environ.get('MIRI_SYSROOT', ROOT / 'scratch/miri-sysroot'))
    exporter = args.exporter.resolve() if args.exporter else ROOT / 'exporter/target/debug/lean-miri-mir-exporter'
    env = os.environ.copy()
    env['PATH'] = f"{toolchain / 'bin'}:{env.get('PATH', '')}"
    env['LD_LIBRARY_PATH'] = str(toolchain / 'lib') + ':' + env.get('LD_LIBRARY_PATH', '')
    env['MIRI_SYSROOT'] = str(sysroot)
    if args.case in {c[0] for c in ORDERING_EXPORTS}:
        _, source_args, source_roots = next(c for c in ORDERING_EXPORTS if c[0] == args.case)
    else:
        c = next(c for c in CASES if c[0] == args.case)
        source_args, source_roots = c[5], c[6]
    compiler_args = []
    for value in source_args:
        if value == '${SOURCE}':
            compiler_args.append(str(ROOT / 'tests/connected/fixtures' / f'{args.case}.rs'))
        elif value == '${SYSROOT}':
            compiler_args.append(str(sysroot))
        elif value == 'dependency=${LIBC_DIR}':
            if not args.libc or not args.libc.is_file():
                parser.error('this case requires --libc')
            compiler_args.append('dependency=' + str(args.libc.resolve().parent))
        elif value.startswith('libc='):
            if not args.libc or not args.libc.is_file():
                parser.error('this case requires --libc (build instructions: tests/connected/README.md)')
            compiler_args.append('libc=' + str(args.libc.resolve()))
        else:
            compiler_args.append(value)
    env['LEAN_MIRI_PREPARED_ALLOC_ID_WORLD'] = '1'
    env['LEAN_MIRI_RUN_PREPARED_MIRI'] = '1'
    env.pop('LEAN_MIRI_REFERENCE_ARGS_JSON', None)
    if args.case == 'fence-acqrel':
        if not args.exporter:
            parser.error('fence-acqrel requires --exporter from tools/build-reference-profile.sh')
        env['LEAN_MIRI_REFERENCE_SEED'] = '2'
        env['LEAN_MIRI_REFERENCE_PREEMPTION_RATE'] = '0'
    cmd = [str(exporter), '--output', str(output)]
    for root in source_roots:
        cmd += ['--root', root]
    cmd += ['--', *compiler_args]
    with output.with_suffix('.export.log').open('x') as log:
        result = subprocess.run(cmd, cwd=ROOT, env=env, stdout=log, stderr=subprocess.STDOUT)
    # Negative fixtures intentionally produce a Miri evaluation error sidecar.
    # Preserve its status and exit; only the fixture's explicit UB oracle can accept it.
    print(f'exporter exit={result.returncode}; inspect {output.with_suffix(".export.log")} and reference sidecar')
    return result.returncode


if __name__ == '__main__':
    raise SystemExit(main())
