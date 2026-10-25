#!/usr/bin/env python3
"""Select one actual rlib from Cargo's compiler-artifact messages, fail closed."""
import argparse
import json
from pathlib import Path


def select_rlib(messages, crate):
    candidates = set()
    for line in messages.splitlines():
        if not line.strip():
            continue
        message = json.loads(line)
        if message.get('reason') != 'compiler-artifact':
            continue
        target = message.get('target', {})
        if target.get('name') != crate or 'lib' not in target.get('kind', []):
            continue
        for filename in message.get('filenames', []):
            path = Path(filename)
            if path.suffix == '.rlib':
                candidates.add(path.resolve())
    if len(candidates) != 1:
        raise ValueError(f'expected one Cargo rlib for {crate}, got {len(candidates)}: '
                         + ', '.join(str(p) for p in sorted(candidates)))
    path = next(iter(candidates))
    if not path.is_file():
        raise ValueError(f'Cargo rlib does not exist: {path}')
    return path


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('messages', type=Path)
    parser.add_argument('crate')
    parser.add_argument('record', type=Path)
    args = parser.parse_args()
    # Never leave a successful old record behind after a failed selection.
    args.record.unlink(missing_ok=True)
    path = select_rlib(args.messages.read_text(), args.crate)
    args.record.write_text(str(path) + '\n')
    print(f'Cargo {args.crate} rlib: {path}')


if __name__ == '__main__':
    main()
