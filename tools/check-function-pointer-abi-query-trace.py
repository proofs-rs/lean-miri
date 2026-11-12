#!/usr/bin/env python3
"""Audit explicit direct/catalog FnPtr calls; helper signatures are separate."""
import argparse
from collections import Counter
from pathlib import Path
import re

parser = argparse.ArgumentParser()
parser.add_argument('oracle')
parser.add_argument('candidate')
parser.add_argument('--keys', type=int, default=18)
parser.add_argument('--helpers', action='store_true', help='audit dummy-binder helper routes')
args = parser.parse_args()
pattern = re.compile(r'^lean_miri_fn_pointer_abi_call route=(\S+) queried=(true|false) signature=(.*) extra=(.*)$')

def load(path):
    rows = []
    for line in Path(path).read_text().splitlines():
        if not line.startswith('lean_miri_fn_pointer_abi_call '):
            continue
        match = pattern.fullmatch(line)
        if not match:
            raise SystemExit('malformed FnPtr ABI instrumentation: ' + line)
        if not match[1].startswith(('helper-',) if args.helpers else ('direct-', 'catalog-')):
            continue
        rows.append((match[1], match[2] == 'true', (match[3], match[4])))
    if not rows:
        raise SystemExit('missing FnPtr ABI instrumentation')
    return rows

oracle, candidate = load(args.oracle), load(args.candidate)
keys = {key for _, queried, key in oracle if queried}
if len(keys) != args.keys:
    raise SystemExit(f'expected {args.keys} independent FnPtr ABI oracle keys, got {len(keys)}')
for key in sorted(keys):
    old = sum(queried and actual == key for _, queried, actual in oracle)
    new = sum(queried and actual == key for _, queried, actual in candidate)
    raw = sum(not queried and actual == key for _, queried, actual in candidate)
    if not old or new or not raw:
        raise SystemExit(f'FnPtr query elimination failed: before={old}, after={new}, raw={raw}: {key}')
    print(f'PASS FnPtr direct/catalog explicit calls {old}->0, raw requests {raw}: {key}')
for label, rows in [('oracle',oracle),('candidate',candidate)]:
    print(label,dict(Counter((route,queried) for route,queried,_ in rows)))
print('Scope: explicit helper dummy-signature calls' if args.helpers else
      'Scope: explicit direct/catalog FnPtr calls; helper routes are audited separately')
