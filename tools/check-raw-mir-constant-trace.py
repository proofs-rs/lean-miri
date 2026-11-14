#!/usr/bin/env python3
"""Explicit source-call tracing only, not rustc's internal query execution."""
import re
import sys
from collections import Counter
from pathlib import Path

pattern=re.compile(r'^lean_miri_const_call route=(\S+) queried=(true|false) category=(\S+) value=(.*)$')
def load(path):
    rows=[]
    for line in Path(path).read_text().splitlines():
        if line.startswith('lean_miri_const_call '):
            match=pattern.fullmatch(line)
            if not match: raise SystemExit('malformed MIR constant trace')
            rows.append((match[1],match[2]=='true',match[3],match[4]))
    if not rows: raise SystemExit('missing MIR constant trace')
    return rows
before,after=map(load,sys.argv[1:])
queried=Counter(value for route,q,category,value in before if route=='mir_eval' and q and category=='ty')
raw=Counter(value for route,q,category,value in after if route=='raw_type' and not q and category=='ty')
remaining=Counter(value for route,q,category,value in after if q and category=='ty')
if len(raw)<5: raise SystemExit('fewer than five genuine Const::Ty values migrated')
for value,count in raw.items():
    if queried[value] != count or remaining[value]:
        raise SystemExit(f'incomplete Const::Ty evaluation removal: {value}')
    print(f'PASS Ty {value}: explicit Const::eval/ValTree route {count}->0')
if not any(q and category=='unevaluated' for _,q,category,_ in after):
    raise SystemExit('missing explicit Unevaluated CTFE residual control')
if not any(route=='literal' and not q and category=='val' for route,q,category,_ in after):
    raise SystemExit('missing raw literal identity control')
print('PASS Unevaluated remains explicit; raw Val literals do not call Const::eval')
