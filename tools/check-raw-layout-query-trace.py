#!/usr/bin/env python3
"""Scoped explicit-call control; does not count rustc-internal query execution."""
import argparse
from collections import Counter
from pathlib import Path
import re
p=argparse.ArgumentParser();p.add_argument('before');p.add_argument('after');a=p.parse_args()
pattern=re.compile(r'^lean_miri_layout_call route=(\S+) queried=(true|false) type=(.*)$')
def load(path):
 rows=[]
 for line in Path(path).read_text().splitlines():
  if line.startswith('lean_miri_layout_call '):
   m=pattern.fullmatch(line)
   if not m: raise SystemExit('malformed instrumentation line: '+line)
   rows.append((m[1],m[2]=='true',m[3]))
 if not rows: raise SystemExit('missing exporter call instrumentation')
 return rows
before=load(a.before);after=load(a.after)
# These constructors have no projection-parent catalog route. Their explicit
# canonical acquisition calls must disappear, rather than merely shrink JSON.
for ty in ['u8','bool','(u8, bool)','[u8; 3_usize]']:
 old=sum(route=='canonical-residual' and queried and t==ty for route,queried,t in before)
 new=sum(route=='canonical-residual' and queried and t==ty for route,queried,t in after)
 skipped=sum(route=='canonical' and not queried and t==ty for route,queried,t in after)
 if old==0 or new!=0 or skipped==0:
  raise SystemExit(f'{ty}: insufficient elimination evidence before={old}, after={new}, raw={skipped}')
 print(f'PASS canonical {ty}: explicit acquisition calls {old}->0; raw requests {skipped}')
if not any(route=='canonical-residual' and queried and 'Residual' in ty for route,queried,ty in after):
 raise SystemExit('missing explicit unsupported-enum residual query control')
print('PASS unsupported enum remains an explicit queried residual')
for label,rows in [('before',before),('after',after)]:
 print(label,dict(Counter((route,queried) for route,queried,_ in rows)))
