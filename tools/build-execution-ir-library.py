#!/usr/bin/env python3
"""Link the checked native runner as the producer's in-process IR compiler.

Caller owns the primary Lake build lock. No input-specific artifact or shared
program cache is built here: this library contains only the fixed interpreter.
"""
import hashlib
import json
from pathlib import Path
import shlex
import subprocess

ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / '.elan/toolchains/leanprover--lean4---v4.35.0'
OUT = ROOT / '.lake/build/lib/libexecution_ir.so'
source = ROOT / 'native/execution_ir_bridge.c'
arguments = shlex.split((ROOT / '.lake/build/bin/native_runner.rsp').read_text())
objects = [Path(arg) for arg in arguments if arg.endswith(('.o.export', '.a'))]
if not objects or not any(p.name == 'NativeRunner.c.o.export' for p in objects):
    raise SystemExit('missing native runner link inputs; build native_runner first')
command = ['cc', '-shared', '-fPIC',
           '-O3', '-I' + str(LEAN / 'include'), str(source),
           *map(str, objects), '-L' + str(LEAN / 'lib/lean'),
           '-lleanshared', '-lInit_shared', '-Wl,-Bsymbolic',
           '-Wl,-z,defs', '-Wl,-rpath,' + str(LEAN / 'lib/lean'),
           '-lm', '-ldl', '-pthread', '-o', str(OUT)]
digest = hashlib.sha256(json.dumps(command).encode())
for path in [source, *objects]:
    digest.update(str(path).encode())
    with path.open('rb') as stream:
        digest.update(hashlib.file_digest(stream, 'sha256').digest())
fingerprint = digest.hexdigest()
stamp = OUT.with_suffix('.so.inputs.sha256')
if OUT.is_file() and stamp.is_file() and stamp.read_text().strip() == fingerprint:
    print('execution IR library: cached')
else:
    result = subprocess.run(command, cwd=ROOT)
    if result.returncode:
        raise SystemExit(f'execution IR library link failed: {result.returncode}')
    stamp.write_text(fingerprint + '\n')
    print('execution IR library:', OUT)
