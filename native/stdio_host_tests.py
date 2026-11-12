#!/usr/bin/env python3
"""Finite native boundary checks; no guest stdio startup equivalence claim."""
import json
import os
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
EXE = ROOT / '.lake/build/bin/native_stdio_host_qa'

def run(*args, **kwargs):
    return subprocess.run([str(EXE), *map(str,args)], capture_output=True, timeout=30, **kwargs)

def main():
    result = run('decode')
    assert result.returncode == 0, result.stderr
    with tempfile.TemporaryDirectory(dir=ROOT/'scratch') as tmp:
        file = Path(tmp)/'control'
        fd = os.open(file, os.O_CREAT|os.O_EXCL|os.O_RDWR, 0o600)
        try:
            result = run('normal', fd, file, pass_fds=(fd,))
            assert result.returncode == 0, result.stderr
            assert result.stdout == bytes([0,255,10,65,90]), result.stdout
            assert result.stderr == bytes([69,0,254,89]), result.stderr
            os.lseek(fd,0,os.SEEK_SET)
            assert os.read(fd,4096) == b'control-only\n'
            assert os.fstat(fd).st_mode & 0o777 == 0o600
        finally:
            os.close(fd)
    # Invalid standard descriptors, absent descriptor, and pipe are rejected.
    for fd in (0,1,2,2147483647):
        result = run('reject',fd)
        assert result.returncode == 0, (fd,result.stderr)
    r,w = os.pipe()
    try:
        result = run('reject',w,pass_fds=(w,))
        assert result.returncode == 0, result.stderr
    finally:
        os.close(r);os.close(w)
    # No SIGPIPE handler is installed by this adapter. Record the actual host
    # startup behavior; signal death is a process failure, never a guest error.
    r,w = os.pipe();os.close(r)
    try:
        result = subprocess.run([str(EXE),'broken'],stdout=w,stderr=subprocess.PIPE,timeout=30)
    finally:
        os.close(w)
    assert result.returncode in (0,-13), (result.returncode,result.stderr)
    if result.returncode == 0:
        assert b'broken-pipe-error:' in result.stderr and b'BrokenPipe' in result.stderr, result.stderr
    report = {'checks':'binary stdout/stderr; distinct regular control; once-only/close; malformed-wire; invalid fd/pipe',
              'closed_pipe_exit':result.returncode,'closed_pipe_stderr':result.stderr.decode(errors='replace'),
              'startup_equivalence_claimed':False}
    (ROOT/'scratch/stdio-native/control-tests.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report))

if __name__ == '__main__': main()
