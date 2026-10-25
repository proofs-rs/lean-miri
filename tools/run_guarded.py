"""Process-group guard shared by finite fixture entry points (no stored run ledger)."""
import os
from pathlib import Path
import signal
import subprocess
import time


def run(command, *, cwd, env, log, timeout, memory_limit):
    memory = Path('/sys/fs/cgroup/memory.current')
    def exceeded():
        return memory.exists() and int(memory.read_text()) > memory_limit
    if exceeded():
        raise RuntimeError('shared cgroup memory limit exceeded before launch; NOT RUN')
    events = Path('/sys/fs/cgroup/memory.events')
    events_before = events.read_text() if events.exists() else None
    started = time.monotonic()
    with log.open('w') as stream:
        process = subprocess.Popen(command, cwd=cwd, env=env, stdout=stream,
                                   stderr=subprocess.STDOUT, start_new_session=True)
        reason = None
        while process.poll() is None:
            if time.monotonic() - started > timeout:
                reason = 'walltime limit'
            elif exceeded():
                reason = 'shared cgroup memory limit'
            if reason:
                os.killpg(process.pid, signal.SIGTERM)
                try:
                    process.wait(timeout=10)
                except subprocess.TimeoutExpired:
                    os.killpg(process.pid, signal.SIGKILL)
                    process.wait()
                raise RuntimeError(f'{reason}; FAIL; exit={process.returncode}; log={log}')
            time.sleep(0.25)
        if events_before is not None and events.read_text() != events_before:
            raise RuntimeError(f'cgroup memory events changed during execution; inspect resource failure; log={log}')
        return subprocess.CompletedProcess(command, process.returncode)


def source_closure(root):
    """Bind read-only execution to unchanged project sources and built OLeans."""
    import hashlib
    paths = [root / 'Miri.lean', root / 'lakefile.lean', root / 'lean-toolchain',
             *sorted((root / 'Miri').rglob('*.lean')),
             *sorted((root / '.lake/build/lib/lean').rglob('*.olean'))]
    return {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest() for p in paths}
