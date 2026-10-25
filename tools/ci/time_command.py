#!/usr/bin/env python3
"""Measure one command, inheriting its output and preserving its exit status."""
from datetime import datetime, timezone
import json
import os
from pathlib import Path
import resource
import subprocess
import sys
import time
import uuid


def measure(label, command, path):
    path = Path(path)
    path.parent.mkdir(parents=True, exist_ok=True)
    invocation = uuid.uuid4().hex
    common = dict(id=invocation, label=label, category=label.split(':', 1)[0],
                  command=command, cwd=os.getcwd())

    def emit(**fields):
        with path.open('a') as stream:
            stream.write(json.dumps(dict(common, **fields)) + '\n')

    emit(event='start', started_at=datetime.now(timezone.utc).isoformat())
    start = time.monotonic()
    before = resource.getrusage(resource.RUSAGE_CHILDREN)
    try:
        code = subprocess.run(command).returncode
    except OSError as error:
        print(f'{label}: {error}', file=sys.stderr)
        code = 127
    after = resource.getrusage(resource.RUSAGE_CHILDREN)
    seconds = round(time.monotonic() - start, 6)
    emit(event='finish', status='passed' if code == 0 else 'failed', exit_code=code,
         seconds=seconds, user_seconds=round(after.ru_utime - before.ru_utime, 6),
         system_seconds=round(after.ru_stime - before.ru_stime, 6),
         max_child_rss_kib=after.ru_maxrss)
    print(f'TIMING {label}: exit={code}, wall={seconds:.3f}s', flush=True)
    return code if code >= 0 else 128 - code


def read_steps(path):
    """Retain starts without finishes when a suite is interrupted or times out."""
    events, errors = {}, []
    if not Path(path).exists():
        return [], []
    for number, line in enumerate(Path(path).read_text().splitlines(), 1):
        try:
            event = json.loads(line)
            identity = event['id']
            if event['event'] == 'start':
                events[identity] = dict(event, status='interrupted')
            elif event['event'] == 'finish':
                events.setdefault(identity, {}).update(event)
            else:
                raise ValueError('unknown timing event')
        except (ValueError, KeyError, TypeError) as error:
            errors.append(f'line {number}: {error}')
    return list(events.values()), errors


def main():
    if len(sys.argv) < 4 or sys.argv[2] != '--':
        raise SystemExit('usage: time_command.py CATEGORY:LABEL -- COMMAND [ARG...]')
    return measure(sys.argv[1], sys.argv[3:], os.environ['CI_TIMING_FILE'])


if __name__ == '__main__':
    raise SystemExit(main())
