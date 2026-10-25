"""Compare the exact pinned allocation-kind policy methods."""
import hashlib
import json
from pathlib import Path
import sys

root = Path(__file__).resolve().parents[2]
relative = 'upstream/miri-source/src/machine.rs'
source = (root / relative).read_bytes()
locked = next(row for row in json.loads((root / 'upstream/source-lock.json').read_text())['files'] if row['path'] == relative)
if hashlib.sha256(source).hexdigest() != locked['sha256']:
    raise SystemExit('pinned machine source changed')
source = source.decode()

def item(marker):
    start = source.index(marker)
    opening = source.index('{', start)
    depth = 0
    for index in range(opening, len(source)):
        depth += (source[index] == '{') - (source[index] == '}')
        if not depth:
            return source[start:index + 1]
    raise ValueError(marker)

names = ['Rust','Miri','C','WinHeap','WinLocal','Machine','Runtime','Global','ExternStatic','Tls','Mmap','SocketAddress']
text = '\n'.join([item('pub enum MiriMemoryKind'), 'trait MayLeak {fn may_leak(self) -> bool;}',
    item('impl MayLeak for MiriMemoryKind'), item('impl MiriMemoryKind {'),
    'fn main(){', *[f'println!("{index} {{}} {{}}", MiriMemoryKind::{name}.may_leak(), MiriMemoryKind::{name}.should_save_allocation_span());' for index, name in enumerate(names)], '}'])
Path(sys.argv[1]).write_text(text)
