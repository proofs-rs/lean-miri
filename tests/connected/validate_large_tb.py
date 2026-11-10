#!/usr/bin/env python3
"""Preserve the exact accepted Frozen-write source/MIR/state assertions."""
import json
from pathlib import Path
import sys
ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'tools'))
from mir_json import decode_mir_document, pool_entry
from connected_large_inputs import validate_reference


def validate(snapshot, log):
    raw = Path(snapshot).read_bytes()
    validate_reference('large-tb', snapshot)
    doc = decode_mir_document(json.loads(raw))
    roots = [root for root in doc['body_roots'] if root['def_path'] == 'miri_start']
    assert len(roots) == 1
    root = roots[0]
    body = pool_entry(doc, 'bodies', root['body'])
    assert body['instance_id'] == root['entry_instance']
    stmt = body['basic_blocks'][1]['statements'][8]
    assert stmt['kind']['variant'] == 'Assign'
    assert stmt['kind']['place']['projection'][0]['kind'] == 'Deref'
    span = pool_entry(doc, 'spans', stmt['source_info']['span'])
    assert span['start']['line'] == 14
    source = ROOT / 'tests/connected/fixtures/large-tb.rs'
    assert '*ptr = 0;' in source.read_text().splitlines()[13]
    text = Path(log).read_text()
    assert all(x in text for x in ['phase=decode-complete', 'phase=lower-complete', 'phase=prepare-complete',
        'StepError.undefinedBehavior', 'ChildAccessForbidden', 'Permission.Frozen',
        'block := 1, statementIndex := 8', 'threads=1', 'diagnostic-choices-consumed=44',
        'stop-after-root-return=false'])
    print('PASS: Frozen child write at source line14/MIR bb1[8], one thread, 44 choices')


if __name__ == '__main__':
    validate(sys.argv[1], sys.argv[2])
