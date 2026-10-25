#!/usr/bin/env python3
"""Preserve the exact accepted Frozen-write source/MIR/state assertions."""
import hashlib
import json
from pathlib import Path
import sys
ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / 'tools'))
from mir_json import decode_mir_document


def validate(snapshot, log):
    raw = Path(snapshot).read_bytes()
    assert hashlib.sha256(raw).hexdigest() == '32870449acfdc89f8ff86d1519fb562d8ad11b9fc3c92cfc012ea2cb1d39b8a7'
    ref = json.loads((ROOT / 'tests/connected/fixtures/large-tb.reference.json').read_text())
    assert ref['reference']['config']['same_tcx'] is True
    assert ref['reference']['outcome']['kind'] == 'miri_evaluation_error'
    assert ref['rustc_commit'] == (ROOT / 'upstream/.pins/rustc.commit').read_text().strip()
    assert ref['miri_commit'] == (ROOT / 'upstream/.pins/miri.commit').read_text().strip()
    doc = decode_mir_document(json.loads(raw))
    body = next(b for b in doc['bodies'] if b['def_path'] == 'miri_start')
    stmt = body['basic_blocks'][1]['statements'][8]
    assert stmt['kind']['variant'] == 'Assign'
    assert stmt['kind']['place']['projection'][0]['kind'] == 'Deref'
    assert stmt['source_info']['span']['start']['line'] == 14
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
