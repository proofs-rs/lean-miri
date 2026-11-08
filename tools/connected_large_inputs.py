"""Fresh inputs for the two large connected cases, with byte-bound Miri references.

Historical archives remain available for provenance. Their failed compiler
payloads are never converted into executable input; only their reviewed Miri
configuration is reused for a new export and same-prepared-TyCtxt reference.
"""
import hashlib
import json
import os
from pathlib import Path
import sys

from run_guarded import run as run_guarded

ROOT = Path(__file__).resolve().parents[1]
FIXTURES = ROOT / 'tests/connected/fixtures'
sys.path.insert(0, str(FIXTURES.parent))
from cases import MIRI_ERRORS

FRESH_CASES = frozenset(('196-slice-custom-dst', 'large-tb'))
SOURCE_SHA256 = {
    '196-slice-custom-dst': 'f875b318085990a0e61ee8d1e1ca749f9e70aa042c0495d6cb854c51dbfc4558',
    'large-tb': 'f3a8fb4e3529d90f1b9a46da5b05079587a52c7875e7d36fec6390f34bb62d91',
}
REFERENCE_CONTRACT = 'same_prepared_tcx_after_snapshot_capture;not_vanilla_miri_alloc_id_history'


def _source(ident):
    if ident not in FRESH_CASES:
        raise ValueError(f'{ident}: not a fresh large-input case')
    source = FIXTURES / f'{ident}.rs'
    if hashlib.sha256(source.read_bytes()).hexdigest() != SOURCE_SHA256[ident]:
        raise ValueError(f'{ident}: original reviewed Rust source changed')
    return source


def reference_paths(snapshot):
    snapshot = Path(snapshot)
    return Path(str(snapshot) + '.miri-reference.json'), snapshot.with_suffix('.export.log')


def validate_reference(ident, snapshot):
    """Validate the new reference, never the historical archive's verdict/hash."""
    _source(ident)
    snapshot = Path(snapshot)
    raw = snapshot.read_bytes()
    sidecar, diagnostic = reference_paths(snapshot)
    reference = json.loads(sidecar.read_text())
    if reference['reference_contract'] != REFERENCE_CONTRACT:
        raise ValueError(f'{ident}: wrong reference contract')
    if Path(reference['snapshot_path']).resolve() != snapshot.resolve():
        raise ValueError(f'{ident}: reference belongs to another snapshot path')
    for key, pin in [('rustc_commit', 'rustc'), ('miri_commit', 'miri')]:
        if reference[key] != (ROOT / 'upstream/.pins' / f'{pin}.commit').read_text().strip():
            raise ValueError(f'{ident}: reference compiler/Miri pin mismatch')
    fnv = 14695981039346656037
    for byte in raw:
        fnv = ((fnv ^ byte) * 1099511628211) & ((1 << 64) - 1)
    if reference['snapshot_byte_length'] != len(raw) or reference['snapshot_fnv1a64'] != f'{fnv:016x}':
        raise ValueError(f'{ident}: reference/snapshot byte identity mismatch')
    actual = reference['reference']
    reviewed = json.loads((FIXTURES / f'{ident}.reference.json').read_text())['reference']['config']
    if actual['config'] != reviewed or actual['config']['same_tcx'] is not True:
        raise ValueError(f'{ident}: reviewed Miri configuration/guest arguments changed')
    if ident in MIRI_ERRORS:
        if reference['status'] != 'failed' or actual['status'] != 'failed' or actual['outcome']['kind'] != 'miri_evaluation_error':
            raise ValueError(f'{ident}: new reference did not establish the expected UB')
        if not all(token in diagnostic.read_text() for token in MIRI_ERRORS[ident]):
            raise ValueError(f'{ident}: new reference lacks the original UB diagnostic')
    elif reference['status'] != 'completed' or actual['status'] != 'completed' or actual['outcome'] != {'kind': 'exit_zero'}:
        raise ValueError(f'{ident}: new reference did not naturally exit zero')
    return reference


def generate(ident, snapshot, *, timeout):
    """Use the current exporter and the unchanged case's compiler flags/roots."""
    source = _source(ident)
    snapshot = Path(snapshot).resolve()
    sidecar, diagnostic = reference_paths(snapshot)
    generation_log = snapshot.with_suffix('.generation.log')
    if not snapshot.is_relative_to(ROOT / 'scratch') or any(path.exists() for path in (snapshot, sidecar, diagnostic, generation_log)):
        raise ValueError('fresh large input requires new output paths under scratch/')
    exporter = Path(os.environ.get('LEAN_MIRI_CONNECTED_PROFILE_EXPORTER',
        ROOT / 'scratch/reference-profile-target/debug/lean-miri-mir-exporter')).resolve()
    if not exporter.is_file():
        raise ValueError(f'missing reference-profile exporter {exporter}; run tools/build-reference-profile.sh')
    tracked = [source, FIXTURES / f'{ident}.reference.json', FIXTURES.parent / 'cases.py',
        ROOT / 'tools/export-connected.py', ROOT / 'tools/connected_large_inputs.py',
        FIXTURES.parent / 'reference/preemption-rate-zero.patch', exporter,
        ROOT / 'exporter/Cargo.toml', ROOT / 'exporter/Cargo.lock', ROOT / 'exporter/build.rs',
        ROOT / 'upstream/.pins/rustc.commit', ROOT / 'upstream/.pins/miri.commit',
        *sorted((ROOT / 'exporter/src').rglob('*.rs'))]
    def hashes():
        return {str(path): hashlib.sha256(path.read_bytes()).hexdigest() for path in tracked}
    before = hashes()
    command = [sys.executable, str(ROOT / 'tools/export-connected.py'), ident, str(snapshot), '--exporter', str(exporter)]
    result = run_guarded(command, cwd=ROOT, env=os.environ.copy(), log=generation_log,
                         timeout=timeout, memory_limit=15_500_000_000)
    if hashes() != before:
        raise ValueError(f'{ident}: compiler/source/profile inputs changed during generation')
    validate_reference(ident, snapshot)
    if (ident in MIRI_ERRORS) != (result.returncode != 0):
        raise ValueError(f'{ident}: exporter exit does not match its validated Miri outcome')
    return sidecar, diagnostic, generation_log
