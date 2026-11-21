"""Read the separately pinned current-schema connected replay cohort."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
HISTORICAL = ROOT / 'tests/connected/fixtures'
CURRENT = HISTORICAL / 'current'


def load_cohort():
    manifest = json.loads((CURRENT / 'manifest.json').read_text())
    if manifest['schema'] != 'lean-miri-connected-cohort-v1' or manifest['schema_version'] != 17:
        raise ValueError('unsupported connected replay cohort')
    for name in ('rustc', 'miri'):
        if manifest[f'{name}_commit'] != (ROOT / f'upstream/.pins/{name}.commit').read_text().strip():
            raise ValueError(f'connected cohort {name} pin mismatch; regenerate and review the cohort')
    for name, expected in manifest['files'].items():
        if Path(name).name != name or hashlib.sha256((CURRENT / name).read_bytes()).hexdigest() != expected:
            raise ValueError(f'connected cohort artifact mismatch: {name}')
    for ident, entry in manifest['cases'].items():
        if hashlib.sha256((HISTORICAL / f'{ident}.rs').read_bytes()).hexdigest() != entry['source_sha256']:
            raise ValueError(f'connected cohort source changed: {ident}')
        if 'snapshot_sha256' in entry:
            reference = json.loads((CURRENT / f'{ident}.reference.json').read_text())
            for name in ('rustc', 'miri'):
                if reference[f'{name}_commit'] != manifest[f'{name}_commit']:
                    raise ValueError(f'connected reference {name} pin mismatch: {ident}')
            reviewed = json.loads((HISTORICAL / f'{ident}.reference.json').read_text())['reference']['config']
            reviewed['rng_seed'] = entry['reference_seed']
            if reference['reference']['config'] != reviewed:
                raise ValueError(f'connected reference configuration changed: {ident}')
    return manifest
