"""The current replay cohort keeps source, reference and choice bindings strict."""
import gzip
import hashlib
import json
from pathlib import Path
import shutil
import sys
import tempfile
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'tools'))
import connected_cohort as cohort


class ConnectedCohortTests(unittest.TestCase):
    def test_current_inputs_and_exact_ordering_prefix_migration(self):
        manifest = cohort.load_cohort()
        for ident, entry in manifest['cases'].items():
            if 'snapshot_sha256' in entry:
                raw = gzip.decompress((cohort.CURRENT / f'{ident}.json.gz').read_bytes())
                self.assertEqual(hashlib.sha256(raw).hexdigest(), entry['snapshot_sha256'])
                self.assertEqual(json.loads(raw)['schema_version'], 17)
        for ident in ('fence-acqrel', 'fence-sc', 'rmw-relaxed', 'rmw-sc'):
            old = json.loads((cohort.HISTORICAL / f'{ident}.observed.json').read_text())
            new = json.loads((cohort.CURRENT / f'{ident}.observed.json').read_text())
            self.assertEqual(new[4:], old)
            self.assertEqual([e['request']['site'] for e in new[:4]],
                             ['addressReuse', 'addressSlack', 'addressReuse', 'addressSlack'])

    def test_corrupt_input_changed_source_and_pin_fail_closed(self):
        for mutation in ('input', 'source', 'pin'):
            with self.subTest(mutation=mutation), tempfile.TemporaryDirectory() as tmp:
                root, historical, current = self.copy_cohort(Path(tmp))
                target = {'input': current / '198-sc-base.json.gz',
                          'source': historical / '198-sc-base.rs',
                          'pin': root / 'upstream/.pins/rustc.commit'}[mutation]
                target.write_bytes(target.read_bytes() + b'changed')
                with patch.multiple(cohort, ROOT=root, HISTORICAL=historical, CURRENT=current):
                    with self.assertRaises(ValueError):
                        cohort.load_cohort()

    def test_resealed_reference_cannot_change_the_reviewed_profile(self):
        with tempfile.TemporaryDirectory() as tmp:
            root, historical, current = self.copy_cohort(Path(tmp))
            reference_path = current / 'fence-acqrel.reference.json'
            reference = json.loads(reference_path.read_text())
            reference['reference']['config']['preemption_rate'] = 0.5
            reference_path.write_text(json.dumps(reference))
            manifest_path = current / 'manifest.json'
            manifest = json.loads(manifest_path.read_text())
            manifest['files'][reference_path.name] = hashlib.sha256(reference_path.read_bytes()).hexdigest()
            manifest_path.write_text(json.dumps(manifest))
            with patch.multiple(cohort, ROOT=root, HISTORICAL=historical, CURRENT=current):
                with self.assertRaisesRegex(ValueError, 'configuration changed'):
                    cohort.load_cohort()

    @staticmethod
    def copy_cohort(root):
        historical = root / 'fixtures'
        current = historical / 'current'
        shutil.copytree(cohort.CURRENT, current)
        manifest = json.loads((current / 'manifest.json').read_text())
        for ident in manifest['cases']:
            for suffix in ('rs', 'reference.json'):
                shutil.copyfile(cohort.HISTORICAL / f'{ident}.{suffix}', historical / f'{ident}.{suffix}')
        pins = root / 'upstream/.pins'
        pins.mkdir(parents=True)
        for name in ('rustc', 'miri'):
            (pins / f'{name}.commit').write_text(manifest[f'{name}_commit'])
        return root, historical, current
