"""Attribution boundaries, not assertions about Rust or Miri semantics."""
import importlib.util
from pathlib import Path
import unittest

spec = importlib.util.spec_from_file_location('exporter_profile',
    Path(__file__).resolve().parents[1] / 'tools/summarize-exporter-profile.py')
profile = importlib.util.module_from_spec(spec)
spec.loader.exec_module(profile)


class ExporterProfileTests(unittest.TestCase):
    def test_driver_excludes_callback_and_nested_spans_are_not_added(self):
        result = profile.summarize('''export_profile_at: direct.before_driver 1
export_profile_at: analysis.enter 2
export_profile: scope.rooted_closure 2
export_profile: scope_obligations 3
export_profile: closure.function_facts 4
export_profile: closure.function_facts 5
export_profile_at: analysis.exit 12
export_profile_at: direct.driver 14
export_profile: direct.driver 13
export_domain: closure.setup instances=5 types=2
export_catalog: instances=9 emitted_mir=3
''')
        self.assertEqual(result['direct_seconds'], {'driver_before_callback': 1,
            'export_callback': 10, 'driver_after_callback': 2, 'driver_total': 13})
        self.assertEqual(result['span_seconds']['closure.function_facts']['total'], 9)
        self.assertEqual(result['domain_snapshots'], [{'phase': 'closure.setup', 'instances': 5, 'types': 2}])
        self.assertEqual(result['catalog_rounds'], [{'instances': 9, 'processed_instances': 3}])

    def test_old_logs_keep_spans_without_inventing_driver_times(self):
        result = profile.summarize('export_profile: share_payloads 3.5\n')
        self.assertEqual(result['direct_seconds'], {})

    def test_incomplete_boundaries_are_rejected(self):
        with self.assertRaises(ValueError):
            profile.summarize('export_profile: x 1\nexport_profile_at: direct.before_driver 1\nexport_profile_at: analysis.enter 2\n')

    def test_invalid_duration_and_duplicate_counts_are_rejected(self):
        for text in ['export_profile: x nan', 'export_profile: x -1',
                     'export_profile: x 1\nexport_catalog: a=1 a=2']:
            with self.subTest(text=text), self.assertRaises(ValueError):
                profile.summarize(text)
