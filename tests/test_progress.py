"""Progress observations must not imply completion or merge repair candidates."""
import importlib.util
import pathlib
import unittest

SCRIPT = pathlib.Path(__file__).resolve().parents[1] / 'tools/summarize-progress.py'
SPEC = importlib.util.spec_from_file_location('progress', SCRIPT)
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class ProgressTests(unittest.TestCase):
    def test_timing_spans_do_not_replace_completion_or_include_later_candidates(self):
        result = MODULE.summarize({'events': {'guest_end': 300},
            'internal_profile_spans': [
                {'provider': 'execution', 'name': 'iteration_42.thread_0.body_20',
                 'seconds': 12.0, 'wall_monotonic_ns': 200},
                {'provider': 'execution', 'name': 'iteration_3.thread_0.body_8',
                 'seconds': 90.0, 'wall_monotonic_ns': 400},
            ]})
        self.assertEqual(result['timed_iteration_count'], 1)
        self.assertEqual(result['slowest_outer_iterations'][0]['iteration'], 42)
        self.assertEqual(result['reported_iteration_seconds_sum'], 12.0)
        self.assertEqual(result['completed_outer_iterations_lower_bound'], 0)
        self.assertFalse(result['process_finalized_exit_observed'])

    def test_timeout_without_samples_is_unknown(self):
        result = MODULE.summarize({'returncode': -15, 'stop_reason': 'wall guard'})
        self.assertEqual(result['completed_outer_iterations_lower_bound'], 0)
        self.assertIsNone(result['last_sample'])
        self.assertFalse(result['process_finalized_exit_observed'])

    def test_sample_gap_does_not_invent_completed_iterations(self):
        result = MODULE.summarize({'events': {'bootstrap_ready': 100},
            'internal_profile_spans': [
                {'provider': 'execution', 'name': 'after.iteration_64.thread_0', 'wall_monotonic_ns': 200},
                {'provider': 'execution', 'name': 'before.iteration_128.thread_0', 'wall_monotonic_ns': 300},
            ]})
        self.assertEqual(result['completed_outer_iterations_lower_bound'], 65)
        self.assertEqual(result['last_sample']['iteration'], 128)
        self.assertFalse(result['process_finalized_exit_observed'])

    def test_later_repair_candidate_is_excluded(self):
        result = MODULE.summarize({'finalized_exit_observed': True, 'events': {'guest_end': 200},
            'internal_profile_spans': [
                {'provider': 'execution', 'name': 'after.iteration_2.thread_0', 'wall_monotonic_ns': 100},
                {'provider': 'execution', 'name': 'after.iteration_999.thread_0', 'wall_monotonic_ns': 300},
            ]})
        self.assertEqual(result['sampled_boundary_count'], 1)
        self.assertEqual(result['completed_outer_iterations_lower_bound'], 3)
        self.assertTrue(result['process_finalized_exit_observed'])
        self.assertNotIn('finalized_exit_observed', result)


if __name__ == '__main__':
    unittest.main()
