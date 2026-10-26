"""Acceptance-oracle regressions: unrelated failures must never become passes."""
from pathlib import Path
import sys
import tempfile
import subprocess
import json
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent / 'upstream_ui'))
from suite import Case, compare, discover, reference_oracle, runtime_profile


def sidecar(kind='miri_evaluation_error', status='failed'):
    return {'reference': {'status': status, 'config': {'same_tcx': True,
            'environment_policy': 'empty', 'num_cpus': 1, 'rng_seed': 0, 'validation': 'Shallow',
            'alignment_check': 'Int', 'provenance_mode': 'Default',
            'data_race_detector': True, 'weak_memory_emulation': True,
            'ignore_leaks': False, 'genmc': False, 'native_libraries': 0,
            'short_fd_operations': True, 'float_nondeterminism': True,
            'cmpxchg_weak_failure_rate': 0.8, 'fixed_scheduling': False,
            'address_reuse_cross_thread_rate': 0.1, 'collect_leak_backtraces': True,
            'borrow_tracker': 'tree_borrows', 'tree_borrows': {
                'precise_interior_mut': True, 'implicit_writes': False}}, 'outcome': {'kind': kind}}}


class UpstreamUiTests(unittest.TestCase):
    def test_all_sources_and_revisions_are_discovered(self):
        cases = list(discover())
        root = Path(__file__).resolve().parents[1] / 'upstream/miri-source/tests'
        expected = {p.relative_to(root).as_posix() for group in ('pass', 'fail')
                    for p in (root / group).rglob('*.rs')}
        self.assertEqual({c.path for c in cases}, expected)
        self.assertEqual(len(cases), len({c.id for c in cases}))
        self.assertGreater(sum(not c.reasons for c in cases), 500)

    def test_revisions_flags_and_annotation_continuations(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / 'fail').mkdir()
            (root / 'pass').mkdir()
            (root / 'fail/test.rs').write_text('''//@revisions: stack tree implicit
//@[tree]compile-flags: -Zmiri-tree-borrows
//@[implicit]compile-flags: -Zmiri-tree-borrows-implicit-writes
fn main() {
    bad();
    //~[stack]^ ERROR: sb
    //~[tree]| ERROR: tb
}
''')
            cases = {c.revision: c for c in discover(root)}
            self.assertEqual(cases['tree'].errors, [(5, 'tb')])
            self.assertEqual(cases['tree'].flags, [])
            self.assertEqual(cases['tree'].reasons, [])
            self.assertTrue(cases['implicit'].reasons)
            self.assertTrue(cases['stack'].reasons)

    def test_cli_shards_partition_the_entire_inventory(self):
        runner = Path(__file__).resolve().parents[1] / 'tools/check-upstream-ui.py'
        partitions = []
        for shard in range(2):
            result = subprocess.run([sys.executable, str(runner), '--inventory',
                                     '--shard-index', str(shard), '--shard-count', '2'],
                                    check=True, text=True, capture_output=True)
            partitions.append({c['id'] for c in json.loads(result.stdout)})
        self.assertFalse(partitions[0] & partitions[1])
        self.assertEqual(partitions[0] | partitions[1], {c.id for c in discover()})

    def test_base_flags_precede_revision_flags_even_when_written_later(self):
        case = next(c for c in discover() if c.id ==
                    'pass/tree_borrows/tree-borrows.rs@tree_implicit_writes')
        self.assertEqual(case.runtime_flags[:2], ['-Zmiri-tree-borrows',
                                                 '-Zmiri-tree-borrows-implicit-writes'])
        self.assertTrue(runtime_profile(case.runtime_flags)['tree_borrows']['implicit_writes'])

    def test_unknown_directive_and_runtime_flags_fail_closed(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            (root / 'pass').mkdir()
            (root / 'fail').mkdir()
            (root / 'pass/test.rs').write_text('//@mystery: value\n//@compile-flags: -Zmiri-unknown-setting\nfn main() {}')
            case, = discover(root)
            self.assertEqual(len(case.reasons), 2)
            self.assertEqual(case.flags, [])

    def test_reference_requires_ub_annotation_and_location(self):
        case = Case('fail/test.rs', errors=[(3, 'expected a boolean')])
        diagnostic = 'error: Undefined Behavior: expected a boolean\n  --> tests/fail/test.rs:3:5\n'
        self.assertEqual(reference_oracle(case, sidecar(), diagnostic), ('ready', 'invalid_bool'))
        self.assertEqual(reference_oracle(case, sidecar(), diagnostic.replace(':3:', ':4:'))[0], 'reference_site_mismatch')
        self.assertEqual(reference_oracle(case, sidecar(), diagnostic.replace('expected a boolean', 'uninitialized'))[0], 'reference_annotation_mismatch')
        self.assertEqual(reference_oracle(case, sidecar('miri_panicked'), diagnostic)[0], 'reference_mismatch')
        self.assertEqual(reference_oracle(case, sidecar(), 'error: compiler failed')[0], 'reference_mismatch')
        altered = sidecar()
        altered['reference']['config']['same_tcx'] = False
        self.assertEqual(reference_oracle(case, altered, diagnostic)[0], 'reference_profile_mismatch')

    def test_runtime_settings_must_match_the_independent_reference(self):
        flags = ['-Zmiri-disable-stacked-borrows', '-Zmiri-disable-validation',
                 '-Zmiri-symbolic-alignment-check', '-Zmiri-strict-provenance']
        case = Case('pass/test.rs', runtime_flags=flags)
        ref = sidecar('exit_zero', 'completed')
        ref['reference']['config'].update(runtime_profile(flags))
        self.assertEqual(reference_oracle(case, ref, ''), ('ready', None))
        ref['reference']['config']['validation'] = 'Shallow'
        self.assertEqual(reference_oracle(case, ref, '')[0], 'reference_profile_mismatch')
        self.assertEqual(runtime_profile(flags)['borrow_tracker'], 'none')
        self.assertEqual(runtime_profile(['-Zmiri-tree-borrows-implicit-writes',
                                         '-Zmiri-tree-borrows'])['tree_borrows']['implicit_writes'], False)
        with self.assertRaises(ValueError):
            runtime_profile(['-Zmiri-disable-stacked-borrows', '-Zmiri-tree-borrows-implicit-writes'])

    def test_expected_ub_rejects_unrelated_stop_kind_and_site(self):
        case = Case('fail/test.rs', errors=[(3, 'expected a boolean')])
        terminal = {'kind': 'ub', 'detail': 'invalidBool 2', 'frames': [
            {'file': 'Real("tests/fail/test.rs")', 'line': 3, 'end_line': 3}]}
        self.assertEqual(compare(case, terminal, 'invalid_bool'), 'passed')
        for kind in ('unsupported', 'failed', 'pending', 'exit'):
            self.assertNotEqual(compare(case, terminal | {'kind': kind}, 'invalid_bool'), 'passed')
        self.assertEqual(compare(case, terminal | {'detail': 'outOfBounds'}, 'invalid_bool'), 'ub_kind_mismatch')
        self.assertEqual(compare(case, terminal | {'frames': []}, 'invalid_bool'), 'ub_site_mismatch')
        self.assertEqual(compare(case, terminal | {'frames': [{'file': case.path, 'line': 1, 'end_line': 9}]}, 'invalid_bool'), 'ub_site_mismatch')
        self.assertEqual(compare(case, terminal, None), 'ub_kind_mismatch')

    def test_uninitialized_bool_is_not_an_invalid_bool_oracle(self):
        case = Case('fail/test.rs', errors=[(3, 'uninitialized')])
        diagnostic = ('error: Undefined Behavior: constructing invalid value of type bool: '
                      'encountered uninitialized memory, but expected a boolean\n'
                      ' --> fail/test.rs:3:5\n')
        self.assertEqual(reference_oracle(case, sidecar(), diagnostic), ('ready', 'uninitialized'))
        terminal = {'kind': 'ub', 'detail': 'validation.uninitialized: invalidBool 2',
                    'frames': [{'file': case.path, 'line': 3, 'end_line': 3}]}
        self.assertEqual(compare(case, terminal, 'uninitialized'), 'ub_kind_mismatch')
        terminal['detail'] = 'InvalidUninitBytes'
        self.assertEqual(compare(case, terminal, 'uninitialized'), 'passed')

    def test_tree_borrows_direction_cannot_be_substituted(self):
        case = Case('fail/test.rs', errors=[(3, '/write access through .* is forbidden/')])
        terminal = {'kind': 'ub', 'detail': 'Tree Borrows write access: ChildAccessForbidden Frozen',
                    'frames': [{'file': 'fail/test.rs', 'line': 3, 'end_line': 3}]}
        self.assertEqual(compare(case, terminal, 'tb_write'), 'passed')
        self.assertEqual(compare(case, terminal | {'detail': terminal['detail'].replace('write', 'read')}, 'tb_write'), 'ub_kind_mismatch')
        self.assertEqual(compare(case, terminal | {'detail': 'Tree Borrows reborrow: ChildAccessForbidden Frozen'}, 'tb_write'), 'ub_kind_mismatch')

    def test_pass_requires_final_exit_zero(self):
        case = Case('pass/test.rs')
        self.assertEqual(compare(case, {'kind': 'exit', 'detail': '0'}, None), 'passed')
        for terminal in ({}, {'kind': 'exit', 'detail': '1'}, {'kind': 'pending'}, {'kind': 'ub'}):
            self.assertNotEqual(compare(case, terminal, None), 'passed')


if __name__ == '__main__':
    unittest.main()
