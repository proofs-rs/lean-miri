"""Check diagnostic canonical-index reconstruction against lowering's ordering."""
import importlib.util
import pathlib
import unittest

SCRIPT = pathlib.Path(__file__).resolve().parents[1] / 'tools/inspect-body.py'
SPEC = importlib.util.spec_from_file_location('body', SCRIPT)
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class BodyTests(unittest.TestCase):
    def test_root_instance_and_promoted_order_with_missing_children(self):
        document = {'bodies': [{'def_path': 'root', 'promoted_bodies': [
            {'body': None}, {'body': {'def_path': 'root-promoted'}}]}],
            'instances': [
                {'def_path': 'no-body', 'body': None},
                {'def_path': 'instance', 'body': {'promoted_bodies': []},
                 'promoted_bodies': [{'body': {'def_path': 'instance-promoted'}}]},
                {'def_path': 'owned', 'body': {'promoted_bodies': [{'body': None}]},
                 'promoted_bodies': [{'body': {'def_path': 'must-not-fallback'}}]},
            ]}
        bodies, _ = MODULE.canonical_bodies(document)
        self.assertEqual([b['definition_path'] for b in bodies],
                         ['root', 'root-promoted', 'instance', 'instance-promoted', 'owned'])
        self.assertEqual(bodies[3]['source_path'], 'instances[1].promoted_bodies[0].body')

    def test_shared_references_do_not_add_body_indices(self):
        document = {'shared_payloads': {'nodes': [{'def_path': 'body'}]},
                    'bodies': [{'$lean_miri_shared_ref': 0}], 'instances': []}
        bodies, deref = MODULE.canonical_bodies(document)
        self.assertEqual(len(bodies), 1)
        self.assertEqual(bodies[0]['definition_path'], 'body')
        with self.assertRaisesRegex(ValueError, 'outside catalog'):
            deref({'$lean_miri_shared_ref': -1})


if __name__ == '__main__':
    unittest.main()
