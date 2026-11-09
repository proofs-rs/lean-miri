"""Check body pool IDs remain stable across root and instance owners."""
import importlib.util
import pathlib
import unittest

SCRIPT = pathlib.Path(__file__).resolve().parents[1] / 'tools/inspect-body.py'
SPEC = importlib.util.spec_from_file_location('body', SCRIPT)
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class BodyTests(unittest.TestCase):
    def test_pool_order_is_the_body_id_order(self):
        document = {'bodies': [{}, {}, {}, {}],
                    'body_roots': [{'body': 2, 'def_path': 'root',
                                    'promoted_bodies': [{'promoted_index': 1, 'body': 0}]}],
                    'instances': [{'def_path': 'instance', 'body': 1,
                                   'promoted_bodies': [{'promoted_index': 0, 'body': 3}]}]}
        bodies = MODULE.canonical_bodies(document)
        self.assertEqual([b['definition_path'] for b in bodies],
                         ['root::promoted[1]', 'instance', 'root', 'instance::promoted[0]'])
        self.assertEqual(bodies[3]['source_path'], 'bodies[3]')

    def test_reused_body_id_keeps_one_definition(self):
        document = {'bodies': [{}],
                    'body_roots': [{'body': 0, 'def_path': 'root'}],
                    'instances': [{'body': 0, 'def_path': 'instance'}]}
        bodies = MODULE.canonical_bodies(document)
        self.assertEqual(len(bodies), 1)
        self.assertEqual(bodies[0]['definition_path'], 'root')
        document['body_roots'][0]['body'] = -1
        with self.assertRaisesRegex(ValueError, 'out of range'):
            MODULE.canonical_bodies(document)


if __name__ == '__main__':
    unittest.main()
