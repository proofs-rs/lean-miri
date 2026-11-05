"""Cross-reader malformed-row and alias checks for the indexed transport."""
import copy
import pathlib
import sys
import unittest

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parents[2] / 'tools'))
from mir_json import decode_mir_document, MirJSONError


def image():
    return {'schema': 'lean-miri-prepared-image', 'schema_version': 1,
            'fields': ['schema', 'schema_version', 'values'],
            'nodes': [[4, 'lean-miri-rustc-mir'], [3, 3], [3, 17],
                      [5, [2, 2]], [6, [[0, 0], [1, 1], [2, 3]]]], 'root': 4}


class ReaderChecks(unittest.TestCase):
    def test_reconstruct(self):
        self.assertEqual(decode_mir_document(image()),
                         {'schema': 'lean-miri-rustc-mir', 'schema_version': 3, 'values': [17, 17]})

    def test_malformed_unused_rows(self):
        for row in ([5, [5]], [6, [[True, 0]]], [6, [[0, 0], [0, 0]]],
                    [6, [[1, 0], [0, 0]]], [6, [[99, 0]]], [3, True], [4, 1],
                    [True], [7], [0, 1], [], [6, [[0]]], [5, [False]]):
            bad = image()
            bad['nodes'].append(row)
            with self.subTest(row=row), self.assertRaises(MirJSONError):
                decode_mir_document(bad)

    def test_headers_and_reserved_names(self):
        for key, value in [('root', True), ('root', 99), ('root', 0),
                           ('schema_version', True), ('fields', ['x', 'x'])]:
            bad = image()
            bad[key] = value
            with self.subTest(key=key, value=value), self.assertRaises(MirJSONError):
                decode_mir_document(bad)
        for name in ('$lean_miri_shared_ref', 'shared_payloads'):
            bad = image()
            bad['fields'][0] = name
            with self.assertRaises(MirJSONError):
                decode_mir_document(bad)

    def test_preserve_alias(self):
        bad = image()
        bad['nodes'][3] = [5, [2, 2]]
        bad['nodes'].insert(4, [5, [3, 3]])
        bad['nodes'][-1][1][-1][1] = 4
        bad['root'] = 5
        result = decode_mir_document(bad)['values']
        self.assertIs(result[0], result[1])


if __name__ == '__main__':
    unittest.main()
