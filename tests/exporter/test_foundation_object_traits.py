#!/usr/bin/env python3
"""Object declarations follow observed dyn principals, independent of Fn names."""
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]


class FoundationObjectTraits(unittest.TestCase):
    def capture(self, directory, source):
        path = Path(directory) / 'source.rs'
        path.write_text(source)
        output = Path(directory) / 'source.json'
        process = subprocess.run(['bash', 'tools/export-mir.sh', '--foundation', '--output', str(output),
            '--root', 'reference', '--', str(path), '--crate-type=lib', '--crate-name=object_graph'],
            cwd=ROOT, capture_output=True, text=True)
        return process, output

    def test_arbitrary_principal_complete_supertraits_and_method_syntax(self):
        with tempfile.TemporaryDirectory(prefix='object-source-') as directory:
            process, output = self.capture(directory, '''#![no_std]
pub trait Base { fn value(&self) -> u8; }
pub trait Principal: Base {}
pub fn reference(value: &dyn Principal) -> &dyn Principal { value }
''')
            self.assertEqual(process.returncode, 0, process.stderr)
            source = json.loads(output.read_text())
            definitions = source['definitions']
            rows = source['fn_vtable_source']['declarations']
            by_path = {definitions[row['definition']]['path']: row for row in rows}
            self.assertEqual(len(by_path), len(rows))
            self.assertIn('Principal', by_path)
            self.assertIn('Base', by_path)
            self.assertFalse(by_path['Principal']['core_source'])
            self.assertEqual(by_path['Principal']['lang_item'], 'other')
            principal_supers = by_path['Principal']['super_clauses']
            self.assertIn('Base', [definitions[row['definition']]['path'] for row in principal_supers])
            # Every declared trait edge has its actual declaration, rather than
            # a successful empty fallback at an unrecognized principal.
            captured = {row['definition'] for row in rows}
            for row in rows:
                for clause in row['super_clauses']:
                    if clause['kind'] == 'trait':
                        self.assertIn(clause['definition'], captured)
            methods = [item['method'] for item in by_path['Base']['associated_items'] if item['kind'] == 'method']
            self.assertEqual(len(methods), 1)
            self.assertEqual(methods[0]['output']['kind'], 'source_type')
            result = source['types'][methods[0]['output']['type']]['shape']
            self.assertEqual((result['kind'], result['name']), ('uint', 'u8'))
            self.assertEqual({row['lang_item'] for row in source['closure_auto_source']['declarations']
                              if row['lang_item'] is not None}, {'unpin', 'unsafe_unpin', 'freeze'})

    def test_unobserved_principal_does_not_create_object_material(self):
        with tempfile.TemporaryDirectory(prefix='object-unobserved-') as directory:
            process, output = self.capture(directory, '''#![no_std]
pub trait Base {}
pub trait Principal: Base {}
pub fn reference(value: u8) -> u8 { value }
''')
            self.assertEqual(process.returncode, 0, process.stderr)
            self.assertIsNone(json.loads(output.read_text())['fn_vtable_source'])

    def test_unsupported_supertrait_arguments_are_not_omitted(self):
        with tempfile.TemporaryDirectory(prefix='object-higher-ranked-') as directory:
            process, output = self.capture(directory, '''#![no_std]
pub trait Base<'a> {}
pub trait Principal: for<'a> Base<'a> {}
pub fn reference(value: &dyn Principal) -> &dyn Principal { value }
''')
            self.assertNotEqual(process.returncode, 0)
            self.assertIn('unsupported Fn declaration generic argument', process.stderr)
            self.assertFalse(output.exists())


if __name__ == '__main__':
    unittest.main()
