#!/usr/bin/env python3
"""Definition symbol attributes are finite inputs, never mangled instance answers."""
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]


class FoundationSymbolNames(unittest.TestCase):
    def export(self, directory, text, roots):
        source = Path(directory) / 'source.rs'
        source.write_text(text)
        output = Path(directory) / 'source.json'
        args = ['bash', 'tools/export-mir.sh', '--foundation', '--output', str(output)]
        for root in roots:
            args += ['--root', root]
        result = subprocess.run([*args, '--', str(source), '--crate-name=symbol_source', '--crate-type=lib'],
                                cwd=ROOT, capture_output=True, text=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        return json.loads(output.read_text())

    def declarations(self, source):
        rows = source['symbol_name_source']['declarations']
        self.assertEqual(len({row['definition'] for row in rows}), len(rows))
        return {source['definitions'][row['definition']]['path']: row for row in rows}

    def test_export_name_no_mangle_and_unavailable_default_mangling(self):
        with tempfile.TemporaryDirectory(prefix='symbol-definition-') as directory:
            source = self.export(directory, '''#![no_std]
#[unsafe(export_name = "exact_export")]
pub fn renamed(value: u8) -> u8 { value }
#[unsafe(no_mangle)]
pub fn plain(value: u8) -> u8 { value }
pub fn needs_mangling(value: u8) -> u8 { value }
''', ['renamed', 'plain', 'needs_mangling'])
            rows = self.declarations(source)
            self.assertEqual(rows['renamed']['attributes']['symbol_name'], 'exact_export')
            self.assertTrue(rows['plain']['attributes']['no_mangle'])
            self.assertEqual(rows['plain']['attributes']['item_name'], 'plain')
            self.assertIsNone(rows['needs_mangling']['attributes']['symbol_name'])
            self.assertFalse(rows['needs_mangling']['attributes']['no_mangle'])
            self.assertFalse(rows['needs_mangling']['attributes']['std_internal_symbol'])
            self.assertFalse(rows['renamed']['foreign_item'])
            self.assertIsNone(rows['renamed']['wasm_import_module'])
            self.assertTrue(all('symbol' not in row and 'instance' not in row for row in rows.values()))

    def test_internal_symbol_is_attribute_material_not_a_mangled_answer(self):
        with tempfile.TemporaryDirectory(prefix='internal-symbol-source-') as directory:
            source = self.export(directory, '''#![no_std]
#![feature(rustc_attrs)]
#![allow(internal_features)]
#[rustc_std_internal_symbol]
pub fn source_internal(value: u8) -> u8 { value }
''', ['source_internal'])
            row = self.declarations(source)['source_internal']
            self.assertTrue(row['attributes']['std_internal_symbol'])
            self.assertIsNone(row['attributes']['symbol_name'])
            self.assertEqual(row['attributes']['item_name'], 'source_internal')
            self.assertTrue(source['foreign_symbol_material']['internal_symbol_namespace'].startswith('_RNvC'))

    def test_link_name_and_implicit_foreign_no_mangle(self):
        with tempfile.TemporaryDirectory(prefix='foreign-symbol-source-') as directory:
            source = self.export(directory, '''#![no_std]
unsafe extern "C" {
    #[link_name = "exact_import"] fn renamed_import(value: u8) -> u8;
    fn default_import(value: u8) -> u8;
}
pub unsafe fn first(value: u8) -> u8 { unsafe { renamed_import(value) } }
pub unsafe fn second(value: u8) -> u8 { unsafe { default_import(value) } }
''', ['first', 'second'])
            rows = self.declarations(source)
            named, default = rows['renamed_import'], rows['default_import']
            self.assertTrue(named['foreign_item'] and default['foreign_item'])
            self.assertEqual(named['attributes']['symbol_name'], 'exact_import')
            self.assertIsNone(default['attributes']['symbol_name'])
            self.assertTrue(default['attributes']['no_mangle'])
            self.assertEqual(default['attributes']['item_name'], 'default_import')
            self.assertIsNotNone(named['foreign_module'])
            self.assertIsNone(named['wasm_import_module'])
            body_names = {source['definitions'][row['definition']]['path'] for row in source['bodies']}
            self.assertNotIn('renamed_import', body_names)
            self.assertNotIn('default_import', body_names)

    def test_wasm_module_attribute_retained_without_symbol_query(self):
        with tempfile.TemporaryDirectory(prefix='wasm-import-source-') as directory:
            source = self.export(directory, '''#![no_std]
#[link(wasm_import_module = "source_module")]
unsafe extern "C" { #[link_name = "exact_member"] fn imported(value: u8) -> u8; }
pub unsafe fn call(value: u8) -> u8 { unsafe { imported(value) } }
''', ['call'])
            row = self.declarations(source)['imported']
            self.assertEqual(row['wasm_import_module'], 'source_module')
            self.assertEqual(row['attributes']['symbol_name'], 'exact_member')
            self.assertTrue(row['foreign_item'])
            # On wasm this pair forces full mangling. Keeping both fields lets
            # the pure query reject that unavailable rule instead of guessing.


if __name__ == '__main__':
    unittest.main()
