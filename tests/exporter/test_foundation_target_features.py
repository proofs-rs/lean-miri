#!/usr/bin/env python3
"""Raw ordered definition features agree with independent compiler-instance reads."""
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]
SOURCE = '''#![no_std]
#![feature(effective_target_features)]
#![allow(incomplete_features)]
#[target_feature(enable = "avx2")]
pub unsafe fn enabled(value: u8) -> u8 { value }
#[unsafe(force_target_feature(enable = "avx2"))]
pub fn forced(value: u8) -> u8 { value }
pub fn plain(value: u8) -> u8 { value }
'''


class FoundationTargetFeatures(unittest.TestCase):
    def export(self, source, output, foundation, roots, extra=()):
        args = ['bash', 'tools/export-mir.sh', '--output', str(output)]
        if foundation:
            args += ['--foundation']
        for root in roots:
            args += ['--root', root]
        return subprocess.run([*args, *extra, '--', str(source), '--crate-type=lib',
                               '--crate-name=target_feature_source'], cwd=ROOT, capture_output=True, text=True)

    def test_enabled_forced_implied_order_and_session_match_compiler(self):
        with tempfile.TemporaryDirectory(prefix='raw-target-features-') as directory:
            source = Path(directory) / 'source.rs'
            source.write_text(SOURCE)
            finite, reference = Path(directory) / 'finite.json', Path(directory) / 'reference.json'
            roots = ['enabled', 'forced', 'plain']
            result = self.export(source, finite, True, roots,
                                 ['--foundation-signature-root', 'enabled', '--foundation-signature-root', 'forced'])
            self.assertEqual(result.returncode, 0, result.stderr)
            result = self.export(source, reference, False, roots)
            self.assertEqual(result.returncode, 0, result.stderr)
            finite, reference = json.loads(finite.read_text()), json.loads(reference.read_text())
            actual = {row['display']: row['target_features']
                      for row in reference['compiler_runtime_queries']['instances']}
            for row in finite['bodies'] + finite['source_function_signatures']:
                name = finite['definitions'][row['definition']]['path']
                features = row['runtime_source']['target_features']
                self.assertEqual([dict(name=f['name'], kind=f['kind'].lower()) for f in features], actual[name])
                if name in ['enabled', 'forced']:
                    expected = 'Enabled' if name == 'enabled' else 'Forced'
                    self.assertIn(dict(name='avx2', kind=expected), features)
                    self.assertTrue(any(f['kind'] == 'Implied' for f in features))
                else:
                    self.assertEqual(features, [])
            self.assertEqual(finite['session']['internal_target_features'],
                             reference['compiler_session_queries']['internal_target_features'])
            self.assertEqual(finite['session']['is_like_wasm'],
                             reference['compiler_session_queries']['is_like_wasm'])

    def test_closure_retains_inherited_definition_features(self):
        with tempfile.TemporaryDirectory(prefix='closure-target-features-') as directory:
            source, output = Path(directory) / 'source.rs', Path(directory) / 'source.json'
            source.write_text('''#![no_std]
#[target_feature(enable="avx2")]
pub unsafe fn outer(value:u8)->u8 { let closure = |value:u8| value; closure(value) }
''')
            result = self.export(source, output, True, ['outer', 'outer::{closure#0}'])
            self.assertEqual(result.returncode, 0, result.stderr)
            document = json.loads(output.read_text())
            body_features = document['bodies'][0]['runtime_source']['target_features']
            self.assertTrue(body_features)
            self.assertEqual(len(document['closure_templates']), 1)
            self.assertEqual(document['closure_templates'][0]['runtime_source']['target_features'], body_features)

    def test_invalid_source_feature_does_not_become_empty_evidence(self):
        with tempfile.TemporaryDirectory(prefix='invalid-target-feature-') as directory:
            source, output = Path(directory) / 'source.rs', Path(directory) / 'source.json'
            source.write_text('#![no_std]\n#[target_feature(enable="not_a_real_target_feature")]\n'
                              'pub unsafe fn invalid(value:u8)->u8 { value }\n')
            result = self.export(source, output, True, ['invalid'])
            self.assertNotEqual(result.returncode, 0)
            self.assertIn('not_a_real_target_feature', result.stderr)
            self.assertFalse(output.exists())


if __name__ == '__main__':
    unittest.main()
