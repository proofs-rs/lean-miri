#!/usr/bin/env python3
"""Finite declaration-source graph vs independent pinned exported candidates.

The comparison adapter derives names from declaration attributes. Neither it nor
its reference candidate/winner tables are foundation input.
"""
import json
from pathlib import Path
import subprocess
import tempfile
import unittest

ROOT = Path(__file__).resolve().parents[2]


def internal_symbol(prefix, name):
    if not name.isascii() or any(not (c.isalnum() or c == '_') for c in name):
        raise ValueError('unsupported internal identifier source')
    separator = '_' if name[:1].isdigit() or name.startswith('_') else ''
    return prefix + str(len(name.encode())) + separator + name


def declaration_candidates(source):
    graph = source['link_section_material']
    formats = graph['executable_dependencies']
    if formats is None:
        raise ValueError('executable dependency format source unavailable')
    namespace = source['foreign_symbol_material']['internal_symbol_namespace']
    candidates = []
    ordinal = 0

    def visit(item, used, crate, name, builtins):
        nonlocal ordinal
        explicit = item['symbol_name'] is not None or item['no_mangle'] or item['std_internal_symbol']
        if explicit:
            assert not item['proc_macro_declarations']
            raw_name = item['symbol_name'] if item['symbol_name'] is not None else item['item_name']
            assert raw_name is not None
            symbol = internal_symbol(namespace, raw_name) if item['std_internal_symbol'] else raw_name
            layers = item['generic_layers']
            assert layers and layers[-1]['owner'] == {
                'crate_index': item['crate_index'], 'definition_index': item['definition_index']}
            parent = None
            count = 0
            for layer in layers:
                assert layer['parent'] == parent and layer['parent_count'] == count
                for parameter in layer['parameters']:
                    assert parameter['index'] == count
                    # Independent schema12 Instance::mono succeeds only on
                    # lifetime slots; type/const declarations cannot fake mono.
                    assert parameter['kind'] == 'region'
                    count += 1
                parent = layer['owner']
            key = item['source_span_key']
            span = item['source_span']
            assert key['lo'] <= key['hi']
            candidates.append({
                'iteration_index': ordinal, 'used': used, 'symbol': symbol,
                'definition': {'crate': item['crate_index'], 'index': item['definition_index']},
                'explicit_symbol': True, 'crate_index': crate, 'crate_name': name,
                'weak': item['symbol_linkage'] == 'WeakAny',
                'definition_kind': item['symbol_kind'], 'compiler_builtins': builtins,
                'span': {'is_dummy': span['is_dummy'], 'root_context': key['ctxt'] == '#0',
                         'file': span['file'], 'start': span['start'], 'end': span['end']}})
        else:
            assert item['generic_layers'] is None
        ordinal += 1

    local = graph['local_crate']
    for item in graph['local_items']:
        assert item['crate_index'] == local
        used = item['used_compiler'] or item['used_linker']
        if used or item['extern_indicator']:
            visit(item, used, local, graph['local_crate_name'], graph['local_compiler_builtins'])
    for index, dependency in enumerate(formats):
        assert dependency['crate_index'] == index
        assert dependency['linkage'] in ('NotLinked', 'Static', 'Dynamic', 'IncludedFromDylib')
        if index == local or dependency['linkage'] == 'NotLinked':
            assert not dependency['exports']
            continue
        for export in dependency['exports']:
            if export['kind'] == 'non_generic' and not export['is_foreign']:
                visit(export['item'], export['used'], index,
                      dependency['crate_name'], dependency['compiler_builtins'])
    return candidates


def reference_candidates(reference):
    result = []
    for original in reference['compiler_runtime_queries']['foreign_symbols']['exported_candidates']:
        row = {k: v for k, v in original.items() if k not in ('instance_id', 'span')}
        row['definition'] = reference['definitions'][row['definition']]
        span = reference['spans'][original['span']]
        row['span'] = {k: span[k] for k in ('is_dummy', 'start', 'end')}
        row['span']['file'] = reference['files'][span['file']]
        # Raw hygiene/BytePos handles belong to separate compiler sessions.
        # Their exact source values are retained, but only root-vs-expansion
        # identity and diagnostic positions compare across independent runs.
        row['span']['root_context'] = span['ctxt'] == '#0'
        result.append(row)
    return result


class ForeignDeclarationSource(unittest.TestCase):
    def capture(self, directory, name, fixture, foundation, extra=()):
        output = directory / f'{name}-{foundation}.json'
        command = ['bash', 'tools/export-mir.sh', '--output', str(output),
                   *(['--foundation'] if foundation else []), '--root', 'main', '--',
                   fixture, '--crate-name', name, *extra]
        result = subprocess.run(command, cwd=ROOT, text=True, capture_output=True)
        self.assertEqual(result.returncode, 0, result.stderr)
        return json.loads(output.read_text())

    def test_normal_custom_and_std_order_count_and_provenance(self):
        with tempfile.TemporaryDirectory(prefix='foreign-source-') as directory:
            directory = Path(directory)
            for name, fixture in [('custom', 'tests/foundation/fixtures/compiler-entry.rs'),
                                  ('standard', 'tests/repro/startup/empty-main.rs')]:
                with self.subTest(name=name):
                    flags = ('-Cpanic=abort',) if name == 'custom' else ()
                    source = self.capture(directory, name, fixture, True, flags)
                    reference = self.capture(directory, name, fixture, False, flags)
                    self.assertEqual((reference['schema'], reference['schema_version']),
                                     ('lean-miri-rustc-mir', 12))
                    actual = declaration_candidates(source)
                    expected = reference_candidates(reference)
                    self.assertEqual(actual, expected)
                    self.assertGreater(len(actual), 0)
                    if name == 'standard':
                        self.assertGreater(len(actual), 100)
                        self.assertTrue(any(r['compiler_builtins'] for r in actual))
                    serialized = json.dumps(source['link_section_material'])
                    for forbidden in ('instance_id', 'selected_export', 'selected_foreign',
                                      'abi_query', 'allocation_id', 'winning'):
                        self.assertNotIn('"' + forbidden + '"', serialized)
                    # A missing executable-format source cannot mean no symbols.
                    source['link_section_material']['executable_dependencies'] = None
                    with self.assertRaises(ValueError):
                        declaration_candidates(source)
                    print(f'{name}: {len(actual)} ordered candidates match complete compiler provenance')


if __name__ == '__main__':
    unittest.main()
