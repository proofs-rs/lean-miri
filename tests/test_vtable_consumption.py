"""Diagnostic joins must distinguish catalog queries from runtime consumption."""
import copy
import importlib.util
import json
from pathlib import Path
import unittest

SPEC = importlib.util.spec_from_file_location('vtable_erasure',
    Path(__file__).resolve().parents[1] / 'tools/check-vtable-erasure.py')
MODULE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(MODULE)


class ConsumptionTests(unittest.TestCase):
    def setUp(self):
        # Synthetic parser data only; never a producer/nonidentity witness.
        self.document = {'producer': {'rustc_commit': 'unit-test'}, 'compiler_vtable_queries': [{
            'query_id': 0, 'input_type': 10, 'output_type': 10,
            'input_predicates': [1], 'output_predicates': [2]}]}
        self.provenance = {'schema': 'lean-miri-vtable-origins-v1', 'queries': [{
            'query_id': 0, 'input_type_id': 10, 'input_predicate_ids': [1],
            'origins': [{'route': 'unsize_cast', 'body': {'role': 'root_template'}}]}]}
        raw = json.dumps(self.document).encode()
        self.provenance.update(snapshot_fnv1a64=MODULE.fingerprint(raw), snapshot_byte_length=len(raw), rustc_commit='unit-test')
        self.mapping = 'vtable_query_map query_id=0 input_type=10 input_token=11 output_type=10 output_token=12\n'
        self.runtime = 'vtable_query input_type=10 input_token=11 query_id=0\n'

    def summarize(self, runtime):
        return MODULE.summarize_queries(json.dumps(self.document).encode(), self.provenance, self.mapping, runtime)

    def test_catalog_nonidentity_is_not_runtime_coverage(self):
        result = self.summarize('')
        self.assertEqual(result['nonidentity_catalog_queries'], 1)
        self.assertEqual(result['runtime_nonidentity_calls'], 0)

    def test_rejects_stale_producer_sidecar(self):
        self.provenance['snapshot_fnv1a64'] = '0000000000000000'
        with self.assertRaisesRegex(ValueError, 'different input bytes'):
            self.summarize(self.runtime)

    def test_counts_actual_repeated_lookup(self):
        self.assertEqual(self.summarize(self.runtime * 2)['runtime_nonidentity_calls'], 2)

    def test_rejects_wrong_complete_pair(self):
        with self.assertRaisesRegex(ValueError, 'exact consumer key'):
            self.summarize(self.runtime.replace('input_token=11', 'input_token=12'))

    def test_rejects_missing_key(self):
        with self.assertRaisesRegex(ValueError, 'no compiler query identity'):
            self.summarize(self.runtime.replace('query_id=0', 'query_id=missing'))

    def test_rejects_unclosed_or_duplicate_origin_rows(self):
        self.provenance['queries'].append(copy.deepcopy(self.provenance['queries'][0]))
        with self.assertRaisesRegex(ValueError, 'missing/duplicate'):
            self.summarize(self.runtime)

    def test_rejects_incorrect_identity_mapping(self):
        self.mapping = self.mapping.replace('output_token=12', 'output_token=11')
        with self.assertRaisesRegex(ValueError, 'predicate identity'):
            self.summarize(self.runtime)


class ExternalConstantTests(unittest.TestCase):
    def setUp(self):
        self.document = {'body_roots': [{'def_path': 'miri_start', 'body': 0}],
                         'bodies': [{'basic_blocks': [{'constant': {
                             'kind': 'evaluated_const', 'value': {
                                 'kind': 'indirect_allocation', 'allocation': 10}}}]}],
                         'allocations': [{'allocation_id': 10, 'relocations': [{'target': 20}]},
                                         {'allocation_id': 20, 'kind': 'vtable'}]}
        self.mir = 'fn miri_start() {\n _1 = const dependency::OBJECT;\n}'

    def test_resolved_constant_with_independent_compiler_origin(self):
        MODULE.require_external_constant(self.document, 'dependency::OBJECT', self.mir)

    def test_rejects_unrelated_external_constant(self):
        with self.assertRaisesRegex(SystemExit, 'lacks external constant'):
            MODULE.require_external_constant(self.document, 'dependency::OTHER', self.mir)

    def test_rejects_ambiguous_external_origins(self):
        with self.assertRaisesRegex(SystemExit, 'ambiguous external constant'):
            MODULE.require_external_constant(self.document, 'dependency::OBJECT',
                self.mir.replace('\n}', '\n _2 = const other::OBJECT;\n}'))

    def test_rejects_local_unsize_control(self):
        with self.assertRaisesRegex(SystemExit, 'local vtable'):
            MODULE.require_external_constant(self.document, 'dependency::OBJECT',
                                             self.mir.replace('\n}', '\n PointerCoercion(Unsize)\n}'))

    def test_rejects_missing_symbolic_relocation(self):
        self.document['allocations'][1]['kind'] = 'memory'
        with self.assertRaisesRegex(SystemExit, 'missing external constant'):
            MODULE.require_external_constant(self.document, 'dependency::OBJECT', self.mir)


if __name__ == '__main__':
    unittest.main()
