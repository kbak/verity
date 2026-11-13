"""Guard independent read projections and fail-closed composition evidence."""
import copy
import unittest

from keccak256 import selector
from solidity_differential.check_packed_memory_hash import word
from solidity_differential.check_packed_storage_read import (
    COMPOSITION_REJECTION, DIGEST, FIXTURE, KEY_READ, READ, key_read_inputs,
    read_prefix, rejected_sources, require_combined, require_rejection, require_source, source_variants,
)
from solidity_differential.pinned_sequence import SENDERS, create_address
from solidity_differential.engine import HarnessError
from solidity_differential.storage_reference_oracle import specification


class PackedStorageReadTests(unittest.TestCase):
    def setUp(self):
        self.spec = specification(create_address(SENDERS[0]), SENDERS[0])

    def test_read_projection_keeps_complete_independent_rows_and_input_immutable(self):
        before = copy.deepcopy(self.spec)
        for shift in (0, 1):
            full = specification(create_address(SENDERS[0]), SENDERS[0], shift)
            reads = read_prefix(full)
            for key in full.keys() - {'transactions', 'expected'}:
                self.assertEqual(reads[key], full[key])
            self.assertEqual(reads['transactions'], full['transactions'][:6])
            self.assertEqual(reads['expected'], full['expected'][:6])
            reads['expected'][0]['data'] = 'mutated copy'
            self.assertNotEqual(reads['expected'][0], full['expected'][0])
        self.assertEqual(self.spec, before)

    def test_projection_rejects_writes_events_reverts_or_missing_initial_world(self):
        for change in ('write', 'event', 'revert', 'storage', 'identity', 'missing'):
            full = copy.deepcopy(self.spec)
            if change == 'write':
                full['transactions'][0]['function'] = 'setCount'
            elif change == 'event':
                full['expected'][0]['events'] = ['unexpected event']
            elif change == 'revert':
                full['expected'][0]['status'] = 'revert'
            elif change == 'storage':
                full['expected'][0]['storage'] = []
            elif change == 'identity':
                full['expected'][0]['id'] = 'wrong transaction'
            else:
                full['transactions'] = full['transactions'][:5]
            with self.subTest(change=change), self.assertRaises(HarnessError):
                read_prefix(full)

    def test_supplied_key_control_never_changes_expected_state_or_environment(self):
        reads = read_prefix(self.spec)
        before = copy.deepcopy(reads)
        control = key_read_inputs(reads)
        self.assertEqual(reads, before)
        for key in reads.keys() - {'transactions'}:
            self.assertEqual(control[key], reads[key])
        for tx, converted in zip(reads['transactions'], control['transactions']):
            for key in tx.keys() - {'function', 'args', 'data'}:
                self.assertEqual(converted[key], tx[key])
            self.assertEqual(converted['function'], 'readKey')
            self.assertEqual(len(converted['args']), 1)
            self.assertEqual(converted['data'], selector(KEY_READ)
                             + word(converted['args'][0]).hex())

    def test_source_success_requires_actual_route_and_no_mismatch(self):
        valid = {'routes': ['source'], 'mismatches': {'source': []}}
        require_source(valid)
        for invalid in ({}, {'routes': [], 'mismatches': {'source': []}},
                        {'routes': ['source'], 'mismatches': {}},
                        {'routes': ['source', 'model'], 'mismatches': {'source': [], 'model': []}},
                        {'routes': ['source'], 'mismatches': {'source': [{'fields': ['data']}]}}):
            with self.assertRaises(HarnessError):
                require_source(invalid)

    def test_mutation_needs_return_data_mismatch_not_failure_or_state_corruption(self):
        for fields in ([], ['status'], ['storage'], ['data', 'status'], ['data', 'storage']):
            rows = [{'fields': fields}] if fields else []
            with self.subTest(fields=fields), self.assertRaises(HarnessError):
                require_source({'routes': ['source'], 'mismatches': {'source': rows}}, True)
        require_source({'routes': ['source'],
                        'mismatches': {'source': [{'fields': ['data']}]}}, True)

    def test_combined_gate_requires_all_executed_routes_against_independent_observations(self):
        valid = {'routes': ['source', 'model', 'compiled'],
                 'mismatches': {route: [] for route in ('source', 'model', 'compiled')},
                 'divergences': []}
        require_combined(valid)
        for route in valid['routes']:
            for defect in ('absent', 'mismatch', 'divergence'):
                result = copy.deepcopy(valid)
                if defect == 'absent':
                    result['routes'].remove(route)
                    del result['mismatches'][route]
                elif defect == 'mismatch':
                    result['mismatches'][route] = [{'fields': ['data']}]
                else:
                    result['divergences'] = ['different result']
                with self.subTest(route=route, defect=defect), self.assertRaises(HarnessError):
                    require_combined(result)

    def test_combined_mutants_must_change_data_on_every_route_without_state_corruption(self):
        valid = {'routes': ['source', 'model', 'compiled'],
                 'mismatches': {route: [{'fields': ['data']}] for route in
                                ('source', 'model', 'compiled')}, 'divergences': []}
        require_combined(valid, True)
        for route in valid['routes']:
            for fields in ([], ['status'], ['data', 'storage']):
                result = copy.deepcopy(valid)
                result['mismatches'][route] = [{'fields': fields}] if fields else []
                with self.subTest(route=route, fields=fields), self.assertRaises(HarnessError):
                    require_combined(result, True)

    def test_unexpected_admission_or_different_rejection_cannot_pass(self):
        for observation in ({}, {'status': 'admitted'},
                            {'status': 'rejected', 'reason': 'evaluation failed'}):
            with self.assertRaises(HarnessError):
                require_rejection(observation, COMPOSITION_REJECTION)

    def test_rejection_matrix_is_distinct_and_source_mutations_leave_fixture_unchanged(self):
        source = FIXTURE.read_text()
        cases = list(rejected_sources(source))
        self.assertEqual(len(cases), 10)
        self.assertEqual(len({text for _, text, _, _ in cases}), 10)
        for name, text, signature, _ in cases:
            self.assertNotEqual(text, source)
            self.assertEqual(signature, DIGEST if name in {
                'partial-cleanup', 'dirty-hash', 'dirty-read', 'unknown-cleanup-alias',
                'abi-allocation'} else READ)
        with self.assertRaises(HarnessError):
            list(rejected_sources(source.replace('mstore(base, 0)', 'mstore(base, 1)')))
        variants = source_variants(source)
        self.assertEqual(variants['original'], source)
        self.assertEqual(FIXTURE.read_text(), source)


if __name__ == '__main__':
    unittest.main()
