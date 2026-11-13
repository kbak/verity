"""Adversarial checks for caller-liveness evidence and frozen expectation reuse."""
import copy
import tempfile
import unittest
from pathlib import Path
from unittest.mock import patch

from solidity_differential.check_packed_memory_hash import SHIFTS
from solidity_differential.check_packed_memory_hash_routes import case
from solidity_differential.check_tail_cleanup_liveness import (
    CONTINUATIONS, FIXTURE, POISONS, REJECTION, SIGNATURE, archive_expectations,
    caller_cases, check_observations, preparation_exit, required_mismatches, source_variants,
)
from solidity_differential.check_packed_storage_read import require_rejection
from solidity_differential.engine import HarnessError
from solidity_differential.pinned_sequence import SENDERS, create_address
from solidity_differential.storage_reference_oracle import specification


class TailCleanupLivenessTests(unittest.TestCase):
    def setUp(self):
        self.expected = specification(create_address(SENDERS[0]), SENDERS[0])['packedExpectations']
        self.cases = caller_cases(self.expected[:1], 'read-before-overwrite')
        self.rows = [{'id': row['id'], 'status': 'ok', 'data': row['expected']}
                     for row in self.cases]

    def exposed_rows(self):
        rows = copy.deepcopy(self.rows)
        for row, want in zip(rows, self.cases):
            if int(want['args'][-2]):
                row['data'] = '0x' + (int(row['data'], 16) ^ 1).to_bytes(32, 'big').hex()
        return rows

    def test_extensions_preserve_every_independent_hash_and_original_inputs(self):
        before = copy.deepcopy(self.expected)
        for name in CONTINUATIONS:
            rows = caller_cases(self.expected, name)
            factor = 2 if name == 'parameter-alias' else 1
            self.assertEqual(len(rows), 54 * len(SHIFTS) * len(POISONS) * factor)
            for row in rows:
                original = self.expected[int(row['id'].split(':')[0])]
                self.assertEqual(row['expected'], '0x' + original['hash'])
                self.assertEqual(row['args'][:4],
                                 [str(int(n) % 2**256) for n in original['values']])
        self.assertEqual(self.expected, before)

    def test_frozen_archives_and_corruption_detection(self):
        with tempfile.TemporaryDirectory() as tmp:
            self.assertEqual(archive_expectations(Path(tmp)), self.expected)
            changed = specification(create_address(SENDERS[0]), SENDERS[0])
            changed['packedExpectations'][0]['hash'] = '00' * 32
            with patch('solidity_differential.check_tail_cleanup_liveness.specification',
                       return_value=changed), self.assertRaises(HarnessError):
                archive_expectations(Path(tmp))

    def test_exposure_inventory_includes_zero_poison_alias_and_byte_boundaries(self):
        rows = [case(f'{poison}:{offset}', SIGNATURE, [0, 0, 0, 0, 0, poison, offset], '00' * 32)
                for poison in (0, 1, 256) for offset in (0, 32)]
        expected = {
            'saved-hash': [], 'overwrite-before-read': [], 'disjoint-tail-read': [],
            'known-alias': [],
            'read-before-overwrite': ['1:0', '1:32', '256:0', '256:32'],
            'insufficient-overwrite': ['1:0', '1:32', '256:0', '256:32'],
            'overlapping-byte-read': ['1:0', '1:32'],
            'parameter-alias': ['1:32', '256:32'],
        }
        for name, ids in expected.items():
            self.assertEqual(required_mismatches(rows, name), ids)
        with self.assertRaises(HarnessError):
            required_mismatches(rows, 'unclassified')

    def test_positive_control_and_required_mutation_detection(self):
        check_observations(self.rows, self.cases, 'saved-hash')
        check_observations(self.exposed_rows(), self.cases, 'read-before-overwrite')
        with self.assertRaises(HarnessError):
            check_observations(self.rows, self.cases, 'read-before-overwrite')
        with self.assertRaises(HarnessError):
            check_observations(self.exposed_rows(), self.cases, 'saved-hash')

    def test_wrong_mismatch_inventory_cannot_count_as_exposure(self):
        for target in (0, 1):
            rows = self.exposed_rows()
            # Index 0 must agree; index 1 must differ. Corrupt either obligation.
            rows[target]['data'] = ('0x' + '00' * 32 if target == 0
                                    else self.cases[target]['expected'])
            with self.assertRaises(HarnessError):
                check_observations(rows, self.cases, 'read-before-overwrite')

    def test_infrastructure_and_missing_observations_never_count_as_detection(self):
        for mutation in ('missing', 'extra', 'reorder', 'duplicate', 'revert', 'size', 'malformed'):
            rows = self.exposed_rows()
            if mutation == 'missing':
                rows.pop()
            elif mutation == 'extra':
                rows.append(rows[-1])
            elif mutation == 'reorder':
                rows.reverse()
            elif mutation == 'duplicate':
                rows[0] = rows[1]
            elif mutation == 'revert':
                rows[0]['status'] = 'revert'
            elif mutation == 'size':
                rows[0]['data'] = '0x00'
            else:
                rows[0]['data'] = 'not hex'
            with self.subTest(mutation=mutation), self.assertRaises(HarnessError):
                check_observations(rows, self.cases, 'read-before-overwrite')

    def test_continuations_cannot_rewrite_helper_or_claim_memory_safety(self):
        source = FIXTURE.read_text()
        prefix, suffix = source.split('            // CALLER_CONTINUATION')
        for text in source_variants(source).values():
            self.assertTrue(text.startswith(prefix))
            self.assertTrue(text.endswith(suffix))
            self.assertNotIn('assembly ("memory-safe")', text)
        for malformed in (source.replace('// CALLER_CONTINUATION', ''), source + source):
            with self.assertRaises(HarnessError):
                source_variants(malformed)
        self.assertEqual(FIXTURE.read_text(), source)

    def test_current_rejection_and_missing_routes_gate_remain_mandatory(self):
        require_rejection({'status': 'rejected', 'reason': REJECTION}, REJECTION)
        for observation in ({'status': 'admitted'},
                            {'status': 'rejected', 'reason': 'tool failure'}):
            with self.assertRaises(HarnessError):
                require_rejection(observation, REJECTION)
        self.assertEqual(preparation_exit(False), 0)
        self.assertEqual(preparation_exit(True), 1)


if __name__ == '__main__':
    unittest.main()
