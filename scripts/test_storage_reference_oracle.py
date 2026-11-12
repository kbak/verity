"""Adversarial tests for independent storage expectations and discovery/replay completeness."""
import copy
import hashlib
import json
from pathlib import Path
import unittest
from unittest.mock import patch

from solidity_differential.anvil import SequenceAdapter
from solidity_differential.check_packed_memory_hash import CONCRETE_HASH, word
from solidity_differential.engine import HarnessError
from solidity_differential.stateful import ROUTES
from solidity_differential.storage_reference_oracle import (
    COUNT_MASK, PACKED_ARCHIVE_SHA256, SLOT_ANCHORS, compare_expected, hexword, record_slot, replay_expected, specification,
)

TARGET = '0x' + '12' * 20
SENDER = '0x' + '34' * 20


class StorageReferenceTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.spec = specification(TARGET, SENDER)

    def observations(self):
        return [{**copy.deepcopy(row), 'touched': []} for row in self.spec['expected']]

    def adapter(self, rows=None):
        observations = rows if rows is not None else self.observations()
        def run(txs, plan):
            result = copy.deepcopy(observations)
            for row, slots in zip(result, plan):
                present = {(a, s) for a, s, _ in row['storage']}
                row['storage'] += [[a, s, hexword(0)] for a, s in slots if (a, s) not in present]
            return result
        return run

    def test_literal_mapping_anchors_and_struct_relative_offset(self):
        for base in (2, 3):
            self.assertEqual(hexword(record_slot(CONCRETE_HASH, base))[2:], SLOT_ANCHORS[base])
        shifted = specification(TARGET, SENDER, 1)
        self.assertNotEqual(self.spec['recordSlots'], shifted['recordSlots'])
        self.assertEqual(self.spec['packedExpectations'], shifted['packedExpectations'])
        self.assertEqual(len(self.spec['packedExpectations']), 54)

    def test_packed_expectation_archive_is_byte_unchanged(self):
        archive = (json.dumps(self.spec['packedExpectations'], indent=2) + '\n').encode()
        self.assertEqual(hashlib.sha256(archive).hexdigest(), PACKED_ARCHIVE_SHA256)

    def test_uint128_update_preserves_padding_other_fields_and_other_keys(self):
        initial = {(a, s): v for a, s, v in self.spec['initialStorage']}
        row = self.spec['expected'][6]  # First write, after six reads.
        after = {(a, s): v for a, s, v in row['storage']}
        slot = (TARGET, self.spec['recordSlots'][0])
        self.assertEqual(int(after[slot], 16), (0xcafe << 128) | COUNT_MASK)
        self.assertEqual({k: v for k, v in after.items() if k != slot},
                         {k: v for k, v in initial.items() if k != slot})
        self.assertEqual(bytes.fromhex(row['data'][2:]), word(COUNT_MASK) + word(101) + word(201))

    def test_exact_rollback_for_existing_and_absent_keys(self):
        failures = 0
        for before, after in zip(self.spec['expected'], self.spec['expected'][1:]):
            if after['status'] == 'revert':
                failures += 1
                self.assertEqual(after['storage'], before['storage'])
                self.assertEqual(after['events'], [])
                self.assertEqual(len(bytes.fromhex(after['data'][2:])), 36)
        self.assertEqual(failures, 3)

    def test_all_routes_agreeing_on_wrong_state_still_fails_independent_oracle(self):
        rows = self.observations()
        rows[0]['storage'][0][2] = hexword(0)
        result = replay_expected(self.spec, {r: self.adapter(rows) for r in ROUTES},
                                 required_routes=ROUTES)
        for route in ROUTES:
            self.assertIn('storage', result['mismatches'][route][0]['fields'])

    def test_exact_return_revert_log_and_storage_observations(self):
        for field, changed in [('data', '0x00'), ('status', 'invalid'),
                               ('events', [{'address': TARGET, 'topics': [], 'data': '0x'}])]:
            rows = self.observations()
            rows[0][field] = changed
            if field == 'status':
                rows[0]['data'] = '0x'
            self.assertIn(field, compare_expected(self.spec, rows)[0]['fields'])
        rows = self.observations()
        failed = next(i for i, row in enumerate(rows) if row['status'] == 'revert')
        rows[failed]['data'] = '0x'
        self.assertEqual(compare_expected(self.spec, rows)[0]['fields'], ['data'])

    def test_missing_sentinel_or_result_is_infrastructure_failure(self):
        for edit in (lambda rows: rows.pop(), lambda rows: rows[0]['storage'].pop(),
                     lambda rows: rows[0].update(id='wrong')):
            rows = self.observations()
            edit(rows)
            with self.assertRaises(HarnessError):
                compare_expected(self.spec, rows)

    def test_unknown_nonzero_slot_is_not_ignored(self):
        rows = self.observations()
        for row in rows:
            row['storage'].append([TARGET, hexword(999), hexword(1)])
        self.assertTrue(all('storage' in r['fields'] for r in compare_expected(self.spec, rows)))

    def test_cumulative_union_includes_every_route_and_reverted_access(self):
        adapters = {}
        revert = next(i for i, row in enumerate(self.spec['expected']) if row['status'] == 'revert')
        for index, route in enumerate(ROUTES):
            rows = self.observations()
            extra = [TARGET, hexword(999 + index)]
            rows[revert]['touched'] = [extra]
            rows[revert]['storage'].append(extra + [hexword(0)])
            adapters[route] = self.adapter(rows)
        result = replay_expected(self.spec, adapters, required_routes=ROUTES)
        extras = [[TARGET, hexword(999 + i)] for i in range(3)]
        for plan in result['slots'][revert:]:
            for slot in extras:
                self.assertIn(slot, plan)
        self.assertTrue(all(not rows for rows in result['mismatches'].values()))

    def test_missing_cross_route_observation_is_not_a_mutation_witness(self):
        rows = self.observations()
        rows[0]['touched'] = [[TARGET, hexword(999)]]
        rows[0]['storage'].append([TARGET, hexword(999), hexword(0)])
        adapters = {'source': self.adapter(rows), 'model': lambda txs, plan: self.observations(),
                    'compiled': self.adapter()}
        with self.assertRaisesRegex(HarnessError, 'cross-route'):
            replay_expected(self.spec, adapters, required_routes=ROUTES)

    def test_discovery_replay_nondeterminism_is_infrastructure_failure(self):
        calls = 0
        def unstable(txs, plan):
            nonlocal calls
            calls += 1
            rows = self.adapter()(txs, plan)
            if calls == 2:
                rows[0]['data'] = '0x00'
            return rows
        with self.assertRaisesRegex(HarnessError, 'changed between'):
            replay_expected(self.spec, {'source': unstable}, required_routes=('source',))

    def test_missing_model_routes_cannot_pass_full_gate(self):
        with self.assertRaisesRegex(HarnessError, 'required execution routes'):
            replay_expected(self.spec, {'source': self.adapter()}, required_routes=ROUTES)
        result = replay_expected(self.spec, {'source': self.adapter()}, required_routes=('source',))
        self.assertEqual(result['routes'], ['source'])

    def test_cancun_sequence_selection_preserves_osaka_default(self):
        for options, expected in [({}, 'osaka'), ({'hardfork': 'cancun'}, 'cancun')]:
            adapter = SequenceAdapter(Path('/tmp/storage-reference-adapter-test'), [], **options)
            with patch('solidity_differential.anvil.Anvil', side_effect=HarnessError('stop')) as node:
                with self.assertRaisesRegex(HarnessError, 'stop'):
                    adapter([], [])
                node.assert_called_once_with(adapter.directory / '0', hardfork=expected)
        with self.assertRaisesRegex(HarnessError, 'unsupported sequence hardfork'):
            SequenceAdapter(Path('/tmp/storage-reference-adapter-test'), [], hardfork='unknown')


if __name__ == '__main__':
    unittest.main()
