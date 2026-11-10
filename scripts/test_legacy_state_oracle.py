"""Requirement-level checks for the independent legacy state/event oracle."""
import unittest

from eth_utils import keccak
from solidity_differential.check_legacy_state_transitions import MASK, error, scenario, word

ACCOUNT = '0x' + '42' * 20
LAYOUT = {'storage': [{'label': name, 'slot': str(i)}
                      for i, name in enumerate(('links', 'count', 'limit'))]}


class LegacyStateOracleTests(unittest.TestCase):
    def observations(self, **kwargs):
        initial, calls, expected = scenario('links', ACCOUNT, LAYOUT, random_cases=0, **kwargs)
        return initial, calls, {tx['label']: expected[tx['id']] for tx in calls}

    def test_unauthorized_preserves_every_observed_slot(self):
        initial, _, rows = self.observations()
        row = rows['unauthorized-threshold']
        self.assertEqual(row['status'], 'revert')
        self.assertEqual(row['data'], error('context'))
        self.assertEqual(row['events'], [])
        self.assertEqual(row['storage'], [list(item) for item in initial])

    def test_failed_nested_update_rolls_back_mapping_count_and_logs(self):
        _, _, rows = self.observations()
        for label, reason in [('rollback-zero', 'zero'), ('rollback-bound', 'bound')]:
            with self.subTest(label=label):
                self.assertEqual(rows[label]['storage'], rows['limit-3']['storage'])
                self.assertEqual(rows[label]['events'], [])
                self.assertEqual(rows[label]['data'], error(reason))

    def test_noop_limit_still_emits_and_insert_event_is_indexed(self):
        _, _, rows = self.observations()
        self.assertEqual(len(rows['limit-3']['events']), 1)
        log = rows['insert-same-limit']['events'][0]
        self.assertEqual(log['data'], '0x')
        self.assertEqual(log['topics'], ['0x' + keccak(text='Inserted(address)').hex(), word(20)])
        self.assertEqual(len(rows['insert-change-limit']['events']), 2)

    def test_zero_and_upper_bound_order_in_empty_initial_world(self):
        _, _, rows = self.observations(initial_count=0)
        self.assertEqual(rows['limit-0']['data'], error('zero'))
        self.assertEqual(rows['limit-1']['data'], error('bound'))

    def test_wide_wrap_can_succeed_without_changing_limit(self):
        _, _, rows = self.observations(initial_count=MASK)
        row = rows['persist-wrapped-count']
        self.assertEqual(row['status'], 'ok')
        storage = {int(slot, 16): int(value, 16) for _, slot, value in row['storage']}
        self.assertEqual(storage[1], 0)
        self.assertEqual(storage[2], MASK)

    def test_packed_high_bits_survive_additions_and_dirty_abi_is_cleaned(self):
        initial, _, rows = self.observations(dirty_mappings=True)
        high_slots = {slot for _, slot, value in initial if int(value, 16) >> 160 == 0xABCDE}
        row = rows['dirty-address-abi']
        self.assertEqual(row['status'], 'ok')
        self.assertEqual(row['events'][0]['topics'][1], word(29))
        for _, slot, value in row['storage']:
            if slot in high_slots:
                self.assertEqual(int(value, 16) >> 160, 0xABCDE)


if __name__ == '__main__':
    unittest.main()
