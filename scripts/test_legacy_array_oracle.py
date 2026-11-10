"""Requirement-level checks of the independent legacy array observation oracle."""
import unittest

from eth_abi import encode
from eth_utils import keccak
from solidity_differential.check_legacy_address_arrays import decode, payload, scenario, words
from solidity_differential.check_legacy_state_transitions import error, word

ACCOUNT = '0x' + '42' * 20
LAYOUT = {'storage': [{'label': name, 'slot': str(i)}
                      for i, name in enumerate(('links', 'count', 'limit'))]}


class LegacyArrayOracleTests(unittest.TestCase):
    def test_dirty_words_are_cleaned_and_shared_tails_are_allowed(self):
        self.assertEqual(decode(words([64, 64, 1, (1 << 200) + 23]), fold=True), ([23], [23]))

    def test_invalid_tail_does_not_become_an_empty_array(self):
        for data in (words([64, 1, 1]), words([64, 1, 2**32]), words([2**32, 1, 0])):
            self.assertIsNone(decode(data))
        self.assertEqual(decode(payload([], 1)), ([], 1))

    def observations(self):
        initial, calls, expected = scenario('links', ACCOUNT, LAYOUT, dirty_mappings=True)
        return initial, {tx['label']: expected[tx['id']] for tx in calls}

    def test_late_errors_roll_back_prior_links_and_events(self):
        initial, rows = self.observations()
        for label, reason in (('late-zero', 'key'), ('adjacent', 'key'), ('duplicate', 'duplicate')):
            row = rows[label]
            self.assertEqual(row['data'], error(reason))
            self.assertEqual(row['storage'], [list(item) for item in initial])
            self.assertEqual(row['events'], [])

    def test_success_commits_order_count_threshold_and_preserves_dirty_bits(self):
        _, rows = self.observations()
        row = rows['dirty-initialize']
        storage = {int(slot, 16): int(value, 16) for _, slot, value in row['storage']}
        for key, successor in ((1, 21), (21, 22), (22, 23), (23, 1)):
            slot = int.from_bytes(keccak(encode(['uint256', 'uint256'], [key, 0])), 'big')
            self.assertEqual(storage[slot], (0xABCDE << 160) + successor)
        self.assertEqual((storage[1], storage[2], storage[9999]), (3, 2, 0xABCDE))
        self.assertEqual([log['topics'][1] for log in row['events']], [word(x) for x in (21, 22, 23)])

    def test_reinitialization_error_precedes_body_guards_but_follows_decoding(self):
        _, rows = self.observations()
        for label in ('reinitialize', 'reinitialize-error-order'):
            self.assertEqual(rows[label]['data'], error('initialized'))
            self.assertEqual(rows[label]['storage'], rows['dirty-initialize']['storage'])
        self.assertEqual(rows['decode-before-body']['data'], '0x')
        self.assertEqual(rows['decode-before-body']['status'], 'revert')


if __name__ == '__main__':
    unittest.main()
