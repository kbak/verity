"""Independent list requirements and exceptional-halt trace admission."""
import copy
import unittest

from solidity_differential.anvil import Anvil
from solidity_differential.engine import HarnessError
from solidity_differential.check_legacy_memory_arrays import enumeration, encoded_array


class MemoryArrayOracleTests(unittest.TestCase):
    def test_empty_and_zero_capacity_differ(self):
        self.assertEqual(enumeration(0, {1: 1}), ('ok', []))
        self.assertEqual(enumeration(0, {1: 9}), ('invalid', []))

    def test_order_dirty_addresses_and_zero_tail(self):
        links = {1: (1 << 200) + 9, 9: 8, 8: 1}
        self.assertEqual(enumeration(4, links), ('ok', [9, 8, 0, 0]))
        self.assertEqual(enumeration(1, links), ('invalid', []))

    def test_cycle_and_missing_sentinel_fail_at_capacity(self):
        self.assertEqual(enumeration(4, {1: 9, 9: 8, 8: 9}), ('invalid', []))
        self.assertEqual(enumeration(4, {1: 9}), ('invalid', []))

    def test_abi_v1_return_preserves_dirty_words(self):
        self.assertTrue(encoded_array([2**256-1]).endswith("ff" * 32))

    def test_allocation_overflow_is_empty_revert(self):
        self.assertEqual(enumeration(2**64, {1: 1}), ('revert', []))
        self.assertEqual(enumeration(2**256-1, {1: 1}), ('revert', []))


class InvalidTraceTests(unittest.TestCase):
    def record(self):
        return {'transaction': {'gas': '0x186a0'},
                'receipt': {'status': '0x0', 'gasUsed': '0x186a0', 'logs': [], 'blockNumber': '0x1'},
                'call': {'error': 'invalid opcode: INVALID'}, 'prestate': {},
                'exceptionalTrace': {'failed': True, 'structLogs': [{'op': 'INVALID', 'depth': 1}]}}

    def observe(self, record):
        return Anvil('/tmp/unused-trace-observer').observe(record, 'test')

    def test_requires_invalid_opcode_and_consumed_allowance(self):
        self.assertEqual(self.observe(self.record())['status'], 'invalid')
        for path, value in [(('call', 'error'), 'out of gas'),
                            (('call', 'error'), 'stack underflow'),
                            (('receipt', 'gasUsed'), '0x5208'),
                            (('exceptionalTrace', 'failed'), False),
                            (('exceptionalTrace', 'structLogs'), [{'op': 'JUMP', 'depth': 1}]),
                            (('exceptionalTrace', 'structLogs'), [{'op': 'INVALID', 'depth': 2}])]:
            record = copy.deepcopy(self.record())
            record[path[0]][path[1]] = value
            with self.subTest(path=path, value=value), self.assertRaises(HarnessError):
                self.observe(record)

    def test_empty_revert_remains_distinct(self):
        record = self.record()
        record['call']['error'] = 'execution reverted'
        record['receipt']['gasUsed'] = '0x520e'
        self.assertEqual(self.observe(record)['status'], 'revert')

    def test_invalid_cannot_supply_return_bytes(self):
        record = self.record()
        record['call']['output'] = '0x01'
        with self.assertRaises(HarnessError):
            self.observe(record)
