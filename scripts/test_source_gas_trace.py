"""Source evidence must identify actual opcode boundaries and complete frames."""
import unittest

from solidity_differential.engine import HarnessError
from solidity_differential.source_gas_trace import evidence, source_map, source_sites


class SourceGasTraceTests(unittest.TestCase):
    def test_push_bytes_are_not_instruction_sites(self):
        code, positions = source_map('605a5a00', '1:2:0;9:3:0;')
        self.assertEqual(code[1], 0x5a)
        self.assertNotIn(1, positions)
        self.assertEqual(positions, {0: '1:2:0', 2: '9:3:0', 3: '9:3:0'})

    def test_shadowed_identifier_is_not_builtin(self):
        def node(ident):
            return {'nodeType': 'FunctionCall', 'src': str(ident),
                    'expression': {'nodeType': 'Identifier', 'name': 'gasleft',
                                   'referencedDeclaration': ident}}
        self.assertEqual(source_sites([node(-1), node(4)]), {'-1'})

    def fixture(self):
        logs = [{'depth': 1, 'pc': 0, 'op': 'GAS', 'gas': 100, 'gasCost': 2,
                 'stack': [], 'memory': []},
                {'depth': 1, 'pc': 1, 'op': 'STOP', 'gas': 98, 'gasCost': 0,
                 'stack': ['62'], 'memory': []}]
        return {'structLogs': logs}, {'gas': '0x64', 'from': '0x100', 'to': '0x200'}

    def test_complete_source_read(self):
        trace, call = self.fixture()
        meter, left, rows = evidence(trace, call, {}, '5a00', '0:1:0;', {'0:1:0'}, coinbase=0)
        self.assertEqual(left, 98)
        self.assertEqual(meter['events'][0], {'type': 'read', 'cost': 0, 'site': '0:1:0'})
        self.assertEqual(rows[0], {'kind': 'read', 'remaining': 98})

    def test_wrong_runtime_opcode_is_rejected(self):
        trace, call = self.fixture()
        with self.assertRaisesRegex(HarnessError, 'GAS opcode'):
            evidence(trace, call, {}, '5800', '0:1:0;', {'0:1:0'}, coinbase=0)

    def test_root_oog_is_not_a_zero_gas_success(self):
        trace, call = self.fixture()
        trace['structLogs'].pop()
        with self.assertRaisesRegex(HarnessError, 'OOG/unknown halt'):
            evidence(trace, call, {}, '5a00', '0:1:0;', {'0:1:0'}, coinbase=0)

    def test_incomplete_or_disagreeing_trace_is_rejected(self):
        trace, call = self.fixture()
        call['gas'] = '0x65'
        with self.assertRaisesRegex(HarnessError, 'disagree on initial gas'):
            evidence(trace, call, {}, '5a00', '0:1:0;', {'0:1:0'}, coinbase=0)

    def test_nested_account_access_needs_journal(self):
        trace, call = self.fixture()
        trace['structLogs'].insert(1, {'depth': 2, 'op': 'BALANCE'})
        with self.assertRaisesRegex(HarnessError, 'journaled warmth'):
            evidence(trace, call, {}, '5a00', '0:1:0;', {'0:1:0'}, coinbase=0)

    def test_unmatched_child_is_rejected(self):
        trace, call = self.fixture()
        call['calls'] = [{'type': 'STATICCALL'}]
        with self.assertRaisesRegex(HarnessError, 'unmatched original child'):
            evidence(trace, call, {}, '5a00', '0:1:0;', {'0:1:0'}, coinbase=0)


if __name__ == '__main__':
    unittest.main()
