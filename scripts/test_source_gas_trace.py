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

    def test_implicit_value_call_gas_site(self):
        def node(names):
            return {'nodeType': 'FunctionCall', 'src': '40:21:0',
                    'expression': {'nodeType': 'FunctionCallOptions', 'names': names,
                                   'expression': {'memberName': 'call'}}}
        self.assertEqual(source_sites(node(['value'])), {'40:21:0'})
        self.assertEqual(source_sites(node(['value', 'gas'])), set())

    def test_typed_gas_site_requires_resolved_nonpayable_void_declaration(self):
        import copy
        declaration = {'id': 17, 'nodeType': 'FunctionDefinition',
                       'stateMutability': 'nonpayable', 'returnParameters': {'parameters': []}}
        call = {'nodeType': 'FunctionCall', 'src': '80:42:0', 'expression': {
            'nodeType': 'MemberAccess', 'referencedDeclaration': 17,
            'typeDescriptions': {'typeString': 'function (uint256,bytes memory) external'}}}
        self.assertEqual(source_sites([call, declaration]), {'80:42:0'})
        self.assertEqual(source_sites(call), set())
        for mutability in ['view', 'pure', 'payable']:
            changed = {**declaration, 'stateMutability': mutability}
            self.assertEqual(source_sites([call, changed]), set())
        changed = {**declaration, 'returnParameters': {'parameters': [{'type': 'bool'}]}}
        self.assertEqual(source_sites([call, changed]), set())
        internal = copy.deepcopy(call)
        internal['expression']['typeDescriptions']['typeString'] = 'function () internal'
        self.assertEqual(source_sites([internal, declaration]), set())

    def test_static_and_recovery_sites_require_resolved_calls(self):
        decl = {'id': 19, 'nodeType': 'FunctionDefinition', 'stateMutability': 'view',
                'returnParameters': {'parameters': [{'type': 'bytes4'}]}}
        call = {'nodeType': 'FunctionCall', 'src': '20:10:0', 'expression': {
            'nodeType': 'MemberAccess', 'referencedDeclaration': 19,
            'typeDescriptions': {'typeString': 'function () view external returns (bytes4)'}}}
        self.assertEqual(source_sites([call, decl]), {'20:10:0'})
        self.assertEqual(source_sites(call), set())
        recovery = {'nodeType': 'FunctionCall', 'src': '30:10:0', 'expression': {
            'nodeType': 'Identifier', 'name': 'ecrecover', 'referencedDeclaration': -5}}
        self.assertEqual(source_sites(recovery), {'30:10:0'})
        recovery['expression']['referencedDeclaration'] = 5
        self.assertEqual(source_sites(recovery), set())

    def test_staticcall_uses_six_operands_and_zero_value(self):
        trace = {'structLogs': [
            {'depth': 1, 'pc': 0, 'op': 'GAS', 'gas': 10000, 'gasCost': 2,
             'stack': [], 'memory': []},
            {'depth': 1, 'pc': 1, 'op': 'STATICCALL', 'gas': 9998, 'gasCost': 103,
             'stack': ['20', '0', '0', '0', '1', '270e'], 'memory': []},
            {'depth': 1, 'pc': 2, 'op': 'STOP', 'gas': 6895, 'gasCost': 0,
             'stack': ['1'], 'memory': []}]}
        call = {'gas': '0x2710', 'from': '0x100', 'to': '0x200', 'value': '0x99',
                'calls': [{'type': 'STATICCALL', 'to': '0x1', 'gas': '0x260d',
                           'gasUsed': '0xbb8', 'input': '0x', 'output': '0x'}]}
        meter, _, _ = evidence(trace, call, {}, '5afa00', '0:1:0;;', {'0:1:0'}, coinbase=0)
        event = meter['events'][1]
        self.assertEqual((event['kind'], event['value']), ('staticcall', 0))
        self.assertFalse(event['context']['transfersValue'])
        self.assertTrue(event['context']['targetWarm'])
        self.assertEqual(event['context']['outputSize'], 32)
        self.assertEqual(event['context']['inputSize'], 0)
        self.assertEqual(event['gasLeft'], 9741 - 3000)

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
