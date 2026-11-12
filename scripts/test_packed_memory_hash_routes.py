"""Adversarial checks for pinned profiles, actual observations and mutation evidence."""
import copy
import json
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

from keccak256 import keccak_256, selector
from solidity_differential import check_packed_memory_hash_routes as campaign
from solidity_differential import hash_execution as execution
from solidity_differential.check_packed_memory_hash import (
    CONCRETE_HASH, CONCRETE_PREIMAGE, SETTINGS, SHIFTS, packed_preimage, vectors,
)
from solidity_differential.engine import HarnessError


class PackedHashRouteTests(unittest.TestCase):
    def setUp(self):
        self.cases = campaign.control_cases()
        self.rows = [{'id': row['id'], 'status': 'ok', 'data': row['expected'],
                      'words': [str(int(row['expected'], 16))], 'storage': []}
                     for row in self.cases]

    def test_original_expectation_inventory_is_preserved(self):
        expected = campaign.expectations()
        self.assertEqual(expected, [
            {'values': list(map(str, row)), 'preimage': packed_preimage(*row).hex(),
             'hash': keccak_256(packed_preimage(*row)).hex()} for row in vectors()])
        self.assertEqual((expected[0]['preimage'], expected[0]['hash']),
                         (CONCRETE_PREIMAGE, CONCRETE_HASH))
        for root in ('digest', 'inspect'):
            cases = campaign.packed_cases(root, expected)
            self.assertEqual(len(cases), len(expected) * (1 if root == 'digest' else len(SHIFTS)))
            execution.validate_cases(campaign.ROOTS[root], cases)
        self.assertEqual(self.cases[0]['expected'], '0x' + campaign.ZERO_WORD_HASH)

    def test_selector_arguments_and_initial_state_must_match(self):
        execution.validate_cases('digest(bytes32)', self.cases)
        mutations = [
            {'calldata': '0x00000000' + '00' * 32}, {'args': ['2']},
            {'storage': [['0', '1']]}, {'observe': ['0']},
            {'timestamp': '0'}, {'args': [str(2**256)]},
        ]
        for mutation in mutations:
            bad = copy.deepcopy(self.cases)
            bad[0].update(mutation)
            with self.subTest(mutation=mutation), self.assertRaises(HarnessError):
                execution.validate_cases('digest(bytes32)', bad)

    def test_agreement_between_wrong_routes_cannot_pass_independent_expectation(self):
        bad = copy.deepcopy(self.rows)
        for row in bad:
            row['data'] = '0x' + 'aa' * 32
        execution.compare_routes({'source': bad, 'denote': bad, 'compiled': bad}, self.cases)
        with self.assertRaises(HarnessError):
            execution.compare_expectations(bad, self.cases)

    def test_mutation_requires_every_hash_to_change(self):
        bad = copy.deepcopy(self.rows)
        for row in bad:
            row['data'] = '0x' + 'aa' * 32
        self.assertEqual(execution.compare_expectations(bad, self.cases, True)['hashMismatches'],
                         [row['id'] for row in self.cases])
        bad[0] = self.rows[0]
        with self.assertRaises(HarnessError):
            execution.compare_expectations(bad, self.cases, True)
        inspect = campaign.packed_cases('inspect', campaign.expectations())[:1]
        row = {'id': inspect[0]['id'], 'status': 'ok',
               'data': inspect[0]['expected'][:-2] + '00'}
        with self.assertRaises(HarnessError):
            execution.compare_expectations([row], inspect, True)

    def test_failures_and_incomplete_outputs_are_never_mutation_evidence(self):
        bad_rows = [None, [], self.rows[:-1], self.rows + [self.rows[0]],
                    self.rows[::-1], [self.rows[0]] * len(self.rows)]
        for change in ({'status': 'revert'}, {'status': 'invalid'}, {'data': None},
                       {'data': '0x0'}, {'data': '0x'}, {'data': '0x' + 'aa' * 64}):
            bad = copy.deepcopy(self.rows)
            bad[0].update(change)
            bad_rows.append(bad)
        for rows in bad_rows:
            with self.subTest(rows=rows and str(rows[0])[:100]), self.assertRaises(HarnessError):
                execution.compare_expectations(rows, self.cases, True)

    def test_route_divergence_is_not_hidden_by_successful_mutation_detection(self):
        bad = copy.deepcopy(self.rows)
        bad[0]['data'] = '0x' + 'aa' * 32
        with self.assertRaises(HarnessError):
            execution.compare_routes({'source': self.rows, 'denote': bad,
                                      'compiled': self.rows}, self.cases)

    def test_missing_route_cannot_count_as_agreement(self):
        for missing in ('source', 'denote', 'compiled'):
            routes = {name: self.rows for name in ('source', 'denote', 'compiled')
                      if name != missing}
            with self.subTest(missing=missing), self.assertRaises(HarnessError):
                execution.compare_routes(routes, self.cases)

    def snapshot(self):
        return {'model': 'model', 'report': 'report', 'digest': 'a' * 64, 'yul': 'object',
                'compilerProof': 'unavailable', 'context': 'context', 'function': 'digest',
                'targetFork': 'cancun', 'selector': int(selector('digest(bytes32)'), 16),
                'denoteCovered': True, 'solcLongVersion': 'pinned', 'solcSha256': 'sha',
                'params': ['tag'], 'settings': json.dumps(SETTINGS), 'results': self.rows}

    def test_model_provenance_profile_and_byte_observations_are_required(self):
        compiler = {'longVersion': 'pinned', 'sha256': 'sha'}
        snapshot = self.snapshot()
        execution.validate_snapshot(snapshot, 'digest(bytes32)', self.cases, compiler)
        mutations = [{'targetFork': 'osaka'}, {'selector': 0x12345678},
                     {'solcLongVersion': 'other'}, {'solcSha256': 'other'}, {'digest': ''},
                     {'model': ''}, {'report': ''}, {'params': []}, {'results': []},
                     {'settings': json.dumps({**SETTINGS, 'evmVersion': 'osaka'})},
                     {'settings': json.dumps({**SETTINGS, 'remappings': ['x=y']})}]
        for mutation in mutations:
            with self.subTest(mutation=mutation), self.assertRaises(HarnessError):
                execution.validate_snapshot({**snapshot, **mutation}, 'digest(bytes32)',
                                            self.cases, compiler)
        for mutation in ({'words': ['0']}, {'storage': ['1']}):
            bad = copy.deepcopy(snapshot)
            bad['results'][0].update(mutation)
            with self.subTest(mutation=mutation), self.assertRaises(HarnessError):
                execution.validate_snapshot(bad, 'digest(bytes32)', self.cases, compiler)

    def test_source_selector_or_mutability_drift_is_rejected(self):
        signature = 'digest(bytes32)'
        built = {'abi': [{'type': 'function', 'name': 'digest', 'stateMutability': 'pure',
                         'inputs': [{'type': 'bytes32'}], 'outputs': [{'type': 'bytes32'}]}],
                 'evm': {'methodIdentifiers': {signature: selector(signature)[2:]}}}
        execution.verify_abi(built, signature, self.cases)
        for change in ('selector', 'mutability'):
            bad = copy.deepcopy(built)
            if change == 'selector':
                bad['evm']['methodIdentifiers'][signature] = '12345678'
            else:
                bad['abi'][0]['stateMutability'] = 'view'
            with self.subTest(change=change), self.assertRaises(HarnessError):
                execution.verify_abi(bad, signature, self.cases)

    def test_rejected_import_is_blocked_without_substitute_execution(self):
        with tempfile.TemporaryDirectory() as tmp, \
                patch.object(campaign, 'verify_abi'), \
                patch.object(campaign, 'execute_evm', return_value=(self.rows, {})), \
                patch.object(campaign, 'import_root', return_value={'status': 'rejected'}), \
                patch.object(campaign, 'snapshot_root') as snapshot:
            row = campaign.run_root(Path(tmp) / 'root', 'WordHash.sol', 'WordHash',
                                    'digest(bytes32)', self.cases, {}, None, {}, False)
            self.assertEqual(row['execution']['status'], 'blocked')
            self.assertEqual(row['execution']['semanticAgreement'], 'not tested')
            snapshot.assert_not_called()

    def test_failed_deployment_is_an_infrastructure_error(self):
        with tempfile.TemporaryDirectory() as tmp, patch.object(execution, 'Anvil') as adapter:
            node = adapter.return_value.__enter__.return_value
            node.rpc.side_effect = [['0x' + '01' * 20], '0x0', True]
            node.transact.return_value = {'receipt': {'status': '0x0'}}
            built = {'evm': {'bytecode': {'object': '00'}, 'deployedBytecode': {'object': '00'}}}
            with self.assertRaisesRegex(HarnessError, 'deployment failed'):
                execution.execute_evm(Path(tmp) / 'evm', built, self.cases)

    def test_tool_errors_use_failure_exit_not_required_admission_exit(self):
        for error in (HarnessError('RPC failure'), OSError('compiler missing'),
                      subprocess.TimeoutExpired('turbo-lean', 10),
                      subprocess.CalledProcessError(-9, 'anvil')):
            with self.subTest(error=error), \
                    patch('sys.argv', ['runner', '--output', '/tmp/unused']), \
                    patch.object(campaign, 'run', side_effect=error):
                self.assertEqual(campaign.main(), 2)
        with patch('sys.argv', ['runner', '--output', '/tmp/unused', '--require-admission']), \
                patch.object(campaign, 'run', return_value=1):
            self.assertEqual(campaign.main(), 1)


if __name__ == '__main__':
    unittest.main()
