"""Fail-closed profile, input-identity, real-route and model-mutation checks."""
import copy
import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from keccak256 import selector
from solidity_differential.check_packed_memory_hash import CONCRETE_HASH, SETTINGS, word
from solidity_differential.check_storage_reference_routes import (
    CONTRACT, SIGNATURES, STATE_ARCHIVES, control_inputs, require_outcome,
)
from solidity_differential.engine import HarnessError
from solidity_differential.pinned_sequence import SENDERS, create_address
from solidity_differential.stateful import ROUTES
from solidity_differential.storage_reference_oracle import specification
from solidity_differential import storage_sequence_execution as execution


class StorageRouteTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.spec = specification(create_address(SENDERS[0]), SENDERS[0])

    def test_control_preserves_all_expectations_and_call_environments(self):
        original = copy.deepcopy(self.spec)
        control = control_inputs(self.spec)
        self.assertEqual(self.spec, original)
        for key in original.keys() - {'transactions'}:
            self.assertEqual(control[key], original[key])
        self.assertEqual(control['transactions'][0]['args'], [int(CONCRETE_HASH, 16)])
        for before, after in zip(original['transactions'], control['transactions']):
            for key in before.keys() - {'data', 'args'}:
                self.assertEqual(after[key], before[key])
            self.assertEqual(after['args'][1:], before['args'][4:])
            self.assertEqual(after['data'], selector(SIGNATURES[after['function']])
                             + b''.join(word(n) for n in after['args']).hex())

    def test_full_state_expectation_archives_are_frozen(self):
        for shift in (0, 1):
            spec = specification(create_address(SENDERS[0]), SENDERS[0], shift)
            archive = (json.dumps(spec, indent=2) + '\n').encode()
            self.assertEqual(hashlib.sha256(archive).hexdigest(), STATE_ARCHIVES[shift])

    def test_control_rejects_changed_packed_payload_or_unknown_key(self):
        for field, value in [('data', '0x00000000'), ('args', [1, 2, 3, 4]), ('args', [])]:
            spec = copy.deepcopy(self.spec)
            spec['transactions'][0][field] = value
            with self.assertRaises(HarnessError):
                control_inputs(spec)

    def snapshot(self):
        sigs = list(SIGNATURES.values())
        return {'roots': list(SIGNATURES), 'signatures': sigs,
                'paramCounts': [1, 2, 2, 2, 2],
                'selectors': [int(selector(s), 16) for s in sigs],
                'contract': CONTRACT, 'targetFork': 'cancun', 'denoteCovered': True,
                'mutation': 'none', 'solcLongVersion': 'pinned', 'solcSha256': 'sha',
                'model': 'actual model', 'importedModel': 'actual model', 'report': 'report',
                'digest': 'a' * 64, 'settings': json.dumps(SETTINGS), 'yul': 'actual Yul',
                'compilerProof': ['unavailable'] * 5}

    def validate(self, snapshot, mutation='none'):
        execution.validate_snapshot(snapshot, list(SIGNATURES.values()), CONTRACT,
                                    {'longVersion': 'pinned', 'sha256': 'sha'}, mutation)

    def test_snapshot_requires_all_roots_and_exact_profile(self):
        self.validate(self.snapshot())
        for change in [{'roots': []}, {'signatures': []}, {'paramCounts': [1]},
                       {'selectors': [0] * 5}, {'contract': 'wrong'}, {'targetFork': 'osaka'},
                       {'denoteCovered': False}, {'solcLongVersion': 'other'}, {'solcSha256': ''},
                       {'compilerProof': []}, {'digest': 'not a digest'}, {'yul': ''},
                       {'report': ''}, {'settings': json.dumps([])},
                       {'settings': json.dumps({**SETTINGS, 'evmVersion': 'osaka'})},
                       {'settings': json.dumps({**SETTINGS, 'remappings': ['x=y']})}]:
            with self.subTest(change=change), self.assertRaises(HarnessError):
                self.validate({**self.snapshot(), **change})

    def test_mutation_must_change_the_executed_model_not_only_its_label(self):
        with self.assertRaises(HarnessError):
            self.validate({**self.snapshot(), 'mutation': 'drop-events'}, 'drop-events')
        with self.assertRaises(HarnessError):
            self.validate({**self.snapshot(), 'model': 'mutated'})
        self.validate({**self.snapshot(), 'model': 'mutated', 'mutation': 'drop-events'},
                      'drop-events')

    def outcome(self):
        return {'routes': list(ROUTES), 'mismatches': {r: [] for r in ROUTES}, 'divergences': []}

    def test_success_requires_every_route_and_independent_agreement(self):
        require_outcome(self.outcome())
        for missing in ROUTES:
            bad = self.outcome()
            del bad['mismatches'][missing]
            with self.assertRaises(HarnessError):
                require_outcome(bad)
        bad = self.outcome()
        for route in ROUTES:
            bad['mismatches'][route] = [{'id': 'x', 'fields': ['storage']}]
        with self.assertRaises(HarnessError):
            require_outcome(bad)

    def test_mutation_requires_only_the_requested_executed_route_to_diverge(self):
        for route in ('model', 'compiled'):
            result = self.outcome()
            result['mismatches'][route] = [{'id': 'x', 'fields': ['events']}]
            result['divergences'] = [{'id': 'x'}]
            require_outcome(result, route)
            with self.assertRaises(HarnessError):
                require_outcome(result, 'compiled' if route == 'model' else 'model')
            result['mismatches'][route][0]['fields'] = ['status']
            with self.assertRaises(HarnessError):
                require_outcome(result, route)
        with self.assertRaises(HarnessError):
            require_outcome(self.outcome(), 'model')

    def reply(self, stdout):
        return {'ok': True, 'import_ok': True, 'crashed': False,
                'timed_out': False, 'errors': [], 'stdout': stdout, 'messages': []}

    def test_evaluation_failures_and_incomplete_snapshots_cannot_pass(self):
        marker = execution.SNAPSHOT_MARKER
        good = self.reply(marker + '{}')
        with patch.object(execution, 'evaluate', return_value=(0, good)):
            self.assertEqual(execution.eval_json(Path('probe.lean'), marker), {})
        for code, reply in [(1, good), (0, self.reply('')),
                            (0, self.reply(marker + '{}\n' + marker + '{}')),
                            (0, self.reply(marker + 'bad JSON')),
                            (0, {**good, 'errors': ['failed']}),
                            (0, {**good, 'crashed': True}),
                            (0, {**good, 'timed_out': True}),
                            (0, {**good, 'import_ok': False})]:
            with patch.object(execution, 'evaluate', return_value=(code, reply)), \
                    self.assertRaises(HarnessError):
                execution.eval_json(Path('probe.lean'), marker)

    def test_cached_denote_stdout_supplies_actual_output_without_filesystem_effects(self):
        with tempfile.TemporaryDirectory() as tmp:
            root = Path(tmp)
            driver, input_path, output = (root / n for n in ('Model.lean', 'input.json', 'output.json'))
            driver.write_text('def activeModel := imported.model\n')
            input_path.write_text(json.dumps({'transactions': [{'id': 'real-input'}]}))
            rows = [{'id': 'actual-output-from-execution'}]
            with patch.object(execution, 'eval_json', return_value=rows):
                execution.execute_sequence(driver, input_path, output)
            self.assertEqual(json.loads(output.read_text()), rows)
            text = output.with_suffix('.eval.lean').read_text()
            self.assertIn('SequenceRunner.execute', text)
            self.assertIn('real-input', text)
            self.assertNotIn('actual-output-from-execution', text)


if __name__ == '__main__':
    unittest.main()
