"""Rollback detector tests; synthetic observations here are not execution evidence."""
import copy
import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch

from solidity_differential import check_packed_storage_rollback as rollback
from solidity_differential.engine import HarnessError
from solidity_differential.pinned_sequence import SENDERS, create_address
from solidity_differential.storage_reference_oracle import compare_expected, hexword, specification


class PackedStorageRollbackTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        cls.spec = specification(create_address(SENDERS[0]), SENDERS[0])
        cls.reverted = [row['id'] for row in cls.spec['expected'] if row['status'] == 'revert']

    def result(self, rows):
        return {'routes': ['source'], 'mismatches': {'source': rows}}

    def error_result(self, spec, mutant, routes):
        observations = [{**row, 'touched': []} for row in spec['expected']]
        for tx, row in zip(spec['transactions'], observations, strict=True):
            if row['status'] == 'revert':
                argument = tx['args'][-1]
                row['data'] = {
                    'wrong-error-argument': f'0xacdeab74{argument ^ 1:064x}',
                    'wrong-error-selector': f'0xebcb6ada{argument:064x}',
                    'empty-revert': '0x',
                }[mutant]
        mismatches = compare_expected(spec, observations)
        return {'routes': list(routes), 'divergences': [],
                'observations': {r: copy.deepcopy(observations) for r in routes},
                'mismatches': {r: copy.deepcopy(mismatches) for r in routes}}

    def test_full_archives_remain_frozen_including_rollback_and_following_reads(self):
        for shift, digest in rollback.STATE_ARCHIVES.items():
            spec = specification(create_address(SENDERS[0]), SENDERS[0], shift)
            raw = (json.dumps(spec, indent=2) + '\n').encode()
            self.assertEqual(hashlib.sha256(raw).hexdigest(), digest)
            self.assertTrue(all(tx['function'] == 'read' for tx in spec['transactions'][-6:]))
            for index, row in enumerate(spec['expected']):
                if row['status'] == 'revert':
                    self.assertEqual(row['storage'], spec['expected'][index - 1]['storage'])
                    self.assertEqual(row['events'], [])

    def test_source_mutants_require_real_semantic_fields_and_later_read_corruption(self):
        failures = [{'id': ident, 'fields': ['status', 'data', 'events', 'storage']}
                    for ident in self.reverted]
        failures.append({'id': self.spec['expected'][11]['id'], 'fields': ['data', 'storage']})
        rollback.require_source_result(self.result(failures), self.spec, 'drop-revert')
        for index in range(len(failures)):
            for field in failures[index]['fields']:
                bad = copy.deepcopy(failures)
                bad[index]['fields'].remove(field)
                with self.subTest(index=index, field=field), self.assertRaises(HarnessError):
                    rollback.require_source_result(self.result(bad), self.spec, 'drop-revert')
        for rows in ([], failures[:-1], [{'id': self.reverted[0], 'fields': ['status']}],
                     failures + [failures[0]], failures + [{'id': 'unknown', 'fields': ['data']}]):
            with self.assertRaises(HarnessError):
                rollback.require_source_result(self.result(rows), self.spec, 'drop-revert')

    def test_error_mutations_cannot_hide_state_log_status_or_successful_call_changes(self):
        for mutant in rollback.ERROR_MUTANTS:
            good = self.error_result(self.spec, mutant, ('source',))
            rollback.require_source_result(good, self.spec, mutant)
            rows = good['mismatches']['source']
            for field in ('status', 'events', 'storage'):
                bad = copy.deepcopy(rows)
                bad[0]['fields'].append(field)
                with self.assertRaises(HarnessError):
                    rollback.require_source_result({**good, 'mismatches': {'source': bad}},
                                                   self.spec, mutant)
            for bad in (rows[:-1], rows + [{'id': self.spec['expected'][0]['id'], 'fields': ['data']}]):
                with self.assertRaises(HarnessError):
                    rollback.require_source_result({**good, 'mismatches': {'source': bad}},
                                                   self.spec, mutant)
        for bad in ({}, {'routes': [], 'mismatches': {'source': []}},
                    {'routes': ['source'], 'mismatches': {}},
                    {'routes': ['source', 'model'], 'mismatches': {'source': [], 'model': []}}):
            with self.assertRaises(HarnessError):
                rollback.require_source_result(bad, self.spec)

    def test_oracle_independently_rejects_state_and_log_leaks_with_correct_revert_bytes(self):
        # The campaign separately executes rollback mutants on all three routes.
        failed = next(i for i, row in enumerate(self.spec['expected']) if row['status'] == 'revert')
        for field in ('storage', 'events', 'data'):
            rows = [{**copy.deepcopy(row), 'touched': []} for row in self.spec['expected']]
            if field == 'storage':
                slot = self.spec['recordSlots'][0]
                entry = next(item for item in rows[failed]['storage'] if item[1] == slot)
                entry[2] = hexword(int(entry[2], 16) ^ 1)
            elif field == 'events':
                rows[failed]['events'] = copy.deepcopy(self.spec['expected'][6]['events'])
                with self.assertRaisesRegex(HarnessError, 'retained emitted events'):
                    compare_expected(self.spec, rows)
                continue
            else:
                rows[failed]['data'] = '0x'
            mismatch = compare_expected(self.spec, rows)
            self.assertEqual(mismatch, [{'id': self.reverted[0], 'fields': [field]}])
            with self.assertRaises(HarnessError):
                rollback.require_source_result(self.result(mismatch), self.spec)

    def test_source_variants_preserve_original_fixture_and_successful_roots(self):
        original = rollback.FIXTURE.read_text()
        sources = rollback.source_variants(original)
        self.assertEqual(set(sources), set(rollback.POSITIVE + rollback.MUTANTS))
        prefix = sources['original'].split('    function writeThenRevert')[0]
        for name in ('void-return', 'drop-revert', 'wrong-error-argument', 'empty-revert'):
            self.assertEqual(sources[name].split('    function writeThenRevert')[0], prefix)
        for source in sources.values():
            self.assertIn('mstore(base, 0) mstore(add(base, 32), 0)', source)
        self.assertEqual(rollback.FIXTURE.read_text(), original)
        self.assertNotIn('mstore(base, 0) mstore(add(base, 32), 0)', original)
        with self.assertRaises(HarnessError):
            rollback.source_variants(original.replace('revert Rejected(next);', 'revert();'))

    def test_commit_mutant_requires_leaked_effects_only_on_the_mutated_routes(self):
        rows = [{'id': ident, 'fields': ['status', 'data', 'events', 'storage']}
                for ident in self.reverted]
        rows.append({'id': self.spec['expected'][11]['id'], 'fields': ['data', 'storage']})
        routes = ('model', 'compiled')
        good = {'routes': list(rollback.ROUTES), 'divergences': ['different status'],
                'mismatches': {'source': [], **{r: copy.deepcopy(rows) for r in routes}}}
        rollback.require_rollback_mutation(good, self.spec, 'drop-revert', routes)
        for route in rollback.ROUTES:
            bad = copy.deepcopy(good)
            bad['mismatches'][route] = rows if route == 'source' else []
            with self.assertRaises(HarnessError):
                rollback.require_rollback_mutation(bad, self.spec, 'drop-revert', routes)

    def test_compiler_boundary_requires_the_exact_structured_result(self):
        rollback.require_compilation({'status': 'compiled'})
        rollback.require_compilation({'status': 'rejected', 'reason': rollback.COMPILER_REJECTION}, False)
        for terminal in (False, True):
            for bad in ({}, {'status': 'crashed'}, {'status': 'rejected', 'reason': 'timeout'},
                        {'status': 'rejected', 'reason': 'other compiler error'}):
                with self.assertRaises(HarnessError):
                    rollback.require_compilation(bad, terminal)
        for result, terminal in (({'status': 'compiled'}, False),
                                  ({'status': 'rejected', 'reason': rollback.COMPILER_REJECTION}, True)):
            with self.assertRaises(HarnessError):
                rollback.require_compilation(result, terminal)
        self.assertEqual({case for case, (_, terminal) in rollback.TAIL_CASES.items() if not terminal},
                         {'nonzero', 'unknown', 'stop', 'conditional-fallthrough'})
        with tempfile.TemporaryDirectory() as tmp:
            directory = Path(tmp)
            with patch.object(rollback, 'eval_json', side_effect=HarnessError('evaluation failed')):
                with self.assertRaisesRegex(HarnessError, 'evaluation failed'):
                    rollback.probe_compilation(directory, directory / 'Source.sol',
                                               'ScalarControl', 'fail(uint128)')

    def test_agreeing_routes_cannot_substitute_another_controls_payload(self):
        for actual in rollback.ERROR_MUTANTS:
            result = self.error_result(self.spec, actual, rollback.ROUTES)
            for claimed in rollback.ERROR_MUTANTS:
                if actual != claimed:
                    with self.subTest(actual=actual, claimed=claimed), self.assertRaisesRegex(
                            HarnessError, 'unexpected replay differences'):
                        rollback.require_rollback_mutation(result, self.spec, claimed, rollback.ROUTES)

    def test_declared_control_needs_exact_errors_and_rollback_on_every_actual_route(self):
        spec = rollback.control_inputs(self.spec)
        mutant = 'wrong-error-argument'
        good = self.error_result(spec, mutant, rollback.ROUTES)

        def check(result):
            rollback.require_rollback_mutation(result, spec, mutant, rollback.ROUTES)

        check(good)
        for route in rollback.ROUTES:
            for field in ('status', 'events', 'storage'):
                bad = copy.deepcopy(good)
                bad['mismatches'][route][0]['fields'].append(field)
                with self.assertRaises(HarnessError):
                    check(bad)
            for truncate in (True, False):
                bad = copy.deepcopy(good)
                row = next(r for r in bad['observations'][route] if r['status'] == 'revert')
                row['data'] = row['data'][:-2] if truncate else row['data'] + '00'
                with self.assertRaisesRegex(HarnessError, 'unexpected replay differences'):
                    check(bad)
            bad = copy.deepcopy(good)
            del bad['observations'][route]
            with self.assertRaisesRegex(HarnessError, 'missing replay observations'):
                check(bad)
            for defect in ('missing-route', 'missed-error', 'divergence'):
                bad = copy.deepcopy(good)
                if defect == 'missing-route':
                    del bad['mismatches'][route]
                elif defect == 'missed-error':
                    bad['mismatches'][route].pop()
                else:
                    bad['divergences'] = ['payload']
                with self.assertRaises(HarnessError):
                    check(bad)


if __name__ == '__main__':
    unittest.main()
