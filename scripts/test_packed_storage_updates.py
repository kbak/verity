"""Guard frozen state projections and real, fail-closed mutation evidence."""
import copy
import unittest

from solidity_differential.check_packed_storage_updates import (
    FIXTURE, SOURCE_MUTANTS, rejected_sources, require_source_mutant,
    source_variants, successful_prefix,
)
from solidity_differential.check_storage_reference_routes import require_outcome
from solidity_differential.engine import HarnessError
from solidity_differential.pinned_sequence import SENDERS, create_address
from solidity_differential.stateful import ROUTES
from solidity_differential.storage_reference_oracle import specification


class PackedStorageUpdatesTests(unittest.TestCase):
    def test_successful_prefix_preserves_every_expected_field_and_initial_world(self):
        for shift in (0, 1):
            full = specification(create_address(SENDERS[0]), SENDERS[0], shift)
            before = copy.deepcopy(full)
            prefix = successful_prefix(full)
            self.assertEqual(prefix['transactions'], full['transactions'][:10])
            self.assertEqual(prefix['expected'], full['expected'][:10])
            self.assertEqual({k: v for k, v in prefix.items() if k not in ('transactions', 'expected')},
                             {k: v for k, v in full.items() if k not in ('transactions', 'expected')})
            prefix['expected'][6]['events'].clear()
            self.assertEqual(full, before)

    def test_prefix_rejects_missing_updates_logs_reverts_and_identity_drift(self):
        full = specification(create_address(SENDERS[0]), SENDERS[0])
        for defect in ('missing', 'update', 'log', 'revert', 'identity', 'boundary'):
            bad = copy.deepcopy(full)
            if defect == 'missing':
                bad['transactions'].pop()
            elif defect == 'update':
                bad['transactions'][6]['function'] = 'read'
            elif defect == 'log':
                bad['expected'][6]['events'] = []
            elif defect == 'revert':
                bad['expected'][6]['status'] = 'revert'
            elif defect == 'identity':
                bad['expected'][6]['id'] = 'other'
            else:
                bad['expected'][10]['status'] = 'ok'
            with self.subTest(defect=defect), self.assertRaises(HarnessError):
                successful_prefix(bad)

    def test_mutants_need_independent_semantic_detection_on_every_executed_route(self):
        for field in ('storage', 'events'):
            valid = {'routes': list(ROUTES), 'divergences': [],
                     'mismatches': {r: [{'fields': [field]}] for r in ROUTES}}
            require_source_mutant(valid, field)
            for route in ROUTES:
                for defect in ('missing', 'escaped', 'status', 'wrong-field', 'divergence'):
                    bad = copy.deepcopy(valid)
                    if defect == 'missing':
                        bad['routes'].remove(route)
                    elif defect == 'escaped':
                        bad['mismatches'][route] = []
                    elif defect == 'status':
                        bad['mismatches'][route][0]['fields'].append('status')
                    elif defect == 'wrong-field':
                        bad['mismatches'][route] = [{'fields': ['data']}]
                    else:
                        bad['divergences'] = ['route mismatch']
                    with self.subTest(field=field, route=route, defect=defect):
                        with self.assertRaises(HarnessError):
                            require_source_mutant(bad, field)

    def test_route_local_event_mutants_cannot_hide_state_or_return_corruption(self):
        for route in ('model', 'compiled'):
            valid = {'routes': list(ROUTES), 'divergences': ['events'],
                     'mismatches': {r: ([{'fields': ['events']}] if r == route else [])
                                    for r in ROUTES}}
            require_outcome(valid, route)
            for field in ('status', 'data', 'storage'):
                bad = copy.deepcopy(valid)
                bad['mismatches'][route][0]['fields'].append(field)
                with self.assertRaises(HarnessError):
                    require_outcome(bad, route)

    def test_variants_preserve_fixture_and_cover_effect_boundaries(self):
        original = FIXTURE.read_text()
        sources = source_variants(original)
        self.assertTrue(set(SOURCE_MUTANTS) <= sources.keys())
        self.assertNotEqual(sources['original'], original)
        cases = list(rejected_sources(original))
        self.assertEqual({name for name, *_ in cases}, {
            'write-then-revert', 'read-after-log', 'hash-after-log', 'guard-after-write',
            'lookup-after-log', 'log-before-hash', 'event-footprint-overflow'})
        self.assertEqual(len({text for _, text, _, _ in cases}), len(cases))
        self.assertEqual(FIXTURE.read_text(), original)


if __name__ == '__main__':
    unittest.main()
