"""Importer observations must fail closed on infrastructure and stale-body errors."""
import copy
import unittest

from solidity_differential.check_packed_memory_hash_import import (
    ROOTS, check_controls, classify,
)
from solidity_differential.engine import HarnessError


class PackedMemoryHashImportTests(unittest.TestCase):
    source = 'contract PackedMemoryHash {\n function digest() {}\n}\n'
    diagnostic = ('Probe.lean:3:0: error: PackedMemoryHash.sol:2:2: FunctionDefinition: '
                  '[solidity-import:unsupported] unsupported construct\n'
                  'closure: PackedMemoryHash.digest -> PackedMemoryHash.hashPacked\n'
                  'function digest() {}\n')

    def reply(self, **changes):
        return dict({'ok': False, 'import_ok': True, 'crashed': False, 'timed_out': False,
                     'messages': [self.diagnostic], 'errors': [self.diagnostic]}, **changes)

    def classify(self, reply, code=1):
        return classify(code, reply, self.source, 'PackedMemoryHash.sol', 'PackedMemoryHash', 'digest')

    def test_rejection_retains_source_location_and_closure(self):
        row = self.classify(self.reply())
        self.assertEqual((row['status'], row['line'], row['column']), ('rejected', 2, 2))
        self.assertEqual(row['reason'], 'unsupported construct')
        self.assertIn('PackedMemoryHash.hashPacked', row['closure'])

    def test_tool_failures_cannot_satisfy_rejection(self):
        for changes in ({'crashed': True}, {'timed_out': True}, {'import_ok': False},
                        {'errors': []}, {'errors': ['missing compiler']},
                        {'errors': [self.diagnostic, 'unrelated elaboration error']},
                        {'errors': [self.diagnostic.replace(':2:2:', ':99:2:')]},
                        {'errors': [self.diagnostic.replace(':2:2:', ':2:99:')]},
                        {'errors': [self.diagnostic.replace('PackedMemoryHash.digest', 'Other.root')]}):
            with self.subTest(changes=changes), self.assertRaises(HarnessError):
                self.classify(self.reply(**changes))
        for code in (0, -9, 124, 127):
            with self.subTest(code=code), self.assertRaises(HarnessError):
                self.classify(self.reply(), code)

    def test_acceptance_requires_consistent_success(self):
        reply = self.reply(ok=True, errors=[], messages=[])
        self.assertEqual(self.classify(reply, 0), {'status': 'admitted'})
        with self.assertRaises(HarnessError):
            self.classify(reply, 1)
        with self.assertRaises(HarnessError):
            self.classify(self.reply(ok=True), 0)

    def rows(self, admitted):
        return {name: {root: ({'status': 'admitted', 'model': name + ':' + root} if admitted else
                             {'status': 'rejected', 'node': 'InlineAssembly', 'reason': 'unsupported',
                              'closure': f'PackedMemoryHash.{root} -> PackedMemoryHash.hashPacked'})
                       for root in ROOTS}
                for name in ('original', 'renamed', 'padded', 'changed-body')}

    def test_rejections_never_count_as_required_admission(self):
        rows = self.rows(False)
        for row in rows['renamed'].values():
            row['closure'] = row['closure'].replace('hashPacked', 'renamedPacked')
        self.assertFalse(check_controls(rows))

    def test_rename_must_preserve_support_and_rejection_reason(self):
        for mutation in ({'status': 'admitted'}, {'reason': 'different boundary'}):
            rows = self.rows(False)
            rows['renamed']['digest'].update(mutation)
            with self.subTest(mutation=mutation), self.assertRaises(HarnessError):
                check_controls(rows)

    def test_accepted_body_changes_cannot_reuse_original_model(self):
        rows = self.rows(True)
        self.assertTrue(check_controls(rows))
        for name in ('padded', 'changed-body'):
            for root in ROOTS:
                stale = copy.deepcopy(rows)
                stale[name][root]['model'] = stale['original'][root]['model']
                with self.subTest(name=name, root=root), self.assertRaises(HarnessError):
                    check_controls(stale)

    def test_body_change_may_be_rejected_without_weakening_admission(self):
        rows = self.rows(True)
        for name in ('padded', 'changed-body'):
            for root in ROOTS:
                rows[name][root] = {'status': 'rejected'}
        self.assertTrue(check_controls(rows))


if __name__ == '__main__':
    unittest.main()
