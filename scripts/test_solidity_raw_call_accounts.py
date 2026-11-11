"""Explicit account prestates must be well formed on both replay routes."""
import tempfile
import unittest
from pathlib import Path

from solidity_differential.anvil import SequenceAdapter as EVM
from solidity_differential.denote import SequenceAdapter as Denote
from solidity_differential.engine import HarnessError

CALLER = '0x' + '11' * 20
TARGET = '0x' + '22' * 20


class RawCallAccountInputs(unittest.TestCase):
    def test_shared_balances_and_foreign_nonce(self):
        with tempfile.TemporaryDirectory() as directory:
            driver = Path(directory) / 'driver.lean'
            driver.write_text('')
            balances = [(CALLER, 123), (TARGET, 17)]
            evm = EVM(directory, [], initial_balances=balances)
            model = Denote(directory, driver, CALLER, identity=object(),
                           initial_balances=balances, account_nonces=[(TARGET, 1)])
            self.assertEqual(evm.initial_balances, balances)
            self.assertEqual(model.initial_balances,
                             [[str(int(a, 16)), str(b)] for a, b in balances])
            self.assertEqual(model.account_nonces, [[str(int(TARGET, 16)), '1']])

    def test_malformed_balances_rejected_by_both_adapters(self):
        cases = [[(CALLER, -1)], [(CALLER, 1 << 256)], [(CALLER, True)],
                 [(CALLER, 1.0)], [('0x1234', 1)], [(CALLER, 1), (CALLER, 2)]]
        with tempfile.TemporaryDirectory() as directory:
            driver = Path(directory) / 'driver.lean'
            driver.write_text('')
            for balances in cases:
                with self.subTest(balances=balances):
                    with self.assertRaises(HarnessError):
                        EVM(directory, [], initial_balances=balances)
                    with self.assertRaises(HarnessError):
                        Denote(directory, driver, CALLER, identity=object(), initial_balances=balances)

    def test_invalid_foreign_nonces_rejected(self):
        cases = [[(CALLER, 1)], [(TARGET, -1)], [(TARGET, 1 << 64)],
                 [(TARGET, True)], [(TARGET, 1), (TARGET, 2)]]
        with tempfile.TemporaryDirectory() as directory:
            driver = Path(directory) / 'driver.lean'
            driver.write_text('')
            for nonces in cases:
                with self.subTest(nonces=nonces), self.assertRaises(HarnessError):
                    Denote(directory, driver, CALLER, identity=object(), account_nonces=nonces)
