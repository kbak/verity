"""Envelope admission failures are instrument errors, never Solidity reverts."""
import argparse
from pathlib import Path
from eth_abi import encode
from eth_utils import keccak
from .denote import SequenceAdapter
from .engine import HarnessError, write_json
from .check_legacy_raw_calls import SENDER, EMPTY, address


def run(output):
    output = Path(output).resolve()
    output.mkdir(parents=True, exist_ok=False)
    caller, target = address(0), address(1)
    tx = {'id': '0', 'function': 'deposit', 'args': [1], 'sender': SENDER,
          'target': caller, 'value': '0x1', 'timestamp': 1000000100, 'blockNumber': 4,
          'data': '0x' + keccak(text='deposit(uint256)')[:4].hex() + encode(['uint256'], [1]).hex(),
          'observeAccounts': [SENDER]}
    options = dict(account_nonce=1, initial_balances=[(SENDER, 10), (caller, 20)],
                   value_transactions=True, byte_call_environment={
                       'program': 'raw-context-echo-v1', 'accounts': [str(int(target, 16))],
                       'emptyAccounts': [str(int(EMPTY, 16))]})

    def replay(name, changes, settings):
        adapter = SequenceAdapter(output / name,
            Path('Contracts/SolidityImportSmoke/LegacyPayableModel.lean'), caller,
            **{**options, **settings})
        return adapter([{**tx, **changes}], [[]])

    rows = replay('control', {}, {})
    deployment = rows[0]['deployment']
    assert rows[0]['status'] == 'ok'
    assert rows[0]['data'] == '0x' + encode(['uint256'] * 4, [1, 21, 1, 1]).hex()
    assert deployment['creator']['balance'] == 21
    assert deployment['accounts'][0]['balance'] == 9 and deployment['accounts'][0]['nonce'] == 1
    cases = [
        ('unfunded', {'value': '0xb'}, {}, 'insufficient transaction balance'),
        ('implicit-mode', {}, {'value_transactions': False}, 'explicit zero-fee'),
        ('nonce-exhausted', {}, {'account_nonces': [(SENDER, (1 << 64)-1)]}, 'nonce exhausted'),
        ('code-sender', {}, {'account_code': [(SENDER, '0x00')]}, 'code-free sender'),
        ('self-sender', {'sender': caller}, {}, 'distinct EOA sender'),
        ('balance-overflow', {}, {'initial_balances': [(SENDER, 10), (caller, (1 << 256)-1)]},
         'transaction balance overflow'),
    ]
    report = []
    for name, changes, settings, diagnostic in cases:
        try:
            replay(name, changes, settings)
        except HarnessError as error:
            if diagnostic not in str(error):
                raise HarnessError(f'{name}: wrong admission failure: {error}') from error
            report.append({'name': name, 'diagnostic': diagnostic})
        else:
            raise HarnessError(f'{name}: invalid envelope was admitted')
    write_json(output / 'results.json', {'passed': True, 'controls': 1, 'rejections': report})
    print(f'{len(report)} envelope rejection controls passed', flush=True)


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    run(**vars(parser.parse_args()))
