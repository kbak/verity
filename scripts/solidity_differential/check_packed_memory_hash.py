"""Source-EVM packed-memory regression; importer/Denote/codegen remain untested.

Expectations encode field widths directly, independently of Solidity, its memory
writes and Verity. Executable source mutations keep those expectations unchanged.
"""
import argparse
import hashlib
import itertools
import random
import shutil
from pathlib import Path

from keccak256 import keccak_256, selector
from setup_solc_import import RELEASES, file_sha256, host_platform
from .anvil import Anvil
from .engine import HarnessError, ROOT, command, solc_compile, write_json

FIXTURE = ROOT / 'Contracts/SolidityImportSmoke/PackedMemoryHash.sol'
MOD = 1 << 256
CONCRETE = (int('1234567890123456789012345678901234567890', 16), -60, 60, 42)
CONCRETE_PREIMAGE = (
    '1234567890123456789012345678901234567890ffffc400003c'
    '000000000000000000000000000000000000000000000000000000000000002a'
)
CONCRETE_HASH = 'd80661cdbaa9a56d329521f782aa547f64b7e6bab5591f0eaa0477beeb91d628'
SHIFTS = (0, 1, 3, 31, 32, 63, 64)
SETTINGS = {'evmVersion': 'cancun', 'viaIR': True,
            'optimizer': {'enabled': True, 'runs': 44444444},
            'metadata': {'bytecodeHash': 'none'}}


def packed_preimage(account, left, right, salt):
    """The specification: 20 + 3 + 3 + 32 bytes, signed fields in two's complement."""
    return (account.to_bytes(20, 'big') + left.to_bytes(3, 'big', signed=True)
            + right.to_bytes(3, 'big', signed=True) + salt.to_bytes(32, 'big'))


def word(value):
    return (value % MOD).to_bytes(32, 'big')


def replay_memory(values, shift=0):
    """Separate byte-level replay of overlapping mstores, never the expectation."""
    account, left, right, salt = values
    base = 128 + shift
    memory = bytearray(b'\xa5' * (base + 128))
    for offset, value in ((38, salt), (6, right), (3, left), (0, account)):
        memory[base + offset:base + offset + 32] = word(value)
    return bytes(memory[base + 12:base + 70])


def vectors(seed=55, random_cases=16):
    """Concrete regression, signed boundaries, address/salt widths and seeded cases."""
    rows = [CONCRETE]
    for left, right in itertools.product((-(1 << 23), -1, 0, 1, (1 << 23) - 1), repeat=2):
        rows.append((CONCRETE[0], left, right, 42))
    for account, salt in itertools.product((0, 1, (1 << 160) - 1),
                                           (0, 1, 1 << 255, MOD - 1)):
        rows.append((account, -60, 60, salt))
    rng = random.Random(seed)
    rows.extend((rng.getrandbits(160), rng.randrange(-(1 << 23), 1 << 23),
                 rng.randrange(-(1 << 23), 1 << 23), rng.getrandbits(256))
                for _ in range(random_cases))
    return rows


def variants(source):
    """Mutate source only. A renamed helper is a mandatory positive control."""
    start, end = '// BEGIN packed body', '// END packed body'
    if source.count(start) != 1 or source.count(end) != 1:
        raise HarnessError('packed body mutation anchors changed')
    before, rest = source.split(start)
    _, after = rest.split(end)
    padded = before + 'return keccak256(abi.encode(account, left, right, salt));\n' + after
    anchor = 'mstore(add(base, 3), left)'
    if source.count(anchor) != 1:
        raise HarnessError('body mutation anchor changed')
    return {
        'original': source,
        'renamed': source.replace('hashPacked', 'renamedPacked'),
        'padded': padded,
        'changed-body': source.replace(anchor, 'mstore(add(base, 3), xor(left, 1))'),
    }


def run(output, solc, seed=55, random_cases=16):
    output = output.resolve()
    output.mkdir(parents=True, exist_ok=False)
    release = RELEASES['0.8.26']
    if not solc.is_file() or file_sha256(solc) != release['sha256'][host_platform()]:
        raise HarnessError('missing or changed pinned Solidity 0.8.26 compiler')
    version = command([solc, '--version']).strip()
    if release['long_version'] not in version:
        raise HarnessError('source compiler version mismatch')
    source = FIXTURE.read_text()
    cases = vectors(seed, random_cases)
    expected = []
    for values in cases:
        payload = packed_preimage(*values)
        if len(payload) != 58 or any(replay_memory(values, s) != payload for s in SHIFTS):
            raise HarnessError('memory replay disagrees with independent field-width specification')
        expected.append({'values': list(map(str, values)), 'preimage': payload.hex(),
                         'hash': keccak_256(payload).hex()})
    if (expected[0]['preimage'], expected[0]['hash']) != (CONCRETE_PREIMAGE, CONCRETE_HASH):
        raise HarnessError('fixed concrete expectation changed')
    write_json(output / 'expectations.json', expected)
    metadata = {
        'scope': 'generic source EVM + independent byte-layout expectations + source mutations',
        'verityBase': command(['git', 'rev-parse', 'HEAD'], cwd=ROOT).strip(),
        'worktreeStatus': command(['git', 'status', '--porcelain'], cwd=ROOT),
        'sourceCompiler': version, 'sourceCompilerSha256': file_sha256(solc),
        'settings': SETTINGS, 'seed': seed, 'randomCases': random_cases,
        'inputCases': len(cases), 'shifts': SHIFTS,
        'files': {str(path.relative_to(ROOT)): file_sha256(path) for path in
                  (FIXTURE, Path(__file__), ROOT / 'scripts/keccak256.py',
                   ROOT / 'scripts/setup_solc_import.py',
                   ROOT / 'scripts/solidity_differential/anvil.py',
                   ROOT / 'scripts/solidity_differential/engine.py')},
        'expectationsSha256': file_sha256(output / 'expectations.json'),
        'importedSemantics': 'not run; pending importer work after fork sync integration',
        'generatedOutput': 'not run; source solc bytecode is not Verity-generated output',
        'proofStatus': 'finite executable evidence, not a correspondence or cryptographic proof',
        'limits': ['generic public fixture, not a complete application import',
                   'storage addressing and storage frames not exercised',
                   'gas/resource equivalence and arbitrary aliasing not established'],
    }
    write_json(output / 'manifest.json', metadata)
    results = {}
    with Anvil(output / 'node', hardfork='cancun') as node:
        sender = node.rpc('eth_accounts')[0]
        for name, variant in variants(source).items():
            directory = output / name
            directory.mkdir()
            (directory / FIXTURE.name).write_text(variant)
            request = {'language': 'Solidity', 'sources': {FIXTURE.name: {'content': variant}},
                       'settings': {**SETTINGS, 'outputSelection': {'*': {'*':
                           ['abi', 'evm.bytecode.object', 'evm.deployedBytecode.object']}}}}
            built = solc_compile(request, directory, directory / 'solc', solc=solc)
            code = built['contracts'][FIXTURE.name]['PackedMemoryHash']['evm']['bytecode']['object']
            deployed = node.transact({'from': sender, 'data': '0x' + code, 'gas': hex(10000000)})
            if deployed['receipt']['status'] != '0x1':
                raise HarnessError(f'{name}: fixture deployment failed')
            target = deployed['receipt']['contractAddress']
            observations, mismatches, hash_mismatches = [], [], []
            for index, (values, expectation) in enumerate(zip(cases, expected)):
                for shift in (None, *SHIFTS):
                    signature = ('digest(address,int24,int24,bytes32)' if shift is None else
                                 'inspect(address,int24,int24,bytes32,uint256)')
                    args = values if shift is None else (*values, shift)
                    data = selector(signature) + b''.join(map(word, args)).hex()
                    want = bytes.fromhex(expectation['hash'])
                    if shift is not None:
                        want += b''.join(map(word, (0, 0, 0, 0, 0xfeed)))
                    actual = node.rpc('eth_call', {'from': sender, 'to': target, 'data': data,
                                                 'gas': hex(10000000)}, 'latest')
                    got = bytes.fromhex(actual.removeprefix('0x'))
                    if len(got) != len(want):
                        raise HarnessError(f'{name}: unexpected ABI return size')
                    ident = f'{index}:{shift}'
                    observations.append({'id': ident, 'calldata': data, 'actual': actual,
                                         'expected': '0x' + want.hex()})
                    if got != want:
                        mismatches.append(ident)
                    if got[:32] != want[:32]:
                        hash_mismatches.append(ident)
            write_json(directory / 'observations.json', observations)
            results[name] = {'calls': len(observations), 'mismatches': mismatches,
                             'hashMismatches': hash_mismatches,
                             'sourceSha256': hashlib.sha256(variant.encode()).hexdigest(),
                             'bytecodeSha256': hashlib.sha256(bytes.fromhex(code)).hexdigest()}
            if name in ('original', 'renamed') and mismatches:
                raise HarnessError(f'{name}: independent expectations failed: {mismatches[:5]}')
            if name in ('padded', 'changed-body') and len(hash_mismatches) != len(observations):
                raise HarnessError(f'{name}: mutation escaped the fixed hash expectations')
        metadata['node'] = {**node.provenance,
                            'binarySha256': file_sha256(Path(shutil.which('anvil')))}
    write_json(output / 'manifest.json', metadata)
    write_json(output / 'results.json', {'passed': True, 'scope': metadata['scope'],
                                        'routes': results})
    print(f'{len(cases)} inputs; {len(cases) * (1 + len(SHIFTS))} calls per variant; '
          'original and rename pass; both source mutations detected')
    return 0


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--solc', type=Path, default=ROOT / '.lake/solidity-import/solc-0.8.26')
    parser.add_argument('--seed', type=int, default=55)
    parser.add_argument('--random-cases', type=int, default=16)
    args = parser.parse_args()
    if args.random_cases < 0:
        parser.error('--random-cases must be nonnegative')
    return run(args.output, args.solc.resolve(), args.seed, args.random_cases)


if __name__ == '__main__':
    raise SystemExit(main())
