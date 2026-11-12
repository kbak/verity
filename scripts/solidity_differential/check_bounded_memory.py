"""Construct-generic positive execution and located-rejection memory regressions."""
import argparse
import json
from pathlib import Path

from keccak256 import keccak_256
from .check_packed_memory_hash import word
from .check_packed_memory_hash_import import observe
from .check_packed_memory_hash_routes import case, run_root
from .engine import HarnessError, ROOT, command, write_json
from .hash_execution import compile_source, pinned_compiler

FIXTURE = ROOT / 'Contracts/SolidityImportSmoke/BoundedMemory.sol'


def rejected_sources():
    """Each mutant violates one independently enforced source-admission boundary."""
    source = FIXTURE.read_text()
    for name, before, after, reason in (
        ('dirty-hash', 'keccak256(add(pointer, 30), 3)', 'keccak256(pointer, 3)',
         'dirty scalar bytes'),
        ('dirty-return', 'keccak256(add(pointer, 30), 3)', 'mload(pointer)',
         'dirty scalar bits'),
        ('missing-cleanup', 'mstore(pointer, 0)', '', 'leaves dirty scalar bytes'),
        ('dirty-arithmetic', 'mstore(pointer, shortWord)', 'mstore(pointer, add(shortWord, 1))',
         'dirty scalar bits'),
        ('dirty-address', 'let pointer := mload(0x40)', 'let pointer := shortWord',
         'dirty scalar bits'),
        ('variable-length', 'keccak256(add(pointer, 30), 3)',
         'keccak256(add(pointer, 30), shortWord)', 'dirty scalar bits'),
        ('unknown-alias', 'mstore(pointer, 0)', 'mstore(128, 0)',
         'cannot establish disjointness'),
        ('unbounded-address', 'let pointer := mload(0x40)', 'let pointer := tag',
         'nonwrapping addresses'),
        ('out-of-range', 'let pointer := mload(0x40)', 'let pointer := 0x100000000',
         'nonwrapping addresses'),
        ('reserved-memory', 'let pointer := mload(0x40)', 'let pointer := 96',
         'nonwrapping addresses'),
        ('branch', 'mstore(pointer, 0)', 'if shortWord { mstore(pointer, 0) }',
         'straight-line assembly'),
    ):
        yield name, source.replace(before, after, 1), 'overlap(uint16,bytes32)', reason
    snapshot = source.replace('let pointer := mload(0x40)',
        'let old := mload(0x40) mstore(0x40, add(old, 32)) let pointer := mload(0x40)', 1)
    snapshot = snapshot.replace('mstore(pointer, 0)', 'mstore(old, 0)', 1)
    yield ('allocator-snapshot-alias', snapshot, 'overlap(uint16,bytes32)',
           'cannot establish disjointness')
    snapshot = source.replace('assembly ("memory-safe") {',
        'uint256 cursor; assembly ("memory-safe") {', 1)
    snapshot = snapshot.replace('let pointer := mload(0x40)',
        'cursor := mload(0x40) let pointer := cursor cursor := add(cursor, 32)', 1)
    snapshot = snapshot.replace('mstore(pointer, 0)', 'mstore(cursor, 0)', 1)
    yield ('scalar-snapshot-alias', snapshot, 'overlap(uint16,bytes32)',
           'cannot establish disjointness')
    allocation = source.replace('assembly ("memory-safe") {',
        'bytes32 encodedHash = keccak256(abi.encode(tag)); assembly ("memory-safe") {', 1)
    allocation = allocation.replace('keccak256(add(pointer, 30), 3)',
        'xor(encodedHash, keccak256(add(pointer, 30), 3))', 1)
    yield ('allocation-observation', allocation, 'overlap(uint16,bytes32)',
           'synthetic allocation memory writes')
    widened = source.replace('assembly ("memory-safe") {',
        'uint256 copied; assembly { copied := shortWord } assembly ("memory-safe") {', 1)
    widened = widened.replace('mstore(pointer, shortWord)', 'mstore(pointer, copied)', 1)
    yield ('unaudited-narrow-copy', widened, 'overlap(uint16,bytes32)',
           'unaudited narrow assembly references')
    helper_copy = widened.replace('uint256 copied; assembly { copied := shortWord }',
                                  'uint256 copied = copyWord(shortWord);', 1)
    helper_copy = helper_copy.rsplit('}', 1)[0] + (
        'function copyWord(uint16 input) internal pure returns (uint256 output) '
        '{ assembly { output := input } } }')
    yield ('unaudited-helper-copy', helper_copy, 'overlap(uint16,bytes32)',
           'unaudited narrow assembly references')
    guard = 'require(offset <= 64, "offset");'
    for name, replacement in (
        ('unguarded-offset', ''),
        ('stale-guard', 'bool bounded = offset <= 64; '
         'offset = 2**255; require(bounded, "offset");'),
        ('excessive-offset', 'require(offset <= 4294967296, "offset");'),
    ):
        yield name, source.replace(guard, replacement), 'shifted(uint256)', 'nonwrapping addresses'


def run(output, prepared=False):
    output = output.resolve()
    if not output.is_relative_to(ROOT):
        raise HarnessError('output must be inside this checkout')
    output.mkdir(parents=True, exist_ok=False)
    if not prepared:
        command(['turbo-lean', '--json', 'build', 'Compiler.SolidityImport.Import',
                 'Compiler.SolidityImport.Differential', '--project-dir', ROOT],
                cwd=ROOT, timeout=1800, log=output / 'build.log')
    solc, compiler = pinned_compiler()
    directory = output / 'positive'
    directory.mkdir()
    (directory / FIXTURE.name).write_text(FIXTURE.read_text())
    built = compile_source(directory, FIXTURE.name, 'BoundedMemory', solc)
    values = [0, 1, 255, 256, 32767, 32768, 65535]
    tags = [0, 1, 255, 2**256 - 1, int.from_bytes(bytes(range(32)), 'big')]
    overlap = [case(f'{n}:{tag}', 'overlap(uint16,bytes32)', [n, tag],
                    keccak_256(n.to_bytes(2, 'big') + bytes([tag % 256])).hex())
               for n in values for tag in tags]
    masked = [case(str(n), 'masked(uint16)', [n], keccak_256(word(n)).hex()) for n in values]
    shifted = [case(str(n), 'shifted(uint256)', [n], keccak_256(word(0x1234)).hex())
               for n in [0, 1, 15, 31, 32, 63, 64]]
    results = {}
    for name, signature, cases in [('overlap', 'overlap(uint16,bytes32)', overlap),
                                    ('masked', 'masked(uint16)', masked),
                                    ('shifted', 'shifted(uint256)', shifted)]:
        result = run_root(directory / name, FIXTURE.name, 'BoundedMemory', signature,
                          cases, built, solc, compiler, False)
        if result['status'] != 'admitted':
            raise HarnessError(f'{name}: required generic memory control rejected: {result}')
        results[name] = result
    source = FIXTURE.read_text().replace('assembly ("memory-safe") {',
        'bytes32 copied; assembly { copied := tag } assembly ("memory-safe") {', 1)
    source = source.replace('mstore(add(pointer, 1), tag)', 'mstore(add(pointer, 1), copied)', 1)
    source = source.replace('let pointer := mload(0x40)', 'let zero let pointer := mload(0x40)', 1)
    source = source.replace('mstore(pointer, 0)', 'mstore(pointer, zero)', 1)
    directory = output / 'full-word-copy'
    directory.mkdir()
    (directory / FIXTURE.name).write_text(source)
    built = compile_source(directory, FIXTURE.name, 'BoundedMemory', solc)
    result = run_root(directory / 'overlap', FIXTURE.name, 'BoundedMemory',
                      'overlap(uint16,bytes32)', overlap, built, solc, compiler, False)
    if result['status'] != 'admitted':
        raise HarnessError(f'full-word-copy: safe scalar assembly rejected: {result}')
    results['full-word-copy'] = result
    for name, source, signature, reason in rejected_sources():
        directory = output / name
        directory.mkdir()
        (directory / FIXTURE.name).write_text(source)
        # A compiler or harness error cannot satisfy a located importer rejection.
        compile_source(directory, FIXTURE.name, 'BoundedMemory', solc)
        result = observe(directory, FIXTURE.name, 'BoundedMemory', signature)
        if result['status'] != 'rejected' or reason not in result['reason']:
            raise HarnessError(f'{name}: expected {reason!r}, observed {result}')
        results[name] = result
    write_json(output / 'results.json', results)
    return {'positiveCases': 2 * len(overlap) + len(masked) + len(shifted), 'routes': 3,
            'locatedRejections': len(results) - 4}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    parser.add_argument('--prepared', action='store_true')
    args = parser.parse_args()
    print(json.dumps(run(args.output, args.prepared), sort_keys=True))


if __name__ == '__main__':
    main()
