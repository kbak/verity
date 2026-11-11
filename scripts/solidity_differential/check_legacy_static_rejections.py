"""Positive and fail-closed neighbors of legacy scalar static calls/fixed-slot stores."""
import argparse
from pathlib import Path
from .check_legacy_void_rejections import run

I = 'interface I { function query(uint256 x) external view returns(bool); }'
RUN = 'function run(address target,uint256 x) public { '
CALL = 'require(I(target).query(x)); '
SIG = 'run(address,uint256)'
CASES = {
    'static-then-write': (I, RUN + CALL + 'assembly { sstore(7,x) } }', SIG, None),
    'pure-callee': (I.replace('external view', 'external pure'), RUN + CALL + '}', SIG, None),
    'word-store': ('', 'function run(uint256 x) public { assembly { sstore(7,x) } }', 'run(uint256)', None),
    'address-store': ('', 'function run(address x) public { assembly { sstore(7,x) } }', 'run(address)', None),
    'two-stores': ('', 'function run(uint256 x) public { assembly { sstore(7,x) sstore(8,9) } }', 'run(uint256)', None),
    'dynamic-slot': ('', 'function run(uint256 x) public { assembly { sstore(x,7) } }', 'run(uint256)', 'storage writes require a constant slot'),
    'store-expression': ('', 'function run(uint256 x) public { assembly { sstore(7,add(x,1)) } }', 'run(uint256)', 'read-only decoding'),
    'store-loop': ('', 'function run(uint256 x) public { assembly { for {} lt(x,5) {x := add(x,1)} {sstore(7,x)} } }', 'run(uint256)', 'read-only decoding'),
    'untracked-helper-address': ('', 'function h(address x) internal { assembly { sstore(7,x) } } function run(address x) public {h(x);}', 'run(address)', 'assembly reads require full-word'),
    'dirty-address-store': ('', 'function run() public {address a; assembly {a := sload(7)} assembly {sstore(8,a)}}', 'run()', 'assembly reads require full-word'),
    'write-after-void': ('interface I { function hook() external; }', RUN + 'I(target).hook(); assembly { sstore(7,x) } }', SIG, 'storage-free trailing continuation'),
    'effectful-argument': (I, RUN + 'require(I(target).query(x++)); }', SIG, 'effect-free'),
    'wrong-result': (I.replace('returns(bool)', 'returns(uint256)'), RUN + 'require(I(target).query(x)>0); }', SIG, 'external calls require'),
    'stateful-bool': (I.replace('external view', 'external'), RUN + CALL + '}', SIG, 'external calls require'),
    'abi-v2': ('pragma experimental ABIEncoderV2; '+I, RUN+CALL+'}', SIG, 'require ABI coder v1'),
    'dynamic-bytes': ('interface I { function query(bytes memory x) external view returns(bool); }', 'function run(address a,bytes memory x) public { require(I(a).query(x)); }', 'run(address,bytes)', 'declared scalar type'),
    'nested-call': ('interface I {function query(bool x) external view returns(bool);}', 'function run(address a) public {require(I(a).query(I(a).query(true)));}', 'run(address)', 'effect-free'),
    'narrow-root': ('', 'function run(bytes4 x) public pure returns(bytes4) {return x;}', 'run(bytes4)', 'narrow fixed-bytes root ABI'),
    'other-type-builtin': ('', 'function run() public pure returns(uint256) {return type(uint256).max;}', 'run()', 'builtin call is outside'),
}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    parser.add_argument('--prepared', action='store_true')
    args = parser.parse_args()
    run(args.output, args.prepared, cases=CASES)
