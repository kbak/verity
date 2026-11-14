"""Keep shared-memory mutation and unsupported legacy aggregates fail-closed."""
import argparse
from pathlib import Path
from .check_legacy_void_rejections import run

RECORD = 'struct R { int24 a; uint8 b; } '
CASES = {
    'signed-memory-read': ('', RECORD +
        'function run(int24 a) external pure returns(int24) { R memory r=R(a,2); return r.a; }',
        'run(int24)', None),
    'storage-member-with-assembly': ('', 'struct R { uint8 b; } R r; '
        'function run() external view returns(uint256 x) { assembly { x := add(1,2) } return x+r.b; }',
        'run()', None),
    'memory-default': ('', RECORD +
        'function run() external pure returns(int24) { R memory r; return r.a; }',
        'run()', None),
    'member-write': ('', RECORD +
        'function run() external pure returns(int24) { R memory r=R(1,2); r.a=3; return r.a; }',
        'run()', 'memory struct writes and rebinding'),
    'tuple-member-write': ('', RECORD +
        'function run() external pure returns(int24) { R memory r=R(1,2); (r.a,r.b)=(3,4); return r.a; }',
        'run()', 'memory struct writes and rebinding'),
    'unsigned-member-write': ('', RECORD +
        'function run() external pure returns(uint8) { R memory r=R(1,2); r.b=3; return r.b; }',
        'run()', 'memory struct writes and rebinding'),
    'helper-write': ('', RECORD +
        'function h(R memory r) internal pure { r.b=3; } '
        'function run() external pure returns(uint8) { R memory r=R(1,2); h(r); return r.b; }',
        'run()', 'memory struct writes and rebinding'),
    'transitive-helper-write': ('', RECORD +
        'function h(R memory r) internal pure { r.b=3; } '
        'function g(R memory r) internal pure { h(r); } '
        'function run() external pure returns(uint8) { R memory r=R(1,2); g(r); return r.b; }',
        'run()', 'memory struct writes and rebinding'),
    'memory-alias': ('', RECORD +
        'function run() external pure returns(int24) { R memory r=R(1,2); R memory s=r; return s.a; }',
        'run()', 'struct local initializer must be'),
    'rebind': ('', RECORD +
        'function run() external pure returns(int24) { R memory r=R(1,2); r=R(3,4); return r.a; }',
        'run()', 'memory struct writes and rebinding'),
    'delete': ('', RECORD +
        'function run() external pure returns(int24) { R memory r=R(1,2); delete r; return r.a; }',
        'run()', 'memory struct writes and rebinding'),
    'increment': ('', RECORD +
        'function run() external pure returns(uint8) { R memory r=R(1,2); r.b++; return r.b; }',
        'run()', 'memory struct writes and rebinding'),
    'storage-copy': ('', RECORD + 'R s; '
        'function run() external view returns(int24) { R memory r=s; return r.a; }',
        'run()', 'storage references are outside'),
    'storage-reference': ('', RECORD + 'R s; '
        'function run() external view returns(int24) { R storage r=s; return r.a; }',
        'run()', 'storage references are outside'),
    'nested': ('', 'struct Inner { uint256 n; } struct R { Inner inner; } '
        'function run() external pure returns(uint256) { R memory r; return r.inner.n; }',
        'run()', 'memory structs require scalar fields'),
    'dynamic': ('', 'struct R { bytes data; } '
        'function run() external pure returns(uint256) { R memory r; return r.data.length; }',
        'run()', 'memory structs require scalar fields'),
    'fixed-array': ('', 'struct R { uint256[2] data; } '
        'function run() external pure returns(uint256) { R memory r; return r.data[0]; }',
        'run()', 'memory structs require scalar fields'),
    'enum': ('', 'enum E { A,B } struct R { E tag; } '
        'function run() external pure returns(uint256) { R memory r; return uint256(r.tag); }',
        'run()', 'memory structs require scalar fields'),
    'abi-parameter': ('pragma experimental ABIEncoderV2;', RECORD +
        'function run(R memory r) public pure returns(int24) { return r.a; }',
        'run(R)', 'struct ABI parameters are outside'),
    'return-reference': ('', RECORD +
        'function h(R memory r) internal pure returns(R memory) { return r; } '
        'function run() external pure returns(int24) { R memory r=R(1,2); return h(r).a; }',
        'run()', 'struct returns are outside'),
    'pointer-assembly': ('', RECORD +
        'function run() external pure returns(uint256 x) { R memory r=R(1,2); assembly { x := mload(r) } }',
        'run()', 'memory struct assembly references are outside'),
    'allocator-observation': ('', RECORD +
        'function run() external pure returns(uint256 x) { R memory r=R(1,2); '
        'assembly { let p := mload(64) mstore(p,1) x := p } return x+uint256(r.b); }',
        'run()', 'cannot share a reached closure with assembly'),
    'helper-allocator-observation': ('', RECORD +
        'function h() internal pure returns(uint256 x) { '
        'assembly { let p := mload(64) mstore(p,1) x := p } } '
        'function run() external pure returns(uint256) { R memory r=R(1,2); return h()+r.b; }',
        'run()', 'cannot share a reached closure with assembly'),
    'unreached-assembly': ('', RECORD +
        'function h() internal pure returns(uint256 x) { assembly { x := mload(64) } } '
        'function run() external pure returns(int24) { R memory r=R(1,2); return r.a; }',
        'run()', None),
    'effectful-positional-constructor': ('', RECORD +
        'function run(uint8 b) external pure returns(uint8) { R memory r=R(1,b++); return r.b; }',
        'run(uint8)', 'struct constructor arguments require effect-free evaluation'),
    'stateful-positional-constructor': ('', RECORD +
        'function h() internal returns(uint8) { stored++; return 1; } '
        'function run() external returns(uint8) { R memory r=R(1,h()); return r.b; }',
        'run()', 'struct constructor arguments require effect-free evaluation'),
    'multiple-failing-arguments': ('', RECORD +
        'function h() internal pure returns(int24) { revert("first"); } '
        'function g() internal pure returns(uint8) { revert("second"); } '
        'function run() external pure returns(uint8) { R memory r=R(h(),g()); return r.b; }',
        'run()', 'struct constructor has multiple potentially failing arguments'),
    'failing-enum-conversion': ('', 'enum E { A,B } struct R { uint8 a; uint8 b; } '
        'function h() internal pure returns(uint8) { revert("helper"); } '
        'function run(uint8 e) external pure returns(uint8) { R memory r=R(uint8(E(e)),h()); return r.b; }',
        'run(uint8)', 'struct constructor has multiple potentially failing arguments'),
    'effectful-named-constructor': ('', RECORD +
        'function run(uint8 b) external pure returns(uint8) { R memory r=R({a:1,b:b++}); return r.b; }',
        'run(uint8)', 'struct constructor arguments require effect-free evaluation'),
}

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--prepared', action='store_true')
    run(**vars(parser.parse_args()), cases=CASES)
