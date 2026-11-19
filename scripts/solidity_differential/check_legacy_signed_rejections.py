"""Fail-closed boundaries next to admitted legacy signed integer expressions."""
import argparse
from pathlib import Path
from .check_legacy_void_rejections import run

CASES = {
    'clean-constant-assembly': ('', 'function h(uint8 x) internal pure returns(uint256 r) '
        '{ assembly { r := x } } function run() external pure returns(uint256) '
        '{ return h(uint8(255)); }', 'run()', None),
    'truncated-constant-assembly': ('', 'function h(uint8 x) internal pure returns(uint256 r) '
        '{ assembly { r := x } } function run() external pure returns(uint256) '
        '{ return h(uint8(256)); }', 'run()', 'assembly reads require full-word or literal'),
    'negative-constant-assembly': ('', 'function h(uint8 x) internal pure returns(uint256 r) '
        '{ assembly { r := x } } function run() external pure returns(uint256) '
        '{ return h(uint8(-1)); }', 'run()', 'assembly reads require full-word or literal'),
    'signed-mapping-key': ('', 'mapping(int128=>uint256) m; '
        'function run(int128 x) external view returns(uint256) { return m[x]; }',
        'run(int128)', 'signed mapping storage is outside'),
    'signed-mapping-key-getter': ('', 'mapping(int128=>uint256) public m;',
        'm(int128)', 'signed mapping storage is outside'),
    'signed-mapping-value-getter': ('', 'mapping(uint256=>int256) public m;',
        'm(uint256)', 'signed mapping storage is outside'),
    'address-to-narrow-signed-getter': ('', 'mapping(address=>int24) public m;',
        'm(address)', 'signed mapping storage is outside'),
    'nested-narrow-signed-value': ('', 'mapping(uint256=>mapping(uint256=>int24)) public m;',
        'm(uint256,uint256)', 'signed mapping storage is outside'),
    'narrow-signed-mapping-compound': ('', 'mapping(uint24=>int24) m; '
        'function run(uint24 k) external { m[k] += 1; }',
        'run(uint24)', 'signed compound assignments are outside'),
    'narrow-signed-mapping-order': ('', 'mapping(uint24=>int24) m; uint24 key; '
        'function next() internal returns(int24) { key=2; return -1; } '
        'function run() external { m[key] = next(); }', 'run()',
        'signed mapping writes require effect-free scalar keys and values'),
    'narrow-signed-mapping-helper': ('', 'mapping(uint24=>int24) m; '
        'function h(mapping(uint24=>int24) storage rows, uint24 k) internal view '
        'returns(int24) { return rows[k]; } function run(uint24 k) external view '
        'returns(int24) { return h(m,k); }', 'run(uint24)', 'signed scalar mapping values require direct'),
    'nested-signed-mapping': ('', 'mapping(uint256=>mapping(int128=>uint256)) m; '
        'function run(int128 x) external view returns(uint256) { return m[0][x]; }',
        'run(int128)', 'signed mapping storage is outside'),
    'signed-storage': ('', 'int128 s; function run() external view returns(int128) '
        '{ return s; }', 'run()', 'does not support type int128 in storage'),
    'signed-member': ('', 'struct S { int128 x; } S s; '
        'function run() external view returns(int128) { return s.x; }', 'run()',
        None),
    'signed-local-default': ('', 'function run() external pure returns(int128) '
        '{ int128 x; return x; }', 'run()', None),
    'signed-increment': ('', 'function run(int128 x) external pure returns(int128) '
        '{ x++; return x; }', 'run(int128)', 'signed unary operators require negation'),
    'signed-compound': ('', 'function run(int128 x) external pure returns(int128) '
        '{ x += 1; return x; }', 'run(int128)', 'signed compound assignments are outside'),
    'signed-shift': ('', 'function run(int128 x) external pure returns(int128) '
        '{ return x >> 1; }', 'run(int128)', None),
    'signed-bitwise': ('', 'function run(int128 x) external pure returns(int128) '
        '{ return x ^ 1; }', 'run(int128)', 'signed operators require arithmetic'),
    'signed-literal-division': ('', 'function run(int128 x) external pure returns(int128) '
        '{ return x/2; }', 'run(int128)', None),
    'signed-literal-modulo': ('', 'function run(int128 x) external pure returns(int128) '
        '{ return x%2; }', 'run(int128)', None),
    'signed-division': ('', 'function run(int128 x,int128 y) external pure returns(int128) '
        '{ require(y != 0); return x/y; }', 'run(int128,int128)', None),
    'signed-modulo': ('', 'function run(int128 x,int128 y) external pure returns(int128) '
        '{ require(y != 0); return x%y; }', 'run(int128,int128)', None),
    'negative-literal-division': ('', 'function run(int8 x) external pure returns(int8) '
        '{ return x / -1; }', 'run(int8)', None),
    'negative-divisor-arm': ('', 'function run(int24 x,int24 d) external pure returns(int24) '
        '{ return 0 > d ? x/d : x; }', 'run(int24,int24)', None),
    'nonzero-after-return': ('', 'function run(int24 x,int24 d) external pure returns(int24) '
        '{ if (d == 0) return x; return x % d; }', 'run(int24,int24)', None),
    'unprotected-division': ('', 'function run(int24 x,int24 d) external pure returns(int24) '
        '{ return x/d; }', 'run(int24,int24)', 'legacy exceptional halt'),
    'zero-allowed': ('', 'function run(int24 x,int24 d) external pure returns(int24) '
        '{ require(d >= 0); return x%d; }', 'run(int24,int24)', 'legacy exceptional halt'),
    'join-without-guard': ('', 'function run(bool f,int24 d) external pure returns(int24) '
        '{ if (f) require(d != 0); return 1/d; }', 'run(bool,int24)', 'legacy exceptional halt'),
    'mutated-divisor': ('', 'function run(int24 x,int24 d) external pure returns(int24) '
        '{ require(d != 0); d = x; return x/d; }', 'run(int24,int24)', 'legacy exceptional halt'),
    'narrowed-divisor': ('', 'function run(int24 x,int24 d) external pure returns(int24) '
        '{ require(d != 0); return x/int8(d); }', 'run(int24,int24)', 'legacy exceptional halt'),
    'caller-only-guard': ('', 'function h(int24 x,int24 d) internal pure returns(int24) '
        '{ return x/d; } function run(int24 x,int24 d) external pure returns(int24) '
        '{ require(d != 0); return h(x,d); }', 'run(int24,int24)', 'legacy exceptional halt'),
    'modifier-argument-before-guard': ('', 'modifier m(int24 q) { require(q != 0); _; } '
        'function run(int24 x,int24 d) external pure m(x/d) returns(int24) '
        '{ require(d != 0); return x; }', 'run(int24,int24)', 'legacy exceptional halt'),
    'signed-assembly': ('', 'function run(int256 x) external pure returns(int256 r) '
        '{ assembly { r := x } }', 'run(int256)', None),
    'narrow-signed-assembly-read': ('', 'function run(int24 x) external pure returns(int256 r) '
        '{ assembly { r := x } }', 'run(int24)', 'signed assembly'),
    'narrow-signed-assembly-write': ('', 'function run(int256 x) external pure returns(int24 r) '
        '{ assembly { r := x } }', 'run(int256)', 'signed assembly'),
    'signed-address': ('', 'function run(int256 x) external pure returns(address) '
        '{ return address(x); }', 'run(int256)', 'signed casts require integer'),
    'signed-bytes': ('', 'function run(int256 x) external pure returns(bytes32) '
        '{ return bytes32(x); }', 'run(int256)', 'signed casts require integer'),
    'signed-callback': ('interface I { function hook(int256 x) external; }',
        'function run(address t,int256 x) external { I(t).hook(x); }',
        'run(address,int256)', 'callback scalar type requires'),
}

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output',type=Path,required=True)
    parser.add_argument('--prepared',action='store_true')
    run(**vars(parser.parse_args()),cases=CASES)
