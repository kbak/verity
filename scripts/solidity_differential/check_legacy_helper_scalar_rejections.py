"""Clean-width provenance must not admit dirty casts, writes or reused bindings."""
import argparse
from pathlib import Path
from .check_legacy_void_rejections import run

DIRTY = 'assembly reads require full-word or literal scalars'
ADDRESS = 'function h(address a) internal pure returns(uint256 r) { assembly { r := a } } '
NARROW = 'function h(uint8 a) internal pure returns(uint256 r) { assembly { r := a } } '
ENUM = 'enum E { A,B,C } function h(E e) internal pure returns(uint256 r) { assembly { r := e } } '
CASES = {
    'address-forward': ('', ADDRESS+'function run(address a) external pure returns(uint256) '
        '{ return h(a); }', 'run(address)', None),
    'payable-forward': ('', ADDRESS+'function run(address payable a) external pure returns(uint256) '
        '{ return h(a); }', 'run(«address payable»)', None),
    'enum-forward': ('', ENUM+'function run(E e) external pure returns(uint256) '
        '{ return h(e); }', 'run(E)', None),
    'cast': ('', ADDRESS+'function run(uint256 n) external pure returns(uint256) '
        '{ return h(address(n)); }', 'run(uint256)', DIRTY),
    'local-cast': ('', ADDRESS+'function run(uint256 n) external pure returns(uint256) '
        '{ address a=address(n); return h(a); }', 'run(uint256)', DIRTY),
    'clean-then-dirty': ('', ADDRESS+'function run(address a,uint256 n) external pure returns(uint256) '
        '{ uint256 first=h(a); return first+h(address(n)); }', 'run(address,uint256)', DIRTY),
    'nested-dirty': ('', ADDRESS+'function f(uint256 n) internal pure returns(uint256) '
        '{ return h(address(n)); } function run(address a,uint256 n) external pure returns(uint256) '
        '{ uint256 first=h(a); return first+f(n); }', 'run(address,uint256)', DIRTY),
    'root-assigned': ('', ADDRESS+'function run(address a,uint256 n) external pure returns(uint256) '
        '{ a=address(n); return h(a); }', 'run(address,uint256)', DIRTY),
    'helper-assigned': ('', 'function h(address a,uint256 n) internal pure returns(uint256 r) '
        '{ a=address(n); assembly { r := a } } '
        'function run(address a,uint256 n) external pure returns(uint256) { return h(a,n); }',
        'run(address,uint256)', DIRTY),
    'helper-later-write': ('', 'function h(uint8 a) internal pure returns(uint256 r) '
        '{ assembly { r := a } a++; } '
        'function run(uint8 a) external pure returns(uint256) { return h(a); }', 'run(uint8)', DIRTY),
    'postincrement': ('', NARROW+'function run(uint8 a) external pure returns(uint256) '
        '{ return h(a++); }', 'run(uint8)', DIRTY),
    'arithmetic': ('', NARROW+'function run(uint8 a) external pure returns(uint256) '
        '{ return h(a+1); }', 'run(uint8)', DIRTY),
    'narrow-cast': ('', NARROW+'function run(uint256 a) external pure returns(uint256) '
        '{ return h(uint8(a)); }', 'run(uint256)', DIRTY),
    'enum-cast': ('', ENUM+'function run(uint256 n) external pure returns(uint256) '
        '{ return h(E(n)); }', 'run(uint256)', DIRTY),
    'helper-yul-write': ('', 'function h(uint8 a) internal pure returns(uint256 r) '
        '{ assembly { a := 1 r := a } } '
        'function run(uint8 a) external pure returns(uint256) { return h(a); }', 'run(uint8)', DIRTY),
    'root-modifier-write': ('', 'modifier m(uint8 n) { _; } '+NARROW+
        'function run(uint8 a) external pure m(a++) returns(uint256) { return h(a); }',
        'run(uint8)', 'only materialized scalar locals are writable'),
    'helper-modifier-write': ('', 'modifier m(uint8 n) { _; } '
        'function h(uint8 a) internal pure m(a++) returns(uint256 r) { assembly { r := a } } '
        'function run(uint8 a) external pure returns(uint256) { return h(a); }',
        'run(uint8)', 'only materialized scalar locals are writable'),
    'bound-enum-receiver': ('library L { enum E { A,B,C } '
        'function h(E e) internal pure returns(uint256 r) { assembly { r := e } } }',
        'using L for L.E; function run(L.E e) external pure returns(uint256) { return e.h(); }',
        'run(L.E)', DIRTY),
    'static-library-enum': ('library L { enum E { A,B,C } '
        'function h(E e) internal pure returns(uint256 r) { assembly { r := e } } }',
        'function run(L.E e) external pure returns(uint256) { return L.h(e); }',
        'run(L.E)', None),
}

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--prepared', action='store_true')
    run(**vars(parser.parse_args()), cases=CASES)
