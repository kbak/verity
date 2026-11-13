"""Fail-closed boundaries next to admitted legacy signed integer expressions."""
import argparse
from pathlib import Path
from .check_legacy_void_rejections import run

CASES = {
    'signed-storage': ('', 'int128 s; function run() external view returns(int128) '
        '{ return s; }', 'run()', 'does not support type int128 in storage'),
    'signed-member': ('', 'struct S { int128 x; } S s; '
        'function run() external view returns(int128) { return s.x; }', 'run()',
        'does not support type int128 in storage'),
    'signed-local-default': ('', 'function run() external pure returns(int128) '
        '{ int128 x; return x; }', 'run()', None),
    'signed-increment': ('', 'function run(int128 x) external pure returns(int128) '
        '{ x++; return x; }', 'run(int128)', 'signed unary operators require negation'),
    'signed-compound': ('', 'function run(int128 x) external pure returns(int128) '
        '{ x += 1; return x; }', 'run(int128)', 'signed compound assignments are outside'),
    'signed-shift': ('', 'function run(int128 x) external pure returns(int128) '
        '{ return x >> 1; }', 'run(int128)', 'signed operators require arithmetic'),
    'signed-division': ('', 'function run(int128 x,int128 y) external pure returns(int128) '
        '{ require(y != 0); return x/y; }', 'run(int128,int128)', 'legacy exceptional halt'),
    'signed-modulo': ('', 'function run(int128 x,int128 y) external pure returns(int128) '
        '{ require(y != 0); return x%y; }', 'run(int128,int128)', 'legacy exceptional halt'),
    'signed-assembly': ('', 'function run(int256 x) external pure returns(int256 r) '
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
