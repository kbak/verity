"""Located scalar-conditional admission and neighboring legacy rejections."""
import argparse
from pathlib import Path
from .check_legacy_void_rejections import run

DIVISION = 'legacy exceptional halt is not modeled'
PREFIX = 'function run(uint256 n,uint256 d) external pure returns(uint256) { '
SCALAR = 'conditionals require an unsigned, bool, address or fixed-bytes result'
CASES = {
    'scalar': ('', 'function run(bool f,uint256 a,uint256 b) external pure returns(uint256) '
        '{ return f ? a : b; }', 'run(bool,uint256,uint256)', None),
    'literal-branches': ('', 'function run(bool f) external pure returns(uint256) '
        '{ return f ? 1 : 2; }', 'run(bool)', None),
    'payable-address': ('', 'function run(bool f,address payable a,address payable b) '
        'external pure returns(address payable) { return f ? a : b; }',
        'run(bool,«address payable»,«address payable»)', None),
    'contract-address': ('contract C {}', 'function run(bool f,address a,address b) '
        'external pure returns(address) { return address(f ? C(a) : C(b)); }',
        'run(bool,address,address)', None),
    'guard-true': ('', PREFIX+'return d != 0 ? n/d : 0; }', 'run(uint256,uint256)', None),
    'guard-false': ('', PREFIX+'return d == 0 ? 0 : n/d; }', 'run(uint256,uint256)', None),
    'guard-negated': ('', PREFIX+'return !(d==0) ? n/d : 0; }', 'run(uint256,uint256)', None),
    'guard-conjunction': ('', PREFIX+'return d>0 && n>0 ? n/d : 0; }',
        'run(uint256,uint256)', None),
    'guard-disjunction-false': ('', PREFIX+'return d==0 || n==0 ? 0 : n/d; }',
        'run(uint256,uint256)', None),
    'wrong-edge': ('', PREFIX+'return d==0 ? n/d : 0; }', 'run(uint256,uint256)', DIVISION),
    'no-leaked-facts': ('', PREFIX+'uint256 q=d==0 ? 0 : 1; return n/d+q; }',
        'run(uint256,uint256)', DIVISION),
    'mutated-condition': ('', PREFIX+'return d++!=0 ? n/d : 0; }',
        'run(uint256,uint256)', DIVISION),
    'mutated-arm': ('', PREFIX+'return d!=0 ? n/(d=0) : 0; }',
        'run(uint256,uint256)', DIVISION),
    'truncation': ('', PREFIX+'return d!=0 ? n/uint8(d) : 0; }',
        'run(uint256,uint256)', DIVISION),
    'storage-guard': ('', 'function run(uint256 n) external view returns(uint256) '
        '{ return stored!=0 ? n/stored : 0; }', 'run(uint256)', DIVISION),
    'caller-guard': ('', 'function h(uint256 n,uint256 d) internal pure returns(uint256) '
        '{ return n/d; } '+PREFIX+'return d!=0 ? h(n,d) : 0; }',
        'run(uint256,uint256)', DIVISION),
    'unselected-unsafe': ('', PREFIX+'return false ? n/d : 0; }',
        'run(uint256,uint256)', DIVISION),
    'tuple-result': ('', 'function run(bool f) external pure returns(uint256,uint256) '
        '{ return f ? (uint256(1),uint256(2)) : (uint256(3),uint256(4)); }', 'run(bool)', SCALAR),
    'bytes-result': ('', 'function run(bool f,bytes memory a,bytes memory b) external pure '
        'returns(uint256) { return (f ? a : b).length; }', 'run(bool,bytes,bytes)', SCALAR),
    'narrow-root-abi': ('', 'function run(bool f,bytes5 a,bytes5 b) external pure '
        'returns(bytes5) { return f ? a : b; }', 'run(bool,bytes5,bytes5)',
        'narrow fixed-bytes root ABI is outside'),
    'enum-result': ('', 'enum E { A,B } function run(bool f) external pure returns(uint256) '
        '{ return uint256(f ? E.A : E.B); }', 'run(bool)', 'enum conditionals are outside'),
    'function-pointer': ('', 'function a() internal pure returns(uint256) { return 1; } '
        'function b() internal pure returns(uint256) { return 2; } '
        'function run(bool f) external pure returns(uint256) '
        '{ function() internal pure returns(uint256) h=f ? a : b; return h(); }', 'run(bool)',
        'does not support FunctionTypeName'),
    'signed': ('', 'function run(bool f,int256 a,int256 b) external pure returns(int256) '
        '{ return f ? a : b; }', 'run(bool,int256,int256)', 'does not support type int256'),
    'unselected-gas': ('', 'function run(bool f) external view returns(uint256) '
        '{ return f ? 1 : gasleft(); }', 'run(bool)', 'builtin call is outside'),
    'effectful-neighbor': ('', 'function h(uint256 a,uint256 b) internal pure returns(uint256) '
        '{ return a+b; } function run(bool f,uint256 n) external pure returns(uint256) '
        '{ return h(f ? n++ : 0,n); }', 'run(bool,uint256)', 'assignment expression in multi-argument call'),
    'post-call-storage': ('interface I { function hook() external; }',
        'function run(address t,bool f) external { I(t).hook(); stored=f ? 1 : 2; }',
        'run(address,bool)', None),
}

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--prepared', action='store_true')
    run(**vars(parser.parse_args()), cases=CASES)
