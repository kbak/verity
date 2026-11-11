"""Located controls for commuting postfix arguments and rejected ordering dependencies."""
import argparse
from pathlib import Path
from .check_legacy_void_rejections import run

ORDER = 'assignment expression in multi-argument call'
HELPER = 'function h(uint256 a,uint256 b) internal pure returns(uint256) { return a+b; } '
ROOT = 'function run(uint256 n,uint256 t) external returns(uint256) { return '
CASES = {
    'local': ('', HELPER+ROOT+'h(n++,t); }', 'run(uint256,uint256)', None),
    'storage': ('', HELPER+ROOT+'h(t,stored++); }', 'run(uint256,uint256)', None),
    'literal': ('', HELPER+ROOT+'h(17,stored++); }', 'run(uint256,uint256)', None),
    'separate-storage': ('', 'uint256 other; '+HELPER+ROOT+'h(other,stored++); }',
        'run(uint256,uint256)', None),
    'narrow': ('', HELPER+'function run(uint8 n) external pure returns(uint256) '
        '{ return h(n++,17); }', 'run(uint8)', None),
    'calldata': ('', 'function h(bytes calldata b,uint256 n) internal pure returns(uint256) '
        '{ return b.length+n; } function run(bytes calldata b) external returns(uint256) '
        '{ return h(b,stored++); }', 'run(bytes)', None),
    'calldata-copy': ('', 'function h(bytes memory b,uint256 n) internal pure returns(uint256) '
        '{ return b.length+n; } function run(bytes calldata b) external returns(uint256) '
        '{ return h(b,stored++); }', 'run(bytes)', None),
    'string-copy': ('', 'function h(string memory b,uint256 n) internal pure returns(uint256) '
        '{ return bytes(b).length+n; } function run(string calldata b) external returns(uint256) '
        '{ return h(b,stored++); }', 'run(string)', 'scalar slice does not support type string calldata'),
    'ten-arguments': ('', 'enum E { A,B } '
        'function h(address a,uint256 v,bytes calldata b,E e,uint256 g,uint256 base,uint256 p,'
        'address token,address refund,uint256 old) internal view returns(uint256) '
        '{ return old+stored+b.length+v+g+base+p+uint256(e)+uint256(a)+uint256(token)+uint256(refund); } '
        'function run(address a,uint256 v,bytes calldata b,E e,uint256 g,uint256 base,uint256 p,'
        'address token,address refund) external returns(uint256) '
        '{ return h(a,v,b,e,g,base,p,token,refund,stored++); }',
        'run(address,uint256,bytes,E,uint256,uint256,uint256,address,address)', None),
    'sibling-read-before': ('', HELPER+ROOT+'h(n,n++); }', 'run(uint256,uint256)', ORDER),
    'sibling-read-after': ('', HELPER+ROOT+'h(n++,n); }', 'run(uint256,uint256)', ORDER),
    'storage-read': ('', HELPER+ROOT+'h(stored++,stored); }', 'run(uint256,uint256)', ORDER),
    'distinct-writes': ('', HELPER+ROOT+'h(n++,t++); }', 'run(uint256,uint256)', ORDER),
    'same-writes': ('', HELPER+ROOT+'h(n++,n++); }', 'run(uint256,uint256)', ORDER),
    'prefix': ('', HELPER+ROOT+'h(++n,t); }', 'run(uint256,uint256)', ORDER),
    'decrement': ('', HELPER+ROOT+'h(n--,t); }', 'run(uint256,uint256)', ORDER),
    'assignment': ('', HELPER+ROOT+'h(n=t,t); }', 'run(uint256,uint256)', ORDER),
    'nested-increment': ('', HELPER+ROOT+'h(n++ + 1,t); }', 'run(uint256,uint256)', ORDER),
    'conditional-increment': ('', HELPER+ROOT+'h(t==0 ? n++ : 0,t); }',
        'run(uint256,uint256)', ORDER),
    'computed-sibling': ('', HELPER+ROOT+'h(n++,t+1); }', 'run(uint256,uint256)', ORDER),
    'pure-sibling-call': ('', HELPER+ROOT+'h(n++,h(t,1)); }', 'run(uint256,uint256)', ORDER),
    'view-sibling-call': ('', HELPER+'function read() internal view returns(uint256) '
        '{ return stored; } '+ROOT+'h(stored++,read()); }', 'run(uint256,uint256)', ORDER),
    'mapping-target': ('', 'mapping(uint256=>uint256) m; '+HELPER+ROOT+'h(m[n]++,t); }',
        'run(uint256,uint256)', ORDER),
    'memory-sibling': ('', 'function h(bytes memory b,uint256 n) internal pure returns(uint256) '
        '{ return b.length+n; } function run(bytes memory b) public returns(uint256) '
        '{ return h(b,stored++); }', 'run(bytes)', ORDER),
    'two-calldata-siblings': ('', 'function h(bytes calldata a,bytes calldata b,uint256 n) '
        'internal pure returns(uint256) { return a.length+b.length+n; } '
        'function run(bytes calldata a,bytes calldata b) external returns(uint256) '
        '{ return h(a,b,stored++); }', 'run(bytes,bytes)', ORDER),
    'external': ('interface I { function hook(uint256 n) external; }',
        'function run(address t) external { I(t).hook(stored++); }', 'run(address)', 'effect-free'),
}

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--prepared', action='store_true')
    run(**vars(parser.parse_args()), cases=CASES)
