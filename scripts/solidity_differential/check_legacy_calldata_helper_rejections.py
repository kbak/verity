"""Source boundaries for legacy internal calldata arguments and memory copies."""
import argparse
from pathlib import Path
from .check_legacy_void_rejections import run

MEMORY = 'function h(bytes memory b) internal pure returns(uint256) { return b.length; } '
CALLDATA = 'function h(bytes calldata b) internal pure returns(uint256) { return b.length; } '
ROOT = 'function run(bytes calldata b) external pure returns(uint256) { return h(b); }'
CASES = {
    'internal-memory-copy': ('', MEMORY+ROOT, 'run(bytes)', None),
    'internal-calldata-forward': ('', CALLDATA+ROOT, 'run(bytes)', None),
    'library-calldata-forward': ('library L { function h(bytes calldata b) internal pure '
        'returns(uint256) { return b.length; } }',
        'function run(bytes calldata b) external pure returns(uint256) { return L.h(b); }',
        'run(bytes)', None),
    'public-calldata-helper': ('', CALLDATA.replace('internal', 'public')+ROOT,
        'run(bytes)', None),
    'external-this-call': ('', CALLDATA.replace('internal', 'external')+
        ROOT.replace('external pure', 'external view').replace('return h(b)', 'return this.h(b)'), 'run(bytes)', 'calldata call arguments are outside'),
    'external-scalar-return': ('interface I { function h(bytes calldata b) external view '
        'returns(uint256); }', 'function run(address t,bytes calldata b) external view '
        'returns(uint256) { return I(t).h(b); }', 'run(address,bytes)', 'calldata call arguments are outside'),
    'caller-abi-v2': ('pragma experimental ABIEncoderV2;', MEMORY+ROOT,
        'run(bytes)', 'requires ABI coder v1'),
    'calldata-slice': ('', MEMORY+ROOT.replace('h(b)', 'h(b[1:])'),
        'run(bytes)', 'does not support IndexRangeAccess'),
    'calldata-reassignment': ('', 'function h(bytes calldata b,bytes calldata c) '
        'internal pure returns(uint256) { b=c; return b.length; } '+ROOT.replace('h(b)', 'h(b,b)'),
        'run(bytes)', 'assignment target is not scalar storage'),
    'calldata-indexing': ('', CALLDATA.replace('b.length', 'uint256(uint8(b[0]))')+ROOT,
        'run(bytes)', 'calldata indexing is outside'),
    'calldata-return': ('', 'function h(bytes calldata b) internal pure returns(bytes calldata) '
        '{ return b; } function run(bytes calldata b) external pure returns(uint256) '
        '{ return h(b).length; }', 'run(bytes)', 'msg.data helper call must take zero arguments'),
    'memory-construction': ('', MEMORY+ROOT.replace('h(b)', 'h(new bytes(b.length))'),
        'run(bytes)', 'byte construction is outside'),
    'independent-postincrement': ('', 'function h(bytes memory b,uint256 n) internal pure '
        'returns(uint256) { return b.length+n; } function run(bytes calldata b,uint256 n) '
        'external pure returns(uint256) { return h(b,n++); }', 'run(bytes,uint256)', None),
    'effectful-neighbor': ('', 'function h(bytes memory b,uint256 n) internal pure '
        'returns(uint256) { return b.length+n; } function run(bytes calldata b,uint256 n) '
        'external pure returns(uint256) { return h(b,n++ + 1); }', 'run(bytes,uint256)',
        'assignment expression in multi-argument call'),
    'post-call-write': ('interface I { function hook() external; }',
        MEMORY+'function run(bytes calldata b,address t) external { I(t).hook(); stored=h(b); }',
        'run(bytes,address)', 'storage-free trailing continuation'),
}

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--prepared', action='store_true')
    run(**vars(parser.parse_args()), cases=CASES)
