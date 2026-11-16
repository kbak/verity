"""Storage aliases must not admit copies, rebinding, or array aggregate paths."""
import argparse
from pathlib import Path
from .check_legacy_void_rejections import run

RECORD = 'struct R { int24 delta; uint8 neighbor; } R first; R second; '
CASES = {
    'single-result': ('', RECORD +
        'function h() internal view returns(R storage) { return first; } '
        'function run() external view returns(int24) { R storage r=h(); return r.delta; }',
        'run()', None),
    'single-conditional-result': ('', RECORD +
        'function h(bool b) internal view returns(R storage) { if(b) return first; return second; } '
        'function run(bool b) external view returns(int24) { R storage r=h(b); return r.delta; }',
        'run(bool)', 'unsupported statement in storage pointer helper'),
    'named-single-continuation': ('', RECORD +
        'function h() internal returns(R storage r) { r=first; r.delta=r.delta+1; } '
        'function run() external returns(int24) { R storage r=h(); return r.delta; }',
        'run()', None),
    'named-single-branch': ('', RECORD +
        'function h(bool b) internal returns(R storage r) { '
        'if(b) r=first; else r=second; r.delta=r.delta+1; } '
        'function run(bool b) external returns(int24) { R storage r=h(b); return r.delta; }',
        'run(bool)', None),
    'named-single-actual-return': ('', RECORD +
        'function h() internal returns(R storage r) { r=first; return r; r.delta=7; } '
        'function run() external returns(int24) { R storage r=h(); return r.delta; }',
        'run()', 'statement after void helper return'),
    'named-single-local-rebind': ('', RECORD +
        'function h() internal returns(R storage r) { r=first; '
        'R storage aliasRow=r; aliasRow=second; } '
        'function run() external returns(int24) { R storage r=h(); return r.delta; }',
        'run()', 'reassigned storage pointer locals are outside this slice'),
    'named-single-modifier': ('', RECORD +
        'modifier checked() { _; } '
        'function h() internal view checked returns(R storage r) { r=first; } '
        'function run() external view returns(int24) { R storage r=h(); return r.delta; }',
        'run()', 'modifiers on storage pointer helpers are outside this slice'),
    'named-single-signed-compound': ('', RECORD +
        'function h() internal returns(R storage r) { r=first; r.delta+=1; } '
        'function run() external returns(int24) { R storage r=h(); return r.delta; }',
        'run()', 'Solidity 0.7.6 signed compound assignments are outside the scalar slice'),
    'rebind': ('', RECORD +
        'function run() external { R storage r=first; r=second; r.delta=1; }',
        'run()', 'storage references are outside'),
    'whole-copy': ('', RECORD +
        'function run() external { first=second; }', 'run()', 'storage references are outside'),
    'nested-record': ('', 'struct Inner { int24 x; } struct R { Inner inner; } R first; '
        'function run() external view returns(int24) { R storage r=first; return r.inner.x; }',
        'run()', 'structs require scalar fields'),
    'mapping-path': ('', RECORD + 'mapping(uint256=>R) table; '
        'function run(uint256 k) external view returns(int24) { R storage r=table[k]; return r.delta; }',
        'run(uint256)', None),
    'signed-key': ('', RECORD + 'mapping(int24=>R) table; '
        'function run(int24 k) external view returns(int24) { R storage r=table[k]; return r.delta; }',
        'run(int24)', 'signed mapping storage is outside'),
    'array-path': ('', RECORD + 'R[] rows; '
        'function run(uint256 k) external view returns(int24) { R storage r=rows[k]; return r.delta; }',
        'run(uint256)', 'storage references are outside'),
    'nested-mapping-path': ('', RECORD + 'mapping(uint256=>mapping(uint256=>R)) table; '
        'function run(uint256 k) external view returns(int24) { R storage r=table[k][k]; return r.delta; }',
        'run(uint256)', 'storage references are outside'),
    'nested-mapping-helper': ('', RECORD + 'mapping(uint256=>mapping(uint256=>R)) table; '
        'function h(mapping(uint256=>mapping(uint256=>R)) storage m) internal view '
        'returns(uint256) { return 1; } '
        'function run() external view returns(uint256) { return h(table); }',
        'run()', 'storage mapping arguments require a single mapping key'),
    'assembly-alias': ('', RECORD +
        'function run() external view returns(uint256 x) { R storage r=first; '
        'assembly { x := sload(r.slot) } }', 'run()', 'unbound Yul identifier r.slot'),
    'mixed-result': ('', RECORD +
        'function h() internal view returns(R storage,uint256) { return (first,1); } '
        'function run() external view returns(int24) { (R storage r,)=h(); return r.delta; }',
        'run()', None),
    'named-mixed-result': ('', RECORD +
        'function h(bool b) internal view returns(R storage r,int24 x) { '
        'if(b) r=second; else r=first; x=r.delta; } '
        'function run(bool b) external returns(int24) { (R storage r,int24 x)=h(b); '
        'r.delta=x+1; return r.delta; }', 'run(bool)', None),
    'named-default-scalar': ('', RECORD +
        'function h() internal view returns(R storage r,uint256 x) { r=first; } '
        'function run() external view returns(int24,uint256) { (R storage r,uint256 x)=h(); '
        'return (r.delta,x); }', 'run()', None),
    'named-rebinding': ('', RECORD +
        'function h() internal view returns(R storage r,int24 x) { r=first; '
        'x=r.delta; r=second; return (r,x); } '
        'function run() external view returns(int24,int24) { (R storage r,int24 x)=h(); '
        'return (r.delta,x); }', 'run()', None),
    'mixed-local-rebind': ('', RECORD +
        'function h() internal view returns(R storage,uint256) { return (first,1); } '
        'function run() external { (R storage r,)=h(); r=second; r.delta=1; }',
        'run()', 'storage references are outside'),
    'mixed-storage-to-memory': ('pragma experimental ABIEncoderV2;', RECORD +
        'function h() internal view returns(R storage,uint256) { return (first,1); } '
        'function run() external view returns(int24) { (R memory r,)=h(); return r.delta; }',
        'run()', 'tuple declaration arity'),
    'mixed-memory-result': ('pragma experimental ABIEncoderV2;', RECORD +
        'function h() internal view returns(R memory,uint256) { return (first,1); } '
        'function run() external view returns(int24) { (R memory r,)=h(); return r.delta; }',
        'run()', 'storage tuple references cannot be converted'),
    'mixed-helper-modifier': ('', RECORD +
        'modifier checked() { _; } '
        'function h() internal view checked returns(R storage,uint256) { return (first,1); } '
        'function run() external view returns(int24) { (R storage r,)=h(); return r.delta; }',
        'run()', None),
    'mixed-nested-body': ('', RECORD +
        'modifier checked() { { _; } } '
        'function h(bool b) internal view checked returns(R storage r,uint256 x) '
        '{ r=first; x=1; } '
        'function run(bool b) external view returns(int24) { (R storage r,)=h(b); return r.delta; }',
        'run(bool)', 'storage tuple modifiers require an unconditional body placeholder'),
    'mixed-repeated-body': ('', RECORD +
        'modifier checked() { _; _; } '
        'function h() internal view checked returns(R storage,uint256) { return (first,1); } '
        'function run() external view returns(int24) { (R storage r,)=h(); return r.delta; }',
        'run()', 'only a single top-level'),
}


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--prepared', action='store_true')
    run(**vars(parser.parse_args()), cases=CASES)
