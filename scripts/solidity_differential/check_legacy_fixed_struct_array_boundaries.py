"""Admit flat fixed storage arrays while preserving unsupported aggregate boundaries."""
import argparse
from pathlib import Path
from .check_legacy_void_rejections import run

RECORD = 'struct R { int24 delta; uint8 neighbor; } '
CASES = {
    'fixed-element': ('', RECORD + 'R[3] rows; '
        'function run(uint256 k) external view returns(int24) { return rows[k].delta; }',
        'run(uint256)', None),
    'fixed-helper': ('', RECORD + 'R[3] rows; '
        'function h(R[3] storage a,uint256 k) internal view returns(int24) { return a[k].delta; } '
        'function run(uint256 k) external view returns(int24) { return h(rows,k); }',
        'run(uint256)', None),
    'dynamic-array': ('', RECORD + 'R[] rows; '
        'function run(uint256 k) external view returns(int24) { return rows[k].delta; }',
        'run(uint256)', 'storage references are outside'),
    'nested-array': ('', RECORD + 'R[2][3] rows; '
        'function run(uint256 k) external view returns(int24) { return rows[k][0].delta; }',
        'run(uint256)', 'storage references are outside'),
    'record-copy': ('', RECORD + 'R[3] rows; '
        'function run(uint256 k) external view returns(int24) { R memory r=rows[k]; return r.delta; }',
        'run(uint256)', 'storage copies to memory'),
    'whole-record-write': ('', RECORD + 'R[3] rows; '
        'function run(uint256 k) external { rows[k]=rows[0]; }',
        'run(uint256)', 'storage references are outside'),
    'helper-rebind': ('', RECORD + 'R[3] rows; R[3] other; '
        'function h(R[3] storage a) internal { a=other; a[0].delta=1; } '
        'function run() external { h(rows); }', 'run()',
        'reassigned fixed storage struct array parameters are outside this slice'),
    'nested-record': ('', RECORD + 'struct S { R r; } S[3] rows; '
        'function run(uint256 k) external view returns(int24) { return rows[k].r.delta; }',
        'run(uint256)', 'storage references are outside'),
}

if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--prepared', action='store_true')
    run(**vars(parser.parse_args()), cases=CASES)
