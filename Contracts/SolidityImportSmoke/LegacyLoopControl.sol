// SPDX-License-Identifier: MIT
pragma solidity 0.7.6;

// Source-only loop controls. Admission requires a corresponding loop model;
// finite test gas must never be substituted for a source termination bound.
contract LegacyLoopControl {
    uint256 public effects;

    function walk(uint256 count, uint256 skip, uint256 stop, uint256 fail, int24 delta)
        external returns (int24 accumulator)
    {
        uint256 i;
        while (i < count) {
            ++i;
            ++effects;
            require(i != fail, "loop");
            if (i == skip) continue;
            accumulator += delta;
            if (i == stop) break;
        }
        effects += 100;
    }

    function search(uint256 low, uint256 high, uint256 target, uint256 skipMask)
        external pure returns (uint256 middle)
    {
        while (true) {
            middle = (low + high) / 2;
            if ((skipMask & (uint256(1) << middle)) != 0) {
                low = middle + 1;
                continue;
            }
            if (middle == target) break;
            if (middle > target) high = middle - 1;
            else low = middle + 1;
        }
    }
}
