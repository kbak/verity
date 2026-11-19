// SPDX-License-Identifier: MIT
pragma solidity 0.7.6;

contract LegacyIntervalSearch {
    function search(uint8 left, uint8 right, uint8 skip, uint8 target, uint8 fail)
        external pure returns (uint256)
    {
        uint8 low = left;
        uint8 high = right;
        uint8 middle;
        uint256 trace;
        while (true) {
            middle = (low + high) / 2;
            if (middle <= low || middle >= high) break;
            trace = trace * 256 + middle;
            if (middle == skip) {
                low = middle + 1;
                continue;
            }
            if (middle == 255 - skip) {
                high = middle - 1;
                continue;
            }
            require(middle != fail);
            if (middle == target) break;
            if (middle > target) high = middle - 1;
            else low = middle + 1;
        }
        return trace * 256 + middle;
    }

    function unguarded(uint8 left, uint8 right, uint8 target) external pure returns (uint8) {
        uint8 low = left;
        uint8 high = right;
        uint8 middle;
        while (true) {
            middle = (low + high) / 2;
            if (middle == target) break;
            if (middle > target) high = middle - 1;
            else low = middle + 1;
        }
        return middle;
    }
}
