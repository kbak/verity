// SPDX-License-Identifier: MIT
pragma solidity 0.7.6;

contract LegacyStoredIntervalKeys {
    struct Record {
        uint32 key;
        bool initialized;
    }

    Record[8] private records;

    function find(uint256 low, uint256 high, uint32 target) external view returns (uint256 mid) {
        while (true) {
            mid = (low + high) / 2;
            if (!records[mid].initialized) {
                low = mid + 1;
                continue;
            }
            uint32 key = records[mid].key;
            if (key <= target && target <= records[mid + 1].key) break;
            if (target < key) high = mid - 1;
            else low = mid + 1;
        }
    }
}
