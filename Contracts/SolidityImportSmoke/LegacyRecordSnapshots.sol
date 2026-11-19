// SPDX-License-Identifier: MIT
pragma solidity 0.7.6;

contract LegacyRecordSnapshots {
    uint256 private pad;
    struct Row {
        uint32 key;
        int56 delta;
        bool ready;
        uint256 payload;
    }
    Row[3] private rows;

    function scan(uint256 low, uint256 high, uint256 target, uint256 count, int56 replacement)
        external returns (bytes32, bytes32)
    {
        Row memory first = Row(0, 0, false, 0);
        Row memory second = Row(0, 0, false, 0);
        uint256 middle;
        while (true) {
            middle = (low + high) / 2;
            first = rows[middle % count];
            rows[middle % count].delta = replacement;
            second = rows[(middle + 1) % count];
            if (!first.ready) {
                low = middle + 1;
                continue;
            }
            if (middle == target) break;
            if (middle > target) high = middle - 1;
            else low = middle + 1;
        }
        return (keccak256(abi.encode(first.key, first.delta, first.ready, first.payload)),
                keccak256(abi.encode(second.key, second.delta, second.ready, second.payload)));
    }
}
