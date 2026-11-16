// SPDX-License-Identifier: MIT
pragma solidity 0.7.6;

contract LegacyObservedStorage {
    uint256 total;
    uint256 afterCalls;
    struct Record { uint128 low; uint128 high; }
    Record[3] records;
    mapping(uint256 => uint256) values;

    function walk(uint256 n, uint256 stop, uint256 fail) external returns (uint256 result) {
        result = walkHelper(n, stop, fail);
        afterCalls += 100;
    }

    function walkHelper(uint256 n, uint256 stop, uint256 fail) internal returns (uint256 result) {
        while (result < n) {
            ++result;
            total += result;
            require(result != fail, "helper");
            if (result == stop) return result;
            if (result == 2) continue;
            afterCalls += 1;
        }
    }

    function nested(uint256 n) external returns (uint256 result) {
        uint256 i;
        while (i < n) {
            uint256 got = walkHelper(2, 1, 0);
            afterCalls += got;
            ++i;
            if (i == 2) continue;
            afterCalls += 10;
        }
        result = total;
    }

    function record(uint256 index, uint128 delta, uint256 n)
        external returns (uint256 result, uint256 nextIndex)
    {
        result = recordHelper(records[index], delta, n);
        nextIndex = index + 1;
        afterCalls += 100;
    }

    function ambiguousRecord(uint256 index, uint128 delta, uint256 n)
        external returns (uint256 result, uint256 nextIndex)
    {
        result = recordHelper(records[index++], delta, n);
        nextIndex = index;
        afterCalls += 100;
    }

    function capture(uint256 index) external returns (uint256 result, uint256 nextIndex) {
        result = captureHelper(records[index++]);
        nextIndex = index;
    }

    function captureHelper(Record storage item) internal returns (uint256 result) {
        while (result < 2) {
            item.low += 1;
            ++result;
        }
        return item.low;
    }

    function recordHelper(Record storage item, uint128 delta, uint256 n)
        internal returns (uint256 result)
    {
        while (result < n) {
            item.low += delta;
            ++result;
            if (result == 2) return item.low;
        }
        return item.low;
    }

    function mappingLoop(uint256 key, uint256 n) external returns (uint256 result) {
        result = mappingHelper(values, key, n);
        afterCalls += 100;
    }

    function mappingHelper(mapping(uint256 => uint256) storage items, uint256 key, uint256 n)
        internal returns (uint256 result)
    {
        while (result < n) {
            items[key] += 1;
            ++result;
        }
        return items[key];
    }

    function voidLoop(uint256 n, uint256 stop) external returns (uint256 result) {
        voidHelper(n, stop);
        result = total;
        afterCalls += 100;
    }

    function voidHelper(uint256 n, uint256 stop) internal {
        uint256 i;
        while (i < n) {
            ++i;
            total += i;
            if (i == stop) return;
        }
    }

    function through(uint256 n, uint256 fail) external returns (uint256 result) {
        total += 10;
        result = forward(n, fail);
        afterCalls += 1000;
    }

    function forward(uint256 n, uint256 fail) internal returns (uint256 result) {
        result = walkHelper(n, 1, fail);
        afterCalls += 7;
        return result;
    }

    function stateBound(uint256 limit) external returns (uint256 result) {
        while (total < limit) {
            voidHelper(1, 0);
        }
        result = total;
    }

    function recursive(uint256 n) external returns (uint256 result) {
        result = recursionHelper(n);
    }

    function recursionHelper(uint256 n) internal returns (uint256 result) {
        if (n == 0) return 0;
        result = recursionHelper(n - 1);
    }
}
