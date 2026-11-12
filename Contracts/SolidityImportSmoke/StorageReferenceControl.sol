// SPDX-License-Identifier: MIT
pragma solidity 0.8.26;

contract StorageReferenceControl {
    struct Record { uint128 count; uint256 accumulator; uint256 checkpoint; }
    struct Bucket {
        uint256 beforeWord;
        mapping(bytes32 => Record) records;
        uint256 afterWord;
    }
    uint256 private outerBefore;
    Bucket private bucket;
    uint256 private outerAfter;

    event Changed(uint8 indexed field, uint256 next);
    error Rejected(uint128 next);

    function locate(bytes32 key)
        internal view returns (Record storage row)
    {
        return bucket.records[key];
    }

    function read(bytes32 key)
        external view returns (uint128, uint256, uint256)
    {
        Record storage row = locate(key);
        return (row.count, row.accumulator, row.checkpoint);
    }

    function setCount(bytes32 key, uint128 next)
        external returns (uint128, uint256, uint256)
    {
        Record storage row = locate(key);
        row.count = next;
        emit Changed(0, next);
        return (row.count, row.accumulator, row.checkpoint);
    }

    function setAccumulator(bytes32 key, uint256 next)
        external returns (uint128, uint256, uint256)
    {
        Record storage row = locate(key);
        row.accumulator = next;
        emit Changed(1, next);
        return (row.count, row.accumulator, row.checkpoint);
    }

    function setCheckpoint(bytes32 key, uint256 next)
        external returns (uint128, uint256, uint256)
    {
        Record storage row = locate(key);
        row.checkpoint = next;
        emit Changed(2, next);
        return (row.count, row.accumulator, row.checkpoint);
    }

    function writeThenRevert(bytes32 key, uint128 next)
        external
    {
        Record storage row = locate(key);
        row.count = next;
        emit Changed(0, next);
        revert Rejected(next);
    }
}
