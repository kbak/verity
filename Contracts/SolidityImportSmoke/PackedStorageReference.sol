// SPDX-License-Identifier: MIT
pragma solidity 0.8.26;

contract PackedStorageReference {
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

    function packedKey(address account, int24 left, int24 right, bytes32 salt)
        internal pure returns (bytes32 digest)
    {
        assembly ("memory-safe") {
            let base := mload(0x40)
            mstore(add(base, 38), salt)
            mstore(add(base, 6), right)
            mstore(add(base, 3), left)
            mstore(base, account)
            digest := keccak256(add(base, 12), 58)
            // Deliberately retain the source pattern's partial cleanup.
            mstore(add(base, 64), 0)
        }
    }

    function locate(address account, int24 left, int24 right, bytes32 salt)
        internal view returns (Record storage row)
    {
        return bucket.records[packedKey(account, left, right, salt)];
    }

    function read(address account, int24 left, int24 right, bytes32 salt)
        external view returns (uint128, uint256, uint256)
    {
        Record storage row = locate(account, left, right, salt);
        return (row.count, row.accumulator, row.checkpoint);
    }

    function setCount(address account, int24 left, int24 right, bytes32 salt, uint128 next)
        external returns (uint128, uint256, uint256)
    {
        Record storage row = locate(account, left, right, salt);
        row.count = next;
        emit Changed(0, next);
        return (row.count, row.accumulator, row.checkpoint);
    }

    function setAccumulator(address account, int24 left, int24 right, bytes32 salt, uint256 next)
        external returns (uint128, uint256, uint256)
    {
        Record storage row = locate(account, left, right, salt);
        row.accumulator = next;
        emit Changed(1, next);
        return (row.count, row.accumulator, row.checkpoint);
    }

    function setCheckpoint(address account, int24 left, int24 right, bytes32 salt, uint256 next)
        external returns (uint128, uint256, uint256)
    {
        Record storage row = locate(account, left, right, salt);
        row.checkpoint = next;
        emit Changed(2, next);
        return (row.count, row.accumulator, row.checkpoint);
    }

    function writeThenRevert(address account, int24 left, int24 right, bytes32 salt, uint128 next)
        external returns (uint128, uint256, uint256)
    {
        Record storage row = locate(account, left, right, salt);
        row.count = next;
        emit Changed(0, next);
        revert Rejected(next);
    }
}
