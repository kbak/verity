// SPDX-License-Identifier: MIT
pragma solidity 0.8.26;

contract PackedStorageRead {
    struct Record { uint128 count; uint256 accumulator; uint256 checkpoint; }
    struct Bucket {
        uint256 beforeWord;
        mapping(bytes32 => Record) records;
        uint256 afterWord;
    }
    uint256 private outerBefore;
    Bucket private bucket;
    uint256 private outerAfter;

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
            mstore(base, 0)
            mstore(add(base, 32), 0)
            mstore(add(base, 64), 0)
        }
    }

    function digest(address account, int24 left, int24 right, bytes32 salt)
        external pure returns (bytes32)
    {
        return packedKey(account, left, right, salt);
    }

    function readKey(bytes32 key) external view returns (uint128, uint256, uint256) {
        Record storage row = bucket.records[key];
        return (row.count, row.accumulator, row.checkpoint);
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
}
