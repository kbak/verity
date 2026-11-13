// SPDX-License-Identifier: MIT
pragma solidity 0.8.26;

// Construct-level controls: a different overlap and an explicit cleanup mask.
contract BoundedMemory {
    function overlap(uint16 shortWord, bytes32 tag) public pure returns (bytes32 result) {
        assembly ("memory-safe") {
            let pointer := mload(0x40)
            mstore(add(pointer, 1), tag)
            mstore(pointer, shortWord)
            result := keccak256(add(pointer, 30), 3)
            mstore(pointer, 0)
            mstore(add(pointer, 32), 0)
        }
    }

    function masked(uint16 shortWord) public pure returns (bytes32 result) {
        assembly ("memory-safe") {
            let pointer := mload(0x40)
            mstore(pointer, and(shortWord, 0xffff))
            result := keccak256(pointer, 32)
        }
    }

    function shifted(uint256 offset) public pure returns (bytes32 result) {
        require(offset <= 64, "offset");
        assembly ("memory-safe") {
            let pointer := add(mload(0x40), offset)
            mstore(pointer, 0x1234)
            result := keccak256(pointer, 32)
        }
    }
}
