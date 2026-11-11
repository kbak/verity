// SPDX-License-Identifier: MIT
pragma solidity 0.7.6;

contract LegacyCalldataHash {
    enum Mode { Zero, One, Two }

    function digest(bytes calldata payload, address account, Mode mode, bytes32 tag, uint256 count)
        public pure returns (bytes32 result)
    {
        assembly {
            let ptr := mload(64)
            calldatacopy(ptr, payload.offset, payload.length)
            let payloadHash := keccak256(ptr, payload.length)
            mstore(ptr, tag)
            mstore(add(ptr, 32), account)
            mstore(add(ptr, 64), mode)
            mstore(add(ptr, 96), count)
            mstore(add(ptr, 128), payloadHash)
            mstore(add(ptr, 32), keccak256(ptr, 160))
            mstore(ptr, 0xabcdef)
            result := keccak256(add(ptr, 29), 35)
        }
    }

    function copy(bytes calldata payload, uint256 source, uint256 count)
        public pure returns (bytes32 result, uint256 free)
    {
        require(count <= 96, "count");
        assembly {
            let ptr := mload(64)
            mstore(ptr, 0x112233)
            mstore(add(ptr, 32), 0xaabbcc)
            mstore(add(ptr, 64), 0xddeeff)
            mstore(add(ptr, 96), 0x778899)
            calldatacopy(add(ptr, 1), source, count)
            result := keccak256(ptr, 128)
            free := mload(64)
        }
    }

    function overlap(bytes calldata payload) public pure returns (bytes32 result, uint256 tail) {
        assembly {
            let ptr := mload(64)
            mstore(add(ptr, 32), 0xff)
            calldatacopy(add(ptr, 31), payload.offset, payload.length)
            mstore(add(ptr, 1), keccak256(add(ptr, 31), payload.length))
            result := keccak256(add(ptr, 1), 64)
            tail := mload(add(ptr, 33))
        }
    }

    function narrow(bytes calldata payload, uint8 small, address account, bool flag)
        public pure returns (bytes32 result)
    {
        assembly {
            let ptr := mload(64)
            mstore(ptr, small)
            mstore(add(ptr, 32), account)
            mstore(add(ptr, 64), flag)
            result := keccak256(ptr, 96)
        }
    }

    function length(bytes calldata payload) public pure returns (uint256) { return payload.length; }

    function cast(uint256 value) public pure returns (Mode) { return Mode(value); }
    function castSmall(uint8 value) public pure returns (Mode) { return Mode(value); }
    function echo(Mode mode) public pure returns (Mode) { return mode; }
    function integer(Mode mode) public pure returns (uint256) { return uint256(mode); }
}
