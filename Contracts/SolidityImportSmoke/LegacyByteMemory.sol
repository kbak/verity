// SPDX-License-Identifier: MIT
pragma solidity >=0.7.6 <0.8.0;

contract LegacyByteMemory {
    function _decode(bytes memory data, uint256 index)
        internal pure returns (uint8 lane, bytes32 first, bytes32 second)
    {
        assembly {
            let offset := mul(0x41, index)
            first := mload(add(data, add(offset, 0x20)))
            second := mload(add(data, add(offset, 0x40)))
            lane := byte(0, mload(add(data, add(offset, 0x60))))
        }
    }

    function decode(bytes memory data, uint256 index)
        public pure returns (uint8, bytes32, bytes32)
    {
        return _decode(data, index);
    }

    function inspect(bytes memory data, bytes memory next, uint256 offset)
        public pure returns (bytes32 word, uint256 length, uint256 nextLength)
    {
        bytes memory aliasData = data;
        assembly { word := mload(add(offset, aliasData)) }
        return (word, data.length, next.length);
    }
}

contract LegacyByteMemoryOne is LegacyByteMemory { uint256 private firstField; }
contract LegacyByteMemoryTwo is LegacyByteMemoryOne { uint256 private secondField; }
