// SPDX-License-Identifier: MIT
pragma solidity 0.7.6;
contract LegacyByteMemoryRejections {
    function index(bytes memory data, uint256 pos) public pure returns (bytes1) {
        return data[pos];
    }
    function allocate(uint256 n) public pure returns (uint256) {
        bytes memory data = new bytes(n);
        return data.length;
    }
    function returnBytes(bytes memory data) public pure returns (bytes memory) { return data; }
    function calldataBuffer(bytes calldata data) external pure returns (uint256) { return data.length; }
    function dirtyRead(bytes memory data, uint256 x) public pure returns (bytes32 word) {
        uint8 small = uint8(x);
        assembly { word := mload(add(data, small)) }
    }
    function dirtyWrite(bytes memory data) public pure returns (uint8 small) {
        assembly { small := mload(add(data, 32)) }
    }
    function pointerWrite(bytes memory data) public pure returns (uint256) {
        assembly { data := 0 }
        return data.length;
    }
    function memoryWrite(bytes memory data) public pure returns (uint256) {
        assembly { mstore(data, 0) }
        return data.length;
    }
    function _len(bytes memory data) internal pure returns (uint256) { return data.length; }
    function literalBuffer(uint256) public pure returns (uint256) { return _len("x"); }
    function uninitialized(uint256) public pure returns (uint256) {
        bytes memory data;
        return data.length;
    }
    function _word(bytes memory data) internal pure returns (bytes32 result) {
        assembly { result := mload(add(data, 32)) }
    }
    function encodedArgument(uint256 x) public pure returns (bytes32) {
        return _word(abi.encode(x));
    }
    function replacement(bytes memory data) public pure returns (uint256) {
        data = "x";
        return data.length;
    }
    function _dirty(bytes memory data) internal pure returns (uint8 small) {
        assembly { small := mload(add(data, 32)) }
    }
    function helperDirtyWrite(bytes memory data) public pure returns (uint256) {
        return _dirty(data);
    }
}

contract LegacyByteMemoryRejectionsTwo is LegacyByteMemoryRejections {
    uint256 private firstField;
    uint256 private secondField;
}
