// SPDX-License-Identifier: MIT
pragma solidity 0.7.6;

interface IByteValidator {
    function validate(bytes32 digest, bytes memory signature) external view returns (bytes4);
    function isValidSignature(bytes32 digest, bytes memory signature) external view returns (bytes4);
}

abstract contract AbstractByteValidator {
    function validate(bytes32 digest, bytes memory signature) external view virtual returns (bytes4);
}

contract LegacySignatureCalls {
    function recover(bytes32 h, uint256 v, bytes32 r, bytes32 s) public pure returns (address) {
        return ecrecover(h, uint8(v), r, s);
    }
    function loop(bytes32 h, uint256 v, bytes32 r, bytes32 s, uint256 n) public pure returns (address) {
        require(n <= 4);
        address result;
        for (uint256 i = 0; i < n; ++i) result = ecrecover(h, uint8(v), r, s);
        return result;
    }
    function abstractWord(address target, bytes32 h, bytes memory data) public view returns (uint256) {
        return uint256(bytes32(AbstractByteValidator(target).validate(h, data)));
    }
    function twice(bytes32 h, uint256 v, bytes32 r, bytes32 s) public pure returns (address, address) {
        address first = ecrecover(h, uint8(v), r, s);
        address second = ecrecover(h, 0, r, s);
        return (first, second);
    }
    function inspect(bytes32 h, uint256 v, bytes32 r, bytes32 s) public pure returns (address, uint256) {
        address signer = ecrecover(h, uint8(v), r, s);
        uint256 pointer;
        assembly { pointer := mload(0x40) }
        return (signer, pointer);
    }
    function word(address target, bytes32 h, bytes memory data) public view returns (uint256) {
        bytes4 result = IByteValidator(target).validate(h, data);
        return uint256(bytes32(result));
    }
    function scratch(address target, bytes32 h, bytes memory data) public view returns (uint256, uint256) {
        uint256 end = 32 + ((data.length + 31) / 32) * 32;
        bytes4 result = IByteValidator(target).validate(h, data);
        uint256 raw;
        assembly { raw := mload(add(data, end)) }
        return (uint256(bytes32(result)), raw);
    }
    function check(address target, bytes32 h, bytes memory data) public view returns (bool) {
        return IByteValidator(target).isValidSignature(h, data) == 0x1626ba7e;
    }
    function checked(address target, bytes32 h, bytes memory data) public view returns (uint256) {
        if (IByteValidator(target).isValidSignature(h, data) != 0x1626ba7e) revert("signature");
        return data.length;
    }
    function gated(bool enabled, address target, bytes32 h, bytes memory data) public view returns (bool) {
        return enabled && IByteValidator(target).isValidSignature(h, data) == 0x1626ba7e;
    }
}
