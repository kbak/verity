// SPDX-License-Identifier: MIT
pragma solidity 0.7.6;

interface IBytesValidator {
    function validate(bytes32 hash, bytes memory data) external view returns (bytes4);
}
interface IScalarPredicate {
    function query(uint256 value) external view returns (bool);
}

contract LegacyStaticCallGas {
    function recover(bytes32 h, uint256 v, bytes32 r, bytes32 s)
        external view returns (address, uint256)
    {
        uint256 beforeGas = gasleft();
        address result = ecrecover(h, uint8(v), r, s);
        return (result, beforeGas - gasleft());
    }

    function repeated(bytes32 h, uint256 v, bytes32 r, bytes32 s)
        external view returns (address, address, uint256)
    {
        uint256 beforeGas = gasleft();
        address first = ecrecover(h, uint8(v), r, s);
        address second = ecrecover(h, uint8(0), r, s);
        return (first, second, beforeGas - gasleft());
    }

    function boundary(bytes32 h, uint256 v, bytes32 r, bytes32 s) external pure {
        require(ecrecover(h, uint8(v), r, s) == address(0));
    }

    function word(address target, bytes32 h, bytes memory data)
        public view returns (uint256, uint256)
    {
        uint256 beforeGas = gasleft();
        bytes4 result = IBytesValidator(target).validate(h, data);
        return (uint256(bytes32(result)), beforeGas - gasleft());
    }

    function checked(address target, bytes32 h, bytes memory data) public view returns (uint256) {
        require(IBytesValidator(target).validate(h, data) == bytes4(0x1626ba7e), "validator");
        return data.length;
    }

    function predicate(address target, uint256 value) external view returns (bool, uint256) {
        uint256 beforeGas = gasleft();
        bool result = IScalarPredicate(target).query(value);
        return (result, beforeGas - gasleft());
    }

    function gated(bool enabled, address target, uint256 value) external view returns (bool) {
        if (enabled) return IScalarPredicate(target).query(value);
        return false;
    }
}
