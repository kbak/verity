// SPDX-License-Identifier: MIT
pragma solidity 0.7.6;

contract LegacyHelperAssemblyScalars {
    enum Mode { First, Second, Third }
    uint256 private count;
    event Observed(uint256 account, uint256 mode, uint256 oldCount);

    function addressWord(address account) internal pure returns (uint256 result) {
        assembly { result := account }
    }
    function enumWord(Mode mode) internal pure returns (uint256 result) {
        assembly { result := mode }
    }
    function narrowWord(uint8 n) internal pure returns (uint256 result) {
        assembly { result := n }
    }
    function boolWord(bool b) internal pure returns (uint256 result) {
        assembly { result := b }
    }
    function forwardedAddress(address account) internal pure returns (uint256) {
        return addressWord(account);
    }
    function forwardedEnum(Mode mode) internal pure returns (uint256) {
        return enumWord(mode);
    }
    function pairWords(address account, Mode mode) internal pure returns (uint256, uint256) {
        return (addressWord(account), enumWord(mode));
    }
    function recordWords(address account, Mode mode, uint256 oldCount) internal {
        emit Observed(addressWord(account), enumWord(mode), oldCount);
    }
    function hashWords(address account, Mode mode, uint256 oldCount)
        internal pure returns (bytes32 result)
    {
        assembly {
            let ptr := mload(0x40)
            mstore(ptr, account)
            mstore(add(ptr, 0x20), mode)
            mstore(add(ptr, 0x40), oldCount)
            result := keccak256(ptr, 0x60)
        }
    }
    function set(uint256 n) external { count = n; }
    function direct(address account, Mode mode, uint8 n, bool b)
        external pure returns (uint256, uint256, uint256, uint256)
    {
        return (addressWord(account), enumWord(mode), narrowWord(n), boolWord(b));
    }
    function nested(address account, Mode mode) external pure returns (uint256, uint256) {
        return (forwardedAddress(account), forwardedEnum(mode));
    }
    function pair(address account, Mode mode) external pure returns (uint256, uint256) {
        return pairWords(account, mode);
    }
    function payableAddress(address payable account) external pure returns (uint256) {
        return addressWord(account);
    }
    function repeated(address first, address second) external pure returns (uint256, uint256) {
        return (addressWord(first), addressWord(second));
    }
    function checkedEnum(Mode mode) external pure returns (uint256, uint256) {
        return (enumWord(mode), uint256(mode));
    }
    function record(address account, Mode mode, bool fail) external {
        recordWords(account, mode, count++);
        require(!fail, "outer");
    }
    function digest(address account, Mode mode, bool fail) external returns (bytes32) {
        bytes32 result = hashWords(account, mode, count++);
        require(!fail, "outer");
        return result;
    }
}
