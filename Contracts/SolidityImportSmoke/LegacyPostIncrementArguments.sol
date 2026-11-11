// SPDX-License-Identifier: MIT
pragma solidity 0.7.6;

contract LegacyPostIncrementArguments {
    uint256 private count;
    event Observed(uint256 tag, uint256 argument, uint256 current);

    function set(uint256 n) external { count = n; }
    function observe(uint256 tag, bool fail, uint256 old) internal returns (uint256) {
        emit Observed(tag, old, count);
        require(!fail, "helper");
        return old;
    }
    function last(uint256 tag, bool failHelper, bool failOuter) external returns (uint256) {
        uint256 old = observe(tag, failHelper, count++);
        require(!failOuter, "outer");
        return old;
    }
    function firstHelper(uint256 old, uint256 tag, bool fail) internal returns (uint256) {
        return observe(tag, fail, old);
    }
    function first(uint256 tag, bool fail) external returns (uint256) {
        return firstHelper(count++, tag, fail);
    }
    function middleHelper(uint256 tag, uint256 old, bool fail) internal returns (uint256) {
        return observe(tag, fail, old);
    }
    function middle(uint256 tag, bool fail) external returns (uint256) {
        return middleHelper(tag, count++, fail);
    }
    function voidHelper(uint256 tag, uint256 old) internal {
        emit Observed(tag, old, count);
    }
    function discard(uint256 tag) external { voidHelper(tag, count++); }
    function pairHelper(uint256 tag, uint256 old) internal view returns (uint256, uint256) {
        return (old + tag, count);
    }
    function pair(uint256 tag) external returns (uint256, uint256) {
        return pairHelper(tag, count++);
    }
    function nestedHelper(uint256 tag, uint256 old) internal returns (uint256) {
        emit Observed(tag, old, count);
        return observe(tag, false, count++);
    }
    function nested(uint256 tag) external returns (uint256) {
        return nestedHelper(tag, count++);
    }
    function forwardHelper(bytes calldata data, uint256 old) internal returns (uint256) {
        return observe(data.length, false, old);
    }
    function forward(bytes calldata data) external returns (uint256) {
        return forwardHelper(data, count++);
    }
    function copyHelper(bytes memory data, uint256 old) internal returns (uint256, uint256) {
        emit Observed(data.length, old, count);
        uint256 end;
        assembly { end := mload(0x40) }
        return (old, end);
    }
    function copy(bytes calldata data) external returns (uint256, uint256) {
        return copyHelper(data, count++);
    }
    function digestHelper(bytes calldata data, uint256 tag, uint256 old) internal view returns (bytes32) {
        return keccak256(abi.encode(old, count, tag, data.length));
    }
    function digest(bytes calldata data, uint256 tag) external returns (bytes32) {
        return digestHelper(data, tag, count++);
    }
    function add(uint256 a, uint256 b) internal pure returns (uint256) { return a + b; }
    function localCounter(uint256 n, uint256 tag) external pure returns (uint256, uint256) {
        uint256 old = add(n++, tag);
        return (old, n);
    }
    function narrow(uint8 n, uint256 tag) external pure returns (uint256, uint256) {
        uint256 old = add(tag, n++);
        return (old, n);
    }
    function aliasedHelper(uint256 a, uint256 b) internal pure returns (uint256, uint256) {
        uint256 old = add(a++, b);
        return (old, a);
    }
    function aliases(uint256 n) external pure returns (uint256, uint256) {
        return aliasedHelper(n, n);
    }
}
