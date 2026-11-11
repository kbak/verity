// SPDX-License-Identifier: MIT
pragma solidity 0.7.6;

contract LegacyScalarConditionals {
    function choose(bool flag, uint256 a, uint256 b) external pure returns (uint256) {
        return flag ? a : b;
    }
    function maximum(uint256 a, uint256 b) external pure returns (uint256) {
        return a >= b ? a : b;
    }
    function nested(bool outer, bool inner, uint256 a, uint256 b, uint256 c)
        external pure returns (uint256)
    { return outer ? (inner ? a : b) : c; }
    function wrapped(bool flag, uint8 a, uint8 b) external pure returns (uint8) {
        return flag ? a + b : a - b;
    }
    function promoted(bool flag, uint8 a, uint16 b) external pure returns (uint16) {
        return flag ? a : b;
    }
    function booleans(bool flag, bool a, bool b) external pure returns (bool) {
        return flag ? a : b;
    }
    function addresses(bool flag, address a, address b) external pure returns (address payable) {
        return flag ? payable(a) : payable(b);
    }
    function fixedBytes(bool flag, bytes32 a, bytes32 b) external pure returns (bytes32) {
        return bytes32(flag ? bytes5(a) : bytes5(b));
    }
    function widenedBytes(bool flag, bytes32 a, bytes32 b) external pure returns (bytes32) {
        return bytes32(flag ? bytes1(a) : bytes5(b));
    }
    function guarded(uint256 n, uint256 d) external pure returns (uint256, uint256) {
        return (d == 0 ? 0 : n / d, d != 0 ? n % d : 0);
    }
    function narrowGuarded(uint256 n, uint8 d) external pure returns (uint256) {
        return d == 0 ? 0 : n / d;
    }
    function guardedNested(uint256 n, uint256 d, bool flag) external pure returns (uint256) {
        return d > 0 ? (flag ? n / d : n % d) : 19;
    }
    function checked(uint256 n) internal pure returns (uint256) {
        require(n > 0, "selected");
        return n + 1;
    }
    function lazy(bool flag, uint256 n) external pure returns (uint256) {
        return flag ? checked(n) : 7;
    }
    function negated(bool flag, uint256 n) external pure returns (uint256) {
        return !flag ? 17 : checked(n);
    }
    function requireChoice(bool flag, uint256 n) external pure returns (uint256) {
        require(flag ? n > 3 : n < 2, "choice");
        return n;
    }
    function identity(uint256 n) internal pure returns (uint256) { return n; }
    function helperArg(bool flag, uint256 a, uint256 b) external pure returns (uint256) {
        return identity(flag ? a : b);
    }
    function measure(bytes memory data) internal pure returns (uint256) { return data.length; }
    function skippedCopy(bool flag, bytes calldata data) external pure returns (uint256 n, uint256 p) {
        n = flag ? measure(data) : 23;
        assembly { p := mload(64) }
    }
}

contract LegacyConditionalEffects {
    uint256 count;
    uint256 trace;
    event Step(uint256 tag, uint256 total);
    function step(uint256 tag) internal returns (uint256) {
        count += 1;
        trace = tag;
        emit Step(tag, count);
        return count;
    }
    function predicate(bool flag) internal returns (bool) {
        step(1);
        return flag;
    }
    function run(bool flag, bool fail) external returns (uint256 result) {
        result = predicate(flag) ? step(2) : step(3);
        require(!fail, "late");
    }
    function increments(bool flag) external returns (uint256 result, uint256 afterCount) {
        result = flag ? count++ : ++count;
        afterCount = count;
    }
    function assignments(bool flag, uint256 a, uint256 b) external returns (uint256) {
        count = flag ? (trace = a) : (trace = b);
        return count;
    }
    function checkedStep(uint256 tag) internal returns (uint256 n) {
        n = step(tag);
        require(tag != 0, "branch");
    }
    function failSelected(bool flag) external returns (uint256) {
        return flag ? checkedStep(0) : step(4);
    }
}
