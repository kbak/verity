// SPDX-License-Identifier: MIT
pragma solidity 0.7.6;

contract LegacyObservedModifiers {
    uint256 total;
    uint256 stamp;
    bool locked;

    modifier marked(uint256 digit) {
        stamp = stamp * 10 + digit;
        _;
        stamp = stamp * 10 + digit + 5;
    }

    modifier guarded(bool failBefore, bool failAfter) {
        require(!locked && !failBefore, "pre");
        locked = true;
        _;
        require(!failAfter, "post");
        locked = false;
        total += 100;
    }

    modifier captured(uint256 beforeValue) {
        _;
        stamp = beforeValue;
        total += 10;
    }

    modifier checked() {
        check();
        _;
    }

    function check() private view { require(!locked, "locked"); }

    function walk(uint256 n, uint256 stop, bool failBefore, bool failAfter)
        external marked(1) marked(2) guarded(failBefore, failAfter) returns (uint256 result)
    {
        while (result < n) {
            ++result;
            total += result;
            if (result == stop) return total;
            if (result == 2) continue;
            stamp = stamp * 10 + 3;
        }
        result = total;
    }

    function tuple(uint256 n) external marked(1) returns (uint256 a, uint256 b) {
        a = 4;
        b = 9;
        while (n > 0) { return (b, a); }
    }

    function snapshot(uint256 n) external captured(total) returns (uint256 result) {
        while (result < n) { ++result; ++total; }
        return total;
    }

    function through(uint256 n, uint256 stop, bool failAfter)
        external checked returns (uint256 result)
    {
        result = helper(n, stop, failAfter);
        stamp = stamp * 10 + 4;
        total += 1000;
    }

    function helper(uint256 n, uint256 stop, bool failAfter)
        internal marked(1) guarded(false, failAfter) returns (uint256 result)
    {
        while (result < n) {
            ++result;
            ++total;
            if (result == stop) return total;
        }
        return total;
    }

    function voidLoop(uint256 n) external marked(1) {
        uint256 i;
        while (i < n) { ++i; ++total; if (i == 2) return; }
        total += 10;
    }

    function failBody(uint256 n) external guarded(false, false) returns (uint256 result) {
        while (result < n) { ++result; ++total; require(result != 2, "body"); }
    }

    modifier conditional(bool run) { if (run) { _; } }
    modifier repeated() { _; _; }
    function skipped(bool run) external conditional(run) returns (uint256 result) { result = 1; }
    function twice() external repeated returns (uint256 result) { result = 1; }
    function ambiguous() external marked(1) returns (uint256 a, uint256 b) {
        return (total++, total);
    }
}
