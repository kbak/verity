// SPDX-License-Identifier: MIT
pragma solidity 0.7.6;
contract LegacyControlFlowRejections {
    function unguarded(uint256 a, uint256 b) public pure returns (uint256) { return a / b; }
    function lateGuard(uint256 a, uint256 b) public pure returns (uint256) {
        uint256 result = a / b; require(b != 0); return result;
    }
    function stale(uint256 a, uint256 b) public pure returns (uint256) {
        require(b != 0); b--; return a / b;
    }
    function staleAssembly(uint256 a, uint256 b) public pure returns (uint256) {
        require(b != 0); assembly { b := 0 } return a / b;
    }
    function wrongBranch(uint256 a, uint256 b) public pure returns (uint256) {
        if (b != 0) return 0; return a / b;
    }
    function partialGuard(uint256 a, uint256 b) public pure returns (uint256) {
        if (a == 0) require(b != 0); return a / b;
    }
    function weakGuard(uint256 a, uint256 b) public pure returns (uint256) {
        require(b >= 0); return a / b;
    }
    function truncation(uint256 a, uint256 b) public pure returns (uint256) {
        require(b != 0); return a / uint8(b);
    }
    function shortCircuit(uint256 a, uint256 b) public pure returns (bool) {
        return b != 0 || a / b == 1;
    }
    function _division(uint256 a, uint256 b) internal pure returns (uint256) { return a / b; }
    function callerGuard(uint256 a, uint256 b) public pure returns (uint256) {
        require(b != 0); return _division(a, b);
    }
    function loopStale(uint256 a, uint256 b) public pure returns (uint256 total) {
        require(b != 0);
        for (uint256 i = 0; i < 2; ++i) { total += a / b; b--; }
    }
    function loopGuard(uint256 a, uint256 b) public pure returns (uint256) {
        for (uint256 i = 0; i < a; ++i) require(b != 0);
        return a / b;
    }
    function inclusive(uint256 n, uint256 total) public pure returns (uint256) {
        for (uint256 i = 0; i <= n; ++i) total++; return total;
    }
    function narrowCounter(uint256 n, uint256 total) public pure returns (uint256) {
        for (uint8 i = 0; i < n; ++i) total++; return total;
    }
    function bodyCounter(uint256 n, uint256 total) public pure returns (uint256) {
        for (uint256 i = 0; i < n; ++i) { i++; total++; } return total;
    }
    function changingBound(uint256 n, uint256 total) public pure returns (uint256) {
        for (uint256 i = 0; i < n; ++i) { n--; total++; } return total;
    }
    function continuing(uint256 n, uint256 total) public pure returns (uint256) {
        for (uint256 i = 0; i < n; ++i) { if (i == 1) continue; total++; } return total;
    }
    function unbounded(uint256 a, uint256 total) public pure returns (uint256) {
        while (a != 0) { total++; a += 1; } return total;
    }
    function arbitraryWhile(uint256 a, uint256 total) public pure returns (uint256) {
        while (!(a == 0)) { total++; a--; } return total;
    }
    function changedBuffer(bytes memory data, bytes memory next) public pure returns (uint256 n) {
        for (uint256 i = 0; i < data.length; ++i) { data = next; n++; }
    }
}
