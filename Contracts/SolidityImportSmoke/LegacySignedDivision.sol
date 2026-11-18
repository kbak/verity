// SPDX-License-Identifier: MIT
pragma solidity 0.7.6;

contract LegacySignedDivision {
    function guarded(int24 x, int24 y) external pure returns (int24, int24) {
        require(y != 0);
        return (x / y, x % y);
    }

    function choose(bool divide, int256 x, int256 y) external pure returns (int256) {
        return divide ? x / y : x % y;
    }

    function guardedChoice(bool divide, int256 x, int256 y) external pure returns (int256) {
        require(y != 0);
        return divide ? x / y : x % y;
    }

    function selectByQuotientSign(int24 x, int24 y) external pure returns (int256) {
        require(y != 0);
        return x / y < 0 ? x : int256(y);
    }

    function alignTowardZero(int24 x, int24 step) external pure returns (int24) {
        require(step > 0);
        return (x / step) * step;
    }

    function byNegativeLiteral(int24 x) external pure returns (int24, int24) {
        return (x / -1, x % -3);
    }

    function selectAssignment(bool takeLeft, int24 x, int24 y) external pure returns (int24, int24) {
        int24 result = takeLeft ? (x = -x) : y;
        return (result, x);
    }

    function fallbackOnZero(int24 x, int24 y) external pure returns (int24) {
        return y == 0 ? x : x / y;
    }
}
