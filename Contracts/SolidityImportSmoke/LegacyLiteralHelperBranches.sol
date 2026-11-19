// SPDX-License-Identifier: MIT
pragma solidity 0.7.6;

contract LegacyLiteralHelperBranches {
    function divide(uint256 n, uint256 d) internal pure returns (uint256) {
        return n / d;
    }

    function single(uint8 mode, uint256 n) internal pure returns (uint256) {
        if (mode == 0) return n + 11;
        if (mode != 1) return divide(n, n);
        return n + 17;
    }

    function pair(uint32 mode, uint256 n) internal pure returns (uint256 a, uint256 b) {
        if (mode == 0) {
            if (n == 3) return (8, 9);
            return (n, n + 1);
        }
        a = divide(n, n);
        b = n;
    }

    function fallthrough(uint8 mode, uint256 n) internal pure returns (uint256) {
        if (mode == 1) {
            n += 2;
            if (n == 5) return 12;
        } else {
            n = divide(n, n);
        }
        return n + 3;
    }

    function selectedFallthrough(uint256 n) external pure returns (uint256) {
        return fallthrough(1, n);
    }

    function checked(uint256 n) internal pure returns (uint256) {
        require(n != 9);
        return n;
    }

    function captured(uint256 n) external pure returns (uint256 a, uint256 b) {
        a = single(0, n);
        b = single(1, n);
    }

    function earlyPair(uint256 n) external pure returns (uint256 a, uint256 b) {
        (a, b) = pair(0, checked(n));
    }

    function changed(uint8 mode, uint256 n) internal pure returns (uint256) {
        mode = uint8(n);
        if (mode == 0) return 31;
        return 47;
    }

    function reassigned(uint256 n) external pure returns (uint256) {
        return changed(0, n);
    }

    function dynamicPair(uint32 mode, uint256 n) external pure returns (uint256 a, uint256 b) {
        (a, b) = pair(mode, n);
    }

    function liveFallback(uint256 n) external pure returns (uint256) {
        return single(2, n);
    }
}
