// SPDX-License-Identifier: MIT
pragma solidity 0.7.6;

contract LegacyUnsignedDivisionHalt {
    function wideRemainder(uint256 a, uint256 b, uint256 m) external pure returns (uint256) {
        return mulmod(a, b, m);
    }

    function quotient(uint256 x, uint256 d) external pure returns (uint256) {
        return x / d;
    }

    function remainder(uint256 x, uint256 d) external pure returns (uint256) {
        x %= d;
        return x;
    }

    function selected(uint8 x, uint8 d, bool divide) external pure returns (uint256) {
        return divide ? x / d : type(uint256).max;
    }

    function positive(uint256 x) internal pure returns (uint256) {
        require(x > 0, "positive");
        return x;
    }

    function competingSum(uint256 x, uint256 d) external pure returns (uint256) {
        return positive(x) + x / d;
    }

    function competingModulus(uint256 x, uint256 d) external pure returns (uint256) {
        return mulmod(positive(x), x / d, 1);
    }
}
