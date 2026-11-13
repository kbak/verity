// SPDX-License-Identifier: MIT
pragma solidity 0.7.6;

library CheckedScalarOps {
    function applyDelta(uint128 x, int128 y) internal pure returns (uint128 z) {
        if (y < 0) {
            require((z = x - uint128(-y)) < x, "decrease");
        } else {
            require((z = x + uint128(y)) >= x, "increase");
        }
    }
    function checkedUnsigned(uint256 y) internal pure returns (uint160 z) {
        require((z = uint160(y)) == y);
    }
    function checkedNarrow(int256 y) internal pure returns (int128 z) {
        require((z = int128(y)) == y);
    }
    function checkedSign(uint256 y) internal pure returns (int256 z) {
        require(y < 2**255);
        z = int256(y);
    }
}

contract LegacySignedScalars {
    function applyDelta(uint128 x, int128 y) external pure returns (uint128) {
        return CheckedScalarOps.applyDelta(x, y);
    }
    function checkedUnsigned(uint256 y) external pure returns (uint160) {
        return CheckedScalarOps.checkedUnsigned(y);
    }
    function checkedNarrow(int256 y) external pure returns (int128) {
        return CheckedScalarOps.checkedNarrow(y);
    }
    function checkedSign(uint256 y) external pure returns (int256) {
        return CheckedScalarOps.checkedSign(y);
    }
    function signedCasts(int256 x) external pure returns (int8, int24, int128, uint16, uint256) {
        return (int8(x), int24(x), int128(x), uint16(x), uint256(x));
    }
    function unsignedCasts(uint256 x) external pure returns (int8, int24, int128, int256) {
        return (int8(x), int24(x), int128(x), int256(x));
    }
    function widen(int8 x, uint8 y) external pure returns (int256, uint16, int16) {
        return (int256(x), uint16(x), int16(y));
    }
    function literals() external pure returns (uint256, uint256, int256, uint256, uint256, int256) {
        return (uint256(uint128(-1)), uint256(uint8(-128)), int256(int8(255)),
            uint256(uint8(256)), uint256(uint8(257)), int256(int8(-129)));
    }
    function defaultLocal() external pure returns (int128) {
        int128 empty;
        return empty;
    }
    function explicitAbi(int8 x, bytes memory unused) public pure returns (int8) {
        return x;
    }
    function arithmetic8(int8 x, int8 y) external pure
        returns (int8, int8, int8, int8) {
        return (x + y, x - y, x * y, -x);
    }
    function compare8(int8 x, int8 y) external pure
        returns (bool, bool, bool, bool, bool, bool) {
        return (x < y, x <= y, x > y, x >= y, x == y, x != y);
    }
    function arithmetic24(int24 x, int24 y) external pure
        returns (int24, int24, int24, int24) {
        return (x + y, x - y, x * y, -x);
    }
    function compare24(int24 x, int24 y) external pure
        returns (bool, bool, bool, bool, bool, bool) {
        return (x < y, x <= y, x > y, x >= y, x == y, x != y);
    }
    function arithmetic128(int128 x, int128 y) external pure
        returns (int128, int128, int128, int128) {
        return (x + y, x - y, x * y, -x);
    }
    function compare128(int128 x, int128 y) external pure
        returns (bool, bool, bool, bool, bool, bool) {
        return (x < y, x <= y, x > y, x >= y, x == y, x != y);
    }
    function arithmetic256(int256 x, int256 y) external pure
        returns (int256, int256, int256, int256) {
        return (x + y, x - y, x * y, -x);
    }
    function compare256(int256 x, int256 y) external pure
        returns (bool, bool, bool, bool, bool, bool) {
        return (x < y, x <= y, x > y, x >= y, x == y, x != y);
    }
}
