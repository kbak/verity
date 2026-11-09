// SPDX-License-Identifier: MIT
pragma solidity >=0.7.6 <0.9.0;

contract FixedBytesMemoryRevert {
    function widen(bytes5 code) internal pure returns (bytes32) {
        return code;
    }

    function failCode(bytes5 code) internal pure {
        assembly {
            let pointer := mload(0x40)
            mstore(pointer, 0x08c379a000000000000000000000000000000000000000000000000000000000)
            mstore(add(pointer, 4), 32)
            mstore(add(pointer, 36), 5)
            mstore(add(pointer, 68), code)
            revert(pointer, 100)
        }
    }

    function signedRoundTrip(uint256 x) external pure returns (bytes32) {
        return bytes32(uint256(int256(x)));
    }

    function exercise(uint256 x, uint256 mode) external pure returns (uint256) {
        if (mode == 0) return uint256(bytes32(bytes1(uint8(x))));
        if (mode == 1) return uint256(bytes32(bytes2(uint16(x))));
        if (mode == 2) return uint256(bytes32(bytes3(uint24(x))));
        if (mode == 3) return uint256(bytes32(bytes4(uint32(x))));
        if (mode == 4) return uint256(bytes32(bytes5(uint40(x))));
        if (mode == 5) return uint256(bytes32(bytes6(uint48(x))));
        if (mode == 6) return uint256(bytes32(bytes7(uint56(x))));
        if (mode == 7) return uint256(bytes32(bytes8(uint64(x))));
        if (mode == 8) return uint256(bytes32(bytes9(uint72(x))));
        if (mode == 9) return uint256(bytes32(bytes10(uint80(x))));
        if (mode == 10) return uint256(bytes32(bytes11(uint88(x))));
        if (mode == 11) return uint256(bytes32(bytes12(uint96(x))));
        if (mode == 12) return uint256(bytes32(bytes13(uint104(x))));
        if (mode == 13) return uint256(bytes32(bytes14(uint112(x))));
        if (mode == 14) return uint256(bytes32(bytes15(uint120(x))));
        if (mode == 15) return uint256(bytes32(bytes16(uint128(x))));
        if (mode == 16) return uint256(bytes32(bytes17(uint136(x))));
        if (mode == 17) return uint256(bytes32(bytes18(uint144(x))));
        if (mode == 18) return uint256(bytes32(bytes19(uint152(x))));
        if (mode == 19) return uint256(bytes32(bytes20(uint160(x))));
        if (mode == 20) return uint256(bytes32(bytes21(uint168(x))));
        if (mode == 21) return uint256(bytes32(bytes22(uint176(x))));
        if (mode == 22) return uint256(bytes32(bytes23(uint184(x))));
        if (mode == 23) return uint256(bytes32(bytes24(uint192(x))));
        if (mode == 24) return uint256(bytes32(bytes25(uint200(x))));
        if (mode == 25) return uint256(bytes32(bytes26(uint208(x))));
        if (mode == 26) return uint256(bytes32(bytes27(uint216(x))));
        if (mode == 27) return uint256(bytes32(bytes28(uint224(x))));
        if (mode == 28) return uint256(bytes32(bytes29(uint232(x))));
        if (mode == 29) return uint256(bytes32(bytes30(uint240(x))));
        if (mode == 30) return uint256(bytes32(bytes31(uint248(x))));
        if (mode == 31) return uint256(bytes32(bytes32(uint256(x))));
        if (mode == 32) return uint256(widen("ABCDE"));
        if (mode == 33) return uint256(widen(""));
        if (mode == 34) return uint256(widen(hex"ff00010203"));
        if (mode == 35) return uint256(widen(unicode"é"));
        if (mode == 36) return uint256(widen(bytes2("xy")));
        if (mode == 37) {
            bytes5 code = "short";
            return uint256(bytes32(code));
        }
        if (mode == 38) failCode("ABCDE");
        if (mode == 39) failCode(hex"ff00010203");
        if (mode == 40) return uint256(bytes32(bytes5(bytes32(x))));
        if (mode == 41) return uint256(bytes32("thirty-two"));
        if (mode == 224) return uint256(uint8(bytes1(bytes32(x))));
        if (mode == 225) return uint256(uint16(bytes2(bytes32(x))));
        if (mode == 226) return uint256(uint24(bytes3(bytes32(x))));
        if (mode == 227) return uint256(uint32(bytes4(bytes32(x))));
        if (mode == 228) return uint256(uint40(bytes5(bytes32(x))));
        if (mode == 229) return uint256(uint48(bytes6(bytes32(x))));
        if (mode == 230) return uint256(uint56(bytes7(bytes32(x))));
        if (mode == 231) return uint256(uint64(bytes8(bytes32(x))));
        if (mode == 232) return uint256(uint72(bytes9(bytes32(x))));
        if (mode == 233) return uint256(uint80(bytes10(bytes32(x))));
        if (mode == 234) return uint256(uint88(bytes11(bytes32(x))));
        if (mode == 235) return uint256(uint96(bytes12(bytes32(x))));
        if (mode == 236) return uint256(uint104(bytes13(bytes32(x))));
        if (mode == 237) return uint256(uint112(bytes14(bytes32(x))));
        if (mode == 238) return uint256(uint120(bytes15(bytes32(x))));
        if (mode == 239) return uint256(uint128(bytes16(bytes32(x))));
        if (mode == 240) return uint256(uint136(bytes17(bytes32(x))));
        if (mode == 241) return uint256(uint144(bytes18(bytes32(x))));
        if (mode == 242) return uint256(uint152(bytes19(bytes32(x))));
        if (mode == 243) return uint256(uint160(bytes20(bytes32(x))));
        if (mode == 244) return uint256(uint168(bytes21(bytes32(x))));
        if (mode == 245) return uint256(uint176(bytes22(bytes32(x))));
        if (mode == 246) return uint256(uint184(bytes23(bytes32(x))));
        if (mode == 247) return uint256(uint192(bytes24(bytes32(x))));
        if (mode == 248) return uint256(uint200(bytes25(bytes32(x))));
        if (mode == 249) return uint256(uint208(bytes26(bytes32(x))));
        if (mode == 250) return uint256(uint216(bytes27(bytes32(x))));
        if (mode == 251) return uint256(uint224(bytes28(bytes32(x))));
        if (mode == 252) return uint256(uint232(bytes29(bytes32(x))));
        if (mode == 253) return uint256(uint240(bytes30(bytes32(x))));
        if (mode == 254) return uint256(uint248(bytes31(bytes32(x))));
        if (mode == 255) return uint256(uint256(bytes32(bytes32(x))));
        if (mode < 64) return uint256(bytes32(bytes5(0)));
        require(mode <= 192, "size");
        uint256 size = mode - 64;
        uint256 offset = x & 31;
        assembly {
            let pointer := mload(0x40)
            mstore(pointer, x)
            mstore(add(pointer, 32), 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)
            revert(add(pointer, offset), size)
        }
    }
}

contract FixedBytesMemoryRevertOne is FixedBytesMemoryRevert {
    uint256 private first;
}

contract FixedBytesMemoryRevertTwo is FixedBytesMemoryRevertOne {
    uint256 private second;
}
