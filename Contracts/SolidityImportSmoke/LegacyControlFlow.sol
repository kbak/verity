// SPDX-License-Identifier: MIT
pragma solidity >=0.7.6 <0.8.0;

contract LegacyControlFlow {
    function _decode(bytes memory data, uint256 index)
        internal pure returns (uint8 lane, bytes32 first, bytes32 second)
    {
        assembly {
            let offset := mul(0x41, index)
            first := mload(add(data, add(offset, 0x20)))
            second := mload(add(data, add(offset, 0x40)))
            lane := byte(0, mload(add(data, add(offset, 0x60))))
        }
    }

    function _product(uint256 a, uint256 b) internal pure returns (uint256) {
        if (a == 0) return 0;
        uint256 result = a * b;
        require(result / a == b);
        return result;
    }

    function arithmetic(uint256 a, uint256 b, uint256 mode) public pure returns (uint256) {
        if (mode == 0) return _product(a, b);
        if (mode == 1) { require(b != 0, "zero"); return a / b; }
        if (mode == 2) { if (b == 0) return 0; return a % b; }
        if (mode == 3) { if (b > 0) return a / b; return 0; }
        if (mode == 4) { require(0 < b); a /= b; return a; }
        if (mode == 5) { require(b > 0); a %= b; return a; }
        if (mode == 6) { if (b == 0 || a / b == 1) return 1; return 0; }
        if (mode == 7) { if (b != 0 && a % b == 0) return 1; return 0; }
        if (mode == 8) { if (!(b != 0)) revert("zero"); return a / b; }
        if (mode == 9) { return a / 65 + a % 65; }
        if (mode == 10) {
            if (a == 0) { require(b != 0); } else { if (b == 0) return 0; }
            return a / b;
        }
        return 0;
    }

    function _count(uint256 n, uint256 seed) internal pure returns (uint256 total) {
        uint256 i = 9;
        for (i = 0; i < n; ++i) total += seed + i;
        return total + i;
    }

    function counted(uint256 n, uint256 seed, uint256 mode) public pure returns (uint256, uint256) {
        require(n <= 12, "bound");
        uint256 total = 0;
        if (mode == 0) {
            for (uint256 j = 0; j < n; ++j) total += seed + j;
            return (total, n);
        }
        if (mode == 2) return (_count(n, seed), n);
        uint256 i = 7;
        if (mode == 3) {
            for (i = 0; i < n; i += 1) {
                for (uint256 j = 0; j < 2; ++j) total += seed + i + j;
            }
            return (total, i);
        }
        if (mode == 4) {
            for (i = 0; i < n; ++i) {
                if (i == 3) return (total, i);
                total += seed + i;
            }
            return (total, i);
        }
        if (mode == 5) {
            require(seed != 0, "zero");
            for (i = 0; i < n; ++i) total += n / seed;
            return (total, i);
        }
        for (i = 0; i < n; ++i) total += seed + i;
        return (total, i);
    }

    function shrinking(uint256 a, uint256 seed, uint256 mode) public pure returns (uint256, uint256) {
        uint256 total = seed;
        uint256 count = 0;
        if (mode == 0) {
            while (a > 0) { total += a; count++; a >>= 1; }
            return (total, count);
        }
        if (mode == 1) {
            while (0 != a) { total += a; count++; a &= a - 1; }
            return (total, count);
        }
        uint8 small = uint8(a);
        while (small != 0) { total += small; count++; small >>= 2; }
        return (total, count);
    }

    function decodeLoop(bytes memory data, uint256 n) public pure returns (uint256, uint256) {
        require(n <= 8, "bound");
        require(data.length >= _product(n, 65), "short");
        uint256 total;
        uint256 i;
        uint256 lane;
        bytes32 first;
        bytes32 second;
        for (i = 0; i < n; ++i) {
            (lane, first, second) = _decode(data, i);
            total += lane + uint256(first) + uint256(second);
        }
        return (total, i);
    }
}
