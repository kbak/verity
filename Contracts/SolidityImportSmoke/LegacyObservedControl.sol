// SPDX-License-Identifier: MIT
pragma solidity 0.7.6;

contract LegacyObservedControl {
    function walk(uint256 n, uint256 skip, uint256 stop, uint256 fail, int24 delta)
        external pure returns (int24 total, uint256 i)
    {
        while (i < n) {
            ++i;
            require(i != fail, "loop");
            if (i == skip) continue;
            total += delta;
            if (i == stop) break;
        }
    }

    function counted(uint256 n, uint256 skip, uint256 stop)
        external pure returns (uint256 total)
    {
        for (uint256 i = 0; i < n; ++i) {
            if (i == skip) continue;
            total += i;
            if (i == stop) break;
        }
    }

    function nested(uint256 n, uint256 m) external pure returns (uint256 total) {
        for (uint256 i = 0; i < n; ++i) {
            uint256 j;
            while (j < m) {
                ++j;
                if (j == 2) break;
                ++total;
            }
            if (i == 1) continue;
            total += 10;
        }
    }

    function conditionEffects(uint256 n, uint256 stop)
        external pure returns (uint256 visits, uint256 tests)
    {
        while (tests++ < n) {
            ++visits;
            if (visits == stop) break;
        }
    }

    function early(uint256 n, uint256 target) external pure returns (uint256 result) {
        uint256 i;
        while (i < n) {
            ++i;
            if (i == target) return i;
        }
        result = 77;
    }

    function postEffects(uint256 n, uint256 skip, uint256 stop)
        external pure returns (uint256 updates, uint256 i)
    {
        for (; i < n; updates += 3) {
            ++i;
            if (i == skip) continue;
            if (i == stop) break;
        }
    }

    function signedOps(uint256 n, int24 delta) external pure returns (int24 result) {
        result = 2;
        while (n > 0) {
            result -= delta;
            result *= delta;
            n -= 1;
        }
    }

    function search(uint256 low, uint256 high, uint256 target, uint256 skipMask)
        external pure returns (uint256 middle)
    {
        while (true) {
            middle = (low + high) / 2;
            if ((skipMask & (uint256(1) << middle)) != 0) {
                low = middle + 1;
                continue;
            }
            if (middle == target) break;
            if (middle > target) high = middle - 1;
            else low = middle + 1;
        }
    }

    function forever() external pure returns (uint256 result) {
        for (;;) { continue; }
    }

    function unguarded(uint256 divisor) external pure returns (uint256 result) {
        while (true) { result = 10 / divisor; break; }
    }

    function staleGuard(uint256 divisor) external pure returns (uint256 result) {
        require(divisor != 0);
        while (true) { divisor = 0; result = 10 / divisor; break; }
    }

    function viewOnly() external view returns (uint256 result) {
        while (true) { result = 1; break; }
    }

    function unnamedResult() external pure returns (uint256) {
        while (true) { return 1; }
    }
}
