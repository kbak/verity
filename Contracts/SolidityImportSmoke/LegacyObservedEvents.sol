// SPDX-License-Identifier: MIT
pragma solidity 0.7.6;

contract LegacyObservedEvents {
    uint256 total;

    event Empty();
    event Stage(uint8 phase);
    event Step(uint16 indexed index, uint256 amount);
    event Typed(address indexed account, bytes4 indexed tag, bool indexed flag,
                uint16 small, bytes1 mark);
    event Signed(int24 indexed key, int24 number);
    event Hidden(uint256 number) anonymous;

    modifier traced(bool failAfter) {
        emit Stage(1);
        _;
        emit Stage(3);
        require(!failAfter, "post");
    }

    function walk(uint256 n, uint256 stop, uint256 failAt, bool failAfter)
        external traced(failAfter) returns (uint256 result)
    {
        uint256 i;
        while (i < n) {
            ++i;
            total += i;
            helper(i);
            require(i != failAt, "body");
            if (i == stop) return total;
            if (i == 2) continue;
            emit Stage(2);
        }
        result = total;
    }

    function helper(uint256 index) internal {
        emit Step(uint16(index), total);
        if (index == 2) return;
        emit Empty();
    }

    function typed(uint16 small, int24 signedValue, bytes4 tag, bool flag) external {
        emit Typed(address(0x5678), tag, flag, small, 0xab);
        emit Signed(signedValue, signedValue);
        emit Empty();
    }

    function hidden() external { emit Hidden(total); }
}
