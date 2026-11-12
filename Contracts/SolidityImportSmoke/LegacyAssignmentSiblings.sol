// SPDX-License-Identifier: MIT
pragma solidity 0.7.6;

library CheckedWordOps {
    function add(uint256 x, uint256 y) internal pure returns (uint256 z) {
        require((z = x + y) >= x);
    }
    function rightSide(uint256 x, uint256 y) internal pure returns (uint256 z) {
        require(x <= (z = x + y));
    }
    function nested(uint256 x, uint256 y) internal pure returns (uint256 z) {
        uint256 copy;
        require((z = (copy = x + y)) >= x);
        require(copy == z);
    }
    function modified(uint256 x, uint256 y) internal pure returns (uint256 z) {
        x += 1;
        require((z = x + y) >= x);
    }
    function skipped(uint256 x, uint256 y, bool enabled) internal pure returns (uint256 z) {
        z = 17;
        require(!enabled || (z = x + y) >= x);
    }
    function shadowed(uint256 x, uint256 y) internal pure returns (uint256 z) {
        { uint256 x = y; require((z = x + 1) >= x); }
        require((z = z + x) >= x);
    }
    function narrow(uint8 x, uint8 y) internal pure returns (uint8 z) {
        require((z = x + y) >= x, "narrow");
    }
}
contract LegacyAssignmentSiblings {
    uint256 public count;
    event Assigned(uint256 amount);
    function add(uint256 x, uint256 y) external pure returns (uint256) {
        return CheckedWordOps.add(x, y);
    }
    function rightSide(uint256 x, uint256 y) external pure returns (uint256) {
        return CheckedWordOps.rightSide(x, y);
    }
    function nested(uint256 x, uint256 y) external pure returns (uint256) {
        return CheckedWordOps.nested(x, y);
    }
    function modified(uint256 x, uint256 y) external pure returns (uint256) {
        return CheckedWordOps.modified(x, y);
    }
    function skipped(uint256 x, uint256 y, bool enabled) external pure returns (uint256) {
        return CheckedWordOps.skipped(x, y, enabled);
    }
    function shadowed(uint256 x, uint256 y) external pure returns (uint256) {
        return CheckedWordOps.shadowed(x, y);
    }
    function narrow(uint8 x, uint8 y) external pure returns (uint8) {
        return CheckedWordOps.narrow(x, y);
    }
    function record(uint256 x, uint256 y) external returns (uint256) {
        count += 1;
        emit Assigned(count);
        uint256 result = CheckedWordOps.add(x, y);
        count = result;
        emit Assigned(result);
        return result;
    }
}
