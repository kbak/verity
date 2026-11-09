// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

contract FixedBytesCustomError {
    error WordAsUint(uint256 word);
    error WordAsBytes(bytes32 word);

    function exercise(uint256 x, uint256 mode) external pure returns (uint256) {
        bytes32 word = bytes32(x);
        if (mode == 0) revert WordAsUint(uint256(word));
        if (mode == 1) revert WordAsBytes(bytes32(x));
        return x;
    }
}
