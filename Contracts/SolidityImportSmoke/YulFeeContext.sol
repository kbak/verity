// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

contract FeeContext {
    function readFees() external view returns (uint256, uint256, uint256) {
        uint256 base;
        uint256 price;
        uint256 combined;
        assembly ("memory-safe") {
            base := basefee()
            price := gasprice()
            combined := add(mul(basefee(), 3), gasprice())
        }
        return (base, price, combined);
    }
}
