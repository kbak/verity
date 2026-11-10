// SPDX-License-Identifier: MIT
pragma solidity 0.7.6;

/// ABI-v1 address cleanup, guarded reads, helper bindings and atomic list writes.
contract LegacyAddressArrays {
    mapping(address => address) internal links;
    uint256 internal count;
    uint256 internal limit;
    event Item(address indexed item);

    function initializeList(address[] memory items, uint256 requested) public {
        require(limit == 0, "initialized");
        require(requested <= items.length, "bound");
        require(requested != 0, "zero");
        address prior = address(1);
        uint256 size = items.length;
        for (uint256 i = 0; i < size; ++i) {
            address item = items[i];
            require(item != address(0) && item != address(1) &&
                item != address(this) && prior != item, "key");
            require(links[item] == address(0), "duplicate");
            links[prior] = item;
            prior = item;
            emit Item(item);
        }
        links[prior] = address(1);
        count = size;
        limit = requested;
    }

    function fold(address[] memory first, address[] memory second) public pure returns (uint256) {
        return sum(first) + sum(second);
    }

    function sum(address[] memory items) internal pure returns (uint256 result) {
        for (uint256 i = 0; i < items.length; ++i) result += uint256(items[i]);
    }
}
