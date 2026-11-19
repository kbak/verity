// SPDX-License-Identifier: MIT
pragma solidity =0.7.6;

contract LegacySignedMappingValues {
    mapping(uint8 => int8) public bytesByKey;
    mapping(uint24 => int24) public entries;
    mapping(uint256 => int248) public wide;

    function store(uint24 key, int24 next, bool undo) external returns (int256 previous, int256 current) {
        previous = entries[key];
        entries[key] = next;
        require(!undo, "rollback");
        current = entries[key];
    }

    function negative(uint24 key) external view returns (bool) {
        return entries[key] < 0;
    }
}
