// SPDX-License-Identifier: MIT
pragma solidity 0.7.6;

library SignedKeyUpdates {
    function change(mapping(int16 => uint256) storage entries, int16 key, uint256 mask)
        internal
    {
        entries[key] ^= mask;
    }

    function forward(mapping(int16 => uint256) storage entries, int16 key, uint256 mask)
        internal
    {
        change(entries, key, mask);
    }
}

contract LegacySignedMappingKeys {
    using SignedKeyUpdates for mapping(int16 => uint256);
    uint256 private neighbor;
    mapping(int16 => uint256) public first;
    mapping(int16 => uint256) public second;
    mapping(int128 => uint8) public narrow;
    event Changed(uint256 stored);

    function update(bool other, int16 key, uint256 mask, bool reject) external returns (uint256) {
        uint256 stored;
        if (other) {
            second.forward(key, mask);
            stored = second[key];
        } else {
            first.forward(key, mask);
            stored = first[key];
        }
        emit Changed(stored);
        require(!reject, "rollback");
        return stored;
    }

    function store(int8 key, uint8 amount) external returns (uint8) {
        narrow[key] = amount;
        return narrow[key];
    }
}
