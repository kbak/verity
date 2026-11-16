// SPDX-License-Identifier: MIT
pragma solidity 0.7.6;

library MappingRows {
    struct Row { uint128 amount; uint8 tag; uint256 total; }

    function at(mapping(bytes32 => Row) storage self, bytes32 key)
        internal view returns (Row storage row)
    {
        row = self[key];
    }

    function forward(mapping(bytes32 => Row) storage self, bytes32 key)
        internal view returns (Row storage)
    {
        return at(self, key);
    }
}

contract LegacyMappingHelpers {
    using MappingRows for mapping(bytes32 => MappingRows.Row);
    uint256 private pad;
    mapping(bytes32 => MappingRows.Row) private first;
    mapping(bytes32 => MappingRows.Row) private second;
    mapping(uint256 => uint8) private small;
    mapping(uint256 => bool) private flags;
    event Changed(uint128 previous, uint128 current, uint256 total);

    function choose(mapping(bytes32 => MappingRows.Row) storage a,
        mapping(bytes32 => MappingRows.Row) storage b, bool other, bytes32 key)
        internal view returns (MappingRows.Row storage, uint256)
    {
        if (other) return (b.forward(key), 1);
        return (a.forward(key), 0);
    }

    function read(bool other, bytes32 key) external view returns (uint128, uint8, uint256) {
        (MappingRows.Row storage row,) = choose(first, second, other, key);
        return (row.amount, row.tag, row.total);
    }

    function direct(bytes32 key) external view returns (uint128, uint8, uint256) {
        MappingRows.Row storage row = first[key];
        return (row.amount, row.tag, row.total);
    }

    function edit(bool other, bytes32 key, uint128 step, bool reject)
        external returns (uint128 previous, uint128 current, uint256 total)
    {
        (MappingRows.Row storage row,) = choose(first, second, other, key);
        previous = row.amount;
        row.amount += step;
        row.total += 1;
        current = row.amount;
        total = row.total;
        emit Changed(previous, current, total);
        require(!reject, "rollback");
    }

    function smallRead(mapping(uint256 => uint8) storage self, uint256 key)
        internal view returns (uint8) { return self[key]; }
    function flagRead(mapping(uint256 => bool) storage self, uint256 key)
        internal view returns (bool) { return self[key]; }
    function store(mapping(uint256 => uint8) storage a, mapping(uint256 => bool) storage b,
        uint256 key, uint8 value, bool flag) internal { a[key] = value; b[key] = flag; }
    function scalarRead(uint256 key) external view returns (uint8, bool) {
        return (smallRead(small, key), flagRead(flags, key));
    }
    function scalar(uint256 key, uint8 value, bool flag) external returns (uint8, bool) {
        store(small, flags, key, value, flag);
        return (smallRead(small, key), flagRead(flags, key));
    }
}

contract LegacySingleMappingHelper {
    using MappingRows for mapping(bytes32 => MappingRows.Row);
    mapping(bytes32 => MappingRows.Row) private first;
    event Changed(uint128 previous, uint128 current, uint256 total);

    function read(bytes32 key) external view returns (uint128, uint8, uint256) {
        MappingRows.Row storage row = first.forward(key);
        return (row.amount, row.tag, row.total);
    }
    function edit(bytes32 key, uint128 step, bool reject)
        external returns (uint128 previous, uint128 current, uint256 total)
    {
        MappingRows.Row storage row = first.forward(key);
        previous = row.amount;
        row.amount += step;
        row.total += 1;
        current = row.amount;
        total = row.total;
        emit Changed(previous, current, total);
        require(!reject, "rollback");
    }
}
