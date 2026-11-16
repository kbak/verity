// SPDX-License-Identifier: MIT
pragma solidity 0.7.6;

library FixedRecordHelpers {
    struct Packed { uint32 stamp; int56 delta; uint160 weight; bool live; }
    struct Wide { uint128 low; uint128 high; int24 delta; bool live; uint256 tail; }

    function at(Packed[65535] storage rows, uint256 index)
        internal view returns (Packed storage result)
    { result = rows[index]; }

    function forward(Packed[65535] storage rows, uint256 index)
        internal view returns (Packed storage)
    { return at(rows, index); }

    function size(Packed[65535] storage rows) internal pure returns (uint256)
    { return rows.length; }

    function wideAt(Wide[3] storage rows, uint256 index)
        internal view returns (Wide storage)
    { return rows[index]; }
}

contract LegacyFixedStructArrays {
    using FixedRecordHelpers for FixedRecordHelpers.Packed[65535];
    uint256 private pad;
    FixedRecordHelpers.Packed[65535] private rows;
    FixedRecordHelpers.Packed[65535] private other;
    uint256 private cursor;
    uint256 private effects;
    FixedRecordHelpers.Wide[3] private wideRows;

    function edit(uint256 index, int56 delta, uint160 weight, bool live, bool fail)
        external returns (uint32, int56, uint160, bool, uint256)
    {
        effects += 1;
        FixedRecordHelpers.Packed storage row = rows.forward(index);
        row.stamp += 1;
        row.delta = delta;
        row.weight = weight;
        row.live = live;
        require(!fail, "rollback");
        return (row.stamp, row.delta, row.weight, row.live, effects);
    }

    function read(uint256 index) external view returns (uint32, int56, uint160, bool, uint256)
    {
        FixedRecordHelpers.Packed storage row = rows[index];
        return (row.stamp, row.delta, row.weight, row.live, rows.size());
    }

    function editOther(uint256 index, uint32 stamp) external returns (uint32, int56)
    {
        FixedRecordHelpers.Packed storage row = other.forward(index);
        row.stamp = stamp;
        return (row.stamp, row.delta);
    }

    function advance(int56 delta) external returns (uint256, int56)
    {
        FixedRecordHelpers.Packed storage row = rows.forward(cursor);
        cursor += 1;
        row.delta = delta;
        return (cursor, row.delta);
    }

    function wide(uint256 index, int24 delta, uint256 tail, bool fail)
        external returns (uint128, uint128, int24, bool, uint256)
    {
        effects += 1;
        FixedRecordHelpers.Wide storage row = FixedRecordHelpers.wideAt(wideRows, index);
        row.high += 1;
        row.delta = delta;
        row.live = !row.live;
        row.tail = tail;
        require(!fail, "rollback");
        return (row.low, row.high, row.delta, row.live, row.tail);
    }
}
