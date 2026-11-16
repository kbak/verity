// SPDX-License-Identifier: MIT
pragma solidity 0.7.6;

contract LegacyNamedStorageResults {
    struct Row { uint128 amount; uint8 tag; uint256 total; }
    uint256 private pad;
    mapping(uint256 => Row) private rows;
    uint256 private cursor;
    uint256 private effects;
    event Stage(uint8 stage, uint128 amount, uint256 total);

    function at(uint256 key) internal view returns (Row storage row) {
        row = rows[key];
    }

    function continueAfterBinding(uint256 key, uint128 step, uint8 mode)
        internal returns (Row storage row)
    {
        row = at(key);
        Row storage original = row;
        uint128 previous = row.amount;
        cursor = key + 1;
        row.amount = previous + step;
        row.total += 1;
        emit Stage(1, row.amount, row.total);
        if (mode == 1) { effects += 1; return row; }
        if (mode == 2) { effects += 2; return original; }
        if (mode == 3) { row = at(key + 1); row.amount += step; }
        if (mode == 4) { return at(key + 1); }
        original.tag += 1;
        if (mode == 3) { row.tag += 2; }
        effects += 4;
        require(mode != 5, "rollback");
        emit Stage(2, row.amount, row.total);
    }

    function forward(uint256 key, uint128 step, uint8 mode)
        internal returns (Row storage row)
    {
        row = continueAfterBinding(key, step, mode);
        row.total += 10;
        emit Stage(3, row.amount, row.total);
    }

    function edit(uint256 key, uint128 step, uint8 mode)
        external returns (uint128, uint8, uint256, uint256, uint256)
    {
        Row storage row = forward(key, step, mode);
        row.amount += 1;
        emit Stage(4, row.amount, row.total);
        return (row.amount, row.tag, row.total, effects, cursor);
    }

    function fromCursor(uint128 step) internal returns (Row storage row) {
        row = rows[cursor];
        cursor += 1;
        row.amount += step;
    }

    function advance(uint128 step) external returns (uint128, uint256) {
        Row storage row = fromCursor(step);
        return (row.amount, cursor);
    }

    function read(uint256 key) external view returns (uint128, uint8, uint256, uint256, uint256) {
        Row storage row = at(key);
        return (row.amount, row.tag, row.total, effects, cursor);
    }
}
