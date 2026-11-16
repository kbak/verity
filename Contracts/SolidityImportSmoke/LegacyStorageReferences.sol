// SPDX-License-Identifier: MIT
pragma solidity 0.7.6;

contract LegacyStorageReferences {
    struct Record { uint8 beforeValue; int24 delta; uint16 afterValue; }
    Record private first;
    Record private second;
    event Changed(int24 delta, uint16 afterValue);
    event Indexed(int24 indexed delta, int256 indexed input);
    event Widened(int256 input, int24 constantDelta);

    function locate() internal view returns (Record storage) { return first; }
    function update(Record storage row, int24 delta) internal {
        row.delta = row.delta + delta;
        row.afterValue = row.afterValue + 1;
    }
    function read() external view returns (int24, uint16, int24, uint16) {
        Record storage row = first;
        return (row.delta, row.afterValue, second.delta, second.afterValue);
    }
    function edit(int24 delta, bool reject) external returns (int24) {
        Record storage row = locate();
        Record storage aliasRow = row;
        update(aliasRow, delta);
        emit Changed(row.delta, row.afterValue);
        emit Indexed(row.delta, int256(delta));
        emit Widened(delta, -1);
        require(!reject, "rollback");
        return row.delta;
    }
    function interleave(int24 delta) external returns (int24, int24) {
        Record storage left = first;
        Record storage right = second;
        update(left, delta);
        update(right, -delta);
        update(left, delta);
        return (left.delta, right.delta);
    }
}
