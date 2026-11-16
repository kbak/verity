// SPDX-License-Identifier: MIT
pragma solidity 0.7.6;

contract LegacyMixedStorageReturns {
    struct Record { uint8 beforeValue; int24 delta; uint16 afterValue; }
    Record private first;
    Record private second;
    event Mixed(int24 previous, int24 current, uint16 count);

    function select(bool other) internal view returns (Record storage, int24, uint16) {
        if (other) return (second, second.delta, second.afterValue);
        return (first, first.delta, first.afterValue);
    }
    function forward(bool other) internal view returns (Record storage, int24, uint16) {
        return select(other);
    }
    function named(bool other) internal view returns
        (Record storage row, int24 previous, uint16 count)
    {
        if (other) { row = second; } else { row = first; }
        previous = row.delta;
        count = row.afterValue;
    }
    function assigned(bool other) internal view returns
        (Record storage row, int24 previous, uint16 count)
    {
        (row, previous, count) = forward(other);
        return (row, previous, count);
    }
    function middle(bool other) internal view returns (int24, Record storage, uint16) {
        (Record storage row, int24 previous, uint16 count) = forward(other);
        return (previous, row, count);
    }
    function conditional(bool other) internal view returns (Record storage, int24, uint16) {
        return other ? (second, second.delta, second.afterValue) :
            (first, first.delta, first.afterValue);
    }
    function paired(bool other) internal view returns (Record storage, int24, Record storage) {
        if (other) return (second, second.delta, first);
        return (first, first.delta, second);
    }
    function defaults(bool other) internal view returns
        (Record storage row, int24 previous, uint16 count)
    {
        if (other) row = second; else row = first;
    }
    function rebound(bool other) internal view returns
        (Record storage row, int24 previous, uint16 count)
    {
        row = first;
        previous = row.delta;
        if (other) row = second;
        count = row.afterValue;
    }
    modifier checked(bool allowed) {
        require(allowed, "guard");
        _;
        first.afterValue = first.afterValue + 3;
    }
    function guarded(bool other, bool allowed) internal checked(allowed)
        returns (Record storage row, int24 previous, uint16 count)
    {
        (row, previous, count) = forward(other);
    }
    function change(Record storage row, int24 previous, uint16 count, int24 step, bool reject)
        internal returns (int24, int24, uint16)
    {
        Record storage aliasRow = row;
        aliasRow.delta = aliasRow.delta + step;
        row.afterValue = row.afterValue + 1;
        emit Mixed(previous, row.delta, count);
        require(!reject, "rollback");
        return (previous, row.delta, count);
    }
    function read() external view returns (int24, uint16, int24, uint16) {
        return (first.delta, first.afterValue, second.delta, second.afterValue);
    }
    function edit(bool other, int24 step, bool reject) external returns (int24, int24, uint16) {
        (Record storage row, int24 previous, uint16 count) = forward(other);
        return change(row, previous, count, step, reject);
    }
    function namedEdit(bool other, int24 step, bool reject) external returns (int24, int24, uint16) {
        (Record storage row, int24 previous, uint16 count) = named(other);
        return change(row, previous, count, step, reject);
    }
    function assignedEdit(bool other, int24 step, bool reject) external returns (int24, int24, uint16) {
        (Record storage row, int24 previous, uint16 count) = assigned(other);
        return change(row, previous, count, step, reject);
    }
    function middleEdit(bool other, int24 step, bool reject) external returns (int24, int24, uint16) {
        (int24 previous, Record storage row, uint16 count) = middle(other);
        return change(row, previous, count, step, reject);
    }
    function conditionalEdit(bool other, int24 step, bool reject)
        external returns (int24, int24, uint16)
    {
        (Record storage row, int24 previous, uint16 count) = conditional(other);
        return change(row, previous, count, step, reject);
    }
    function defaultEdit(bool other, int24 step, bool reject)
        external returns (int24, int24, uint16)
    {
        (Record storage row, int24 previous, uint16 count) = defaults(other);
        return change(row, previous, count, step, reject);
    }
    function reboundEdit(bool other, int24 step, bool reject)
        external returns (int24, int24, uint16)
    {
        (Record storage row, int24 previous, uint16 count) = rebound(other);
        return change(row, previous, count, step, reject);
    }
    function guardedEdit(bool other, int24 step, bool reject, bool allowed)
        external returns (int24, int24, uint16)
    {
        (Record storage row, int24 previous, uint16 count) = guarded(other, allowed);
        return change(row, previous, count, step, reject);
    }
    function dropEdit(bool other, int24 step) external returns (int24, int24) {
        (, int24 previous,) = forward(other);
        first.delta = first.delta + step;
        return (previous, first.delta);
    }
    function pairEdit(bool other, int24 step) external returns (int24, int24, int24) {
        (Record storage left, int24 previous, Record storage right) = paired(other);
        left.delta = left.delta + step;
        right.delta = right.delta - step;
        return (previous, left.delta, right.delta);
    }
}
