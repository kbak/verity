// SPDX-License-Identifier: MIT
pragma solidity 0.7.6;

abstract contract LegacySelfContext {
    function checkContext() private view {
        require(msg.sender == address(this), "context");
    }
    modifier selfContext() {
        checkContext();
        _;
    }
}

// Address-keyed writes, wrapping count, events, and a failing nested update.
contract LegacyStateTransitions is LegacySelfContext {
    mapping(address => address) private links;
    uint256 private count;
    uint256 private limit;
    event Inserted(address indexed key);
    event Limit(uint256 next);

    function setLimit(uint256 next) public selfContext {
        require(next <= count, "bound");
        require(next != 0, "zero");
        limit = next;
        emit Limit(next);
    }
    function insert(address key, uint256 next) public selfContext {
        require(key != address(0) && key != address(1) && key != address(this), "key");
        require(links[key] == address(0), "duplicate");
        links[key] = links[address(1)];
        links[address(1)] = key;
        ++count;
        emit Inserted(key);
        if (limit != next) setLimit(next);
    }
}

// No storage: the modifier's helper still has to execute.
contract LegacyStatelessEffects is LegacySelfContext {
    event Value(uint256 next);
    function record(uint256 next) public selfContext { emit Value(next); }
}

// One storage field: packed writes retain dirty high bits and wrap at uint8.
contract LegacyScalarEffects is LegacySelfContext {
    uint8 private stored;
    event Value(uint8 next);
    modifier afterWrite() { _; ++stored; }
    function set(uint8 next) public selfContext { stored = next; emit Value(stored); }
    function increment() public selfContext { ++stored; emit Value(stored); }
    function compound(uint8 next) public selfContext afterWrite {
        stored += next;
        emit Value(stored);
    }
    function failAfterWrite(uint8 next) public selfContext {
        stored = next;
        emit Value(stored);
        require(next == 0, "rollback");
    }
}
