// SPDX-License-Identifier: MIT
pragma solidity 0.7.6;

library SignedRecordBounds {
    int24 internal constant LOW = -400;
    int24 internal constant HIGH = -LOW;
}

contract LegacyMemoryStructs {
    struct Record {
        address account;
        int24 first;
        int24 second;
        int128 delta;
        uint8 tag;
        bool enabled;
        bytes4 marker;
    }
    function read(Record memory r) internal pure
        returns (address, int24, int24, int128, uint8, bool, bytes32)
    {
        return (r.account, r.first, r.second, r.delta, r.tag, r.enabled, r.marker);
    }
    function relay(Record memory r) internal pure
        returns (address, int24, int24, int128, uint8, bool, bytes32)
    {
        return read(r);
    }
    function positional(uint256 a, uint256 b, int256 d) external pure
        returns (address, int24, int24, int128, uint8, bool, bytes32)
    {
        return read(Record(address(a), int24(a), int24(b), int128(d), uint8(b), true, 0x12345678));
    }
    function named(uint256 a, uint256 b, int256 d) external pure
        returns (address, int24, int24, int128, uint8, bool, bytes32)
    {
        return relay(Record({delta: int128(d), second: int24(b), account: address(a),
            marker: 0x12345678, first: int24(a), enabled: true, tag: uint8(b)}));
    }
    function captured(uint256 a, uint256 b, int256 d) external pure
        returns (address, int24, int24, int128, uint8, bool, bytes32)
    {
        Record memory r = Record(address(a), int24(a), int24(b), int128(d), uint8(b), true, 0x12345678);
        a = 0;
        b = 0;
        d = 0;
        return relay(r);
    }
    function defaults() external pure
        returns (address, int24, int24, int128, uint8, bool, bytes32)
    {
        Record memory r;
        return relay(r);
    }
    function unary(uint256 a) external pure returns (int24, bool, uint8) {
        Record memory r = Record(address(0), int24(a), 0, 0, uint8(a), true, 0);
        return (-r.first, !r.enabled, ~r.tag);
    }
    function qualified(int24 a, int24 b) external pure returns (int256, int256) {
        require(a <= b, "order");
        require(a >= SignedRecordBounds.LOW, "low");
        require(b <= SignedRecordBounds.HIGH, "high");
        return (SignedRecordBounds.LOW, SignedRecordBounds.HIGH);
    }
}
