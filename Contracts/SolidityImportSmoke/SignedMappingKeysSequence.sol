// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

interface SignedArgument { function accept(int128 value) external; }

contract SequenceFixture {
    mapping(int8 => uint256) private small;
    mapping(int64 => uint256) private medium;
    mapping(int128 => uint256) private large;
    mapping(int256 => uint256) private full;
    struct Packed { int128 low; int128 high; }
    mapping(int128 => Packed) private packed;

    function _raw() private pure returns (Packed storage result) {
        assembly ("memory-safe") { result.slot := 4096 }
    }

    function change(uint256 input) external returns (uint256, uint256, uint256, uint256, uint256, uint256, bytes32) {
        int8 a = int8(int256(input));
        int64 b = int64(int256(input));
        int128 c = int128(int256(input));
        int256 d = int256(input);
        require(c <= type(int128).max && c >= type(int128).min, "signed bounds");
        uint256 amount = (input & 255) + 1;
        small[a] += amount;
        medium[b] += amount;
        large[c] += amount;
        full[d] += amount;
        packed[c].high = int128(int256(input >> 128));
        packed[c].low = c;
        Packed storage raw = _raw();
        raw.high = int128(int256(input >> 128));
        raw.low = c;
        require(raw.low == c && raw.high == packed[c].high, "signed raw reads");
        return (small[a], medium[b], large[c], full[d],
            uint256(int256(packed[c].low)), uint256(int256(packed[c].high)),
            keccak256(abi.encodeCall(SignedArgument.accept, (c))));
    }

    function fail() external returns (uint256) {
        small[-1] = 99;
        medium[-1] = 99;
        large[-1] = 99;
        full[-1] = 99;
        packed[-1].low = 99;
        packed[-1].high = 99;
        _raw().low = 99;
        require(false, "rollback signed mapping writes");
        return small[-1];
    }

    function read() external view returns (uint256, uint256, uint256, uint256,
        uint256, uint256, uint256, uint256, uint256, uint256) {
        return (small[-1], medium[-1], large[-1], full[-1],
            small[0], medium[0], large[0], full[0],
            uint256(int256(packed[-1].low)), uint256(int256(packed[-1].high)));
    }
}
