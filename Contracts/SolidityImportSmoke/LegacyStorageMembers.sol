// SPDX-License-Identifier: MIT
pragma solidity 0.7.6;

contract StorageMemberBase { uint128 private inheritedCanary; }
contract LegacyStorageMembers is StorageMemberBase {
    struct Header {
        uint160 payload;
        int24 signedCanary;
        uint16 counter;
        uint8 marker;
        bool flag;
    }
    struct Values {
        uint8 tiny;
        bool enabled;
        address owner;
        uint32 other;
        bytes32 digest;
        uint256 wide;
    }
    Header private primary;
    Header private secondary;
    Values private values;
    event Edited(uint16 counter);
    event Tagged(uint8 marker);

    modifier entered(bool reject) {
        require(primary.flag, "closed");
        primary.flag = false;
        _;
        require(!reject, "after");
        primary.flag = true;
    }
    function read() external view returns
        (uint160, uint16, uint8, bool, address, bytes32, uint256, uint8, bool, uint16) {
        return (primary.payload, primary.counter, primary.marker, primary.flag,
            values.owner, values.digest, values.wide, values.tiny, values.enabled, secondary.counter);
    }
    function setPayload(uint160 x) external { primary.payload = x; }
    function setCounter(uint16 x) external { primary.counter = x; }
    function setMarker(uint8 x) external { primary.marker = x; }
    function setFlag(bool x) external { primary.flag = x; }
    function setOwner(address x) external { values.owner = x; }
    function setDigest(bytes32 x) external { values.digest = x; }
    function setWide(uint256 x) external { values.wide = x; }
    function setTiny(uint8 x) external { values.tiny = x; }
    function setEnabled(bool x) external { values.enabled = x; }
    function bump(uint16 x) internal { primary.counter += x; }
    function increment(uint16 x) external { bump(x); }
    function guarded(uint16 x, bool reject) external entered(reject) returns (uint16 result) {
        bump(x);
        emit Edited(primary.counter);
        result = primary.counter;
        if (x == 0) return result;
    }
    function failAfterWrite(uint8 x) external {
        primary.marker = x;
        emit Tagged(x);
        require(x != 13, "blocked");
    }
}
