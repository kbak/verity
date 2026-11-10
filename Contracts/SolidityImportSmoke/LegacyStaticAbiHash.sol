// SPDX-License-Identifier: MIT
pragma solidity 0.7.6;

contract LegacyStaticAbiHash {
    bytes32 private constant TAG = bytes32(uint256(0x123456));

    function digest(bytes32 tag, uint256 quantity, address account) public pure returns (bytes32) {
        return keccak256(abi.encode(tag, quantity, account));
    }
    function scalars(uint256 quantity, address account, bool flag, bytes32 word)
        public pure returns (bytes32)
    {
        return keccak256(abi.encode(uint8(quantity), uint16(quantity), uint96(quantity),
            quantity, account, flag, bytes1(word), bytes4(word), bytes12(word), bytes20(word), word));
    }
    function raw(uint8 small, address account, bool flag, bytes32 tag) public pure returns (bytes32) {
        return keccak256(abi.encode(small, account, flag, bytes4(tag)));
    }
    function literals() public pure returns (bytes32) {
        return keccak256(abi.encode(0, 255, true, bytes4(0x12345678)));
    }
    function empty() public pure returns (bytes32, uint256) {
        bytes32 hash = keccak256(abi.encode());
        uint256 free;
        assembly { free := mload(64) }
        return (hash, free);
    }
    function domain() public view returns (bytes32) {
        uint256 id;
        assembly { id := chainid() }
        return keccak256(abi.encode(TAG, id, this));
    }
    function viaHelper(bytes32 tag) public view returns (bytes32) {
        return helper(tag);
    }
    function helper(bytes32 tag) internal view returns (bytes32) {
        uint256 id;
        assembly { id := chainid() }
        return keccak256(abi.encode(tag, id, this));
    }
    function inspect(bytes memory pad, bytes32 word, uint256 offset)
        public pure returns (bytes32, uint256, uint256)
    {
        require(pad.length <= 256, "pad");
        uint256 start;
        assembly { start := mload(64) }
        bytes32 hash = keccak256(abi.encode(uint8(7), word, bytes4(0x12345678)));
        uint256 free;
        uint256 observed;
        bytes memory viewData;
        assembly {
            free := mload(64)
            viewData := add(start, offset)
            observed := mload(viewData)
        }
        return (hash, free, observed);
    }
    function mixed(bytes32 word, uint256 offset) public pure returns (bytes32, uint256, uint256) {
        bytes32 first = keccak256(abi.encodePacked(hex"aabbcc", word));
        bytes32 second = keccak256(abi.encode(first, uint16(513)));
        uint256 free;
        uint256 observed;
        bytes memory viewData;
        assembly { free := mload(64) viewData := add(128, offset) observed := mload(viewData) }
        return (second, free, observed);
    }
    function loop(bytes32 word, uint256 count) public pure returns (bytes32, uint256) {
        require(count <= 4, "count");
        for (uint256 i = 0; i < count; ++i) {
            word = keccak256(abi.encode(uint8(i), word));
        }
        uint256 free;
        assembly { free := mload(64) }
        return (word, free);
    }
}
