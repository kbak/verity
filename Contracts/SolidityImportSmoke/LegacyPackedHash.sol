// SPDX-License-Identifier: MIT
pragma solidity 0.7.6;

contract LegacyPackedHash {
    function digest(bytes32 word) public pure returns (bytes32) {
        return keccak256(abi.encodePacked("Typed digest:\n32", word));
    }
    function scalars(uint256 quantity, address account, bool flag, bytes32 word)
        public pure returns (bytes32)
    {
        return keccak256(abi.encodePacked(uint8(quantity), uint16(quantity), uint96(quantity),
            quantity, account, flag, bytes1(word), bytes4(word), bytes12(word), bytes20(word), word));
    }
    function literals(bytes32 word) public pure returns (bytes32) {
        return keccak256(abi.encodePacked(hex"", unicode"\u03bb\u0000", word,
            hex"000102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20",
            hex"ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff", hex"00"));
    }
    function empty() public pure returns (bytes32, uint256) {
        bytes32 hash = keccak256(abi.encodePacked());
        uint256 free;
        assembly { free := mload(64) }
        return (hash, free);
    }
    function inspect(bytes memory pad, bytes32 word, uint256 offset)
        public pure returns (bytes32, uint256, uint256)
    {
        // Retain the input decoder's allocation while examining encoder writes.
        require(pad.length <= 256, "pad");
        uint256 start;
        assembly { start := mload(64) }
        bytes32 hash = keccak256(abi.encodePacked(hex"010203", word, uint16(513)));
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
    function chain(bytes32 word, uint256 offset) public pure returns (bytes32, uint256, uint256) {
        bytes32 first = keccak256(abi.encodePacked(hex"aabbcc", word));
        bytes32 second = keccak256(abi.encodePacked(first, hex"dd"));
        uint256 free;
        uint256 observed;
        bytes memory viewData;
        assembly { free := mload(64) viewData := add(128, offset) observed := mload(viewData) }
        return (second, free, observed);
    }
    function loop(bytes32 word, uint256 count) public pure returns (bytes32, uint256) {
        require(count <= 4, "count");
        for (uint256 i = 0; i < count; ++i) {
            word = keccak256(abi.encodePacked(uint8(i), word));
        }
        uint256 free;
        assembly { free := mload(64) }
        return (word, free);
    }
    function recover(bytes32 word, uint256 v, bytes32 r, bytes32 s) public pure returns (address) {
        return ecrecover(keccak256(abi.encodePacked("Typed digest:\n32", word)), uint8(v), r, s);
    }
    function scratch(bytes32 word, uint256 offset) public pure returns (bytes32, uint256, uint256) {
        address recovered = ecrecover(word, 0, word, word);
        require(recovered == address(0), "recovery");
        bytes32 hash = keccak256(abi.encodePacked(hex"ab"));
        uint256 free;
        uint256 observed;
        bytes memory viewData;
        assembly { free := mload(64) viewData := add(160, offset) observed := mload(viewData) }
        return (hash, free, observed);
    }
}
