// SPDX-License-Identifier: MIT
pragma solidity 0.7.6;

contract LegacySignedPackedHash {
    function hashKey(address account, int24 left, int24 right) internal pure returns (bytes32) {
        return keccak256(abi.encodePacked(account, left, right));
    }
    function key(address account, int24 left, int24 right) external pure returns (bytes32) {
        return hashKey(account, left, right);
    }
    function unsignedKey(address account, uint24 left, uint24 right)
        external pure returns (bytes32)
    {
        return keccak256(abi.encodePacked(account, left, right));
    }
    function inspect(address account, int24 left, int24 right, uint256 offset)
        external pure returns (bytes32, uint256, uint256)
    {
        uint256 start;
        assembly { start := mload(64) }
        bytes32 hash = hashKey(account, left, right);
        uint256 free;
        uint256 observed;
        bytes memory viewData;
        assembly { free := mload(64) viewData := add(start, offset) observed := mload(viewData) }
        return (hash, free, observed);
    }
    function chain(address account, int24 left, int24 right, uint256 offset)
        external pure returns (bytes32, uint256, uint256)
    {
        bytes32 first = hashKey(account, left, right);
        bytes32 second = keccak256(abi.encodePacked(first, right));
        uint256 free;
        uint256 observed;
        bytes memory viewData;
        assembly { free := mload(64) viewData := add(128, offset) observed := mload(viewData) }
        return (second, free, observed);
    }
    function widthsLow(int256 value) external pure returns (bytes32) {
        return keccak256(abi.encodePacked(int8(value), int16(value), int24(value), int32(value),
            int40(value), int48(value), int56(value), int64(value)));
    }
    function widthsMiddle(int256 value) external pure returns (bytes32) {
        return keccak256(abi.encodePacked(int72(value), int80(value), int88(value), int96(value),
            int104(value), int112(value), int120(value), int128(value)));
    }
    function widthsHigh(int256 value) external pure returns (bytes32) {
        return keccak256(abi.encodePacked(int136(value), int144(value), int152(value), int160(value),
            int168(value), int176(value), int184(value), int192(value)));
    }
    function widthsFull(int256 value) external pure returns (bytes32) {
        return keccak256(abi.encodePacked(int200(value), int208(value), int216(value), int224(value),
            int232(value), int240(value), int248(value), value));
    }
}

library SignedPackedRecords {
    struct Row { uint128 amount; uint8 tag; }
    function get(mapping(bytes32 => Row) storage self, address account, int24 left, int24 right)
        internal view returns (Row storage row)
    {
        row = self[keccak256(abi.encodePacked(account, left, right))];
    }
}

contract LegacySignedPackedMapping {
    using SignedPackedRecords for mapping(bytes32 => SignedPackedRecords.Row);
    mapping(bytes32 => SignedPackedRecords.Row) private rows;
    event Changed(uint128 amount);

    function read(address account, int24 left, int24 right) external view returns (uint128, uint8) {
        SignedPackedRecords.Row storage row = rows.get(account, left, right);
        return (row.amount, row.tag);
    }
    function edit(address account, int24 left, int24 right, uint128 step, bool reject)
        external returns (uint128)
    {
        SignedPackedRecords.Row storage row = rows.get(account, left, right);
        row.amount += step;
        emit Changed(row.amount);
        require(!reject, "rollback");
        return row.amount;
    }
}
