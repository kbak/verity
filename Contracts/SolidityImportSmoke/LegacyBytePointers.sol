// SPDX-License-Identifier: MIT
pragma solidity 0.7.6;
interface IBytePointerValidator {
    function validate(bytes32, bytes memory) external view returns (bytes4);
}
contract LegacyBytePointers {
    function inspect(bytes memory data, uint256 offset) public pure returns (uint256, uint256, uint256) {
        bytes memory viewData;
        uint256 header;
        uint256 first;
        assembly {
            viewData := add(add(data, offset), 32)
            header := viewData
            first := mload(add(viewData, 32))
        }
        return (header, viewData.length, first);
    }
    function empty(uint256) public pure returns (uint256, uint256, uint256) {
        bytes memory data;
        uint256 header;
        uint256 free;
        assembly { header := data free := mload(64) }
        return (header, data.length, free);
    }
    function zero(bytes memory data) public pure returns (uint256) {
        assembly { data := 0 }
        return data.length;
    }
    function lazy(uint256 target) public pure returns (uint256 result) {
        bytes memory data;
        assembly { data := target }
        bytes memory aliasData = data;
        assembly { result := aliasData }
    }
    function root(bytes memory data, uint256 offset) public pure returns (uint256, uint256) {
        bytes memory aliasData = data;
        assembly { data := add(data, offset) }
        return (data.length, aliasData.length);
    }
    function choose(bytes memory a, bytes memory b, uint256 offset, bool take)
        public pure returns (uint256, uint256, uint256)
    {
        bytes memory selected = a;
        bytes memory saved = selected;
        if (take) {
            assembly { selected := add(add(b, offset), 32) }
        } else { selected = b; }
        return (selected.length, saved.length, a.length);
    }
    function loop(bytes memory data, uint256 offset, uint256 count) public pure returns (uint256) {
        require(count <= 3, "count");
        bytes memory selected;
        for (uint256 i = 0; i < count; ++i) {
            assembly { selected := add(add(data, offset), 32) }
            offset += 32;
        }
        return selected.length;
    }
    function helper(bytes memory data, uint256 offset) public pure returns (uint256, uint256) {
        uint256 size = _view(data, offset);
        return (size, data.length);
    }
    function _view(bytes memory data, uint256 offset) internal pure returns (uint256) {
        assembly { data := add(add(data, offset), 32) }
        return data.length;
    }
    function live(bytes memory data) public pure returns (uint256, uint256, uint256) {
        uint256 end = 64 + ((data.length + 31) / 32) * 32;
        bytes memory selected;
        assembly { selected := add(data, end) }
        bytes memory aliasData = selected;
        uint256 before = selected.length;
        address recovered = ecrecover(bytes32(uint256(7)), 0, 0, 0);
        require(recovered == address(0));
        uint256 afterFirst = aliasData.length;
        uint256 afterSecond = _overwrite(selected);
        return (before, afterFirst, afterSecond);
    }
    function _overwrite(bytes memory data) internal pure returns (uint256) {
        address recovered = ecrecover(bytes32(uint256(11)), 0, 0, 0);
        require(recovered == address(0));
        return data.length;
    }
    function overlap(address target, bytes32 h, uint256 offset) public view returns (uint256) {
        bytes memory selected;
        assembly { selected := add(mload(64), offset) }
        return uint256(bytes32(IBytePointerValidator(target).validate(h, selected)));
    }
    function validate(address target, bytes32 h, bytes memory data, uint256 offset)
        public view returns (uint256)
    {
        uint256 start = offset + 32;
        require(start >= offset, "overflow");
        require(start <= data.length, "header");
        uint256 size;
        assembly { size := mload(add(add(data, offset), 32)) }
        uint256 finish = start + size;
        require(finish >= start, "overflow");
        require(finish <= data.length, "payload");
        bytes memory selected;
        assembly { selected := add(add(data, offset), 32) }
        return uint256(bytes32(IBytePointerValidator(target).validate(h, selected)));
    }
}
