pragma solidity 0.7.6;

contract LegacyMemoryArrays {
    mapping(address => address) internal links;
    uint256 internal capacity;
    uint256 internal revision;
    address internal constant SENTINEL = address(1);
    event Attempt(uint256 index);

    function allocate(uint256 size) public pure returns (address[] memory) {
        address[] memory items = new address[](size);
        return items;
    }

    function echo(address[] memory items) public pure returns (address[] memory) {
        return items;
    }

    function read(address[] memory items, uint256 index) public pure returns (address) {
        return readCell(items, index);
    }

    function readCell(address[] memory items, uint256 index) internal pure returns (address) {
        return items[index];
    }

    function replace(address[] memory items, uint256 index, address value) public returns (address[] memory) {
        revision += 1;
        emit Attempt(index);
        items[index] = value;
        return items;
    }

    function sumPrefix(address[] memory items, uint256 size) public pure returns (uint256 total) {
        for (uint256 index = 0; index < size; ++index) total += uint256(items[index]);
        return total;
    }

    function sumOffset(address[] memory items) public pure returns (uint256 total) {
        for (uint256 index = 0; index < items.length; ++index) total += uint256(items[index + 1]);
        return total;
    }

    function sumExpanded(address[] memory items) public pure returns (uint256 total) {
        uint256 size = items.length;
        size += 1;
        for (uint256 index = 0; index < size; ++index) total += uint256(items[index]);
        return total;
    }

    function fill(address[] memory items) public pure returns (address[] memory) {
        for (uint256 index = 0; index < items.length; ++index) items[index] = address(2);
        return items;
    }

    function enumerate() public view returns (address[] memory) {
        address[] memory items = new address[](capacity);
        uint256 index = 0;
        address cursor = links[SENTINEL];
        while (cursor != SENTINEL) {
            items[index] = cursor;
            cursor = links[cursor];
            ++index;
        }
        return items;
    }
}
