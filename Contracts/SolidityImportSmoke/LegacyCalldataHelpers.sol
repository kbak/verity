// SPDX-License-Identifier: MIT
pragma solidity 0.7.6;

contract LegacyCalldataHelpers {
    function forward(bytes calldata data) external pure returns (uint256, bytes32, uint256) {
        return relay(data);
    }
    function relay(bytes calldata data) internal pure returns (uint256, bytes32, uint256) {
        return leaf(data);
    }
    function leaf(bytes calldata data) private pure returns (uint256, bytes32 result, uint256 free) {
        assembly {
            let p := mload(64)
            calldatacopy(p, data.offset, data.length)
            result := keccak256(p, data.length)
            free := mload(64)
        }
        return (data.length, result, free);
    }
    function copy(bytes calldata data) external pure
        returns (uint256, uint256, uint256, uint256, uint256, uint256)
    { return inspect(data); }
    function inspect(bytes memory data) internal pure
        returns (uint256 p, uint256 size, uint256 free, uint256 first, uint256 tail, uint256 beyond)
    {
        size = data.length;
        assembly {
            p := data
            free := mload(64)
            first := mload(add(data, 32))
            tail := mload(add(add(data, 32), size))
        }
        bytes memory canary;
        assembly { canary := add(mload(64), 32) }
        beyond = canary.length;
    }
    function pair(bytes calldata a, bytes calldata b) external pure
        returns (uint256, uint256, uint256, uint256, uint256)
    { return pairMemory(a, b); }
    function pairMemory(bytes memory a, bytes memory b) internal pure
        returns (uint256 pa, uint256 pb, uint256 na, uint256 nb, uint256 free)
    {
        na = a.length;
        nb = b.length;
        assembly { pa := a pb := b free := mload(64) }
    }
    function header(bytes memory data) internal pure returns (uint256 p) {
        assembly { p := data }
    }
    function siblings(bytes calldata data) external pure returns (uint256, uint256, uint256) {
        uint256 first = header(data);
        uint256 second = header(data);
        uint256 free;
        assembly { free := mload(64) }
        return (first, second, free);
    }
    function live(bytes calldata data) external pure returns (uint256, uint256, uint256) {
        bytes memory future;
        assembly { future := mload(64) }
        uint256 before = future.length;
        uint256 copied = header(data);
        return (before, future.length, copied);
    }
    function aliasPointer(bytes calldata data) external pure returns (uint256, uint256, uint256) {
        return aliasMemory(data);
    }
    function aliasMemory(bytes memory data) internal pure returns (uint256, uint256, uint256) {
        bytes memory saved = data;
        assembly { data := add(data, 32) }
        uint256 p;
        assembly { p := saved }
        return (saved.length, data.length, p);
    }
    function dirty(bytes calldata data) external pure
        returns (uint256, uint256, uint256, uint256, uint256, uint256)
    {
        require(data.length <= 96, "size");
        uint256 fill = uint256(-1);
        assembly {
            let p := mload(64)
            mstore(p, fill)
            mstore(add(p, 32), fill)
            mstore(add(p, 64), fill)
            mstore(add(p, 96), fill)
            mstore(add(p, 128), fill)
            mstore(add(p, 160), fill)
            mstore(add(p, 192), fill)
            mstore(add(p, 224), fill)
        }
        return inspect(data);
    }
    function mixed(bytes memory a, bytes calldata b) external pure
        returns (uint256, uint256, uint256, uint256, uint256)
    { return mixedMemory(a, b, a); }
    function mixedMemory(bytes memory a, bytes memory b, bytes memory aliasData) internal pure
        returns (uint256 pa, uint256 pb, uint256 same, uint256 nb, uint256 free)
    {
        nb = b.length;
        assembly { pa := a pb := b same := aliasData free := mload(64) }
    }
    function copyThenForward(bytes calldata data) external pure returns (uint256, bytes32, uint256) {
        header(data);
        return relay(data);
    }
    function skipped(bytes calldata data, bool take) external pure returns (uint256 free) {
        if (take) { header(data); }
        assembly { free := mload(64) }
    }
    function through(bytes calldata data) external pure
        returns (uint256, uint256, uint256, uint256, uint256, uint256)
    { return calldataRelay(data); }
    function calldataRelay(bytes calldata data) internal pure
        returns (uint256, uint256, uint256, uint256, uint256, uint256)
    { return inspect(data); }
    function unusedMemory(bytes memory) internal pure {}
    function unusedCalldata(bytes calldata) internal pure {}
    function skipCopy(bytes calldata data) external pure returns (uint256 free) {
        unusedMemory(data);
        assembly { free := mload(64) }
    }
    function skipForward(bytes calldata data) external pure returns (uint256 free) {
        unusedCalldata(data);
        assembly { free := mload(64) }
    }

}
