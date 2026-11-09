// SPDX-License-Identifier: MIT
pragma solidity >=0.7.6 <0.9.0;

contract FixedBytesMemoryRevertRejections {
    function dirtyPadding(uint256 x) external pure {
        bytes5 code = bytes5(bytes32(x));
        assembly { mstore(0, code) revert(0, 32) }
    }
    function dirtyInteger(uint256 x) external pure {
        uint8 small = uint8(x);
        assembly { mstore(0, small) revert(0, 32) }
    }
    function rootBytes(bytes5 x) external pure returns (bytes32) { return x; }
    function indexByte(uint256 i) external pure returns (bytes32) {
        return bytes5("ABCDE")[i];
    }
    function nonterminal(uint256 x) external pure returns (uint256) {
        assembly { mstore(0, x) }
        return x;
    }
    function unsupportedBuiltin(uint256 x) external pure {
        assembly { mstore(0, div(x, 2)) revert(0, 32) }
    }
    function conditionalAssembly(uint256 x) external pure {
        assembly { if x { mstore(0, x) } revert(0, 32) }
    }
    function dynamicBuffer(uint256) external pure {
        bytes memory x = new bytes(5);
        assembly { revert(add(x, 32), 5) }
    }
    function division(uint256 x) external pure returns (uint256) { return 1 / x; }
    function arbitraryLoad(uint256 x) external pure {
        assembly { let y := mload(x) mstore(0, y) revert(0, 32) }
    }
}
