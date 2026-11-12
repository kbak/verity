// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

// Independent finite test program. Each static query checks its complete ABI
// input, then supplies an arbitrary response word, size and failure behavior.
contract StaticBoolOracle {
    function configure(uint256 word, uint256 length, uint256 mode, bytes32 expected) external {
        require(length <= 128 && mode <= 3);
        assembly { sstore(0, word) sstore(1, length) sstore(2, mode) sstore(3, expected) }
    }
    fallback() external {
        assembly {
            let word := sload(0)
            let length := sload(1)
            let mode := sload(2)
            let expected := sload(3)
            calldatacopy(128,0,calldatasize())
            if and(iszero(iszero(expected)),iszero(eq(expected,keccak256(128,calldatasize())))) {
                mstore(0,shl(224,0xbad0ca11))
                revert(0,4)
            }
            mstore(0,word)
            if eq(mode,1) { revert(0,length) }
            if eq(mode,2) { invalid() }
            if eq(mode,3) { sstore(0,42) }
            return(0,length)
        }
    }
}
