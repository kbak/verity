// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

// Independent finite child program: records exact input/context, supports
// phase-specific rejection, and returns deliberately untyped successful bytes.
contract VoidCallOracle {
    fallback() external payable {
        assembly {
            let selector := shr(224, calldataload(0))
            let beforeSelector := 2894857179
            let afterSelector := 1528555473
            let typed := or(eq(selector,beforeSelector),eq(selector,afterSelector))
            let mode := byte(0,calldataload(0))
            if eq(selector,beforeSelector) { mode := calldataload(132) sstore(20,mode) }
            if eq(selector,afterSelector) { mode := sload(20) }
            calldatacopy(0,0,calldatasize())
            log0(0,calldatasize())
            sstore(21,add(sload(21),1))
            sstore(22,keccak256(0,calldatasize()))
            sstore(23,caller())
            sstore(24,address())
            sstore(25,callvalue())
            if or(and(eq(selector,beforeSelector),eq(mode,200)),
                  or(and(eq(selector,afterSelector),eq(mode,202)),and(iszero(typed),eq(mode,1)))) {
                revert(0,calldatasize())
            }
            if or(and(eq(selector,beforeSelector),eq(mode,201)),
                  or(and(eq(selector,afterSelector),eq(mode,203)),and(iszero(typed),eq(mode,2)))) {
                invalid()
            }
            if typed { return(0,mod(mode,128)) }
            return(0,calldatasize())
        }
    }
}
