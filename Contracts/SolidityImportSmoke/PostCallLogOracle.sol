// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

// Independent EVM program with raw LOG0..LOG4 and bounded test-selected nested calls.
contract PostCallLogOracle {
    fallback() external payable {
        assembly {
            let size := calldatasize()
            calldatacopy(0, 0, size)
            sstore(7, add(sload(7), 1))
            log0(0, size)
            log1(0, size, address())
            log2(0, size, caller(), callvalue())
            log3(0, size, 0x33, address(), caller())
            log4(0, size, 0x44, address(), caller(), callvalue())
            let mode := byte(0, calldataload(0))
            switch mode
            case 1 { revert(0, size) }
            case 2 { invalid() }
            default {
                if and(gt(mode, 2), lt(mode, 6)) {
                    let target := shr(96, calldataload(1))
                    let count := sub(size, 21)
                    calldatacopy(0x400, 21, count)
                    let success := 0
                    switch mode
                    case 4 { success := delegatecall(1000000, target, 0x400, count, 0, 0) }
                    default { success := call(1000000, target, 0, 0x400, count, 0, 0) }
                    log2(0, size, 0x55, success)
                    if eq(mode, 5) { revert(0, size) }
                }
                return(0, size)
            }
        }
    }
}
