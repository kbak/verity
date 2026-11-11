// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

// Independent EVM program: commit context/hash, echo exact calldata, or fail.
contract RawCallOracle {
    fallback() external payable {
        assembly {
            calldatacopy(0, 0, calldatasize())
            sstore(0, keccak256(0, calldatasize()))
            sstore(1, caller())
            sstore(2, address())
            sstore(3, callvalue())
            sstore(4, selfbalance())
            sstore(5, origin())
            sstore(6, add(sload(6), 1))
            switch byte(0, calldataload(0))
            case 1 { revert(0, calldatasize()) }
            case 2 { invalid() }
            default { return(0, calldatasize()) }
        }
    }
}
