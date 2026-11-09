// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

// Test-only validator fallback. All calldata bits influence the high four bytes
// of a hashed response. Responses and storage accesses are modeled independently.
contract SignatureCallOracle {
    uint256 private value;
    bool private failed;
    uint256 private length;
    uint256 private mask;

    constructor(uint256 v, bool f, uint256 n, uint256 m) {
        value = v;
        failed = f;
        length = n;
        mask = m;
    }

    fallback() external {
        uint256 v = value;
        bool f = failed;
        uint256 n = length;
        uint256 m = mask;
        assembly ("memory-safe") {
            let ptr := mload(0x40)
            calldatacopy(ptr, 0, calldatasize())
            let digest := keccak256(ptr, calldatasize())
            mstore(0, xor(v, and(digest, m)))
            if f { revert(0, n) }
            return(0, n)
        }
    }
}
