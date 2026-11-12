// SPDX-License-Identifier: MIT
pragma solidity 0.8.26;

// A source-execution probe. Raw caller observations deliberately have no memory-safe annotation.
contract TailCleanupCaller {
    function packedKey(address account, int24 left, int24 right, bytes32 salt, uint256 poison)
        internal pure returns (bytes32 digest)
    {
        assembly {
            let base := mload(0x40)
            mstore(add(base, 38), salt)
            mstore(add(base, 6), right)
            mstore(add(base, 3), left)
            // Contaminate only the twelve bytes excluded from the frozen packed preimage.
            mstore(base, or(account, shl(160, poison)))
            digest := keccak256(add(base, 12), 58)
            mstore(add(base, 64), 0)
        }
    }

    function probe(address account, int24 left, int24 right, bytes32 salt,
        uint256 shift, uint256 poison, uint256 cleanupOffset) external pure returns (bytes32 result)
    {
        require(shift <= 64, "shift");
        require(poison <= 0xffffffffffffffffffffffff, "poison");
        require(cleanupOffset <= 32, "cleanup offset");
        uint256 original;
        assembly {
            original := mload(0x40)
            mstore(0x40, add(original, shift))
        }
        result = packedKey(account, left, right, salt, poison);
        assembly {
            let base := mload(0x40)
            // CALLER_CONTINUATION
            mstore(0x40, original)
        }
    }
}
