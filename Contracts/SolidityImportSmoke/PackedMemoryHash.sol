// SPDX-License-Identifier: MIT
pragma solidity 0.8.26;

/// Construct regression: address[20] || int24[3] || int24[3] || bytes32[32].
contract PackedMemoryHash {
    function digest(address account, int24 left, int24 right, bytes32 salt)
        public pure returns (bytes32)
    {
        return hashPacked(account, left, right, salt);
    }

    function hashPacked(address account, int24 left, int24 right, bytes32 salt)
        internal pure returns (bytes32 result)
    {
        // BEGIN packed body
        assembly ("memory-safe") {
            let base := mload(0x40)
            mstore(add(base, 38), salt)
            mstore(add(base, 6), right)
            mstore(add(base, 3), left)
            mstore(base, account)
            result := keccak256(add(base, 12), 58)
            mstore(add(base, 64), 0)
            mstore(add(base, 32), 0)
            mstore(base, 0)
        }
        // END packed body
    }

    /// Observe overlapping writes at aligned and unaligned temporary addresses.
    function inspect(address account, int24 left, int24 right, bytes32 salt, uint256 shift)
        public pure returns (bytes32 result, uint256 freeDelta, uint256 first,
            uint256 second, uint256 third, uint256 guard)
    {
        require(shift <= 64, "shift");
        uint256 original;
        uint256 base;
        // Intentionally unannotated: move the free pointer for this bounded probe.
        assembly {
            original := mload(0x40)
            base := add(original, shift)
            mstore(0x40, base)
            mstore(base, not(0))
            mstore(add(base, 32), not(0))
            mstore(add(base, 64), not(0))
            mstore(add(base, 96), 0xfeed)
        }
        result = hashPacked(account, left, right, salt);
        assembly {
            freeDelta := sub(mload(0x40), base)
            first := mload(base)
            second := mload(add(base, 32))
            third := mload(add(base, 64))
            guard := mload(add(base, 96))
            mstore(0x40, original)
        }
    }
}
