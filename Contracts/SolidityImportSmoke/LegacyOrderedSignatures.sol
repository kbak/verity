// SPDX-License-Identifier: MIT
pragma solidity 0.7.6;

interface IOrderedSignatureValidator {
    function isValidSignature(bytes32, bytes memory) external view returns (bytes4);
}

/// Ordered, thresholded signature records exercise composition of legacy constructs.
contract LegacyOrderedSignatures {
    mapping(address => address) private members;
    uint256 private threshold;
    mapping(address => mapping(bytes32 => uint256)) private approvals;

    function checkThreshold(address executor, bytes32 h, bytes memory records)
        public view returns (uint256)
    {
        uint256 required = threshold;
        if (required == 0) revert("threshold");
        return checkN(executor, h, records, required);
    }

    function checkN(address executor, bytes32 h, bytes memory records, uint256 count)
        public view returns (uint256)
    {
        uint256 staticSize = recordBytes(count);
        require(records.length >= staticSize, "length");
        address previous = address(0);
        address current;
        for (uint256 i = 0; i < count; ++i) {
            bytes32 r;
            bytes32 s;
            uint256 tag;
            assembly {
                r := mload(add(add(records, 32), mul(i, 65)))
                s := mload(add(add(records, 64), mul(i, 65)))
                tag := byte(0, mload(add(add(records, 96), mul(i, 65))))
            }
            if (tag == 0) {
                current = address(uint160(uint256(r)));
                uint256 offset = uint256(s);
                require(offset >= staticSize, "offset");
                validateRecord(current, h, records, offset);
            } else if (tag == 1) {
                current = address(uint160(uint256(r)));
                require(executor == current || approvals[current][h] != 0, "approval");
            } else if (tag > 30) {
                current = ecrecover(keccak256(abi.encodePacked(
                    "\x19Ethereum Signed Message:\n32", h)), uint8(tag - 4), r, s);
            } else {
                current = ecrecover(h, uint8(tag), r, s);
            }
            if (current <= previous || members[current] == address(0) || current == address(1)) {
                revert("member");
            }
            previous = current;
        }
        return 1;
    }
    function recordBytes(uint256 count) internal pure returns (uint256) {
        if (count == 0) return 0;
        uint256 result = count * 65;
        require(result / count == 65);
        return result;
    }

    function validateRecord(address target, bytes32 h, bytes memory records, uint256 offset)
        internal view
    {
        uint256 start = offset + 32;
        require(start >= offset);
        require(start <= records.length, "header");
        uint256 size;
        assembly { size := mload(add(add(records, offset), 32)) }
        uint256 end = start + size;
        require(end >= start);
        require(end <= records.length, "payload");
        bytes memory selected;
        assembly { selected := add(add(records, offset), 32) }
        require(IOrderedSignatureValidator(target).isValidSignature(h, selected)
            == bytes4(0x1626ba7e), "validator");
    }

}
