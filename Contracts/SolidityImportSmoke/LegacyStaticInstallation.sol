// SPDX-License-Identifier: MIT
pragma solidity 0.7.6;

interface IStaticFlag {
    function acceptsTag(bytes4 tag) external view returns (bool);
    function assess(uint256 n, bytes32 word, address owner, bool enabled, bytes4 tag) external view returns (bool);
    function ready() external view returns (bool);
}
interface ICapability is IStaticFlag {
    function beforeAction(uint256 n) external;
    function afterAction(bytes32 word, bool success) external;
}
interface IResponse {
    function configure(uint256 word, uint256 length, uint256 mode, bytes32 expected) external;
}
contract LegacyStaticInstallation {
    uint256 public marker;
    bytes32 private constant CANDIDATE_SLOT = 0x0000000000000000000000000000000000000000000000000000000000000007;
    event Changed(address candidate);
    modifier authorized() { require(msg.sender == address(this), "self"); _; }

    function seedResponse(address target, uint256 word, uint256 length, uint256 mode, bytes32 expected) public {
        IResponse(target).configure(word, length, mode, expected);
    }
    function install(address candidate) public authorized {
        if (candidate != address(0) && !ICapability(candidate).acceptsTag(type(ICapability).interfaceId)) {
            revert("unsupported");
        }
        assembly { sstore(CANDIDATE_SLOT, candidate) }
        emit Changed(candidate);
    }
    function installAndFail(address candidate) public authorized {
        marker = 99;
        if (candidate != address(0) && !ICapability(candidate).acceptsTag(type(ICapability).interfaceId)) {
            revert("unsupported");
        }
        assembly { sstore(CANDIDATE_SLOT, candidate) }
        emit Changed(candidate);
        revert("late");
    }
    function readCandidate() public view returns(address candidate) {
        assembly { candidate := sload(CANDIDATE_SLOT) }
    }
    function readWord() public view returns(uint256 word) {
        assembly { word := sload(CANDIDATE_SLOT) }
    }
    function storeWord(uint256 word) public {
        assembly { sstore(CANDIDATE_SLOT, word) }
    }
    function probe(address target, bytes32 tag) public view returns(bool value, uint256 beforeP, uint256 afterP, uint256 raw) {
        assembly { beforeP := mload(64) }
        value = IStaticFlag(target).acceptsTag(bytes4(tag));
        assembly {
            let ptr := mload(64)
            afterP := ptr
            raw := mload(ptr)
            mstore(ptr, raw)
        }
    }
    function probeMany(address target, uint256 n, bytes32 word, address owner, bool enabled, bytes32 tag) public view returns(bool) {
        return IStaticFlag(target).assess(n, word, owner, enabled, bytes4(tag));
    }
    function probeEmpty(address target) public view returns(bool) {
        return IStaticFlag(target).ready();
    }
    function probePair(address firstTarget, address secondTarget) public view returns(bool first, bool second) {
        first = IStaticFlag(firstTarget).ready();
        second = IStaticFlag(secondTarget).ready();
    }
    function advertises(bytes32 tag) public pure returns(bool) {
        return bytes4(tag) == type(ICapability).interfaceId || bytes4(tag) == type(IStaticFlag).interfaceId;
    }
}
