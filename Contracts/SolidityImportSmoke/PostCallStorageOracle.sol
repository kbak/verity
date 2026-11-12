// SPDX-License-Identifier: MIT
pragma solidity 0.8.34;

contract PostCallStorageLedger {
    mapping(address => uint256) private balances;
    uint256 private mode;
    function credit(address account, uint256 paid, uint256 nextMode) external {
        unchecked { balances[account] += paid; }
        mode = nextMode;
        assembly { mstore(0, paid) log0(0, 32) }
    }
    function read(address account) external returns (uint256) {
        uint256 amount = balances[account];
        uint256 selected = mode;
        assembly {
            mstore(0, amount)
            switch selected
            case 1 { return(0, 31) }
            case 2 { mstore(0, 0x004100) revert(29, 3) }
            case 3 { invalid() }
            case 4 { mstore(32, 700) return(0, 64) }
            case 5 { sstore(1, 0) }
            case 6 { return(0, 0) }
            default { }
            return(0, 32)
        }
    }
}
interface IPostCallStorageParent {
    function isOpen() external view returns (bool);
    function setNeighbor(uint128 n) external;
}
contract PostCallStoragePayer {
    uint256 private calls;
    function settle(address ledger, uint256 paid, uint256 mode, bytes calldata data) external {
        PostCallStorageLedger(ledger).credit(msg.sender, paid, mode);
        require(!IPostCallStorageParent(msg.sender).isOpen(), "unlocked");
        (bool entered, bytes memory reason) = msg.sender.call(
            abi.encodeWithSignature("guardedPing()"));
        require(!entered && keccak256(reason) == keccak256(
            abi.encodeWithSignature("Error(string)", "locked")), "reentry");
        IPostCallStorageParent(msg.sender).setNeighbor(uint128(paid));
        unchecked { calls += 1; }
        assembly { mstore(0, mode) log0(0, 32) }
        if (mode == 7) {
            assembly { mstore(0, 0x005200) revert(29, 3) }
        }
        if (mode == 8) { assembly { invalid() } }
        // Successful callback bytes are deliberately unrelated to the balance.
        assembly { calldatacopy(0, data.offset, data.length) return(0, data.length) }
    }
}
