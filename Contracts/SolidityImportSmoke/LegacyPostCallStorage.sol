// SPDX-License-Identifier: MIT
pragma solidity 0.7.6;

interface IBalanceRead {
    function read(address account) external view returns (uint256);
}
interface IBalanceCallback {
    function settle(address ledger, uint256 paid, uint256 mode, bytes calldata data) external;
}
library CheckedBalanceAdd {
    function add(uint256 a, uint256 b) internal pure returns (uint256 c) {
        require((c = a + b) >= a, "overflow");
    }
}
contract LegacyPostCallStorage {
    using CheckedBalanceAdd for uint256;
    address public immutable ledger;
    address public immutable callback;
    uint256 public sequence;
    struct Flags { uint128 neighbor; bool unlocked; uint64 untouched; }
    Flags private flags;
    uint256 public receipt;
    event Changed(uint256 neighbor);
    modifier guarded() {
        require(flags.unlocked, "locked");
        flags.unlocked = false;
        _;
        flags.unlocked = true;
    }
    modifier postcheck(uint256 mode) { _; require(mode != 9, "late"); }
    function isOpen() external view returns (bool) { return flags.unlocked; }
    function neighbor() external view returns (uint128) { return flags.neighbor; }
    function setNeighbor(uint128 n) external { flags.neighbor = n; emit Changed(n); }
    function guardedPing() external guarded {}
    event Starting(uint256 sequence);
    event Received(uint256 sequence, uint256 amount);
    constructor(address l, address c) { ledger = l; callback = c; flags.unlocked = true; flags.untouched = 700; }
    function query() private view returns (uint256) {
        (bool ok, bytes memory data) = ledger.staticcall(
            abi.encodeWithSelector(IBalanceRead.read.selector, address(this)));
        require(ok && data.length >= 32);
        return abi.decode(data, (uint256));
    }
    function observe() external view returns (uint256) { return query(); }
    function settle(uint256 due, uint256 paid, uint256 mode, bytes calldata data)
        external postcheck(mode) guarded returns (uint256 result) {
        sequence += 1;
        uint256 ticket = sequence;
        emit Starting(ticket);
        uint256 beforeAmount = query();
        IBalanceCallback(callback).settle(ledger, paid, mode, data);
        uint256 afterAmount = query();
        require(beforeAmount.add(due) <= afterAmount, "payment");
        emit Received(ticket, afterAmount);
        receipt = paid;
        if (mode == 4) return afterAmount;
        result = afterAmount;
    }
}
