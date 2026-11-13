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
contract LegacyPostCallBalance {
    using CheckedBalanceAdd for uint256;
    address public immutable ledger;
    address public immutable callback;
    uint256 public sequence;
    event Starting(uint256 sequence);
    event Received(uint256 sequence, uint256 amount);
    constructor(address l, address c) { ledger = l; callback = c; }
    function query() private view returns (uint256) {
        (bool ok, bytes memory data) = ledger.staticcall(
            abi.encodeWithSelector(IBalanceRead.read.selector, address(this)));
        require(ok && data.length >= 32);
        return abi.decode(data, (uint256));
    }
    function observe() external view returns (uint256) { return query(); }
    function settle(uint256 due, uint256 paid, uint256 mode, bytes calldata data)
        external returns (uint256) {
        sequence += 1;
        uint256 ticket = sequence;
        emit Starting(ticket);
        uint256 beforeAmount = query();
        IBalanceCallback(callback).settle(ledger, paid, mode, data);
        uint256 afterAmount = query();
        require(beforeAmount.add(due) <= afterAmount, "payment");
        emit Received(ticket, afterAmount);
        return afterAmount;
    }
    function settleTwice(uint256 due, uint256 first, uint256 second, bytes calldata data)
        external returns (uint256) {
        uint256 beforeAmount = query();
        IBalanceCallback(callback).settle(ledger, first, uint256(0), data);
        uint256 middleAmount = query();
        require(beforeAmount.add(first) <= middleAmount, "first");
        IBalanceCallback(callback).settle(ledger, second, uint256(0), data);
        uint256 afterAmount = query();
        require(beforeAmount.add(due) <= afterAmount, "payment");
        return afterAmount;
    }
}
