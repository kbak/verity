// SPDX-License-Identifier: MIT
pragma solidity 0.7.6;

library CheckedPaymentArithmetic {
    function add(uint256 a, uint256 b) internal pure returns (uint256 c) {
        c = a + b;
        require(c >= a, "addition");
    }
    function mul(uint256 a, uint256 b) internal pure returns (uint256 c) {
        if (a == 0) return 0;
        c = a * b;
        require(c / a == b, "multiplication");
    }
}

contract LegacyValuePayments {
    using CheckedPaymentArithmetic for uint256;
    uint256 public nonce;

    function pay(uint256 units, uint256 overhead, uint256 rate,
        address asset, address payable recipient, bool failAfter)
        external returns (uint256 amount) {
        nonce++;
        amount = payment(units, overhead, rate, asset, recipient);
        require(!failAfter, "outer");
    }

    function cursor(address payable receiver) external returns (uint256 beforePtr, uint256 afterPtr) {
        assembly { beforePtr := mload(64) }
        (bool success, ) = receiver.call{value: 1}("");
        if (!success) { assembly { mstore(0, 0xdecafe) revert(29, 3) } }
        assembly { afterPtr := mload(64) }
    }

    function payment(uint256 units, uint256 overhead, uint256 rate,
        address asset, address payable recipient) private returns (uint256 amount) {
        address payable receiver = recipient == address(0) ? payable(tx.origin) : recipient;
        if (asset == address(0)) {
            amount = units.add(overhead).mul(rate < tx.gasprice ? rate : tx.gasprice);
            (bool success, ) = receiver.call{value: amount}("");
            require(success, "native payment");
        } else {
            amount = units.add(overhead).mul(rate);
            require(invoke(asset, receiver, amount), "asset payment");
        }
    }

    function invoke(address target, address recipient, uint256 amount)
        private returns (bool accepted) {
        bytes memory payload = abi.encodeWithSelector(0x12345678, recipient, amount);
        assembly {
            let ok := call(sub(gas(), 10000), target, 0,
                add(payload, 32), mload(payload), 0, 32)
            switch returndatasize()
            case 0 { accepted := ok }
            case 32 { accepted := iszero(or(iszero(ok), iszero(mload(0)))) }
            default { accepted := 0 }
        }
    }
}
