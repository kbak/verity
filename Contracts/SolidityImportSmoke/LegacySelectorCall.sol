// SPDX-License-Identifier: MIT
pragma solidity 0.7.6;

interface IMessage {
    function record(address account, uint256 amount) external;
}

library CheckedMessage {
    function send(address target, address account, uint256 amount) internal {
        (bool success, bytes memory data) =
            target.call(abi.encodeWithSelector(IMessage.record.selector, account, amount));
        require(success && (data.length == 0 || abi.decode(data, (bool))), "response rejected");
    }
}

contract LegacySelectorCall {
    uint256 private attempts;

    function checked(address target, address account, uint256 amount) external {
        attempts += 1;
        CheckedMessage.send(target, account, amount);
    }

    function inspect(address target, address account, uint256 amount)
        external returns (bool, uint256, uint256, uint256, uint256)
    {
        (bool success, bytes memory data) =
            target.call(abi.encodeWithSelector(IMessage.record.selector, account, amount));
        uint256 first;
        uint256 second;
        uint256 third;
        assembly {
            first := mload(add(data, 32))
            second := mload(add(data, 64))
            third := mload(add(data, 96))
        }
        return (success, data.length, first, second, third);
    }
}
