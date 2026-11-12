// SPDX-License-Identifier: MIT
pragma solidity 0.7.6;

enum Operation { Call, DelegateCall }
interface ITypedCallback {
    function beforeCall(address target, uint256 amount, bytes memory input, Operation operation,
        uint256 mode, uint256 base, uint256 price, address token, address payable receiver,
        bytes memory auxiliary, address sender) external;
    function afterCall(bytes32 token, bool success) external;
    function settle(uint256 first, uint256 second, bytes memory data) external;
}
contract LegacyTypedCallGas {
    uint256 public serial;
    event Completed(bytes32 token);

    function before(address target, bytes calldata data, bytes memory auxiliary) internal {
        ITypedCallback(target).beforeCall(target, uint256(7), data, Operation.Call, uint256(0), uint256(7), uint256(8),
            address(0), address(0), auxiliary, msg.sender);
    }
    function run(address first, address second, bytes calldata data, bytes memory auxiliary,
        bool fail) external returns (uint256 spent) {
        serial += 1;
        bytes32 token = bytes32(serial);
        uint256 initial = gasleft();
        before(first, data, auxiliary);
        bool paid;
        assembly { paid := call(1000000, 0x3344, 3, 0, 0, 0, 0) }
        require(paid, "payment");
        emit Completed(token);
        ITypedCallback(second).afterCall(token, true);
        require(!fail, "outer");
        return initial - gasleft();
    }
    function settle(address target, uint256 first, uint256 second, bytes calldata data) external {
        ITypedCallback(target).settle(first, second, data);
    }
}
