// SPDX-License-Identifier: MIT
pragma solidity 0.7.6;
import "./LegacyVoidCallbacks.sol";

contract LegacyPostCallMemoryLoops is LegacyVoidCallbacks {
    function beforeCopy(address callback, address target, uint256 amount, bytes calldata input,
        Operation operation, bytes memory auxiliary, uint256 mode) internal {
        IVoidCallback(callback).beforeCall(target, amount, input, operation, mode,
            uint256(7), uint256(8), address(0), address(0), auxiliary, msg.sender);
    }

    function runCalldata(address target, uint256 amount, bytes calldata input,
        Operation operation, bytes memory auxiliary, uint256 mode)
        external payable returns (bool success) {
        address callback = readCallback();
        serial += 1;
        bytes32 token = bytes32(serial);
        emit Starting(msg.sender, serial);
        if (callback != address(0)) {
            beforeCopy(callback, target, amount, input, operation, auxiliary, mode);
        }
        // Converting this immutable calldata into memory now occurs after the callback.
        success = invoke(target, amount, input, operation, 1000000);
        bool paid;
        assembly { paid := call(1000000, 0x77, 3, 0, 0, 0, 0) }
        require(paid, "payment");
        emit Outcome(target, success, 0);
        if (callback != address(0)) {
            IVoidCallback(callback).afterCall(token, success);
        }
    }
}
