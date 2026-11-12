// SPDX-License-Identifier: MIT
pragma solidity 0.7.6;

contract LegacyCalldataExecution {
    enum Operation { Call, DelegateCall }
    function invoke(address target, uint256 amount, bytes memory input,
        Operation operation, uint256 gasLimit) internal returns (bool success)
    {
        if (operation == Operation.DelegateCall) {
            assembly { success := delegatecall(gasLimit, target, add(input, 32), mload(input), 0, 0) }
        } else {
            assembly { success := call(gasLimit, target, amount, add(input, 32), mload(input), 0, 0) }
        }
    }
    function relay(address target, uint256 amount, bytes calldata input,
        Operation operation, uint256 gasLimit) internal returns (bool)
    { return invoke(target, amount, input, operation, gasLimit); }
    function run(address target, uint256 amount, bytes calldata input,
        Operation operation, uint256 gasLimit) external returns (bool success, uint256 size)
    {
        success = relay(target, amount, input, operation, gasLimit);
        assembly { size := returndatasize() }
    }
    function forward(address target, uint256 amount, bytes calldata input,
        Operation operation, uint256 gasLimit) external
    {
        relay(target, amount, input, operation, gasLimit);
        assembly {
            let p := mload(64)
            returndatacopy(p, 0, returndatasize())
            revert(p, returndatasize())
        }
    }
}
