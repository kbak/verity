// SPDX-License-Identifier: MIT
pragma solidity 0.7.6;

// Generic raw CALL/DELEGATECALL through an enum-bearing internal helper.
contract LegacyRawCalls {
    enum Operation { Call, DelegateCall }

    function invoke(address target, uint256 amount, bytes memory input,
                    Operation operation, uint256 gasLimit) internal returns (bool success) {
        if (operation == Operation.DelegateCall) {
            assembly { success := delegatecall(gasLimit, target, add(input, 32), mload(input), 0, 0) }
        } else {
            assembly { success := call(gasLimit, target, amount, add(input, 32), mload(input), 0, 0) }
        }
    }

    function run(address target, uint256 amount, bytes memory input,
                 Operation operation, uint256 gasLimit) public returns (bool success, uint256 size) {
        success = invoke(target, amount, input, operation, gasLimit);
        assembly { size := returndatasize() }
    }

    // Forward the entire buffer even on child success; outer REVERT undoes it.
    function forward(address target, uint256 amount, bytes memory input,
                     Operation operation, uint256 gasLimit) public {
        invoke(target, amount, input, operation, gasLimit);
        assembly {
            let ptr := mload(64)
            returndatacopy(ptr, 0, returndatasize())
            revert(ptr, returndatasize())
        }
    }

    function twice(address first, address second, uint256 amount, bytes memory input,
                   Operation operation, uint256 gasLimit) public returns (bool success, uint256 size) {
        invoke(first, amount, input, operation, gasLimit);
        success = invoke(second, amount, input, operation, gasLimit);
        assembly { size := returndatasize() }
    }

    function unused(Operation) internal pure returns(uint256) { return 7; }
    function converted(Operation mode) internal pure returns(uint256) { return uint256(mode); }
    function ignore(Operation mode) public pure returns(uint256) { return unused(mode); }
    function castHelper(Operation mode) public pure returns(uint256) { return converted(mode); }

    function compare(Operation a, Operation b) public pure returns (bool, bool, bool, bool, bool, bool) {
        return (a == b, a != b, a < b, a <= b, a > b, a >= b);
    }
}
