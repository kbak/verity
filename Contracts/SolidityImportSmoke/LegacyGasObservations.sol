// SPDX-License-Identifier: MIT
pragma solidity 0.7.6;

contract LegacyGasObservations {
    using GasMaximum for uint256;
    uint256 public nonce;
    enum Operation { Call, Delegatecall }

    function observe() external view returns (uint256) { return gasleft(); }

    function ordered(bool choose) external view returns (uint256 first, uint256 second) {
        first = gasleft();
        if (choose) second = gasleft();
        else second = first;
    }

    function guarded(uint256 requested) external view returns (uint256) {
        require(gasleft() >= ((requested << 6) / 63).maximum(requested + 2500) + 500, "budget");
        return gasleft();
    }

    function run(address target, uint256 amount, uint256 requested, bytes memory data,
        bool delegated, bool allGas, bool failAfter)
        external returns (uint256 beforeGas, uint256 afterGas, bool success) {
        nonce++;
        beforeGas = gasleft();
        uint256 allowance = allGas ? gasleft() - 2500 : requested;
        if (delegated) {
            assembly { success := delegatecall(allowance, target, add(data, 32), mload(data), 0, 0) }
        } else {
            assembly { success := call(allowance, target, amount, add(data, 32), mload(data), 0, 0) }
        }
        afterGas = gasleft();
        if (!success && requested == 0 && allGas) {
            assembly {
                let p := mload(64)
                returndatacopy(p, 0, returndatasize())
                revert(p, returndatasize())
            }
        }
        require(!failAfter, "outer");
    }

    function assemblyGas(address target) external returns (uint256 beforeGas, bool success) {
        assembly {
            beforeGas := gas()
            success := call(sub(gas(), 2500), target, 0, 0, 0, 0, 0)
        }
    }

    function perform(address target, uint256 allowance) internal returns (bool success) {
        assembly { success := call(allowance, target, 0, 0, 0, 0, 0) }
    }

    function forward(address target, uint256 requested, bool allGas)
        external returns (bool success, uint256 beforeGas, uint256 afterGas) {
        beforeGas = gasleft();
        success = perform(target, allGas ? gasleft() - 2500 : requested);
        afterGas = gasleft();
    }

    function performData(address target, bytes memory data, Operation operation, uint256 allowance)
        internal returns (bool success) {
        if (operation == Operation.Call) {
            assembly { success := call(allowance, target, 0, add(data, 32), mload(data), 0, 0) }
        } else {
            assembly { success := delegatecall(allowance, target, add(data, 32), mload(data), 0, 0) }
        }
    }

    function forwardData(address target, bytes calldata data, Operation operation,
        uint256 requested, bool allGas)
        external returns (bool success, uint256 beforeGas, uint256 afterGas) {
        beforeGas = gasleft();
        success = performData(target, data, operation, allGas ? gasleft() - 2500 : requested);
        afterGas = gasleft();
    }

    function twice(address target) external returns (bool first, bool second) {
        first = perform(target, gasleft() - 2500);
        second = perform(target, gasleft() - 2500);
    }
}

library GasMaximum {
    function maximum(uint256 a, uint256 b) internal pure returns (uint256) {
        return a > b ? a : b;
    }
}
