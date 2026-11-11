// SPDX-License-Identifier: MIT
pragma solidity 0.7.6;

contract LegacyPostCallEvents {
    uint256 public serial;
    enum Operation { Call, DelegateCall }
    event Starting(address indexed sender, uint256 serial);
    event Outcome(address indexed target, bool success, uint256 size);

    function invoke(address target, uint256 amount, bytes memory input,
                    Operation operation, uint256 gasLimit) internal returns (bool success) {
        if (operation == Operation.DelegateCall) {
            assembly { success := delegatecall(gasLimit,target,add(input,32),mload(input),0,0) }
        } else {
            assembly { success := call(gasLimit,target,amount,add(input,32),mload(input),0,0) }
        }
    }
    function run(address target, address next, uint256 amount, bytes memory input,
                 Operation operation, uint256 gasLimit, uint256 mode)
                 public payable returns (bool success, uint256 size) {
        serial += 1;
        emit Starting(msg.sender, serial);
        success = invoke(target, amount, input, operation, gasLimit);
        assembly { size := returndatasize() }
        emit Outcome(target, success, size);
        if (mode == 1) {
            success = invoke(next, amount, input, operation, gasLimit);
            assembly { size := returndatasize() }
            emit Outcome(next, success, size);
        }
        require(mode != 2, "LATE");
        if (mode == 3) {
            assembly { let p := mload(64) returndatacopy(p,0,returndatasize()) revert(p,returndatasize()) }
        }
    }
    function lateInvalid(address target, bytes memory input, Operation checked, uint256 gasLimit)
                         public payable returns (uint256) {
        serial += 1;
        emit Starting(msg.sender, serial);
        bool success = invoke(target, 0, input, Operation.Call, gasLimit);
        emit Outcome(target, success, 0);
        return uint256(checked);
    }
}
