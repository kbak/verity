// SPDX-License-Identifier: MIT
pragma solidity 0.7.6;

contract LegacyPayable {
    uint256 public total;
    enum Operation { Call, DelegateCall }
    event Paid(address indexed sender, uint256 amount, uint256 tag);

    function readValue() internal view returns (uint256) { return msg.value; }
    function deposit(uint256 tag) public payable returns (uint256, uint256, uint256, uint256) {
        total += msg.value;
        emit Paid(msg.sender, msg.value, tag);
        return (msg.value, address(this).balance, total, readValue());
    }
    function guarded(uint256 tag) public payable {
        total += msg.value;
        emit Paid(msg.sender, msg.value, tag);
        require(tag != 0, "PAY");
    }
    function nonpayable(uint256 tag) public returns (uint256) { total += tag; return total; }
    function enumUse(Operation mode) public payable returns (uint256) { return uint256(mode); }
    function invoke(address target, uint256 amount, bytes memory input,
                    Operation operation, uint256 gasLimit) internal returns (bool success) {
        if (operation == Operation.DelegateCall) {
            assembly { success := delegatecall(gasLimit,target,add(input,32),mload(input),0,0) }
        } else {
            assembly { success := call(gasLimit,target,amount,add(input,32),mload(input),0,0) }
        }
    }
    function run(address target, uint256 amount, bytes memory input,
                 Operation operation, uint256 gasLimit) public payable returns (bool success, uint256 size) {
        success = invoke(target, amount, input, operation, gasLimit);
        assembly { size := returndatasize() }
    }
    function forward(address target, uint256 amount, bytes memory input,
                     Operation operation, uint256 gasLimit) public payable {
        invoke(target, amount, input, operation, gasLimit);
        assembly { let p := mload(64) returndatacopy(p,0,returndatasize()) revert(p,returndatasize()) }
    }
}

contract LegacyPayableStateless {
    function accept(uint256 tag) public payable returns (uint256, uint256, uint256) {
        return (msg.value, address(this).balance, tag);
    }
    function reject(uint256 tag) public payable { require(tag != 0, "PAY"); }
    function nonpayable(uint256 tag) public pure returns (uint256) { return tag; }
}
