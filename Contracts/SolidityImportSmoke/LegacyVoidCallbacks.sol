// SPDX-License-Identifier: MIT
pragma solidity 0.7.6;

enum Operation { Call, DelegateCall }
interface IVoidCallback {
    function beforeCall(address target, uint256 amount, bytes memory input, Operation operation,
                        uint256 mode, uint256 base, uint256 price, address token,
                        address payable receiver, bytes memory auxiliary, address sender) external;
    function afterCall(bytes32 serial, bool success) external;
}
contract LegacyVoidCallbacks {
    uint256 public serial;
    uint256 private callbackWord;
    bytes32 private constant CALLBACK_SLOT = 0x0000000000000000000000000000000000000000000000000000000000000001;
    event Starting(address indexed sender, uint256 serial);
    event Outcome(address indexed target, bool success, uint256 size);

    function configure(uint256 word) public { callbackWord = word; }
    function readCallback() public view returns (address callback) {
        assembly { callback := sload(CALLBACK_SLOT) }
    }
    function invoke(address target, uint256 amount, bytes memory input,
                    Operation operation, uint256 gasLimit) internal returns (bool success) {
        if (operation == Operation.DelegateCall) {
            assembly { success := delegatecall(gasLimit,target,add(input,32),mload(input),0,0) }
        } else {
            assembly { success := call(gasLimit,target,amount,add(input,32),mload(input),0,0) }
        }
    }
    function run(address target, uint256 amount, bytes memory input, Operation operation,
                 bytes memory auxiliary, uint256 mode) public payable returns (bool success) {
        address callback = readCallback();
        serial += 1;
        bytes32 token = bytes32(serial);
        emit Starting(msg.sender, serial);
        if (callback != address(0)) {
            IVoidCallback(callback).beforeCall(target,amount,input,operation,mode,uint256(7),uint256(8),address(0),address(0),auxiliary,msg.sender);
        }
        success = invoke(target, amount, input, operation, 1000000);
        emit Outcome(target, success, 0);
        if (callback != address(0)) {
            IVoidCallback(callback).afterCall(token,success);
        }
    }
    function notify(address callback, bytes calldata input, bytes calldata auxiliary,
                    Operation operation, uint256 mode) external {
        IVoidCallback(callback).beforeCall(callback,mode,input,operation,mode,uint256(7),uint256(8),address(0),address(0),auxiliary,msg.sender);
    }
    function aliasBuffers(address callback, bytes memory input, bytes memory auxiliary,
                          Operation operation, uint256 shift, uint256 mode) public {
        assembly { auxiliary := add(input,shift) }
        IVoidCallback(callback).beforeCall(callback,mode,input,operation,mode,uint256(7),uint256(8),address(0),address(0),auxiliary,msg.sender);
    }

    function headAlias(address callback, bytes memory input, bytes memory auxiliary,
                       Operation operation, uint256 mode) public {
        assembly { input := add(mload(64),164) }
        IVoidCallback(callback).beforeCall(callback,mode,input,operation,mode,uint256(7),uint256(8),address(0),address(0),auxiliary,msg.sender);
    }

    function lengthAlias(address callback, bytes memory input, bytes memory auxiliary,
                         Operation operation, uint256 mode) public {
        assembly { let p := mload(64) mstore(add(p,357),1) }
        assembly { input := add(mload(64),357) }
        IVoidCallback(callback).beforeCall(callback,mode,input,operation,mode,uint256(7),uint256(8),address(0),address(0),auxiliary,msg.sender);
    }

    function mixed(address callback, bytes calldata input, bytes memory auxiliary,
                   Operation operation, uint256 mode) external {
        IVoidCallback(callback).beforeCall(callback,mode,input,operation,mode,uint256(7),uint256(8),address(0),address(0),auxiliary,msg.sender);
    }

}
