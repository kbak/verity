// SPDX-License-Identifier: MIT
pragma solidity 0.7.6;

interface IWordSource {
    function read(address account) external view returns (uint256);
}

contract LegacyStaticWord {
    function word(address target, address account) public view returns (uint256) {
        (bool success, bytes memory data) = target.staticcall(
            abi.encodeWithSelector(IWordSource.read.selector, account));
        require(success && data.length >= 32);
        return abi.decode(data, (uint256));
    }

    function selfWord(address target) external view returns (uint256) {
        return word(target, address(this));
    }

    function twice(address first, address second, address account)
        external view returns (uint256, uint256)
    {
        uint256 a = word(first, account);
        uint256 b = word(second, account);
        return (a, b);
    }

    function inspect(address target, address account)
        external view returns (bool success, uint256 size, uint256 pointer, uint256 free)
    {
        bytes memory input = abi.encodeWithSelector(IWordSource.read.selector, account);
        bytes memory data;
        (bool ok, bytes memory returned) = target.staticcall(input);
        data = returned;
        assembly { pointer := data free := mload(0x40) }
        return (ok, data.length, pointer, free);
    }

    function decoded(address target, address account) external view returns (uint256) {
        (bool success, bytes memory data) = target.staticcall(
            abi.encodeWithSelector(IWordSource.read.selector, account));
        require(success);
        return abi.decode(data, (uint256));
    }

    function inspectPair(address first, address second, address account)
        external view returns (bool, bool, uint256, uint256)
    {
        (bool a, bytes memory x) = first.staticcall(
            abi.encodeWithSelector(IWordSource.read.selector, account));
        (bool b, bytes memory y) = second.staticcall(
            abi.encodeWithSelector(IWordSource.read.selector, account));
        return (a, b, x.length, y.length);
    }

    function atLeast(address target, address account, uint256 minimum)
        external view returns (bool)
    {
        uint256 observed = word(target, account);
        require(observed >= minimum, "insufficient");
        return true;
    }
}
