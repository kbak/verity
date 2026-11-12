// SPDX-License-Identifier: MIT
pragma solidity 0.7.6;

interface IImmutableWordSource {
    function read(address account) external view returns (uint256);
}

abstract contract ImmutableOrigin {
    address private immutable original;
    uint256 private immutable shared;
    constructor() { original = address(this); shared = 17; }
    function origin() public view returns (address) { return original; }
    function baseValue() public view returns (uint256) { return shared; }
    modifier directOnly() { require(address(this) == original, "delegate"); _; }
}

contract DeployedImmutables is ImmutableOrigin {
    address public immutable target;
    uint24 public immutable narrow;
    uint128 public immutable wide;
    bytes4 public immutable tag;
    bool public immutable enabled;
    int24 public immutable signedUnused;
    uint256 public immutable fixedValue = 91;
    uint256 private immutable shared;
    constructor(address t, uint24 n, uint128 w, bytes4 b, bool e, int24 s) {
        target = t; narrow = n; wide = w; tag = b; enabled = e; signedUnused = s;
        shared = 29;
    }
    function ownValue() external view returns (uint256) { return shared; }
    function current() external view returns (address) { return address(this); }
    function guarded() external view directOnly returns (uint256) { return narrow; }
    function query() private view returns (uint256) {
        (bool ok, bytes memory data) = target.staticcall(
            abi.encodeWithSelector(IImmutableWordSource.read.selector, address(this)));
        require(ok && data.length >= 32);
        return abi.decode(data, (uint256));
    }
    function readTarget() external view returns (uint256) { return query(); }
}

contract ImmutableDelegateProxy {
    address private immutable implementation;
    constructor(address code) { implementation = code; }
    fallback() external {
        address code = implementation;
        assembly {
            calldatacopy(0, 0, calldatasize())
            let ok := delegatecall(gas(), code, 0, calldatasize(), 0, 0)
            returndatacopy(0, 0, returndatasize())
            if iszero(ok) { revert(0, returndatasize()) }
            return(0, returndatasize())
        }
    }
}
