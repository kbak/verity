// SPDX-License-Identifier: MIT
pragma solidity 0.7.6;

contract LegacyWordArithmetic {
    function assemblyWords(uint256 a, uint256 b, uint256 m)
        external pure returns (uint256 residue, uint256 ceiling, uint256 borrow)
    {
        assembly {
            residue := mulmod(a, b, m)
            ceiling := add(div(a, b), gt(mod(a, b), 0))
            borrow := lt(not(a), b)
        }
    }
}
