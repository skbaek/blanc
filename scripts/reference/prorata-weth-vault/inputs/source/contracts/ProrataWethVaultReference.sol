// SPDX-License-Identifier: MIT
pragma solidity 0.8.36;

import {IERC20} from "openzeppelin-contracts/contracts/token/ERC20/IERC20.sol";
import {ERC20} from "openzeppelin-contracts/contracts/token/ERC20/ERC20.sol";
import {ERC4626} from "openzeppelin-contracts/contracts/token/ERC20/extensions/ERC4626.sol";

contract ProrataWethVaultReference is ERC4626 {
    constructor(IERC20 asset_)
        ERC20("PRORATA WETH Vault", "prWETH")
        ERC4626(asset_)
    {}

    function _decimalsOffset() internal pure override returns (uint8) {
        return 3;
    }
}
