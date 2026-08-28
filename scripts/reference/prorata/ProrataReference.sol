// SPDX-License-Identifier: CC0-1.0
pragma solidity 0.8.36;

/// Exact-surface shadow implementation of Blanc PRORATA for benchmarking.
/// It deliberately uses one payable fallback so short calldata is zero-padded,
/// trailing calldata is ignored, and caller shares occupy the raw caller slot.
contract ProrataReference {
    fallback() external payable {
        assembly {
            let sig := shr(224, calldataload(0))
            switch sig
            case 0xd0e30db0 {
                let a := callvalue()
                if gt(a, 0xffffffffffffffffffffffff) { revert(0, 0) }
                let b := sub(selfbalance(), a)
                if gt(b, 0x3fffffffffffffffffffffffffffffff) { revert(0, 0) }
                let supplySlot := not(0)
                let s := sload(supplySlot)
                let m := div(mul(a, add(s, 1000)), add(b, 1))
                let next := add(s, m)
                if gt(next, 0x3fffffffffffffffffffffffffffffff) { revert(0, 0) }
                sstore(supplySlot, next)
                sstore(caller(), add(sload(caller()), m))
                mstore(0, m)
                return(0, 32)
            }
            case 0x2e1a7d4d {
                if callvalue() { revert(0, 0) }
                let shares := calldataload(4)
                let owner := caller()
                let owned := sload(owner)
                if lt(owned, shares) { revert(0, 0) }
                sstore(owner, sub(owned, shares))
                let b := selfbalance()
                if gt(b, 0x3fffffffffffffffffffffffffffffff) { revert(0, 0) }
                let supplySlot := not(0)
                let s := sload(supplySlot)
                let payout := div(mul(shares, add(b, 1)), add(s, 1000))
                sstore(supplySlot, sub(s, shares))
                if iszero(call(gas(), owner, payout, 0, 0, 0, 0)) { revert(0, 0) }
                mstore(0, payout)
                return(0, 32)
            }
            case 0xc6e6f592 {
                if callvalue() { revert(0, 0) }
                let assets := calldataload(4)
                if gt(assets, 0xffffffffffffffffffffffff) { revert(0, 0) }
                let b := selfbalance()
                if gt(b, 0x3fffffffffffffffffffffffffffffff) { revert(0, 0) }
                let s := sload(not(0))
                let minted := div(mul(assets, add(s, 1000)), add(b, 1))
                if gt(add(s, minted), 0x3fffffffffffffffffffffffffffffff) { revert(0, 0) }
                mstore(0, minted)
                return(0, 32)
            }
            case 0x07a2d13a {
                if callvalue() { revert(0, 0) }
                let shares := calldataload(4)
                if gt(shares, 0x3fffffffffffffffffffffffffffffff) { revert(0, 0) }
                let b := selfbalance()
                if gt(b, 0x3fffffffffffffffffffffffffffffff) { revert(0, 0) }
                let payout := div(mul(shares, add(b, 1)), add(sload(not(0)), 1000))
                mstore(0, payout)
                return(0, 32)
            }
            default {
                if calldatasize() { revert(0, 0) }
                stop()
            }
        }
    }
}
