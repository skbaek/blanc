# Blanc: A Minimal EVM Programming Language for Interactive Verification

[![CI](https://github.com/skbaek/blanc/actions/workflows/ci.yml/badge.svg)](https://github.com/skbaek/blanc/actions/workflows/ci.yml)

Blanc is an EVM programming language optimized for formal verification 
with interactive theorem provers. Blanc's toolchain is implemented in Lean 4.
This repo contains the following files:

- [Basic.lean](Blanc/Basic.lean): generic definitions and lemmas (for Booleans, 
  lists, bit vectors, bytes, etc.) useful for but not specific to Blanc.
- [Semantics.lean](Blanc/Semantics.lean): formalized semantics of EVM and Blanc.
- [Common.lean](Blanc/Common.lean): definitions and lemmas for writing and 
  verifying Blanc programs, including the Blanc compiler's correctness proof and 
  tactics for automating Blanc program verification. 
- [Weth.lean](Blanc/Weth.lean): proof-of-concept implementation of the Wrapped 
  Ether (WETH) contract in Blanc.
- [Solvent.lean](Blanc/Solvent.lean): proof of solvency for the WETH implementation.

## Verification status

Blanc builds against a **pinned revision** of
[ELEVM](https://github.com/skbaek/elevm) — `require elevm from git … @ 1facd137…`
in [`lakefile.lean`](lakefile.lean) — so a fresh clone builds reproducibly
without a sibling checkout, and bumping ELEVM is a reviewed one-line change.

CI ([`scripts/check.sh`](scripts/check.sh)) builds the library and then runs an
**axiom audit** ([`scripts/AxiomCheck.lean`](scripts/AxiomCheck.lean)) of the
four headline solvency theorems:

- `weth_inv_solvent`
- `stateTransition_inv_solvent`
- `chain_inv_solvent`
- `addBlockToChain_inv_solvent`

The audit fails if any of them depends on `sorryAx`, `ofReduceBool`, or
`ofReduceNat` — i.e. no `sorry` and no `native_decide`-style axiom in the
trusted path of these results.


