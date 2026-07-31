# Blanc: A Minimal EVM Programming Language for Interactive Verification

[![CI](https://github.com/skbaek/blanc/actions/workflows/ci.yml/badge.svg)](https://github.com/skbaek/blanc/actions/workflows/ci.yml)

Blanc is an EVM programming language optimized for formal verification 
with interactive theorem provers. Blanc's toolchain is implemented in Lean 4.
This repo contains the following files:

- [Basic.lean](Blanc/Basic.lean): generic definitions and lemmas (for Booleans, 
  lists, bit vectors, bytes, etc.) useful for but not specific to Blanc.
- [Semantics.lean](Blanc/Semantics.lean): formalized semantics of EVM and Blanc.
- [CommonCore.lean](Blanc/CommonCore.lean), [Tactics.lean](Blanc/Tactics.lean),
  and [CommonProofs.lean](Blanc/CommonProofs.lean): definitions and lemmas for
  writing and verifying Blanc programs, including the Blanc compiler's
  correctness proof and tactics for automating Blanc program verification.
  They import in that order.
- [Weth.lean](Blanc/Weth.lean): proof-of-concept implementation of the Wrapped 
  Ether (WETH) contract in Blanc.
- [Solvent.lean](Blanc/Solvent.lean): proof of solvency for the WETH implementation.

Every module is wrapped in `namespace Blanc`, and Blanc's Jaune imports are
wrapped in `namespace Jaune`, so downstream code writes qualified names or
opens the namespace explicitly.

## Verification status

Blanc builds against a **pinned revision** of
[Jaune](https://github.com/skbaek/jaune) — `require jaune from git … @ 739fa42d…`
in [`lakefile.lean`](lakefile.lean) — so a fresh clone builds reproducibly
without a sibling checkout, and bumping Jaune is a reviewed one-line change.

CI ([`scripts/check.sh`](scripts/check.sh)) builds the library and then runs an
**axiom audit** ([`scripts/AxiomCheck.lean`](scripts/AxiomCheck.lean)) of the
five headline solvency theorems:

- `Blanc.weth_preserves_solvent`
- `Blanc.stateTransition_preserves_solvent`
- `Blanc.chain_preserves_solvent`
- `Blanc.addBlockToChain_preserves_solvent`
- `Blanc.stateTransitionUsing_preserves_solvent`

The audit fails if any of them depends on `sorryAx`, `ofReduceBool`, or
`ofReduceNat` — i.e. no `sorry` and no `native_decide`-style axiom in the
trusted path of these results.


