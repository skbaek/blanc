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
- [WethCode.lean](Blanc/WethCode.lean): the compiled WETH runtime bytecode and
  the witness that Blanc's compiler emits it. Generated in full by
  [`scripts/gen-weth-code.lean`](scripts/gen-weth-code.lean) — do not edit by
  hand.
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
**axiom audit** ([`scripts/AxiomCheck.lean`](scripts/AxiomCheck.lean)) of eight
top theorems. Seven are the headline solvency theorems:

- `Blanc.weth_preserves_solvent`
- `Blanc.stateTransition_preserves_solvent`
- `Blanc.chain_preserves_solvent`
- `Blanc.addBlockToChain_preserves_solvent`
- `Blanc.stateTransitionUsing_preserves_solvent`
- `Blanc.chainUsing_preserves_solvent`
- `Blanc.addBlockToChainUsing_preserves_solvent`

The eighth is the **compile witness**:

- `Blanc.wethCode_compile` — `Prog.compile weth = some wethCode`. All seven
  theorems above are conditioned on the WETH account's code being what
  `Prog.compile weth` returns, so without this equation they could all hold
  vacuously; the witness states that the compiler really does emit the
  866-byte [`wethCode`](Blanc/WethCode.lean) for `weth`. It is proved by
  `decide +kernel` — kernel evaluation of the same reduction, no raised
  elaboration limit and nothing added to the trusted base (in particular, not
  `native_decide`).

Each audited theorem carries its **own pinned expected axiom set** in
`scripts/check.sh`, and the audit fails if a theorem's axiom closure differs
from its pin in either direction — extra or missing. In particular it fails on
`sorryAx`, `ofReduceBool`, or `ofReduceNat` — no `sorry` and no
`native_decide`-style axiom in the trusted path of these results. It also fails
if `AxiomCheck.lean` and `check.sh` disagree about which theorems are audited,
so a row cannot be dropped silently from either side. All eight rows currently
pin exactly `[propext, Classical.choice, Quot.sound]`.

