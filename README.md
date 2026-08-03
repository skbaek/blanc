# Blanc: A Minimal EVM Programming Language for Interactive Verification

[![CI](https://github.com/skbaek/blanc/actions/workflows/ci.yml/badge.svg)](https://github.com/skbaek/blanc/actions/workflows/ci.yml)

Blanc is an EVM programming language optimized for formal verification 
with interactive theorem provers. Blanc's toolchain is implemented in Lean 4.
This repo contains the following files:

- [Basic.lean](Blanc/Basic.lean): Blanc's own prefix/split algebra over lists
  (`Split`, `Pref`, `Frel`) and the small tactic helpers built on it. The
  generic list, word and `Except`/`Option` lemmas that used to live here are
  now upstream in Jaune, where any client of Jaune gets them.
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

Blanc's WETH is a reimplementation; observable deviations from deployed WETH9
are catalogued in [`WETH_DEVIATIONS.md`](WETH_DEVIATIONS.md).

Every module is wrapped in `namespace Blanc`, and Blanc's Jaune imports are
wrapped in `namespace Jaune`, so downstream code writes qualified names or
opens the namespace explicitly.

## Verification status

**What you are trusting.** Blanc's trusted base is Jaune's plus three
additions, so the base document is Jaune's
[`TRUSTED.md`](https://github.com/skbaek/jaune/blob/main/TRUSTED.md) — the
kernel and pins, what is deliberately absent from the library and which gate
enforces each absence, the known exceptions, and where the line between testing
and proof falls. It is not duplicated here. Blanc adds exactly:

1. **the pinned Jaune revision** below — trusting a Blanc theorem is trusting
   that specific Jaune, not the sibling checkout on your disk;
2. **the axiom audit** below, which is stricter than Jaune's own gates: it
   pins the exact axiom set of eight named results and fails on an extra *or*
   missing axiom;
3. **Blanc's own source**, which carries no gate equivalent to Jaune's
   `check-hygiene.sh`/`check-integrity.sh`; what stands behind it is the audit
   in (2), and the audit constrains only what enters those eight theorems'
   dependency cones. Scanning `Blanc/` finds no `@[extern]`, `axiom`,
   `opaque`, `sorry`, `implemented_by`, or `bv_decide`, and no use of
   `native_decide` — its one textual occurrence is the `WethCode.lean` comment
   saying the compile witness is deliberately *not* proved that way. The three
   `partial def`s and eight `dbg_trace`s are all in
   [`Blanc/Tactics.lean`](Blanc/Tactics.lean), inside `TacticM`
   proof-automation procedures rather than object-level definitions: a
   non-terminating or chatty tactic can fail to produce a proof, but any proof
   it does produce is still checked by the kernel, so none of them is in the
   trusted base.

As in Jaune's document, this section is about whether the proofs are sound, not
about whether they are the right theorems. Read the statements in
[`Blanc/Solvent.lean`](Blanc/Solvent.lean) rather than inferring them from a
theorem's name.

Blanc builds against a **pinned revision** of
[Jaune](https://github.com/skbaek/jaune) — `require jaune from git … @ 4e6a6555…`
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

## WETH fixture suite — execution evidence

The audit above proves things *about* `wethCode`'s bytes; it never runs them.
[`scripts/check-weth.sh`](scripts/check-weth.sh) closes that gap: it runs
eleven committed fixtures ([`scripts/fixtures/weth/`](scripts/fixtures/weth/),
generated by [`scripts/gen-weth-fixtures.py`](scripts/gen-weth-fixtures.py))
through [Jaune](https://github.com/skbaek/jaune)'s fixture runner, each with
`Blanc.wethCode` as the WETH account's code and every expectation filled by
the pinned frozen EELS oracle's `t8n`: the five happy paths (deposit,
withdraw, transfer, approve+transferFrom, and an adversarial reentrancy
attempt against `withdraw`), two view-function probes that make the
hand-rolled ABI return encoding externally observable, the balance and
allowance guards refusing, and the two `WETH_DEVIATIONS.md` claims that are
testable at all. This is external adjudication: Jaune and the frozen oracle
agreeing on what the exact bytes the compile witness is about actually do,
including that the reentrancy attempt does not double-spend and that every
guard fires rather than the suite passing for a contract that refuses
nothing.

The generator also computes each case's WETH-semantic expectation from the
pre-state and the transaction alone and asserts it against the oracle's
answer before writing the fixture — agreement between Jaune and the oracle
alone cannot see a contract that is wrong the same way to everyone — and a
[selector coverage gate](scripts/check-weth-coverage.sh) obtains Blanc's own
ten selectors from `wethFuncs` and confirms all ten, plus the fallback, are
exercised, against a shrink-only budget currently empty. See [the fixtures
README](scripts/fixtures/weth/README.md#what-the-suite-establishes) for what
this is worth and what it is not: specification-checked differential testing
on chosen inputs, not a liveness proof — the eight audited theorems above
remain pure safety statements.

It is a local gate (CI does not get the Jaune executable for free from the
dependency build, so CI runs `lake build jaune/jaune` before it), and both it
and the coverage gate are wired into
[`.github/workflows/ci.yml`](.github/workflows/ci.yml).
