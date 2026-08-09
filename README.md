# Blanc: A Minimal EVM Programming Language for Interactive Verification

[![CI](https://github.com/skbaek/blanc/actions/workflows/ci.yml/badge.svg)](https://github.com/skbaek/blanc/actions/workflows/ci.yml)

Blanc is an EVM programming language optimized for formal verification 
with interactive theorem provers. Blanc's toolchain is implemented in Lean 4.

When a Blanc contract reimplements an existing one, what that port does and
does not claim — and the deviation-registry discipline that backs it — is
governed by [PORTING.md](PORTING.md).

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
- [Ladder.lean](Blanc/Ladder.lean): the contract-generic verification ladder,
  including the `ContractSpec` record each contract instantiates and the
  dispatcher decomposition (`FuncSound`, `sound_of_dispatch`) that reduces a
  whole-contract obligation to one obligation per dispatch target.
- [Compiled.lean](Blanc/Compiled.lean): a gas-exact sibling of `Func.Run`/
  `Prog.Run` — `Func.RunCompiled`, `Prog.RunCompiled` — and
  `Prog.runCompiled_iff_exec`, the biconditional relating a gas-exact run of a
  compiled pc-free program to a successful Jaune execution of its code at pc 0,
  in both directions. It imports only `CommonCore.lean`, and the one module
  that imports it is `Forward.lean` below. It was a leaf until that module
  arrived; what the leaf sentence existed to guarantee is unchanged, and is
  the part to hold onto: `Func.Run`, `Prog.Run`, `correct` and `correct_core`
  are untouched by its existence, and by `Forward.lean`'s.
  **This is not liveness.** The biconditional
  converts run witnesses into executions and back; it does not produce a run
  witness for any contract, and nothing in this module says any contract call
  ever succeeds — the first theorems that do are `FmintLive.lean`'s and
  `WethLive.lean`'s below. At every external call the witness
  *contains* the callee's execution as a premise, so for a contract with an
  external call every consequence stays conditional on callee behaviour. It
  also says nothing about transaction-level execution (intrinsic gas, the
  63/64 rule and transaction validity are a further layer) and is `.ok`-level
  only: contraposition yields "no successful execution", never "the EVM
  reverts with *this* error".
- [Forward.lean](Blanc/Forward.lean): the dual of `Tactics.lean`. Where that
  file is entirely inversion — every tactic in it matches a run in *antecedent*
  position — this one is goal-directed: given a state and the instruction that
  runs on it, it produces `Func.RunCompiled`'s premise with the successor state
  written out, so a chain of these **constructs** a derivation instead of
  taking one apart. Composed through `Prog.exec_of_runCompiled`, that chain is
  a successful `Exec`. Shared and contract-agnostic; a demonstration belongs in
  a contract-owned module, since a shared module importing a contract is the
  inverted import `scripts/check-layering.sh` rejects. It also carries
  `func_run`, the tactic that is `Tactics.lean`'s `func_inv` read backwards: it
  walks the same `Func` structure and *applies* `Func.RunCompiled`'s rules,
  naming every intermediate state and gas account itself and handing back only
  the obligations no construction can compute — which comparison a dispatch
  fork decided, what a memory expansion cost, and the frame's terminal
  instruction.
- [Reverts.lean](Blanc/Reverts.lean): the error-carrying sibling of
  `Compiled.lean`. `Func.RunCompiledTo` generalises `Func.RunCompiled`'s
  terminal outcome from `.ok` to an arbitrary `Execution`, with the bridge to
  `exec` to match — the layer that lets a statement end in a *named* error
  instead of contraposition's "no successful execution exists".
- [ForwardCall.lean](Blanc/ForwardCall.lean): crossing a `CALL`, forward — the
  one instruction `Forward.lean` cannot step, because its outcome spawns a
  child frame. The child's execution comes from totality — Jaune's `exec` is
  total and fuel-free — never from a premise about the callee, which is what
  lets the settlement family below quantify over arbitrary borrower bytecode.
  The module also carries the EIP-150 retained-gas lower bound and the
  fatal/failed/successful split of child resumption.
- [FmintLive.lean](Blanc/FmintLive.lean): fmint's demonstration of that layer,
  and the first place in this repository where a contract call is proved to
  **succeed**. `fmint_totalSupply_succeeds` drives `func_run` over `fmint`'s
  compiled `Func` to build the run witness for a `totalSupply()` call, and
  composes it through `Prog.exec_of_runCompiled`. Six of the seven hints the
  walk takes are what the dispatch comparisons decided; everything else — the
  twenty-two instruction steps, the state chain, and every gas and headroom side
  condition — is derived. It costs 2218 gas, exactly, of which
  `gasColdSload`'s 2100 is the storage read. Read the scope off the docstring:
  it is one call-free entrypoint of one contract, at message-call altitude
  rather than transaction level, for one fixed selector, with an exact gas
  figure rather than a bound. No entrypoint that makes an external call can
  have a statement of this shape — its witness contains the callee's execution
  as a premise, which is arbitrary and, for a flash loan, adversarial.
- [WethLive.lean](Blanc/WethLive.lean): WETH's demonstration of the same layer,
  and the evidence that it is not target-specific. `weth_balanceOf_succeeds`
  drives the same `func_run` over `weth`'s compiled `Func` for a
  `balanceOf(guy)` call, at 2260 gas exactly — 19 of them the shared
  `nonpayable` entry guard every recognized WETH selector now sits behind,
  which is also why the statement carries a zero-call-value hypothesis. It
  differs from fmint's
  demonstration where it matters: the storage key is read from calldata rather
  than being a constant, so the statement is quantified over the argument word
  and WETH's lack of address validation is visible in it; and `wethTree` puts
  the target four dispatch forks down instead of three. Nothing had to be added
  to `Forward.lean` for it — the whole module is the target's own text. Its
  scope caveats are `FmintLive.lean`'s, unchanged.
- [FmintGas.lean](Blanc/FmintGas.lean) and [WethGas.lean](Blanc/WethGas.lean):
  what those calls *cost* — the same runs restated with exact cold and warm
  gas as a conjunct of the statement, plus the `fmintGas`/`wethGas` closed
  forms and their maxima. `WethGas.lean`'s module docstring carries the
  rationale; `FmintGas.lean` mirrors it.
- [Weth.lean](Blanc/Weth.lean): proof-of-concept implementation of the Wrapped 
  Ether (WETH) contract in Blanc.
- [WethCode.lean](Blanc/WethCode.lean): the compiled WETH runtime bytecode and
  the witness that Blanc's compiler emits it. Generated in full by
  [`scripts/gen-weth-code.lean`](scripts/gen-weth-code.lean) — do not edit by
  hand.
- [Solvent.lean](Blanc/Solvent.lean): proof of solvency for the WETH implementation.
- [Fmint.lean](Blanc/Fmint.lean): implementation of an ERC-3156 flash-mint
  token (FMINT) in Blanc — the second contract, and the one that makes the
  hierarchy rule below load-bearing.
- [FmintCode.lean](Blanc/FmintCode.lean): the compiled FMINT runtime bytecode
  and its compile witness. Generated in full by
  [`scripts/gen-fmint-code.lean`](scripts/gen-fmint-code.lean) — do not edit by
  hand.
- [Conserved.lean](Blanc/Conserved.lean): proof of supply conservation for the
  FMINT implementation — `totalSupply = Σ balances` at every observable point,
  preserved by arbitrary executions, including the reentrant borrower code a
  flash loan hands control to. Conservation is an equality about storage: it is
  **not** solvency and not liveness, and during a flash loan the minted supply
  is unbacked by construction — that is the design, and the claim is that the
  books balance at every point an observer can reach.
- [FlashSpec.lean](Blanc/FlashSpec.lean): fmint's `flashLoan` specification —
  the entry route, the callback calldata image, `CallbackBoundary`, the
  headline `fmint_flashLoan_spec` with its seven `no_success_of_*`
  corollaries and their seven `settles_with_error_of_*` strengthenings, and
  the frame-level restoration family. Partial correctness throughout: every
  theorem takes a successful run as a hypothesis or rules one out, and each
  restoration claim names a frame, never a transaction.
- [FmintReverts.lean](Blanc/FmintReverts.lean): fmint's deliberate reverts,
  constructed rather than ruled out — the unknown-selector and
  `token ≠ self` executions built instruction by instruction to
  `.error (.revert, _)` with empty returndata: statements that a call
  *reverts*, with *this* error and *no* data, on the deployed bytes.
- [FmintSettles.lean](Blanc/FmintSettles.lean): the walk that runs
  `flashLoan`'s state-changing half — three guards passed, the mint written,
  the frame handed to the callback — and, across the `CALL`, the settlement
  trichotomy `fmint_flashLoan_settles` and its corollaries: with no premise
  about the borrower, a non-static canonical call funded at
  `flashLoanGas data.length` ends in a success, a deliberate revert, or the
  non-consensus fault channel — never a consensus exceptional halt.
- [Weth10.lean](Blanc/Weth10.lean) and
  [Weth10Code.lean](Blanc/Weth10Code.lean): the parameterized 27-selector plus
  payable-receive WETH10 runtime and its universal compiler witness. Concrete
  deployment parameters select one exact member of the 6,313-byte runtime
  family; the generated byte module also owns the fixed patch offsets and
  canonical mainnet artifact.
- [Weth10Sound.lean](Blanc/Weth10Sound.lean),
  [Weth10StateFunctional.lean](Blanc/Weth10StateFunctional.lean),
  [Weth10StateSound.lean](Blanc/Weth10StateSound.lean),
  [Weth10Functional.lean](Blanc/Weth10Functional.lean),
  [Weth10TransferFunctional.lean](Blanc/Weth10TransferFunctional.lean),
  [Weth10Erc677Functional.lean](Blanc/Weth10Erc677Functional.lean),
  [Weth10FlashFunctional.lean](Blanc/Weth10FlashFunctional.lean),
  [Weth10Permit.lean](Blanc/Weth10Permit.lean),
  [Weth10Read.lean](Blanc/Weth10Read.lean),
  [Weth10Live.lean](Blanc/Weth10Live.lean), and
  [Weth10Errors.lean](Blanc/Weth10Errors.lean): the backing, endpoint-effect,
  callback, permit, read, exact-gas, and rollback/error proof families for all
  27 selectors and receive.
- [Weth10DeployDomainSlices.lean](Blanc/Weth10DeployDomainSlices.lean),
  [Weth10DeployUpperSlices.lean](Blanc/Weth10DeployUpperSlices.lean),
  [Weth10Deploy.lean](Blanc/Weth10Deploy.lean),
  [Weth10DeployExec.lean](Blanc/Weth10DeployExec.lean), and
  [Weth10DeployProof.lean](Blanc/Weth10DeployProof.lean): fixed-width runtime
  span proofs, the separate generic constructor, exact runtime-parameter
  patching, phase-composed constructor execution, fresh-state invariant,
  creation-message settlement, and Blanc deployment-gas evidence.

Blanc's WETH is a reimplementation; observable deviations from deployed WETH9
are catalogued in [`WETH_DEVIATIONS.md`](WETH_DEVIATIONS.md). FMINT's
deviations from OpenZeppelin's `ERC20FlashMint` are catalogued in
[`FMINT_DEVIATIONS.md`](FMINT_DEVIATIONS.md). WETH10's implementation
freedoms, exclusions, deployed quirks, and current-main drift are catalogued in
[`WETH10_DEVIATIONS.md`](WETH10_DEVIATIONS.md); no true in-scope deviation is
accepted.

Every module is wrapped in `namespace Blanc`, and Blanc's Jaune imports are
wrapped in `namespace Jaune`, so downstream code writes qualified names or
opens the namespace explicitly.

## Module hierarchy: contracts are siblings

Each contract occupies a sibling module family: at minimum its program,
compiled bytes and property layer, and for a larger contract any additional
functional, error, gas, deployment or callback proof modules it needs.
**Every contract's modules sit at the same level of the import hierarchy as
every other's.** No contract's module imports another contract's, in either
direction, at any layer. This binds contracts not yet written exactly as it
binds WETH, FMINT and WETH10 here.

The rule earns its keep as a diagnostic. When one contract needs something
another already defines, that is not a licence to import across; it is evidence
that the thing was never the property of whichever contract happened to define
it first. Rename it if its name says otherwise, then move it upstream into a
layer both contracts already import — `CommonCore.lean` for definitions,
`CommonProofs.lean` for lemmas, `Ladder.lean` for generic verification
machinery.

`balSum` is the worked example. It began as `wbsum` — "weth balance sum" — in
`Solvent.lean`, both named and placed as though summing a contract's
address-keyed balances were a WETH notion. It is not: WETH pairs that sum with
its ETH balance to state solvency, FMINT pairs it with its supply slot to state
conservation, and neither use is prior to the other. So it moved to
`CommonCore.lean`, beside the `sum` it was already built from, and lost the
`w`. A future contract that finds itself reaching into `Weth.lean` or
`Solvent.lean` has found the same kind of factoring defect, not a shortcut.

The rule is enforced, not merely documented:
[`scripts/check-layering.sh`](scripts/check-layering.sh) parses the import
lines and fails on a cross-contract import, on a shared module importing a
contract (the same break, other direction), and on any module missing from its
classification — so a new contract cannot escape the rule by never being
listed. It needs no Lean toolchain and runs ahead of the build in CI.

## Verification status

**What you are trusting.** Blanc's trusted base is Jaune's plus three
additions, so the base document is Jaune's
[`TRUSTED.md`](https://github.com/skbaek/jaune/blob/main/TRUSTED.md) — the
kernel and pins, what is deliberately absent from the library and which gate
enforces each absence, the known exceptions, and where the line between testing
and proof falls. It is not duplicated here. Blanc adds exactly:

1. **the pinned Jaune revision** below — trusting a Blanc theorem is trusting
   that specific Jaune, not the sibling checkout on your disk;
2. **the axiom audit** below, which is stricter than Jaune's own gates: its
   current source inventory pins the exact axiom set of 275 named results—149
   in the WETH10/`Weth10Inv` family—and fails on an extra *or* missing axiom.
   Run `scripts/check.sh --no-build`; its `275/275` summary belongs to the
   source identity printed by `git rev-parse HEAD`;
3. **Blanc's own source**, guarded by
   [`scripts/check-trust-surface.sh`](scripts/check-trust-surface.sh). The gate
   traverses the exact transitive local import closure of `Blanc.lean` and
   fail-closed checks `sorry`, bespoke `axiom`, `opaque`, `@[extern]`,
   `implemented_by`, `native_decide`, object-level `partial def`, and
   `dbg_trace`. Its 21 current occurrences are exact reviewed rows: nine are
   comment-only explanations, five are `TacticM`/`MetaM` partial procedures,
   and seven are tactic diagnostics. Unimported Lean helpers and generators are
   outside this library-root gate; importing one immediately brings it into
   scope. A non-terminating or chatty tactic can fail to produce a proof, but
   any proof it does produce is still checked by the kernel, so none of these
   proof-automation rows enlarges the trusted base.

As in Jaune's document, this section is about whether the proofs are sound, not
about whether they are the right theorems. Read the statements in
[`Blanc/Solvent.lean`](Blanc/Solvent.lean) and
[`Blanc/Conserved.lean`](Blanc/Conserved.lean) rather than inferring them from
a theorem's name.

Blanc builds against a **pinned revision** of
[Jaune](https://github.com/skbaek/jaune) — `require jaune from git … @ 4e6a6555…`
in [`lakefile.lean`](lakefile.lean) — so a fresh clone builds reproducibly
without a sibling checkout, and bumping Jaune is a reviewed one-line change.

CI builds the library and runs an
**axiom audit** ([`scripts/AxiomCheck.lean`](scripts/AxiomCheck.lean)) whose
current source inventory contains **275** top theorems, including **149**
WETH10/`Weth10Inv` rows. `scripts/check.sh`'s row list is the authority on
membership; run `scripts/check.sh --no-build` and bind its exact-set verdict to
`git rev-parse HEAD`. The separate `scripts/check-claims.sh` Lean-checks the
exact statements of the WETH10 flagship set; the axiom audit itself pins
dependency closures, not theorem statements. The families follow. Seven are
WETH's headline solvency theorems:

- `Blanc.weth_preserves_solvent`
- `Blanc.stateTransition_preserves_solvent`
- `Blanc.chain_preserves_solvent`
- `Blanc.addBlockToChain_preserves_solvent`
- `Blanc.stateTransitionUsing_preserves_solvent`
- `Blanc.chainUsing_preserves_solvent`
- `Blanc.addBlockToChainUsing_preserves_solvent`

Seven are FMINT's headline conservation theorems, the same family at the same
rungs:

- `Blanc.fmint_preserves_conserved`
- `Blanc.stateTransition_preserves_conserved`
- `Blanc.chain_preserves_conserved`
- `Blanc.addBlockToChain_preserves_conserved`
- `Blanc.stateTransitionUsing_preserves_conserved`
- `Blanc.chainUsing_preserves_conserved`
- `Blanc.addBlockToChainUsing_preserves_conserved`

They are a different *kind* of claim, not a stronger version of the same one:
solvency is an inequality relating a contract's bookkeeping to the ETH it
holds, conservation is an equality internal to storage. FMINT's says that
`totalSupply` equals the sum of the balances at every observable point, under
arbitrary executions and arbitrary reentrant borrower code. It does not say the
minted supply is backed — during a flash loan it is not, by construction — and
neither family says anything about liveness.

Preservation needs the invariant to hold *once* before it can carry it forward,
and for a genesis-installed FMINT it does: storage that reads zero at every key
is conserved, because both sides of the equality are then zero
(`Blanc.Stor.Conserved.of_get_eq_zero`, with `Blanc.Stor.Conserved.of_empty`
for the canonical empty map). That covers the genesis case and only the genesis
case — FMINT compiles one runtime and has no constructor, so **no
initcode/`CREATE` deployment theorem exists**, and nothing here says an FMINT
deployed by a transaction starts conserved. That remains a declared non-claim;
`rg -n 'processCreateMessage|createTransaction' Blanc/Fmint*.lean` is the
runnable source check for the absent deployment layer.

Eight are FMINT's `flashLoan` specification — the headline
`Blanc.Fmint.fmint_flashLoan_spec` and its seven `no_success_of_*` corollaries
(`callback_never_magic`, `callback_never_returns_word`, `token_ne_self`,
`receiver_not_address`, `amount_over_maxFlashLoan`, `allowance_below_amount`,
`balance_below_amount`), all in
[`Blanc/FlashSpec.lean`](Blanc/FlashSpec.lean). They are **partial
correctness, never liveness**: the headline factors a successful top-level
execution *given as a hypothesis*, and the corollaries rule executions out.
Nothing in them — or anywhere in this repository — says a `flashLoan` call
ever succeeds, and none of them is a state-restoration claim — the
restoration family below carries those.

Their scope is stated in that module's headline docstring, which is the
authority on it, and it is narrower than the names suggest in two ways worth
naming here. **Four premises** restrict the headline: canonically encoded
calldata, the `196 + ceil32 data.length < 2 ^ 256` size bound, an explicit
frame-freshness premise, and the selector premise. And the seven corollaries
are **not one kind of theorem**: two (`callback_never_magic`,
`callback_never_returns_word`) are contrapositives of the headline, and their
premise quantifies over the callback **boundaries** the headline could
produce, *not* over the receiver's code — the weaker and honest form, because
this repository has no determinism lemma pinning that frame uniquely. The
other five are contrapositives of `flashLoan`'s own guards.

Four are the **compile-witness declarations**:

- `Blanc.wethCode_compile` — `Prog.compile weth = some wethCode` — and
  `Blanc.fmintCode_compile`, the same equation for FMINT. Every theorem above
  is conditioned on its contract's account code being what `Prog.compile`
  returns, so without these equations they could all hold vacuously; the
  witnesses state that the compiler really does emit the 988-byte
  [`wethCode`](Blanc/WethCode.lean) for `weth`, and the 1257-byte
  [`fmintCode`](Blanc/FmintCode.lean) for `fmint`. These two fixed-program
  witnesses are proved by `decide +kernel` — kernel evaluation of the same
  reduction, no raised elaboration limit and nothing added to the trusted base
  (in particular, not `native_decide`).
- `Blanc.Weth10.weth10_compiles` kernel-checks compiler success for every
  `DeployParams`, and `Blanc.Weth10.weth10Code_compile` exposes the universal
  equation `Prog.compile (weth10 dp) = some (weth10Code dp)`. The first reuses
  one closed `decide +kernel` result through a proved compile-shape equation;
  the second derives the exact bytes equation from that Boolean witness. The
  pair connects each concrete WETH10 comparison world to its exact member of
  the parameterized runtime family; it is not a liveness or functional theorem.

The longstanding restoration, liveness, gas, error-genre and settlement rows
are catalogued here by family:

- **Frame-level state restoration** (eleven rows, in
  [`Blanc/FlashSpec.lean`](Blanc/FlashSpec.lean), with the shared
  `Blanc.ProcessMessage.rollback_of_error` in `CommonProofs.lean`):
  `rollback_of_callback_failure` at the borrower's frame, and
  `rollback_of_no_success` with its `_total` form and seven per-guard
  instantiations at fmint's own message frame — a frame that cannot succeed
  comes back with its world state restored. Every claim names a frame, never
  a transaction.
- **View-call liveness and exact gas** (the longstanding 37 WETH/FMINT rows
  plus eight WETH10 compiled-walk rows, in
  [`Blanc/FmintLive.lean`](Blanc/FmintLive.lean),
  [`Blanc/WethLive.lean`](Blanc/WethLive.lean),
  [`Blanc/FmintGas.lean`](Blanc/FmintGas.lean) and
  [`Blanc/WethGas.lean`](Blanc/WethGas.lean), with the three
  `Prog.runCompiled`-to-`exec` bridge rows): `fmint_totalSupply_succeeds`,
  `fmint_decimals_succeeds`, `weth_balanceOf_succeeds` and
  `weth_decimals_succeeds` construct successful message-call executions,
  together with exact cold and warm gas and the `fmintGas`/`wethGas` closed
  forms and maxima. [`Blanc/Weth10Live.lean`](Blanc/Weth10Live.lean) adds
  successful compiled walks and exact cold/warm gas for `flashFee`,
  `balanceOf`, `totalSupply`, and `maxFlashLoan`, uniformly over
  `DeployParams` and at the declarations' stated compiled-function altitude.
- **Error genre** (thirteen rows: the seven `settles_with_error_of_*`
  corollaries in `FlashSpec.lean`, and six rows in
  [`Blanc/FmintReverts.lean`](Blanc/FmintReverts.lean)): each no-success
  condition settles with *some* error, and the unknown-selector and
  `token ≠ self` families are constructed all the way to
  `.error (.revert, _)` with empty returndata — *this* error, *no* data.
- **Settlement** (six rows, in
  [`Blanc/FmintSettles.lean`](Blanc/FmintSettles.lean) over
  [`Blanc/ForwardCall.lean`](Blanc/ForwardCall.lean)):
  `fmint_flashLoan_settles` — with **no premise about the borrower**, a
  non-static, canonically-encoded `flashLoan` frame funded at
  `flashLoanGas data.length` ends in a success, a deliberate `.revert`, or
  the non-consensus machine-fault channel, never a consensus exceptional
  halt — with `fmint_flashLoan_settles_of_call` dropping the three guard
  premises (its two further guard walks included) and
  `fmint_flashLoan_frame_settles` restating it at `ProcessMessage`
  altitude. A trichotomy over outcomes, not a success theorem: nothing in
  this repository says a `flashLoan` call ever succeeds.

Each audited theorem carries its **own pinned expected axiom set** in
`scripts/check.sh`, and the audit fails if a theorem's axiom closure differs
from its pin in either direction — extra or missing. In particular it fails on
`sorryAx`, `ofReduceBool`, or `ofReduceNat` — no `sorry` and no
`native_decide`-style axiom in the trusted path of these results. It also fails
if `AxiomCheck.lean` and `check.sh` disagree about which theorems are audited,
so a row cannot be dropped silently from either side. Every permitted pin is
an exact subset of `[propext, Classical.choice, Quot.sound]`; most use all
three, while the seven compile-shape emitter declarations are pinned to
`[propext]`.

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
ten selectors from `wethFuncs`. It records four direct entries and six
internal CALLs whose straight-line prop commits a changed recorder slot after
the call; a selector-shaped PUSH alone receives no credit. All ten, plus the
direct fallback, are reached against a shrink-only budget currently empty.
See [the fixtures
README](scripts/fixtures/weth/README.md#what-the-suite-establishes) for what
this is worth and what it is not: specification-checked differential testing
on chosen inputs, not a liveness proof — the audited theorems above
remain pure safety statements.

It is a local gate (CI does not get the Jaune executable for free from the
dependency build, so CI runs `lake build jaune/jaune` before it), and both it
and the coverage gate are wired into
[`.github/workflows/ci.yml`](.github/workflows/ci.yml).

## fmint fixture suite — execution evidence

The same closure for contract #2.
[`scripts/check-fmint.sh`](scripts/check-fmint.sh) runs **eleven** committed
fixtures ([`scripts/fixtures/fmint/`](scripts/fixtures/fmint/), generated by
[`scripts/gen-fmint-fixtures.py`](scripts/gen-fmint-fixtures.py)) through the
same Jaune fixture runner, each with `Blanc.fmintCode` as the lender account's
code and every expectation filled by the pinned frozen EELS oracle's `t8n`:
the full `flashLoan` success path, a wrong magic word and a reverting
borrower, spectra over returndata shape / `data` length / allowance arm, a
depth-2 reentrant loan, a borrower that moves its minted balance away before
answering, nine guard and dispatcher probes in one case, the ERC-20 view and
`transferFrom` surface, and a Solidity-compiled borrower.

Every **borrower** here is a real Blanc program compiled by Blanc's own
compiler ([`scripts/gen-fmint-borrowers.lean`](scripts/gen-fmint-borrowers.lean)
→ [`scripts/fmint-borrowers.json`](scripts/fmint-borrowers.json)) rather than
hand-authored bytecode — a second, cheap exercise of the code-reuse question.
The trigger/prober contracts that drive them stay hand-authored Python-built
bytecode, on the WETH suite's precedent: they are the fixture's own *input*,
not an oracle-derived expectation.

Four things this harness has that the WETH one does not:

- **A scenario manifest, cross-checked by the harness.**
  [`manifest.json`](scripts/fixtures/fmint/manifest.json) carries each case's
  name, outcome class and assertion count — eleven scenarios, 188 assertions
  — and `check-fmint.sh` cross-checks it against the directory, so a deleted
  or never-generated case fails the gate instead of silently shrinking the
  "all PASS" count.
- **A runtime-byte equality gate.**
  [`scripts/check-runtime-bytes.py`](scripts/check-runtime-bytes.py) parses
  the committed Lean literal straight from source and requires every fixture's
  lender account to be byte-identical to it — 1257 bytes here. It was written
  for this suite and is now run by **both** suite gates, `check-weth.sh`
  included at 988, so neither suite's evidence can drift from the contract it
  is about.
- **An independently checked Solidity-source digest.**
  [`scripts/check-fmint-borrower-source.py`](scripts/check-fmint-borrower-source.py)
  hashes the checker-pinned borrower source with an in-repo Keccak
  implementation independent of the fixture generator and requires the result
  to equal the compiler artifact's `sourceKeccak256`. This catches silent
  source drift; it does not recompile Solidity or claim that the runtime was
  produced by those bytes.
- **A discriminating clean-failure triple.** Each of the twelve *rejected*
  probes, spread across six cases, asserts flag `0`, `RETURNDATASIZE + 1 = 1`
  and an in-EVM gas-floor bit — not merely that the call failed. That triple
  is exactly the `PUSH0 PUSH0 REVERT` shape, and each of the three shapes
  Blanc's older bare `.rev` produced (a garbage-data revert, a stack-underflow
  halt, a memory-expansion out-of-gas halt) breaks at least one of its legs;
  the demonstration is a [falsifier
  table](scripts/fixtures/fmint/README.md#what-the-clean-failure-triple-discriminates),
  not an argument.

**Events are asserted from the specification, not only locked as a golden.**
Jaune recomputes each block's receipts root and logs bloom from its own
execution and fails the block on either mismatch, so the committed goldens pin
fmint's exact emissions — but those goldens are the oracle running our own
bytecode, which locks the behavior without saying it is the right one. So
every case additionally *declares*, at generation time, the log sequence
proposal D6 says it must produce — per transaction, in emission order, with
the revert-only and view-only cases declaring the **empty** sequence — and
generation aborts, writing nothing, if the declaration disagrees with what the
oracle executed. That moves the question from "do two implementations of our
bytecode agree" to "does our bytecode match the specification we wrote down".
What it does not buy: the declarations are only as good as their reading of
D6, so a misreading shared with `Blanc/Fmint.lean` would still agree, and the
RLP and bloom encoders are the oracle's own — deliberately, since they are
consensus rules adjudicated elsewhere and are not what D6 decides.

**One borrower is not Blanc's**, and it is evidence **diversity** rather than
a second proof. `11-flashloan-solc-borrower.json` installs a borrower compiled
by a pinned, digest-verified `solc` into a committed artifact (so neither CI
nor fixture generation needs a Solidity compiler). Every other borrower
decodes `onFlashLoan`'s arguments with the same machinery that encoded them,
and `Blanc.Fmint.fmint_flashLoan_spec` proves the callback window equals
*Blanc's definition* of the canonical ABI encoding — so neither can see a
definition that misstates the standard. An independent decoder can, and this
one recovers the five arguments the suite claims are sent, agreeing word for
word with the Blanc borrower's mid-callback observations. It is one borrower
on one set of chosen inputs: it says nothing about borrowers in general and
widens no theorem. The FMINT gate independently re-hashes the source named by
the compiler artifact before running the fixture; that verifies source
identity, not a fresh Solidity compilation.

A [selector coverage gate](scripts/check-fmint-coverage.sh) obtains fmint's
twelve selectors from `fmintFuncs` and separates two direct entries, seven
internal CALLs tied to changed recorder slots, and mere embedding. Nine are
currently reached; `totalSupply`, `balanceOf`, and `transfer` occur in
branching borrower code but have no callsite-execution witness, so the honest
budget is three. Five built-in corruptions keep embedding, a wrong target, a
missing marker, a branchable recorder, or overwritten calldata from earning
credit. The corrected budget is shrink-only from here.
Both gates are wired into
[`.github/workflows/ci.yml`](.github/workflows/ci.yml) beside WETH's.

**What this is not** is what it is not for WETH: specification-checked
differential testing on chosen inputs. It is not a proof — the conservation
family and the `flashLoan` specification above are the proofs, and nothing in
this directory discharges either — and it is not a liveness result. See [the
fixtures README](scripts/fixtures/fmint/README.md#what-the-suite-establishes)
for the case-by-case account and for what each mechanism is separately worth.

## WETH10 assurance boundary — Blanc proofs and deployed-oracle tests

WETH10 is a high-level Blanc implementation of WETH10's ordinary public
functionality; it is not bytecode-identical to, or a proof of, the deployed
9,975-byte Solidity runtime at
`0xf4BB2e28688e89fCcE3c0580D37d36A7672E8A9F`. The standing semantics of that
port claim are in [`PORTING.md`](PORTING.md). Its 6,313-byte Blanc runtime is
parameterized by deployment chain ID and cached domain separator.
`Blanc.Weth10.weth10Code_compile` proves
`Prog.compile (weth10 dp) = some (weth10Code dp)` for every `DeployParams`.
The named mainnet member has SHA-256
`7e8db17e5ef02cfdc0637547e6a6054a0bfb62aa501a59ccc342f3ac83f5aefc`;
the synthetic chain-31337/address-`0x1000` member has SHA-256
`7adf0712b839be5d46bf10e24e4c860e63593fe4b67ec5ffb3892ca14635b1e8`.

| Assurance class | What is established | Artifact boundary |
|---|---|---|
| Formally proved | Compilation to each named Blanc runtime; compiled endpoint effects; backing preservation; exact flash-counter restoration; transaction/block/chain preservation of `Weth10.Stable`; a direct creation-message seed on the actual post-state; and constructive canonical `withdraw`/`withdrawTo` redemption at ordinary-message and Prague type-2 transaction altitude. `chain_reachable_backed_and_flash_zero` literally concludes `flashMinted = 0` and `balSum ≤ ETH balance`; `Stable.messageRedemption_enabled_of_le` and `Stable.transactionRedemption_enabled_of_le` construct success for each natural amount within one holder's booked balance under explicit code-free-recipient, access/storage, funding, and sufficient-gas envelopes. | The theorems are about the Blanc program and its generated runtime under their stated Jaune premises. They compose existing `ContractSpec` results; they do not verify the deployed oracle, construct keys, promise inclusion, or cover arbitrary receiver code. |
| Executably tested | `scripts/check-weth10-differential.sh` executes 145 generated canonical-call rows against both the literal deployed runtime and the exact named Blanc family members, covering all 27 selectors plus receive in two identity worlds with zero mismatches. `scripts/check-weth10-redemption.sh --no-build` separately replays two committed Prague blockchain fixtures: a type-2 zero/nonzero/failed-redemption sequence with receipt statuses `[true, true, false]`, and a valid type-4 authorization that changes the recipient's code and nonce. | Finite differential rows and transaction fixtures on chosen inputs, not semantic equivalence or a proof. |
| Not established | Verification of the deployed runtime; deployed-vs-Blanc semantic equivalence; establishment from a top-level creation transaction or deployment block; malformed/noncanonical input-calldata closure; arbitrary receiver/borrower liveness or settlement; exact gas, storage, codehash, or CREATE2 parity. | These are non-claims, not assumptions supplied by the proof or test suites. See `WETH10_COMPATIBILITY.md` and `WETH10_DEVIATIONS.md`. |

The generated differential gate's 145 rows include 65 live
CALL/STATICCALL traces, five state-mutating or hostile reentrancy rows, 26
static-context rows, and eight channel falsifiers. Public compiled-effect
theorems separately cover 28/28 runtime entries, including transfer/withdraw,
all three ERC-677-style typed callbacks, permit, flash-loan
callback/repayment/log ordering, exact rollback and error genres, and backing
preservation through recursive calls. `Weth10Live.lean` gives exact Blanc
cold/warm gas for the required views.

The separate constructor is 6,490 bytes: a 177-byte prefix copies and patches
the 6,313-byte zero-parameter template. The deployment gate executes it in two
fresh identity worlds under the pinned Prague EELS and checks nonpayability,
independently derived chain and
domain words, exact installed family members, empty initial storage, no
constructor calls/logs/storage instructions, and six falsifiers. Blanc's
closed accounting is 1,471 init-execution gas, 1,262,600 code-deposit gas,
1,264,071 for the direct creation message, 406 for EIP-3860 initcode metering,
and a 1,421,317 top-level arithmetic ceiling. These are Blanc/Jaune modeled
costs, not deployed-gas parity. `weth10Init_exec_zero` and
`weth10Init_exec_nonzero` connect the actual appended-data initcode to its
successful and nonpayable-rejection executions. Under its explicit
exact-initcode, zero-value, no-code-address, adequate-gas, and code-size
premises, `processCreateMessage_weth10_success` proves that Jaune creation
succeeds, installs the exact freshly parameterized runtime, leaves target
storage empty satisfying `Weth10Inv`, emits no logs, returns the runtime bytes,
and subtracts the named direct creation-message cost.

Both the Blanc runtime and initcode contain `PUSH0`, so Shanghai is the minimum
execution fork. The executable evidence is specifically under the pinned
Prague EELS; neither fact implies deployability on pre-Shanghai forks or a
broader fork-parametric claim.

The execution proof is deliberately compositional: copy, chain-word patches,
five prehash writes, hash, separator patches, and return are proved separately
and then joined. This replaced an all-at-once elaboration that ran beyond
1,000 seconds and drove anomalous aggregate memory use. With no resource limit
raised, historical targeted snapshots completed `lake build
Blanc.Weth10DeployExec` at 917/917 in 28.48 seconds and `lake build
Blanc.Weth10DeployProof` at 920/920 in 132 seconds. Those commands regenerate
current receipts; the recorded figures are proof-engineering snapshots, not
runtime-gas measurements or an industry deployment-verification standard.

The precise behavior contract, evidence ownership, and non-claims are in
[`WETH10_COMPATIBILITY.md`](WETH10_COMPATIBILITY.md) and
[`WETH10_DEVIATIONS.md`](WETH10_DEVIATIONS.md). No arbitrary-borrower
settlement theorem is established, and no such claim is implied here.
