# Blanc: A Minimal EVM Programming Language for Interactive Verification

[![CI](https://github.com/skbaek/blanc/actions/workflows/ci.yml/badge.svg)](https://github.com/skbaek/blanc/actions/workflows/ci.yml)

**[skbaek.github.io/blanc](https://skbaek.github.io/blanc/)** — the guided
tour: the language, what each contract is promised, and what none of it claims.
**[Jaune](https://github.com/skbaek/jaune)**
([site](https://skbaek.github.io/jaune/)) — the EVM semantics every theorem
here is stated against.

Blanc is an EVM programming language optimized for formal verification 
with interactive theorem provers. Blanc's toolchain is implemented in Lean 4.

Blanc compiles to deployable EVM bytecode, and several contracts here
reimplement contracts that exist on mainnet. **A Blanc theorem is a statement
about Jaune's modeled semantics, not a deployment audit** — see
[`SECURITY.md`](SECURITY.md) before treating any result here as a safety claim
about anything on chain.

When a Blanc contract reimplements an existing one, what that port does and
does not claim — and the deviation-registry discipline that backs it — is
governed by [PORTING.md](PORTING.md).

The TriggerableWithdrawalsGateway port's finite differential boundary and
known observable differences are recorded in
[`LIDO_TRIGGERABLE_WITHDRAWALS_GATEWAY_COMPATIBILITY.md`](LIDO_TRIGGERABLE_WITHDRAWALS_GATEWAY_COMPATIBILITY.md)
and
[`LIDO_TRIGGERABLE_WITHDRAWALS_GATEWAY_DEVIATIONS.md`](LIDO_TRIGGERABLE_WITHDRAWALS_GATEWAY_DEVIATIONS.md).

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
- [ExecutionSettlement.lean](Blanc/ExecutionSettlement.lean) and
  [ExecutionOccurrence.lean](Blanc/ExecutionOccurrence.lean): common
  proof-indexed execution evidence. The first owns settlement-aware retained
  frame traversal; the second owns all-outcome instruction occurrences,
  same-frame `ParentPrefix`, exact invocation identity, and compiler-structural
  source cursors. Raw occurrences include terminal errors and work later
  reverted; settlement survival is a separate refinement.
- [ExecutionTrace.lean](Blanc/ExecutionTrace.lean),
  [ExecutionHistory.lean](Blanc/ExecutionHistory.lean), and
  [ExecutionPath.lean](Blanc/ExecutionPath.lean): exact retained wrapper
  carriers from messages through configured histories, plus stable paths to
  settlement-retained frames.
- [ExecutionStateTrace.lean](Blanc/ExecutionStateTrace.lean) and its
  `ExecutionMessageStateTrace`, `ExecutionTransactionStateTrace`,
  `ExecutionBodyStateTrace`, and `ExecutionHistoryStateTrace` layers: ordered,
  provenance-carrying world-state replays across those retained wrappers.
- `ExecutionMessageEffects`, `ExecutionTransactionEffects`,
  `ExecutionBodyEffects`, and `ExecutionHistoryEffects`: contract-neutral
  storage, balance, and `ContractSpec` invariant transports for each retained
  wrapper layer. The [common API registry](docs/COMMON_API.md) is the
  need-first index for the carriers, chronologies, and effect families.
- [CycleWriteFree.lean](Blanc/CycleWriteFree.lean): a total finite-component
  certificate and arbitrary-outcome theorem for **same-frame source-level
  SSTORE-occurrence freedom**. It scans selected bodies structurally, treats
  internal `Func.call` as a finite-component edge, and accepts SSTORE-free
  source cycles without fuel or a termination premise. The theorem follows an
  actual finite source cursor and says nothing about endpoint storage equality,
  TSTORE, logs, balances, memory/code effects, EVM CALL-family or CREATE child
  frames, settlement, gas sufficiency, termination, or any particular
  contract until that contract supplies the exact cursor and certificate. It
  does not establish installation, authorization, transaction behavior, ABI
  enumeration, or any Lido-specific claim.
- [LidoCircuitBreakerRegistry.lean](Blanc/LidoCircuitBreakerRegistry.lean):
  the contract-local Registry integrity family. It relates the ordered pure
  model to concrete owner storage, proves tagged-region separation and all
  length/index/count bounds from `RegistryWitness`, replays every chronological
  shared-kernel write, extracts the stable post-Registry state from successful
  exact-code execution, constructs the target-zero pre-write revert, carries
  register success and pause pre-yield boundaries, and proves frame-settled
  Registry rollback. Its three report-shaped corollaries cover membership,
  removal cleanup, and global count conservation. These are Blanc partial-
  correctness statements over canonical address words and one named message
  frame; they are not deployed-Solidity verification, arbitrary enumeration,
  callback noninterference, access-control completeness, or a whole-history
  theorem.
- [LidoCircuitBreakerEnumeration.lean](Blanc/LidoCircuitBreakerEnumeration.lean):
  the contract-local Registry read and observability family. For every finite
  `RegistryWitness` it constructs the exact emitted `getPausables()` run with
  no contract-chosen cap, exact ordered dynamic-`address[]` ABI bytes, finite
  length-scaled resources, constant stack cursor height, and successful
  state/log silence. It packages exact `getPauser` and `getPausableCount`
  bodies over the same snapshot, lifts the enumeration cycle certificate to
  actual same-frame SSTORE-occurrence freedom, and connects the sole
  production `PauserSet` suffix to the stable Registry poststate and its
  register/pre-yield-pause continuation. Direct-register success preserves
  that event through optional heartbeat records and clean message settlement,
  while exact direct-message errors expose neither the rolled-back event nor
  Registry writes. The committed local-monitor corollary re-runs the three
  exact views on the matching clean snapshot; it is not a history, finality,
  delivery, callback, or real-block-feasibility claim.
- [LidoCircuitBreakerHistory.lean](Blanc/LidoCircuitBreakerHistory.lean),
  [LidoCircuitBreakerHistoryEndpoints.lean](Blanc/LidoCircuitBreakerHistoryEndpoints.lean)
  and
  [LidoCircuitBreakerHistoryChain.lean](Blanc/LidoCircuitBreakerHistoryChain.lean):
  the induction principle that carries Registry integrity through arbitrary
  histories. Registry coherence — *some* ordered entry list witnesses every
  projected Registry region of the contract's own storage — is packaged as a
  storage-only `ContractSpec`, discharged one dispatch target at a time, joined
  across the exact three-pivot hybrid dispatcher rather than either dispatcher
  shape the generic ladder already supports, and lifted from there to messages,
  transactions, blocks and chain reachability: from a checkpoint where the exact
  compiled runtime is installed at an address and that address's storage carries
  a `RegistryWitness`, every state reachable by the configured valid-chain
  relation still has that runtime installed and still admits a witness. The
  family is discharged in full — no `sorry` anywhere in it, and every public
  theorem depends on exactly `propext`, `Classical.choice` and `Quot.sound`. The
  reach is in what the premises decline to say — the frame theorem quantifies
  over arbitrary successful runs of the exact runtime and over arbitrary callee
  bytecode, including code that re-enters this very instance, and the transport
  above it takes arbitrary finite sequences of successful and reverting
  transactions. There is no target-honesty premise and no count or interval
  noninterference premise anywhere in the family. The witness it produces need
  not be the one it started with, and that is deliberate: a callback re-entering
  as admin may register a pauser, so requiring the returned entry list to be the
  entered list would be a false strengthening. Four corollaries hand a reader
  that content at the reached state rather than making it unfold the invariant —
  the exact installed runtime, an actual `RegistryWitness`, membership and index
  equivalence at an arbitrary canonical target, and global count conservation —
  at the configured-chain and the Prague rung alike.
  `emptyRegistryWorld_registryStable` exhibits a state satisfying the
  checkpoint, so none of this is vacuously true; that state is synthetic, built
  by hand rather than reached, and it is not a deployment. The general history
  theorem itself remains conditional on such a checkpoint. The exact official
  direct-deployment family below now supplies one non-synthetic checkpoint and
  then applies these same arbitrary-future consequences from it.

  Read the remaining boundary as closely as the statement. Because the
  invariant is existential, nothing says a transaction returns the entry list
  it began with, and nothing produces a source-level history trace. Nothing
  states that the pauser count and the recorded expiry are coherent at callback
  time — the source has a real mid-pause state with a zero assignment count and
  a still-live old expiry — and nothing composes the public `pause` entry through
  `setPauser`. One limit sits in the reachability relation rather than in the Registry:
  `BlockChain.ReachUsing.step` and `BlockChain.Reach.step`
  ([Ladder.lean](Blanc/Ladder.lean)) admit a block only when the world's total
  wei balance plus that block's withdrawals stays below `2 ^ 256`, so "every
  reachable state" silently excludes any history that would cross that bound — a
  restriction the Registry invariant itself never consults. Every statement is
  partial correctness over storage: no gas, liveness, or differential claim,
  universal or otherwise. And none of it speaks about Lido's deployed bytecode —
  that remains the interface/accident port claim [`PORTING.md`](PORTING.md)
  owns, supported separately by the pinned differential campaign.
  `scripts/check-lido-circuit-breaker-history.sh` is the family's assurance
  gate, and its own summary line is the authority on which owners are live.
- [LidoCircuitBreakerDeploymentInput.lean](Blanc/LidoCircuitBreakerDeploymentInput.lean),
  [LidoCircuitBreakerDeploymentLayout.lean](Blanc/LidoCircuitBreakerDeploymentLayout.lean),
  [LidoCircuitBreakerDeploymentTrace.lean](Blanc/LidoCircuitBreakerDeploymentTrace.lean),
  [LidoCircuitBreakerDeploymentMessage.lean](Blanc/LidoCircuitBreakerDeploymentMessage.lean),
  [LidoCircuitBreakerDeploymentTransaction.lean](Blanc/LidoCircuitBreakerDeploymentTransaction.lean),
  [LidoCircuitBreakerDeploymentBlock.lean](Blanc/LidoCircuitBreakerDeploymentBlock.lean),
  [LidoCircuitBreakerDeploymentRoot.lean](Blanc/LidoCircuitBreakerDeploymentRoot.lean),
  [DeploymentCompiled.lean](Blanc/DeploymentCompiled.lean), and
  [DeploymentMessage.lean](Blanc/DeploymentMessage.lean): the exact official
  direct-deployment ladder. From a valid base world and a strict singleton
  type-2 Prague block envelope, its only named-chain premise is the configured
  `stateTransitionUsing` equation. Under the envelope's explicit recovered-
  sender and computed-address premises, the ladder derives the prepared message
  target and executes at that address, runs the frozen 5,122-byte official
  creation input through the actual constructor and creation-message machinery,
  proves the collision check,
  transaction settlement, successful receipt, request-empty system suffix, and
  deployed valid context, and reconstructs the resulting root. That root pins
  the 4,282-byte official runtime, the two official configuration values, the
  empty Registry witness, three ordered constructor logs, successful receipt,
  empty requests, and `RegistryStable`; its methods then carry code, witness,
  membership, and count conservation through every configured reachable future.

  The public base and envelope predicates explicitly carry valid-context,
  sender-recovery and transaction-checking, funding, gas/code-size, system-
  predeploy, nonce/address, and strict block-shape facts. Collision freedom is
  reconstructed at the prepared post-prefix, post-nonce, post-fee-debit message
  state. No execution result, poststate, receipt, installed-code fact, or
  `RegistryStable` result is smuggled into those inputs.

  This is one exact direct, zero-endowment, singleton-block deployment of the
  Blanc port. It is not a claim about the deployed Solidity bytes or historical
  mainnet inclusion, and it does not cover arbitrary constructor parameters,
  factory/proxy/clone/CREATE2 creation, nonzero endowment, or arbitrary block
  shapes. The finite clone namespace remains differential evidence for distinct
  storage owners, not a second deployment root. A temporary strict singleton
  replay against the pinned EELS and Jaune evaluators is a separate finite
  channel and no Lean premise. The assurance gate is
  `scripts/check-lido-circuit-breaker-deployment.sh`.
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
  canonical mainnet artifact.  The downstream
  [Weth10MainnetCodeEq.lean](Blanc/Weth10MainnetCodeEq.lean) owner derives the
  artifact equality from the parameterized deployment-patch correspondence,
  keeping the generated byte owner free of the duplicate whole-compiler
  decision while preserving the exact public theorem name and byte statement.
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
- [Weth10Stable.lean](Blanc/Weth10Stable.lean) and
  [Weth10DeploymentRoot.lean](Blanc/Weth10DeploymentRoot.lean): the packaged
  code/backing/zero-flash stable predicate, its configured-chain preservation,
  and the strict canonical singleton Prague deployment bridge. The latter
  crosses Jaune's system prefix, transaction preparation and collision check,
  successful receipt insertion, empty withdrawals, both checked request-system
  suffix calls, and deployed-context reconstruction before exporting future
  configured-chain stability and its literal code/flash/solvency projections.

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

## Proof recipe lookup

Before beginning a manual multi-step walk or inversion, consult the generated
[proof recipe index](docs/PROOF_RECIPES.md) or run the read-only
`blanc_suggest` tactic at the goal. The index and the tactic's lookup table are
both generated from `scripts/proof-recipes.toml`; edit that registry and
regenerate the surfaces rather than editing either generated file by hand.
`blanc_suggest` prints each matching recipe's validated registered symbols as
well as its route and boundary.

For need-first declaration discovery that does not depend on a goal matcher,
start at the branching [common API registry](docs/COMMON_API.md). Follow its
execution, invariance, state-update, memory, settlement, or compilation branch
before adding a contract-local helper; the leaves point to shared modules and
named declarations rather than sibling-contract examples.

The registry also carries the standing **common-library-first workflow** for
any needed declaration with a generic shape: search before rolling your own,
use or generalize what a shared module already provides, hoist a
contract-local original to the common library before using it, build a
genuinely new generic declaration in a shared module rather than the contract
that first needs it, and close every common-library change with the registry
and recipe discoverability updates in the same change. Follow it there rather
than restating it elsewhere.

## Proof-performance conventions: defeq, wide-record updates, state towers, and walk term size

Several elaboration-cost bombs have been measured in this repository,
including definitional-equality bombs and term-size growth in forward walks.
The conventions below are the working rules for avoiding them. They apply to
all Blanc proof work, whatever the contract and whatever agent or editor is
driving it.

Before commissioning a new whole-tree offender census, start from the
[post-cure offender catalogue](docs/offender-catalogue.md). It records the
committed-budget comparison and current ceiling population, the terminal scope
of prior routes, and the protocol for freezing a new independent census.

**The predictor.** Call a definition a *wide-recursion state constructor* when
its right-hand side uses its own state/accumulator argument more than once
(for example, a storage-write state builder that mentions its base state in a
refund computation, a current-value read, and the write itself). Nesting k
layers of such a definition unfolds geometrically. The hazard is therefore any
step that leaves a **definitional-equality obligation spanning one or more
layers the tactic did not name**:

- a bare `exact`, `assumption`, `change`, `show`, or `rfl` whose stated type
  differs from the goal by tower unfolding;
- a **partial** `simp only`/`dsimp only` — one that unfolds some layers of the
  tower but leaves an inner layer (often a `let`-bound intermediate state)
  opaque, so the following `exact` has to cross it by defeq;
- instantiating a lemma's abstract state variable with a concrete tower and
  leaving the normalization to unification.

**The count of definitions in a `simp only` set is not the signal —
completeness relative to the tower is.** This was measured directly: a site
naming *all* seven layers and closing with `exact` compiles in ~3 s, while
deleting a *single* intermediate name from that same set — leaving one
unnamed layer for `exact` to bridge — took the whole module from 161 s to
still-running past 400 s. A larger simp set is not the problem; an incomplete
one is.

Two safe routes, in order of preference:

1. **One-layer projection lemmas over an abstract base**, applied by `rw`
   after unfolding only the local `let` binding. They are `rfl`-provable
   precisely because one layer over a variable stays small, they compose
   additively where defeq composes multiplicatively, and they do not depend on
   the author remembering every layer name. A measured instance took a
   five-line step from more than twenty minutes to five seconds.
2. **A complete unfold** naming every layer including `let`-bound
   intermediates, so both sides normalize and the closing step has nothing
   left to bridge. Correct but fragile: adding a layer later silently makes
   the set partial again, which is exactly how the twenty-minute bomb arose.

"`rfl`-provable" does not mean "cheap to use by defeq". The sibling trap — the
kernel eagerly folding `Nat` operations at closed program-sized terms — is
documented in the WETH10 elaboration-cost history and has the same flavor:
keep expensive evaluation out of both the elaborator's and the kernel's
definitional paths by routing through named lemmas.

**The third bomb: forward walks that carry their own concrete internals.**
The two traps above are about definitional equality; this one is about the size
of the term itself. Constructing a compiled walk over a large concrete body —
`Func.RunCompiled` and its siblings, driven by `func_run` — builds an
intermediate term at every step. When each step carries the whole concrete
remaining program, the memory image written so far, and the concrete values
staged into it, that term grows along the walk instead of staying flat, and the
cost grows with it.

**Its signature** is a staging or patching walk over a concrete body that only
gets through after a `maxRecDepth` or `maxHeartbeats` ceiling is raised,
typically across a run of consecutive `MSTORE`s. The raised ceiling is the
symptom that gets treated; the term growth is the disease. Raising a ceiling
suppresses the diagnostic without reducing the work, so a walk that compiles
only because its ceiling was raised is a candidate, not a solved problem.

**The route** is to factor the walk into named sub-components, abstract each
one over the memory or value it threads, and instantiate the concrete facts
through opaque top-level lemmas. This is safe route 1 above applied to a walk
rather than to a `let`-bound state tower, and it works for the same reason: one
layer over a variable stays small, and abstractions compose additively where
term growth composes multiplicatively. The worked instance is
`ConstructorPatchInvariant` in `Blanc/LidoCircuitBreakerDeploymentTrace.lean` —
a carrier structure over a variable `Mem`, stepped by
`ConstructorPatchInvariant.runCompiled_write`, driving a named staircase in
place of a concrete memory tower.

**Measured on the Lido constructor walk, 2026-08-23.** Abstracting a three-op
prefix over memory and value took its artifact from a 14.5 GiB store wall that
did not complete to a 0.8 s build. The constructor body went from a
15.5-minute hard stop with 12.6 GiB of swap to a 737 ms compile. These are
whole-artifact build times from that goal's working log rather than
`check-elab.sh` rows; they are recorded here because this class had no measured
entry at all, not because they are gate evidence.

**The discipline** is to build each certificate separately and abstract only
the ones that cross the breaker. The abstraction costs source and indirection,
and a short bounded walk does not need it. WETH10 largely does not — it already
uses dispatcher views and named line certificates. The 2026-08-25 Lido
retrofit applied local carriers to `pause_stageArgs_runCompiled` and the two
replacement-registration body walks, removing all six of their raised
recursion/heartbeat scopes. In sequential `check-elab.sh` checkpoints the
Pause owner moved from 47.842 s to 31.984 s and Replacement from 30.441 s to
2.326 s; target profiler entries that had been 29.898 s, 28.371 s and 41.545 s
all fell below the 2 s reporting threshold. The Registry staging walk stayed
concrete: its carrier improved the isolated target from 15.638 s to 10.531 s
but regressed the three-owner closure from 23.655/47.842/30.441 s to
37.989/67.316/53.222 s, so it was reverted. That is the intended boundary:
cross the breaker on the closure that owns the walk, not on a target-only
profile. The exact dispositions and non-applicability boundaries remain in the
`runcompiled-construction` proof-recipe entry.

**The fourth bomb: changed-field projections through wide record updates.**
For an N-field record, `{r with f := v}` is a fresh N-argument constructor
application. Projecting the changed field across that update can therefore
leave the checker comparing two applications of the same constructor head. It
tries congruence first and must evaluate the concrete payload before it can
discover that congruence fails; projections of unchanged slots through other
update layers stay syntactic and cheap. This is why the shape is deceptive:
the expensive line can be a bare `change`, `show`, `rfl`, or `exact` after the
real effect tower was already constructed elsewhere.

The elaborator's `isSimple` guard skips this walk for projection chains, while
the kernel applies the congruence-first heuristic without that guard and
ignores `maxHeartbeats`. This class can therefore cost tens of seconds with
**zero raised ceilings**. Route it through Jaune's update-first projection kit,
whose lemmas are named `Devm.<update>_<projection>` (for example,
`Devm.withOutput_refundCounter`) and are proved over an abstract base; do not
bridge a concrete update tower by definitional equality. In the measured pilot,
the `officialConstructorPost_refundCounter` bridge fell from 30.232 s to below
a 100 ms profiler threshold, a speedup of at least 302x.

The same trap remains armed in `withError`, `withReturnData`,
`withAccountsToDelete`, and every other wrapper that rebuilds `Meta` through
`setMeta`. A succeeding concrete `getStor` walk can expose the same projection
mechanism after the effect tower has already been built. Route it through an
early semantic cut such as `Devm.withRefundCounter_getStor` or
`Devm.addLog_getStor`; when the warm/cold storage branch itself carries the
concrete tower, isolate that branch behind a narrow module-private boundary.
That route moved `LidoCircuitBreakerDeploymentTrace` from 62.173 to 17.050
seconds. `setMach`-chain normalization remains governed by the measured
refutation in `successor-projection-normalization`.

**Typed route data before proof search.** A long `Prog.SourceStep` append chain
can spend most of a module repeatedly postponing `.rest` and branch constructors
against an unassigned element type. Give `List.replicate n .rest` a helper whose
result is `List Prog.SourceStep`, spell branch constructors with their full
`Prog.SourceStep` name, and measure the owning module. The final census review
moved `LidoCircuitBreakerPauseOkRoute` from 10.22 to 2.56 user seconds and the
remaining `LidoCircuitBreakerAttainment` paths from 38.12 to 30.15. This is a
profile-triggered repair, not a tree-wide formatting rule. The
`runcompiled-construction` recipe records the proof-boundary interaction and
the owner-measurement requirement; this section is the definition-level
trigger, because no proof goal exists while a `SourcePath` value elaborates.

**The fifth bomb: repeated kernel decisions over one closed subject.** A closed
compiler artifact, structural site inventory, or similar subject is expensive
when normalization must traverse a large recursive value before exposing the
small observation in the proposition. If several decisions inspect that same
subject, bind it once and decide a tuple or conjunction of observations, then
project the results; when one exact normalized equality already exists, derive
the other views with `congrArg`. The discriminator is shared normalization:
unlike a term-size bomb, no growing proof state is threaded through a walk, and
unlike a defeq bomb, the proposition may be syntactically exact before the
kernel evaluates it.

This rule is subject-specific, not a license to combine unrelated facts. An
authoritative owner-row measurement decides whether the subjects were truly
shared: the Attainment pilot's six bundled pins cost the sum rather than the
maximum and was reverted. Ceiling counts cannot find this class. The point of
`decide +kernel` is to move evaluation outside the elaborator, where heartbeat
budgets do not apply, so a zero-ceiling proof can still repeat seconds of
kernel normalization.

**Why budgets do not save you.** Inside `simp`'s defeq discharging the work is
not heartbeat-metered, and the kernel's certificate check ignores
`maxHeartbeats` entirely — a generous budget that has "never fired" is not
evidence of health. Language-server diagnostics are equally unable to detect
this class: on a file whose elaboration outruns the client's inactivity
window, an empty diagnostics list with a failed completion flag is a timeout,
not a verdict.

**Class 9: an unmeasured resource ceiling.** A raised limit can cost no
time itself while hiding the next regression inside a declaration whose need
was never measured; timing instruments cannot identify that ceiling-only
offender. The two resources are asymmetric. `maxRecDepth` is a shape budget and
costs nothing when unused. A necessary `maxHeartbeats` raise is evidence of a
lower bound on elaborator work, but heartbeats cannot be converted to seconds,
and the kernel ignores them entirely.

Treat an existing ceiling as a hypothesis. Read its source history, establish a
biting anti-vacuity control for the family, and run deletion probes in an
isolated worktree with a cloned cache. Probe depth and heartbeats separately,
restore exact values after a failing arm, and confirm a passing heartbeat
deletion twice. Language-server checks on exact source prefixes are useful for
fast midpoint search, but the final source owns the verdict: where an exact
minimum is claimed, its immediate predecessor is red and the value itself is
green on the complete real file. Record every deletion, narrowing,
right-sizing, or named load-bearing restore with its reopen condition.

The ceiling-debt campaign confirmed that provenance is not necessity: copied
per-genre depth budgets and heartbeat values tuned per declaration both
contained deletable scopes. Of 415 launch scopes, 352 deleted, nine ambient
scopes narrowed to 40 measured command owners, 16 right-sized, and 38 were
retained after a named failure; zero ambient scopes remain.

The linked catalogue joins that historical disposition evidence to all 94
current scope identities and distinguishes exact adjacent boundaries from the
weaker retained-justified and reopen-triggered cases.

New ceilings are never ambient, file-wide, namespace-wide, unlimited,
unexplained, or “just in case.” Use the smallest measured finite value on the
exact command or tactic-local owner and record the probe, justification, and
reopen condition with the raise. The proof-debt gate blocks every unexcepted
new or increased ceiling. Its permanent writer admission names an exact stable
ID and is limited to a reviewed new/null command- or tactic-local scope at its
observed value. A temporary need or an increase of an existing finite ceiling
uses an exact owned, evidence-bearing, expiring exception with a removal
condition; no ambient or wildcard exception is accepted.

**The measurement method that works.** Compile a file prefix once into an
importable `.olean` (stripping `private` so probe segments can reference it),
compile each suspect segment as its own module importing the previous probe's
result under a wall-clock cap, and truncate inside a slow theorem with `sorry`
to isolate the guilty step. Cost is then paid once per segment rather than
once per probe, and a multi-thousand-line file bisects to a single tactic in a
handful of runs.

**The routine instrument.** The bisection above is for a file that has already
stopped responding. To catch the same class *before* it becomes a hang, profile
the module. Ask *which declaration* first:

```
lake env lean -Dtrace.profiler=true -Dtrace.profiler.threshold=2000 Blanc/<Module>.lean
```

Read `[Elab.definition.value]` and `[Elab.command]` alongside `[Elab.async]`:
the corpus contains 341 rows in the first two classes against 327 async rows,
so an async-only view misses the majority. These attributed lines name their
declarations, so one run ranks the proofs in a module. Prefer this to
`-Dprofiler=true`, whose output is a flat list of tactic durations with no
attribution — useful only once you already know where you are.

A `[Kernel]` row attached to a `structure` or `inductive` is a synchronous join
barrier charged for draining the preceding asynchronous queue, never that
declaration's own cost. The arithmetic matched barrier time to the sum of its
siblings within 4.2 ms and a removal edit moved the barrier to 3.0 ms. The
decisive control on `LidoCircuitBreakerDeploymentInput` preserved the two
theorem kernel rows at 5.490 s and 5.301 s under `-DElab.async=false`, while
the approximately 10.678 s structure row fell below the 2 s reporting
threshold. The barrier interpretation is therefore control-confirmed.

To recognize a serialized cumulative cohort, sort rows in source order and
count adjacent inversions: zero inversions across at least eight rows means to
read staircase deltas, not the cumulative values. Also compare the sum of
`[Kernel]` rows divided by available cores with module wall time; an impossible
sum exposes overlapping waits. Per-declaration profiler figures are ordinal
evidence and must never be summed as cardinal seconds.

Read the per-tactic view by name, not by duration alone. `exact`, `assumption`,
`rfl`, `apply` and `change` perform no search, so a multi-second entry naming
one of them is almost always definitional-equality work — the subcritical form
of the trap above, quietly costing tens of seconds per site rather than
hanging. `simp`, `omega`, `decide`, `func_run` and `congr` are expected to take
real time, and their durations carry no such implication. A repeated identical
cluster of timings is one defect with several call sites, not several defects,
and is fixed once.

Cost tracks neither line count nor declaration count. In this repository's
registration family the largest module is the cheapest by a factor of six, and
two proofs out of ninety-six held sixty percent of the elaboration time.

**A failed alternative is not free.** `first | tac₁ | tac₂ | …`, `try`, and
`all_goals` charge full elaboration for every alternative that is *attempted*,
not merely the one that succeeds. That is harmless when the alternatives fail
cheaply and ruinous when failing requires an expensive unification. The
same charging can occur inside the unifier's own strategy ladder —
`isDefEq.delta` tries congruence before unfolding — even when no alternative
combinator appears in source. The measured instance: four memory-extension
goals discharged by

```
all_goals first
  | exact Devm.extCost_of_size (n := 0)   rfl          (by decide +kernel)
  | exact Devm.extCost_of_size (n := 544) (hM1Size _)  (by decide +kernel)
  | …
```

Each goal that needed a later alternative first unified `N.size = n` against a
nested `Mem.write` tower for every earlier `n` and threw the result away. One
45-line proof cost **46.4 s**; dispatching each goal by its tag in the order
`func_run` emits them —

```
case h_ext => exact Devm.extCost_of_size (n := 0) rfl (by decide +kernel)
case h_ext => exact Devm.extCost_of_size (n := 544) (hM1Size _) (by decide +kernel)
```

— brought the identical proof to **5.1 s**. Three copies of that shape were
95 s of a 161 s module. So: when the alternatives of a `first` differ only in
an implicit argument that must be unified against a large term, do not let the
combinator guess. Name the goal and apply the one lemma that fits. Repeated
`case <tag> =>` blocks consume same-tagged goals in emission order, which is
what makes this rewrite mechanical.

## Proof-module size and partition

A derivation module should be partitioned from its dependency structure, not
from an assumed line-count latency threshold. On 2026-08-22, using Lean 4.32.1
at Blanc commit `159b75f4f1c09b5a6c3b596da9e933e1881a5cbd`, a serialized
fresh-server protocol measured cold open, warm goal, matching-version
whole-file diagnostics, and harmless tail and line-1 edits three times on eight
modules. An independent 135-unit reproduction repeated the result. The
1,244-line `LidoCircuitBreakerRegistryModel.lean` cold-open median was 1.971 s
(2.069 s reproduction), not the formerly quoted ~21 s. Three modules over
8,000 lines had cold medians of 71.835, 8.566, and 10.815 s (71.393, 8.719, and
10.981 s reproduction), so 8,000 lines did not define a client-latency
boundary.

Cold-open and line-1-edit medians correlated with committed batch elaboration
cost at Spearman 1.000 and with physical lines at 0.119. A 722-line module cost
about 48 s while a 5,528-line module cost about 7 s. Tail edits remained
0.074–1.738 s, real warm goals 0.0007–0.0041 s, and current full-file
diagnostics 0.00018–0.00094 s. Therefore the 1,250 warning and 8,000 hard cap
are not supported as author-visible latency constants by current evidence.
They may remain separate structural policy constants only with a rationale
that does not cite the former timing claims.

The experiment did not split a module. Use the mechanical dependency partition
below as a candidate construction, then measure the same practical upstream
edit before and after. Do not claim that a shorter file improves the edit loop
until the isolated elaboration/import closure is actually faster.

Three rules make the split mechanical rather than a judgement call.

**Compute the partition; do not guess it.** Extract each declaration's
dependencies textually, take the public results of each independent case as
roots, and assign a declaration to the shared substrate exactly when two or
more roots reach it — or none do — and to a case leaf otherwise. The shape is
then acyclic by construction, and the check that no leaf references another
leaf is what proves it. A hand-written list of "what looks shared" will
misplace declarations whose names have drifted from their content.

**A generic declaration must not carry a case's name.** Names like
`absentZeroRemovePost` or `freshRegisterMemory`, for a storage-write state
builder and a memory image that no chronology owns, are not merely untidy: they
cause exactly the misplacement above, and once a gate pins a name, renaming
stops being free. Rename on the way into the substrate. This is the
sibling-module discipline of `AGENTS.md` applied within a contract — a name
claiming one case while serving all of them is evidence that the declaration
belongs upstream.

**Re-check reachability after every deduplication.** Replacing several parallel
walks with one generic walk leaves the superseded intermediates behind, and an
unused `private` theorem produces no warning whatsoever. A reachability pass
over this module found 253 such lines, still being elaborated on every build.

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
   current source inventory pins the exact axiom set of 962 named results and
   fails on an extra *or* missing axiom.
   Run `scripts/check.sh --no-build`; its `962/962` summary belongs to the
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
current source inventory contains **962** top theorems. `scripts/check.sh`'s
row list is the authority on membership; run `scripts/check.sh --no-build` and
bind its exact-set verdict to
`git rev-parse HEAD`. The separate `scripts/check-claims.sh` Lean-checks the
exact statements of the WETH10 flagship set and the protected Lido Registry
mutation, enumeration, view-coherence, observability, exact official
constructor/message/transaction/block, direct-root, and rooted-future
boundaries; the axiom audit itself pins dependency closures, not theorem
statements. The families follow. Seven are WETH's
headline solvency theorems:

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
| Formally proved | Compilation to each named Blanc runtime; compiled endpoint effects; backing preservation; exact flash-counter restoration; transaction/block/chain preservation of `Weth10.Stable`; a direct creation-message seed; and a strict canonical singleton type-2 deployment through Jaune's actual configured Prague block pipeline into a `DeploymentRoot` with successful receipt, exact installed runtime, empty storage/logs/requests, deployed `ValidContext`, and stable future reachability. Constructive canonical `withdraw`/`withdrawTo` redemption is also proved at ordinary-message and Prague type-2 transaction altitude. The root projections literally conclude exact code, `flashMinted = 0`, and `balSum ≤ ETH balance` at every reachable configured-chain boundary. Committed balance credits are proved not to wrap, and holder flow is proved in `Nat` for the exact Blanc runtime over a proof-carrying Prague-only `AccountedHistory`: with `B0`/`Bt` the checkpoint/later booked balances, `B0 + ordinaryIn + selfTransfer + flashCredit = Bt + redeemed + externalTransferredOut + selfTransfer + flashRepayment`; exact flash pairing and cancellation give `B0 + ordinaryIn = Bt + redeemed + externalTransferredOut`, hence `B0 ≤ Bt + redeemed + externalTransferredOut` and the corresponding truncated and withdrawal-only floors. The history retains the full applied block sequence, ordinary transaction roots, `BlockOutput`, and the beacon, history, withdrawal-request, and consolidation-request system roots, and its fold includes only settlement-surviving effects. It projects to ordinary Prague reach, which admits such a history from every stable checkpoint. Hardened authorization provenance is proved over that same runtime and history: unconditionally `hardenedOutflow ≤ permanentOutflow` per holder, and under a trace-local `NoAllowanceKeyCollision` hypothesis — that distinct touched raw `(owner, spender)` word pairs project to distinct allowance keys — the two are equal as a literal `Nat`. For arbitrary checkpoints the root taxonomy includes a value already present at the checkpoint. Across the full window from a proved deployment's empty storage, every nonzero permanent-outflow record instead traces exactly to the holder's own call, an in-window `approve` called by that holder, or an in-window `permit` signature recovering to that holder; the checkpoint case is eliminated by replaying the rooted allowance ledger. Corollaries give the hardened floor `B0 ≤ Bt + hardenedOutflow` and a deployment-rooted dormant-holder theorem: if the holder performs no effectful authorizing act — no debit as actual caller, `approve` write as caller, or `permit` recovering to it — then its booked balance cannot decrease across a collision-free history; same-caller reads and other inert calls do not void the premise, and deployment-root empty storage discharges allowance quiescence over all raw aliases. The dual-selector future-redeemability flagship packages, for every ordinary Prague-only reachable future of a constructed `DeploymentRoot`, an authentic accounted history with its cancelled conservation equation, residual floor, and `withdraw`/`withdrawTo` message and transaction enabledness for every amount within that residual, with rebased full-booked-balance corollaries and the `NoCollision`-conditional hardened description. A supplied-list any-order corollary proves that, for any duplicate-free holder list and admissible recipient map, every permutation of one full-booked-balance claim per listed holder succeeds at message altitude, one canonical message at a time, with stable boundaries and remaining claims. | All results are about the Blanc program and generated runtime. The deployment/root results use their explicit valid-base, strict-block, collision-free, funding, gas, system-predeploy, arithmetic, and successful configured-transition premises. The holder-flow family itself is about the exact compiled Blanc runtime and assumes no `NoCollision` condition: each debit is only **runtime-authorized**, with the actual caller and accepted direct, allowance, or flash branch recorded; raw branch words remain distinct from normalized storage addresses. The hardened family adds exactly one hypothesis, `NoAllowanceKeyCollision`, and consumes it solely for **attribution**: redemption success, message and transaction enabledness, and the residual floor are never conditioned on it. Collision-freedom is a stated hypothesis, not a proved property, and its scope is the pairs the trace actually recorded. Attribution names the account whose recorded act the runtime accepted; it is not evidence that the holder consented to, intended, or was aware of that act — a relayed `permit` signature and a phished `approve` both attribute to the signing account. Its exact-invocation witness excludes WETH bytes run by `DELEGATECALL`/`CALLCODE` against another account's storage and foreign lookalike slots or logs. Raw-message theorems inject a caller and prove execution only; they do not authenticate that caller or mine a transaction. At transaction altitude, admissible senders are exactly the senders Ethereum's modeled rules admit: code-free or valid EIP-7702-delegated accounts. Direct `withdraw` pays the sender and therefore retains the code-free-recipient restriction; `withdrawTo` permits any nonzero, non-precompile, code-free recipient. For a funded code-free external holder with canonical nonce, fees, gas, and payload, the non-signature transaction envelope proves every other admission obligation, leaving only recovery of that holder's own signature. No theorem forges it. A holder with non-delegation contract code that cannot call WETH10 — WETH10 itself remains an example, because it can legally receive its own token — keeps a conserved balance but has no transaction-altitude exit of its own. The supplied everyone-list is input; no theorem enumerates holders from state. The results do not verify the deployed oracle, establish holder consent, intent, or awareness, construct keys or signatures, promise inclusion, generalize to arbitrary deployment shapes, or cover arbitrary receiver code. |
| Executably tested | `scripts/check-weth10-differential.sh` executes 147 generated canonical-call rows against both the literal deployed runtime and the exact named Blanc family members, covering all 27 selectors plus receive in two identity worlds with zero mismatches. `scripts/check-weth10-redemption.sh --no-build` separately replays two committed Prague blockchain fixtures: a type-2 zero/nonzero/failed-redemption sequence with receipt statuses `[true, true, false]`, and a valid type-4 authorization that changes the recipient's code and nonce. `scripts/check-weth10-deployment.sh` additionally generates one fresh singleton type-2 creation block in memory, checks 16 semantic assertions including its successful receipt and exact installed runtime, and replays it through Jaune at Prague. | Finite differential rows and transaction fixtures on chosen inputs, not semantic equivalence or a proof. The generated deployment fixture is temporary evidence and does not claim a signing-key or inclusion construction in Lean. |
| Not established | Verification of the deployed runtime; deployed-vs-Blanc semantic equivalence; arbitrary co-block/factory/CREATE2 deployment shapes; key custody, propagation, or inclusion; malformed/noncanonical input-calldata closure; arbitrary receiver/borrower liveness or settlement; exact deployed gas, storage, or codehash parity. | These are non-claims, not assumptions supplied by the proof or test suites. See `WETH10_COMPATIBILITY.md` and `WETH10_DEVIATIONS.md`. |

The generated differential gate's 147 rows include 69 live
CALL/STATICCALL traces, seven state-mutating or hostile reentrancy rows, 26
static-context rows, and eight channel falsifiers. They include a callback
that catches a failed nested WETH10 transfer while its parent commits without
child flow, and a successful flash callback whose ordinary transfer commits
between the paired mint and settlement burn. Public compiled-effect
theorems separately cover 28/28 runtime entries, including transfer/withdraw,
all three ERC-677-style typed callbacks, permit, flash-loan
callback/repayment/log ordering, exact rollback and error genres, and backing
preservation through recursive calls. `Weth10Live.lean` gives exact Blanc
cold/warm gas for the required views.

The separate constructor is 6,490 bytes: a 177-byte prefix copies and patches
the 6,313-byte zero-parameter template. The deployment gate executes it in two
fresh identity worlds under the pinned Prague EELS and also generates a strict
singleton type-2 creation block whose successful receipt, exact installed
family member, empty storage/logs, fee accounting, and state-neutral system
predeploys are checked before Jaune replays the block. It checks nonpayability,
independently derived chain and domain words, no constructor
calls/logs/storage instructions, and six falsifiers. Blanc's
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

`canonicalDeploymentStep_establishes_root` is the transaction/block crossing:
from a valid configured base, strict `CanonicalBlock` evidence, the closed
type-2 envelope, and an actual `stateTransitionUsing` success, it reconstructs
the post-system prepared message rather than assuming it, proves the collision
branch and receipt success, preserves backing and zero flash debt across both
checked request-predeploy suffix calls, and derives the deployed valid context.
`DeploymentRoot.reachable_stable` then composes that root with the existing
configured-chain preservation theorem. The result is deliberately specific to
the named Prague-only anchor and does not turn the finite fixture into a proof.

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

## Contact

Blanc is maintained by one person, [skbaek](https://github.com/skbaek)
(<seulkeebaek@gmail.com>). There is no team behind it and no service-level
promise; expect a reply within about a week.

The most useful thing you can send is **a claim on this page, in a module
docstring, or on [the site](https://skbaek.github.io/blanc/) that outruns the
theorem behind it.** This repository is built around the discipline of never
saying more than has been proved, and an outside reader finding a place where
it slipped is the strongest available evidence that the discipline is real.
Open an issue; it will be treated as a defect, not a disagreement.

After that: a divergence from a deployed original that is missing from the
relevant `*_DEVIATIONS.md` registry, a gate that passes when it should fail, or
a source program whose compiled bytecode does not do what the source semantics
say. [`SECURITY.md`](SECURITY.md) has the full list and the private-report
address.

If you have a contract with an invariant worth proving and are wondering
whether this stack could reach it, that conversation is welcome — including
the answer "not yet, and here is what would have to exist first."
