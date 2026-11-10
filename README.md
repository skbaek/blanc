# Blanc: A Verification Stack for EVM Smart Contracts in Lean 4

[![CI](https://github.com/skbaek/blanc/actions/workflows/ci.yml/badge.svg)](https://github.com/skbaek/blanc/actions/workflows/ci.yml)

**[skbaek.github.io/blanc](https://skbaek.github.io/blanc/)** — the guided
tour: what Blanc proves about bytecode already deployed on mainnet, how, and on
which premises; the Blanc language and its contracts; and what none of it claims.
**[Jaune](https://github.com/skbaek/jaune)**
([site](https://skbaek.github.io/jaune/)) — the EVM semantics every theorem
here is stated against.

Blanc is a verification stack for EVM smart contracts, built in Lean 4 on Jaune's
executable EVM semantics. It proves theorems about Ethereum bytecode as it is
deployed — Curve 3pool and its 3Crv LP token, USDC, the Vyper nonreentrancy
pair (V+/V-) and the EIP-7002 system contract — with exact gas, liveness, and
no axioms beyond
Lean's three. The bytes are read from mainnet without trusting the compilers
that produced them; what is claimed about each artifact, and where, is mapped
in [`docs/DEPLOYED_BYTECODE_CLAIM_MAP.md`](docs/DEPLOYED_BYTECODE_CLAIM_MAP.md).
Curve 3pool, 3Crv, USDC and the Vyper pair are released: their proofs are at the
tags `release/<family>-20261108`, listed in [`scripts/live-set.toml`](scripts/live-set.toml).

The stack also offers the option of programming in Blanc's native language:
the EVM's own instructions, arranged by four constructors, with a compiler
whose correctness is a Lean theorem. Because every implementation choice stays
open, down to the instruction, it lets developers push performance
optimization, proof simplicity and customization as far as they choose.
Contracts formerly written in it are historical exhibits outside paper v2
(see the archive note below); the language and its compiler theorem remain
([the language](https://skbaek.github.io/blanc/language.html)).

Historical exhibits outside paper v2, including WETH9, Beacon deposit, Lido, Uniswap and Blanc-native programmes, are preserved in the [archived corpus](https://github.com/skbaek/blanc/blob/corpus-v1-20261105/docs/DEPLOYED_BYTECODE_CLAIM_MAP.md). The archive is outside the live corpus and is not promised to build against later revisions.
**A Blanc theorem is a statement about Jaune's modeled semantics, not a
deployment audit** — see
[`SECURITY.md`](SECURITY.md) before treating any result here as a safety claim
about anything on chain.

When a Blanc contract reimplements an existing one, what that port does and
does not claim — and the deviation-registry discipline that backs it — is
governed by [PORTING.md](PORTING.md).

## Building

The first checkout on a host may fetch the pinned dependency artifacts and
then build Blanc:

```
lake exe cache get
lake build
scripts/check-lake-artifact-cache.sh
scripts/check-gates.sh --certify-build
```

Blanc also enables Lake's local artifact cache. Later fresh worktrees normally
need only `lake build`: Lake restores immutable artifacts by build identity
while each worktree keeps its own `.lake`, traces, hashes, certificates,
reports, and gate state. Do not share or symlink a writable `.lake`, and do not
repeat `lake exe cache get` merely to reuse artifacts already present in the
local cache.

Before certifying a restored build, the integrity check above recomputes Lake's
own artifact hash for the cache and materialized outputs; ordinary restore,
`--no-build`, and `--rehash` do not authenticate those bytes. The check detects
accidental corruption and wrong-name restores, with collision resistance of
Lake's 64-bit non-cryptographic hash explicitly remaining inside the local
trust boundary. It does not authenticate Lake's separate input-hash-to-output
mapping files, and certification does not invoke it automatically; the two
commands above are therefore one required operator sequence within the
same-user trust boundary. If a restore is suspect, preserve the failure
evidence, run `lake cache clean`, and rebuild. Setting
`LAKE_ARTIFACT_CACHE=false` for that rebuild disables local artifact-cache
restore without changing the repository configuration.

Cache garbage collection is a coordinated maintenance operation. From a Creme
goal that holds the exclusive host semaphore, preview and then execute it with:

```
scripts/gc-lake-artifact-cache.py
scripts/gc-lake-artifact-cache.py --execute --ack-exclusive-semaphore
```

The collector keeps artifacts referenced by every live cache-participating
worktree, reports nonparticipants, and fails closed on participant state it
cannot interpret. `scripts/GATES.md` is the authoritative trust, recovery, and
verification contract.

Authors changing Python evidence scripts should use the shared hash, format,
fixture, and checkout primitives in [the evidence toolkit](docs/EVIDENCE_TOOLKIT.md).

Authoring tools (simp migration, discharge trace, census tools) and a tactic table are in
[the tools page](docs/TOOLS.md).

## Optional enhanced agent workflow

Agents start at [`AGENTS.md`](AGENTS.md), a task-to-file map.

Blanc is standalone: its pinned Jaune dependency is fetched by Lake, and Creme
is not a build dependency. For the optional shared Jaune/Blanc agent workflow,
clone the public Creme repository alongside Blanc (and Jaune when needed),
launch the agent client with Creme as its project directory, and follow
`../creme/docs/guides/execution.md` for host setup and coordination. Blanc's
repository-specific commands and pass criteria remain in `scripts/GATES.md`.

This repo contains the following files:

- [Basic.lean](Blanc/Basic.lean): Blanc's own prefix/split algebra over lists
  (`Split`, `Pref`, `Frel`) and the small tactic helpers built on it. The
  generic list, word and `Except`/`Option` lemmas that used to live here are
  now upstream in Jaune, where any client of Jaune gets them.
- [Semantics.lean](Blanc/Semantics.lean): Blanc's compiled-program language
  (`Func`, `Prog`, `Stack`) and its relations. The EVM-generic execution layer
  (the canonical `Exec` relation, its inversions and adequacy, derivations,
  settlement, chronology and message execution) is owned by Jaune
  (`Jaune.ExecFrame` … `Jaune.MessageExecution`) and imported here.
- [CommonCore.lean](Blanc/CommonCore.lean), [Tactics.lean](Blanc/Tactics.lean),
  and the [CommonProofs modules](Blanc/CommonProofs/): definitions and lemmas
  for writing and verifying Blanc programs, including the Blanc compiler's
  correctness proof and tactics for automating Blanc program verification.
  Import the specific common module needed for a proof.
- [ProofRecipeTactic.lean](Blanc/ProofRecipeTactic.lean): the unimported
  authoring leaf that joins `Tactics` with the generated recipe registry and
  provides `blanc_suggest` without putting registry churn on production import
  paths.
- [Ladder.lean](Blanc/Ladder.lean): the contract-generic verification ladder,
  including the `ContractSpec` record each contract instantiates and the
  dispatcher decomposition (`FuncSound`, `sound_of_dispatch`) that reduces a
  whole-contract obligation to one obligation per dispatch target. It is the
  `Prog.compile` instance of the same ladder over an arbitrary certified code
  image ([LadderSem.lean](Blanc/LadderSem.lean), `ContractSpecSem`); the
  vocabulary both share is in [LadderBase.lean](Blanc/LadderBase.lean).
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
  ever succeeds. At every external call the witness
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
- [`Blanc/Lift/`](Blanc/Lift/): kernel-checked lifts of bytecode already on
  mainnet — among them Curve's 3Crv token and 3pool, USDC's proxy and
  implementations, the EIP-7002 system contract, and the fixed and vulnerable
  Vyper pool pair (now at their release tags), plus token and attacker fixtures. The EIP-4788, EIP-2935 and
  EIP-7251 SystemExecution support groups are concrete dependencies
  of configured EIP histories, not standalone paper-v2 exhibits. The certificate registry
  [`scripts/lift/certificates.json`](scripts/lift/certificates.json) is the
  authoritative list of lifted inputs.
  [`docs/DEPLOYED_BYTECODE_CLAIM_MAP.md`](docs/DEPLOYED_BYTECODE_CLAIM_MAP.md)
  maps each claim to its theorem, premises and non-claims, and states the
  deployment caveats.
  How a deployed contract is lifted and certified:
  [`docs/LIFT_WORKFLOW.md`](docs/LIFT_WORKFLOW.md).

Historical exhibits outside paper v2, including WETH9, Beacon deposit, Lido, Uniswap and Blanc-native programmes, are preserved in the [archived corpus](https://github.com/skbaek/blanc/blob/corpus-v1-20261105/docs/DEPLOYED_BYTECODE_CLAIM_MAP.md). The archive is outside the live corpus and is not promised to build against later revisions.


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
binds every retained contract family.

The rule earns its keep as a diagnostic. When one contract needs something
another already defines, that is not a licence to import across; it is evidence
that the thing was never the property of whichever contract happened to define
it first. Rename it if its name says otherwise, then move it upstream into a
layer both contracts already import — `CommonCore.lean` for definitions,
the relevant `CommonProofs/` module for lemmas, `Ladder.lean` for generic verification
machinery.

A worked factoring example from the archive era (`balSum`, factored out of
a retired WETH module into `CommonCore.lean`) is preserved in the archived
corpus; the rule it illustrates is the sibling rule above, stated abstractly.

The rule is enforced, not merely documented:
[`scripts/check-layering.sh`](scripts/check-layering.sh) reads the actual Lean
module header, not physical lines. For Lean 4.32.1 it recognizes local imports
in the complete command shape `public? meta? import all? ident`, after the
optional bare `module` and `prelude` directives. The elaborating modifier cases
are plain `import`; with `module`, `public import`, `meta import`, `import all`,
`public meta import`, and `meta import all`. Identifiers may use quoted
components such as `«Main»` and Lean's unquoted letter-like Unicode characters;
whitespace and nested comments may occur between the pieces, an import may span
lines, and a trailing line comment is trivia.
`public`, `meta`, and `all` require a `module` header. `public import all` and
the reversed `meta public import` modifier order are rejected because Lean
rejects those combinations. A partial trailing dot
(`import Blanc.`) is an editor-completion parse shape, not an elaborating
import, so the gate rejects it closed as it does an unterminated header comment
or string.

The reader stops at the first non-header command. Thus an `import`-shaped line
in a declaration, string literal, or later comment is never mistaken for a
module dependency. It fails on a cross-contract import, on a shared module
importing a contract (the same break, other direction), and on any module
missing from its classification — so a new contract cannot escape the rule by
never being listed. Import recognition is category-agnostic: `imports_of`
returns a local-looking module name before, and without, consulting the
classification table, so a category added later receives the same complete
header reading. It needs no Lean toolchain and runs ahead of the build in CI;
[`scripts/check-layering-controls.py`](scripts/check-layering-controls.py)
separately pairs the accepted forms with real Lean elaboration.

### The composition stratum

Some theorems are genuinely about two contracts at once. Such a theorem
has no honest home in either family: putting it in one makes the other family's
name that family's property, and the sibling rule above rightly rejects both
directions.

So there is exactly one downstream place for it. `Blanc/Composition/*` is a
distinct **COMPOSITION** stratum, and the graph is one-way:

```
        roots (Blanc.lean, Main.lean)          aggregate everything
              ▲
        Blanc/Composition/*                    may name several families
              ▲                 ▲
   contract families      shared modules       siblings; neither sees composition
              ▲                 ▲
        shared modules                         upstream of every contract
```

* Every composition module declares its contract families with `COMPOSITION`.
  Its direct contract imports must belong to that declaration, and any imported
  composition must declare a subset of those families. Missing, empty, malformed
  or unknown family declarations fail closed. Shared-module imports remain allowed.
* No shared module and no contract module may import composition, and a
  composition module may not import a root. Roots aggregate composition; the
  dependency never runs back.
* The sibling rule is unchanged for contract modules: an ordinary
  contract-to-other-contract import is still rejected.

Roots are deliberately *not* the place for this. They are aggregation surfaces,
exempt from the import checks by construction, so a cross-family theorem hidden
in a root would be invisible to the gate — which is precisely why composition
gets its own classified, checked category instead.

Retained compositions include Curve 3pool with 3Crv, USDC's own histories (both at their release tags), and configured EIP histories, within the scope stated by the claim map.

## Proof recipe lookup

Before beginning a manual multi-step walk or inversion, consult the generated
[proof recipe index](docs/PROOF_RECIPES.md) or run the read-only
`blanc_suggest` tactic at the goal. The index and the tactic's lookup table are
both generated from `scripts/proof-recipes.toml`; edit that registry and
regenerate the surfaces rather than editing either generated file by hand.
`blanc_suggest` prints each matching recipe's validated registered symbols as
well as its route and boundary.

Every registry module name is validated as raw text before a path object is
constructed. The accepted language begins with the literal `Blanc/`, ends with
the literal `.lean`, and has only nonempty NFC Unicode-identifier components;
empty, `.`, `..`, absolute, trailing-separator, backslash, whitespace-alias,
and non-NFC spellings are rejected. Dereferencing then requires every directory
entry to have the exact requested spelling, forbids file and component
symlinks, forbids multiply linked files, and verifies canonical containment
under the repository root. This deliberately rejects wrong-case and Unicode
normalization aliases on hosts that resolve them. The checked census in
`scripts/module-path-dereference-census.json` binds that policy to the module
size walk, both proof-recipe corpus consumers, Git/import-derived source reads,
all registry module/owner/example reads, and both generated-output bindings; a
zero-module walk fails closed.

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

The examples and measurements in this section are historical methodology
evidence from the named dates and source revisions. Retired contract names and
source paths identify the archived corpus, not live paper-v2 modules. Their
measured populations, timings and failed alternatives are preserved to explain
the conventions; they are not current corpus counts or performance claims.

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

The linked catalogue joined that historical disposition evidence to the 94
scope identities current at that measurement and distinguished exact adjacent
boundaries from the weaker retained-justified and reopen-triggered cases.
Those 94 identities are not a census of the current paper-v2 tree.

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
stops being free. Rename on the way into the substrate. This applies the
repository's [sibling-module discipline](#module-hierarchy-contracts-are-siblings)
within a contract — a name claiming one case while serving all of them is
evidence that the declaration belongs upstream.

**Re-check reachability after every deduplication.** Replacing several parallel
walks with one generic walk leaves the superseded intermediates behind, and an
unused `private` theorem produces no warning whatsoever. A reachability pass
over this module found 253 such lines, still being elaborated on every build.

## Verification status

**What you are trusting.** Blanc's trusted base is Jaune's plus three
additions, so the base document is Jaune's
[`TRUSTED.md`](https://github.com/skbaek/jaune/blob/c73f7ead1b104bf1ce36f9744138399de8385cbe/TRUSTED.md) — the
kernel and pins, what is deliberately absent from the library and which gate
enforces each absence, the known exceptions, and where the line between testing
and proof falls. It is not duplicated here. Blanc adds exactly:

1. **the pinned Jaune revision** below — trusting a Blanc theorem is trusting
   that specific Jaune, not the sibling checkout on your disk;
2. **the axiom audit** below, which is stricter than Jaune's own gates: one
   from-scratch walk over every constant of the library fails on any axiom
   outside `propext`, `Classical.choice` and `Quot.sound`, and the leaf search
   finds the leaf results — theorems no other
   theorem uses — that this one walk covers.
   Run `scripts/check.sh --no-build`; its leaf-results summary belongs to
   the source identity printed by `git rev-parse HEAD`;
3. **Blanc's own source**, guarded by
   [`scripts/check-trust-surface.sh`](scripts/check-trust-surface.sh). The gate
   traverses the exact transitive local import closure of `Blanc.lean` and
   fail-closed checks `sorry`, bespoke `axiom`, `opaque`, `@[extern]`,
   `implemented_by`, `native_decide`, object-level `partial def`, and
   `dbg_trace`. Its current occurrences are exact reviewed rows
   (the gate is the authority). Unimported Lean helpers and generators are
   outside this library-root gate; importing one immediately brings it into
   scope. A non-terminating or chatty tactic can fail to produce a proof, but
   any proof it does produce is still checked by the kernel, so none of these
   proof-automation rows enlarges the trusted base.

As in Jaune's document, this section is about whether the proofs are sound, not
about whether they are the right theorems. Read the statement in the file
the claim map cites rather than inferring it from a theorem's name.

Blanc builds against a **pinned revision** of
[Jaune](https://github.com/skbaek/jaune) — `require jaune from git … @ c73f7ead…`
in [`lakefile.lean`](lakefile.lean) — so a fresh clone builds reproducibly
without a sibling checkout, and bumping Jaune is a reviewed one-line change.

CI builds the library and runs an
**axiom audit** ([`scripts/AxiomCheck.lean`](scripts/AxiomCheck.lean)): one
union walk over every constant of the library, then a leaf search that finds
the leaf results — theorems no other theorem
uses, each covered by that walk. The leaf search is the authority on
membership and its number is the generated
[`scripts/leaf-count.json`](scripts/leaf-count.json), never edited by hand; run
`scripts/check.sh --no-build` and bind its verdict to
`git rev-parse HEAD`. The review ledger separately records the last review;
the audit reports new or changed leaves. The separate `scripts/check-claims.sh` Lean-checks the exact statements of the live paper-v2 families mapped in [`docs/DEPLOYED_BYTECODE_CLAIM_MAP.md`](docs/DEPLOYED_BYTECODE_CLAIM_MAP.md); the axiom audit itself checks dependency closures, not theorem statements.

Historical exhibits outside paper v2, including WETH9, Beacon deposit, Lido, Uniswap and Blanc-native programmes, are preserved in the [archived corpus](https://github.com/skbaek/blanc/blob/corpus-v1-20261105/docs/DEPLOYED_BYTECODE_CLAIM_MAP.md). The archive is outside the live corpus and is not promised to build against later revisions.

Every constant of the library is covered by one union walk in
`scripts/check.sh`: it fails on any axiom other than `propext`,
`Classical.choice` and `Quot.sound` that any declaration reaches — in
particular on `sorryAx`, `ofReduceBool`, `ofReduceNat` and the `native_decide`
and `bv_decide` auxiliary axioms — so no `sorry` and no `native_decide`-style
axiom is in the trusted path of these results. There is no list of audited
theorems to keep in step: the walk's population is what
[`scripts/AxiomCheck.lean`](scripts/AxiomCheck.lean) imports, and the audit
refuses a Blanc module that its imports do not reach. A smaller axiom set is
checked only where a register or a gate states one — `0` such claims, the
`#expect_axioms` rows of `AxiomCheck.lean`, each checked in both directions.

## Archived fixture and assurance exhibits

Historical exhibits outside paper v2, including WETH9, Beacon deposit, Lido, Uniswap and Blanc-native programmes, are preserved in the [archived corpus](https://github.com/skbaek/blanc/blob/corpus-v1-20261105/docs/DEPLOYED_BYTECODE_CLAIM_MAP.md). The archive is outside the live corpus and is not promised to build against later revisions.

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
relevant live register or claim map, a gate that passes when it should fail, or
a source program whose compiled bytecode does not do what the source semantics
say. [`SECURITY.md`](SECURITY.md) has the full list and the private-report
address.

If you have a contract with an invariant worth proving and are wondering
whether this stack could reach it, that conversation is welcome — including
the answer "not yet, and here is what would have to exist first."
