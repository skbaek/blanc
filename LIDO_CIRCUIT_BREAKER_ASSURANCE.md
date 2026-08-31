# Lido CircuitBreaker — end-to-end assurance register

**Status:** authoritative claim map for Blanc's Lido CircuitBreaker port.
**Reconciled:** 2026-08-27.
**Machine-checked by:** `scripts/check-lido-circuit-breaker-assurance.sh`.

This register maps every assurance claim Blanc makes about its Lido
CircuitBreaker port onto the exact declarations that carry it, the premises
those declarations require, the axioms they depend on, the gate that owns
them, the differential channel that independently corroborates them, and — in
every row, without exception — what the row does **not** claim.

It exists because a proof corpus is not an argument until someone can say, for
each sentence a reader might quote, which theorem makes it true and where that
theorem stops. The plain-language companion
(`lido-circuit-breaker-assurance-companion.md`, in the plans repository) is the
same material written for owners; where the two disagree, this register wins,
and where this register disagrees with a Lean statement, an axiom inventory, or
a gate verdict, **the evidence wins and the prose is narrowed**.

## How to read a row

Every row is a `####` block carrying seven labelled fields:

| Field | Meaning |
|---|---|
| **Declarations** | The exact declaration(s) the claim rests on. Every name here is inside the pin table of the authority this row's **Gate** field names — either the repository axiom audit (`scripts/AxiomCheck.lean`) or the family gate's own `#print axioms` probe — so every name is one the kernel has checked and one whose axiom set a gate pins. Blanc has several such authorities and they do not overlap; a name in one is usually not in the others. |
| **Premises** | The load-bearing hypotheses. A row whose premises are unstated is a row that overclaims, so "none beyond the statement" is written out rather than left blank. |
| **Axioms** | The exact axiom set the declaration depends on. `propext`, `Classical.choice`, `Quot.sound` are the three standard logical axioms the rest of the repository uses; anything else would appear here. |
| **Gate** | The gate that owns the row's evidence and would fail if it moved. |
| **Differential channel** | The independent Solidity-oracle case that corroborates the row, or the explicit words `no direct oracle channel` where none exists. The differential campaign is finite evidence and is **never** a Lean premise. |
| **Non-claims** | What this row does not say. These travel with the claims; a row quoted without its non-claims is a row misquoted. |
| **Source** | Where each field came from: a completion report line, a Lean source line, or both. |

## What this register is checked against

The verifier is static and fail-closed. It reads this file and requires that:

1. every row carries all seven fields, and the pillar and total row counts match
   the numbers the gate pins — a row reworded out of the gate's sight fails
   rather than passing silently;
2. every name in a **Declarations** field is **pinned by an authority that the
   row's own `Gate` field names**. There are several such authorities and they
   do not overlap: the repository axiom audit (`scripts/AxiomCheck.lean` with
   the expectation table in `scripts/check.sh`), and the per-family pin tables
   inside the access, enumeration, registry, and history gates. A name pinned
   by a different authority than the row names, or pinned by none at all, is a
   failure — so the `Gate` field is load-bearing rather than decorative;
3. every **Axioms** field equals, exactly and order-insensitively, that
   authority's expectation for that name, with the single word `none` meaning
   "depends on no axioms at all" in both directions. Where two authorities pin
   the same name, they must agree with each other, and a disagreement is
   reported as a repository inconsistency rather than resolved in either
   direction;
4. every **Gate** path exists and is registered in `scripts/GATES.md`; and
5. every load-bearing non-claim phrase still appears somewhere in this file.

Channels 2 and 3 are static comparisons against expectations that the
authorities themselves verify against Lean by elaborating a `#print axioms`
probe — so this register's axiom column is Lean-checked transitively, through
gates whose own verdicts are recorded on the completion candidate. Running this
gate with `--probe` closes that loop directly: it regenerates a `#print axioms`
file from this register's own citations and elaborates it.

A row may legitimately have **no** audited declaration behind it — the emitted
error table and the finite differential matrix are owned by gates, not by
theorems. Such a row says so in its **Declarations** field in exactly those
words, carries `not applicable` axioms, and is counted: the number of
gate-owned rows is pinned too, so a normal row cannot be quietly converted into
one to dodge the axiom check.

## The claim, stated once

> Blanc's faithful CircuitBreaker port proves a combined Registry invariant
> whose corollaries match the three obligations left unresolved in the cited
> April 2026 industrial campaign on blob-identical Registry source; proves
> compiled access-control, temporal-authority, and hostile-world reentrancy
> properties under the stated EVM and trust assumptions; and roots the
> arbitrary-history Registry-integrity family in one exact official direct
> deployment.

Every clause of that sentence is a row below, with one deliberate exception:
the **blob identity across revisions** is not a row, because no gate on this
repository witnesses it. It is recorded as a named gap in the Cyfrin section.
Nothing else in this repository is licensed to say more.

## The trust boundary, stated once

Three assumptions hold up everything below, and none of them is hidden.

1. **Jaune's EVM semantics are the ground truth.** Every theorem is about
   Blanc's compiled bytecode executing under Jaune, not about a model of it and
   not about Lido's deployed Solidity.
2. **A pause target is not assumed honest.** The hostile-world family
   quantifies over arbitrary callee bytecode. What it proves is what the
   CircuitBreaker *observed and did* — never that the target is really paused.
3. **The admin is privileged, and one family says so.** Registry coherence
   across histories permits admin interference by returning an existentially
   updated witness. The exact final state of one successful pause does not, and
   names `PauseSuccessNoninterference` as an explicit assumption rather than
   deriving it.

## What is deliberately not claimed, in one place

These are load-bearing. Each is also repeated in the rows it constrains,
because a non-claim that lives only in a summary is one edit away from being
lost.

- **No deployed-bytecode claim.** Nothing here verifies the Solidity at
  `0x6019CB557978296BA3C08a7B73225C0975DFB2F7`. The mainnet address,
  deployment transaction, and block are provenance identifiers only.
- **No target-truth claim.** "The target returned a canonical `true`" is an
  observation about returndata. It is not "the target is paused".
- **No universal gas claim.** The gas evidence is a finite 175-row /
  464-boundary vector against a pinned oracle. Blanc's mandatory `.branch`
  control-flow representation may carry a small intrinsic dispatch overhead.
- **No parameter-generic deployment root.** The root is one exact official
  direct creation: frozen official constructor arguments and full CREATE
  input, zero value, one collision-free top-level creation, a strict singleton
  type-2 Prague block. No co-block, clone, factory, proxy, or CREATE2 path, no
  nonzero endowment, no arbitrary fork.
- **No signature, inclusion, or historical-mainnet claim.** The root theorem
  constructs and authenticates no signing key or signature and proves no
  historical inclusion.
- **The history witness is existential, not the same list.** An admin
  re-entering during a callback may legitimately register a pauser, so the
  guarantee is that *some* coherent registration list describes the storage.
- **Reachability carries a wei bound.** The chain relation admits a block only
  while total ether across all accounts plus that block's withdrawals stays
  below `2 ^ 256`. Histories crossing that ceiling are simply not among those
  quantified over. The Registry invariant never consults the figure; the
  restriction is inherited from the shared chain model.
- **No liveness.** Nothing here says the contract can be paused, only what
  happens when it is.
- **No callback-time count/expiry coherence.** Mid-call, after the target is
  unregistered and before the callback returns, the count is already zero and
  the expiry is stale. That is real source behaviour, and no theorem claims
  otherwise.
- **Finite replay and differential evidence are never Lean premises.** The
  EELS/Jaune replay and the Solidity oracle corroborate; they do not support.
- **The synthetic stable world receives no deployment credit.** The
  hand-built satisfying state is an anti-vacuity exhibit. It is not a
  deployment and must never be reported as one.
- **No source-level history trace.** The history family produces reachable-state
  consequences, not a step-by-step source narrative.
- **No universal closure from the finite differential matrix.**

## The Cyfrin comparison, stated exactly

Cyfrin's April 2026 campaign (Certora Prover 8.8.1) reports 38 of 41 specified
properties verified and three `registerPauser` obligations unresolved:
membership equivalence between the pauser mapping and the one-based index,
clean state after removal, and global conservation between per-pauser counts
and registry length. The report cites circular inductive dependencies, four
mutation modes, and swap-and-pop as the difficulty.

The exact `Registry.sol` Git blob is identical across the mitigation revision,
the deployment-source revision, and v1.0.0; the enclosing `CircuitBreaker.sol`
changed before deployment.

**Named gap, stated because this premise is load-bearing.** That blob identity
is what makes the comparison about the same artifact, and **no gate here
witnesses it.** The reference lock pins exactly one `Registry.sol` blob — the
v1.0.0 one — and no checker compares blobs across revisions. The cross-revision
identity rests on the cited report and the programme's source anchor, not on
anything this repository verifies. A reader who needs it verified must check
Lido's Git history directly. So the honest statement is:

> A named industrial campaign left three coupled Registry preservation
> obligations open on Registry source blob-identical across those three
> revisions. Blanc closed those **obligation shapes** for its own faithful
> port, by making all three corollaries of one combined invariant designed
> together with the representation.

It is **not** "the deployed contract is only 38/41 verified", and it is **not**
"Certora cannot prove this". A tool given a different problem — recovering a
property from an existing artifact rather than designing property and
representation together — is not a tool that failed.

---

## Pillar — Registry integrity

The combined invariant is `RegistryWitness` (`Blanc/LidoCircuitBreakerRegistryModel.lean`):
a `Prop`-valued structure over a logical storage and an entry list, instantiated
at the contract's own concrete storage through the single projection
`logicalStorageOfStor s = { read := s.get }`. It ties array membership,
assignment, one-based reverse index, per-pauser counts, and array length into
one finite relation, and the three obligations the Cyfrin campaign left open
fall out of it as corollaries rather than being assumed alongside it. It is a
definition, so it has no axiom set of its own; it appears in the **Premises**
of the rows below.

Two scope facts govern this whole pillar and are repeated in the rows they
constrain. First, these rows are about **single operations**: the shared
`setPauser` kernel, the register continuation, the pause **pre-yield** boundary,
and settled-error restoration. Coherence *across whole histories* — including
terminal successful pause, the configuration setters, and `heartbeat` — is the
deployment-and-history pillar's `HIST` rows, not these. Second, the tagged
storage projection is contract-local; it assumes neither global Keccak
injectivity nor raw-slot/storage-root equality.

#### REG-1 — Tagged slot arithmetic is injective on payloads and separating across regions, with no wrap below `2 ^ 256`, and the entry list is bounded by the address domain rather than by an assumed capacity field

- **Declarations:** `Blanc.LidoCircuitBreaker.slot_toNat_of_region_payload_lt`, `Blanc.LidoCircuitBreaker.slot_injective_payload`, `Blanc.LidoCircuitBreaker.slot_ne_of_region_ne`, `Blanc.LidoCircuitBreaker.RegistryWitness.entries_length_le`
- **Premises:** `region < 16` and `payload < 2 ^ 252`; canonical address words contribute payloads below `2 ^ 160`. `entries_length_le` additionally needs target-noduplication from the witness.
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **Gate:** `scripts/check-lido-circuit-breaker-registry.sh`
- **Differential channel:** no direct oracle channel
- **Non-claims:** derives `entries.length + 1 ≤ 2 ^ 160` from the address domain. It does not assert a contract-chosen cap, and no public premise imposes one — `getPausables()` remains a parametric dynamic `address[]`.
- **Source:** `reports/lido-circuit-breaker-registry-integrity-completion.md:373-390`; `Blanc/LidoCircuitBreakerRegistry.lean:22,59,72,89`

#### REG-2 — The executable source trace of `setPauser` refines the pure list model: the trace's post-entries are exactly `setPauser entries target newPauser`

- **Declarations:** `Blanc.LidoCircuitBreaker.setPauser_sourceTrace_refines_model`
- **Premises:** the target-zero disposition `htarget0`, and `htrace : setPauserSourceTrace … = some trace`.
- **Axioms:** `propext`, `Quot.sound`
- **Gate:** `scripts/check-lido-circuit-breaker-registry.sh`
- **Differential channel:** no direct oracle channel
- **Non-claims:** pure-model and source-trace altitude only. It establishes no EVM run; the compiled bridge is REG-4.
- **Source:** `reports/lido-circuit-breaker-registry-integrity-completion.md:45,405`; `Blanc/LidoCircuitBreakerRegistry.lean:3405`

#### REG-3 — Replaying every chronological Registry write of a valid source trace onto concrete owner storage re-establishes the witness at the post-trace entry list

- **Declarations:** `Blanc.LidoCircuitBreaker.RegistryWitness.applySetPauserSourceTrace`
- **Premises:** an entry-state `RegistryWitness` over `logicalStorageOfStor s`; `canonicalAddress target`; `canonicalAddress newPauser`; and `htrace : setPauserSourceTrace entries target newPauser = some trace`. **The premise names the trace, not the post-witness** — there is no result-equivalent hypothesis.
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **Gate:** `scripts/check-lido-circuit-breaker-registry.sh`
- **Differential channel:** `register-fresh#1:action`, `register-distinct-pauser#2:action`, `register-same-pauser#2:action`, `register-absent-to-zero#1:action`, `remove-only#2:action`, `remove-first#4:action`, `remove-middle#4:action`, `remove-last#4:action`, `moved-element-followup-replace#5:action`, `moved-element-followup-remove#5:action`
- **Non-claims:** the witness holds **at the stable boundary after all writes replay**, not at intermediate stores. Source-trace altitude, not compiled execution.
- **Source:** `reports/lido-circuit-breaker-registry-integrity-completion.md:88-104,417-424`; `Blanc/LidoCircuitBreakerRegistry.lean:3462`

#### REG-4 — A successful actual execution of the emitted shared `setPauser` kernel *derives* its source trace, and exposes the post-Registry intermediate state and continuation run

- **Declarations:** `Blanc.LidoCircuitBreaker.setPauserKernel_exec_extracts_sourceTrace`, `Blanc.LidoCircuitBreaker.setPauserKernel_run_of_exec`, `Blanc.LidoCircuitBreaker.setPauser_run_extracts_sourceTrace`
- **Premises:** owner and code-address agreement, the exact production bytes `sevm.code.toList = lidoCircuitBreakerCode dp`, the production table slice at `setPauserSlot`, `Mem.Wf` and `Mem.Reads`, three calldata-word reads, an entry-state witness, two `canonicalAddress` facts, and a successful `Exec`. **There is no trace or other result-equivalent premise:** an earlier version that accepted one was rejected in review and repaired.
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **Gate:** `scripts/check-lido-circuit-breaker-registry.sh`
- **Differential channel:** `register-fresh#1:action`
- **Non-claims:** success inversion only. No error taxonomy, no exhaustiveness, no termination claim, and no all-message success theorem.
- **Source:** `reports/lido-circuit-breaker-registry-integrity-completion.md:46,110-160`; `Blanc/LidoCircuitBreakerRegistry.lean:17170,17088,3509`

#### REG-5 — For a zero target word the compiled program constructs the exact `PausableZero` revert, and no instruction occurrence in that derivation is an `SSTORE`

- **Declarations:** `Blanc.LidoCircuitBreaker.setPauser_zero_runCompiledTo_pausableZero_noRegistryWrite`
- **Premises:** the complete resource and code domain — owner, code address, exact bytes, table slice, stack, `Mem.Wf`, `Mem.Reads`, the target read, `canonicalAddress target`, `target = 0`, `pre.memory.size % 32 = 0`, an exact gas equation, and `pre.stack.length < 1023`.
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **Gate:** `scripts/check-lido-circuit-breaker-registry.sh`
- **Differential channel:** `register-zero-target-before-write#1:action`
- **Non-claims:** a **construction** over the stated domain, not a converse use of `RunCompiledTo`, and not error exhaustiveness. The guard's ordering is what is at stake: a compiled mutant that writes the assignment slot before the zero check is executed and refuted by `targetZeroGuardAfterAssignment_compiled_rejected`.
- **Source:** `reports/lido-circuit-breaker-registry-integrity-completion.md:162-207`; `Blanc/LidoCircuitBreakerRegistry.lean:17025`

#### REG-6 — Every raw outcome of the `registerAfterSet` continuation preserves the Registry slots, and a successful register kernel execution reaches the source-model post-witness

- **Declarations:** `Blanc.LidoCircuitBreaker.registerAfterSet_runCompiledTo_preserves_registry`, `Blanc.LidoCircuitBreaker.registerPauser_kernel_exec_preserves_registry`
- **Premises:** memory well-formedness and reads, previous- and new-pauser word reads, owner, two `canonicalAddress` facts, an entry-state witness, the arithmetic-panic table slot, and `Func.RunCompiledTo fs sevm pre registerAfterSet out`. The caller instantiation additionally fixes the continuation read to zero.
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **Gate:** `scripts/check-lido-circuit-breaker-registry.sh`
- **Differential channel:** `register-fresh#1:action`, `register-absent-to-zero#1:action`, `register-same-pauser#2:action`
- **Non-claims:** the conclusion is an `Execution.Rel` and so covers **every** raw outcome, not only success — but it is a raw-frame, pre-settlement fact.
- **Source:** `reports/lido-circuit-breaker-registry-integrity-completion.md:47,209-238,250-269`; `Blanc/LidoCircuitBreakerRegistry.lean:5065,17239`

#### REG-7 — A successful pause kernel execution reaches `pauseAfterSet` at a state where the target's assignment and index slots are both zero and the target is absent from the post-entry list

- **Declarations:** `Blanc.LidoCircuitBreaker.pause_kernel_exec_reaches_pauseAfterSet`
- **Premises:** REG-4's premise set, plus a zero new-pauser read and a nonzero continuation word.
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **Gate:** `scripts/check-lido-circuit-breaker-registry.sh`
- **Differential channel:** `pause-eoa#2:action`
- **Non-claims:** **deliberately a pre-yield boundary.** The theorem stops before the target receives control. It is not a terminal successful-pause final state and carries no descendant or callback noninterference.
- **Source:** `reports/lido-circuit-breaker-registry-integrity-completion.md:272-317`; `Blanc/LidoCircuitBreakerRegistry.lean:17296`

#### REG-8 — An exact direct register or pause message that settles with an error restores the entry-state Registry witness, even when raw Registry `SSTORE`s really occurred inside the frame

- **Declarations:** `Blanc.LidoCircuitBreaker.registerPauser_settled_error_restores_registry`, `Blanc.LidoCircuitBreaker.pause_settled_error_restores_registry`, `Blanc.LidoCircuitBreaker.pause_direct_postWrite_revert_settles_and_restores_registry`
- **Premises:** `ProcessMessage msg slot (.ok post)` with `post.error.isSome`, and an entry-state witness at the settled owner storage. The two caller wrappers add the exact direct-instance target, current target, code address, production bytes, zero value, canonical calldata, and canonical-address hypotheses. The underlying rollback fact is `Blanc.ProcessMessage.rollback_of_error`, itself audited at `scripts/AxiomCheck.lean:249`.
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **Gate:** `scripts/check-lido-circuit-breaker-registry.sh`
- **Differential channel:** `pause-eoa#2:action`
- **Non-claims:** settlement-frame restoration only. Not an error taxonomy, and not a claim about arbitrary descendant frames.
- **Source:** `reports/lido-circuit-breaker-registry-integrity-completion.md:240-248,409-413,426-434`; `Blanc/LidoCircuitBreakerRegistry.lean:5120,5141,15980`

#### REG-9 — Cyfrin CB-3a: at any witness-carrying owner storage, a canonical target has a nonzero assignment iff a nonzero one-based index iff it occurs in the array, and a found entry's index is the unique array position holding it

- **Declarations:** `Blanc.LidoCircuitBreaker.membershipEquivalence_registerPauser`
- **Premises:** a `RegistryWitness` over the owner's concrete storage, and `canonicalAddress target`. **Nothing else — in particular no execution premise.**
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **Gate:** `scripts/check-lido-circuit-breaker-registry.sh`
- **Differential channel:** `register-fresh#1:action`, `remove-first#4:action`, `remove-middle#4:action`, `remove-last#4:action`
- **Non-claims:** **derived from the combined invariant, not from any run.** Despite the `_registerPauser` suffix the statement mentions no `registerPauser` execution; it becomes an execution postcondition only in composition with REG-4, REG-6, and REG-8. It is not a reproduction of the Certora harness or CVL rules, which are recorded as unavailable evidence.
- **Source:** `reports/lido-circuit-breaker-registry-integrity-completion.md:320-337,365-368`; `Blanc/LidoCircuitBreakerRegistry.lean:17389`

#### REG-10 — Cyfrin CB-6a: after replaying a removal trace's writes, both lookup slots and the dead array tail are clear and the swap-and-pop moved element's index is repaired

- **Declarations:** `Blanc.LidoCircuitBreaker.cleanStateAfterRemoval_registerPauser`
- **Premises:** an entry-state `RegistryWitness`, `nonzeroCanonicalAddress target`, and `setPauserSourceTrace entries target 0 = some trace`.
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **Gate:** `scripts/check-lido-circuit-breaker-registry.sh`
- **Differential channel:** `remove-only#2:action`, `remove-first#4:action`, `remove-middle#4:action`, `remove-last#4:action`, `moved-element-followup-remove#5:action`, `register-absent-to-zero#1:action`
- **Non-claims:** stated over the replayed writes — **source-trace altitude, not compiled execution.** The compiled bridge is REG-4 and REG-7, not this theorem. In the absent-target branch it asserts only that the append-hole slot is zero.
- **Source:** `reports/lido-circuit-breaker-registry-integrity-completion.md:339-359`; `Blanc/LidoCircuitBreakerRegistry.lean:17478`

#### REG-11 — Cyfrin CB-8a: every canonical pauser's stored count equals its multiplicity in the entry list, the zero-address count is zero, and the stored counts sum to the registry length

- **Declarations:** `Blanc.LidoCircuitBreaker.globalCountConservation_registerPauser`
- **Premises:** a `RegistryWitness` over the owner's concrete storage. Nothing else.
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **Gate:** `scripts/check-lido-circuit-breaker-registry.sh`
- **Differential channel:** `moved-element-followup-replace#5:action`
- **Non-claims:** the sum is over the pausers **actually present** in the entry list, not over the address space. Invariant-level, not execution-level. Conservation follows from finite multiset cardinality; it is not a separately assumed invariant, which is precisely what breaks the circular dependency the campaign reported.
- **Source:** `reports/lido-circuit-breaker-registry-integrity-completion.md:353-364,399-401`; `Blanc/LidoCircuitBreakerRegistry.lean:17654`

#### REG-12 — The empty registry satisfies the combined invariant

- **Declarations:** `Blanc.LidoCircuitBreaker.emptyWitness`
- **Premises:** none beyond the statement.
- **Axioms:** `propext`, `Quot.sound`
- **Gate:** `scripts/check-lido-circuit-breaker-registry.sh`, `scripts/check.sh`
- **Differential channel:** no direct oracle channel
- **Non-claims:** an inhabitation exhibit that keeps the invariant from being vacuous. It is not a deployment and confers no deployment credit.
- **Source:** `Blanc/LidoCircuitBreakerRegistryModel.lean`; axiom pin in `scripts/check.sh`

---

## Pillar — ABI and observability

One narrowing governs this pillar and is stated here so no row has to carry it
alone. The programme's intended property is that *every* public selector, view,
custom error, and event behaves compatibly. **Only the enumeration half of that
is a theorem quantified over arbitrary length.** The rest — dispatcher topology,
the error table, decoding, dirty address words, malformed and short calldata — is
established by byte-level gates and a finite frozen differential matrix. That is
strong evidence and it is not a universal ABI-compatibility theorem, and this
register never lets the pillar's name imply otherwise.

#### ABI-1 — For every finite entry list, with no contract-chosen cap, a well-formed `getPausables()` run on the exact emitted runtime returns the canonical dynamic address array in stored order

- **Declarations:** `Blanc.LidoCircuitBreaker.getPausables_runCompiled`
- **Premises:** a four-byte calldata length, zero value, the `getPausables` selector, code-address agreement, the exact production bytes, a `RegistryWitness`, and — load-bearing — that every enumeration storage key is already in `accessedStorageKeys` (warm), starting from a state whose gas is the exact list-scaled budget.
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **Gate:** `scripts/check-lido-circuit-breaker-enumeration.sh`
- **Differential channel:** `view-enumeration-empty#1:action`, `enumeration-singleton#2:action`, `enumeration-64-targets#65:action`
- **Non-claims:** arbitrary **length**, not arbitrary **conditions** — the warm-key and exact-gas premises are load-bearing, and a cold-storage or under-gassed run is outside the statement. It constructs one successful finite run; it classifies no failure mode, says nothing about malformed or short calldata, and asserts no real-block admission.
- **Source:** `reports/lido-circuit-breaker-enumeration-observability-completion.md:60,88-101,117-121`; `Blanc/LidoCircuitBreakerEnumeration.lean:1082`

#### ABI-2 — No instruction occurrence below the `getPausables` source cursor is an `SSTORE`, on arbitrary outcomes

- **Declarations:** `Blanc.LidoCircuitBreaker.getPausables_noSstore_occurrence`, `Blanc.LidoCircuitBreaker.enumeration_writing_mutant_rejected`
- **Premises:** an exact source cursor, the exact compiled runtime, the enumeration component certificate, and an owned parent prefix.
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **Gate:** `scripts/check-lido-circuit-breaker-enumeration.sh`, `scripts/check.sh`
- **Differential channel:** no direct oracle channel
- **Non-claims:** excludes **same-frame `SSTORE` occurrences only**. By itself it says nothing about `TSTORE`, logs, balance or code effects, child frames, termination, or out-of-gas. World and log silence on the successful path comes from ABI-3's constructed run, not from this theorem.
- **Source:** `reports/lido-circuit-breaker-enumeration-observability-completion.md:61,122-124`; `Blanc/LidoCircuitBreakerEnumeration.lean:1196`, `Blanc/LidoCircuitBreaker.lean:743`

#### ABI-3 — The three read views agree with one another and with the registry snapshot they read

- **Declarations:** `Blanc.LidoCircuitBreaker.registryViews_coherent`
- **Premises:** owner agreement across the three execution states, calldata-length guards on both scalar views, exact argument words, two `canonicalAddress` facts, a `RegistryWitness`, the enumeration warm keys, two scalar warm keys, and the enumeration loop's table slot.
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **Gate:** `scripts/check-lido-circuit-breaker-enumeration.sh`
- **Differential channel:** `view-get-pauser#1:action`, `view-get-count#1:action`, `view-enumeration-empty#1:action`
- **Non-claims:** three named **body** runs against one snapshot. Not a dispatcher-level or transaction-level statement.
- **Source:** `reports/lido-circuit-breaker-enumeration-observability-completion.md:62`; `Blanc/LidoCircuitBreakerEnumeration.lean:1456`

#### ABI-4 — The executable dispatcher's selector list is definitionally the contract's own ABI metadata list

- **Declarations:** `Blanc.LidoCircuitBreaker.funcs_selectors_eq_runtimeEndpoints`
- **Premises:** none beyond the statement. The companion sortedness fact `funcs_sorted` is a `decide +kernel` result outside the axiom audit and is therefore cited here as context, not as a declaration of this row.
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **Gate:** `scripts/check-lido-circuit-breaker-dispatchers.sh`, `scripts/check.sh`
- **Differential channel:** the full 175-row manifest; the differential gate covers all 17 selectors plus the constructor
- **Non-claims:** **selector-list identity, not behavioural compatibility.** It says nothing about decoding, dirty address words, or malformed calldata.
- **Source:** `scripts/GATES.md`; `Blanc/LidoCircuitBreaker.lean:479`

#### ABI-5 — The emitted runtime's error table is an instruction-aligned table whose compact selector reverters are independently reconstructed from the locked ABI

- **Declarations:** no audited declaration — gate-owned row
- **Premises:** the locked ABI reference and the emitted runtime bytes. The slot-binding theorems `runtime_emptyRevertSlot`, `runtime_pauseFailedErrorSlot`, and `runtime_bubbleRevertSlot` exist in the tree but are outside the axiom audit, so they are named here as context rather than cited as this row's declarations.
- **Axioms:** not applicable
- **Gate:** `scripts/check-lido-circuit-breaker-runtime-errors.sh`
- **Differential channel:** the differential matrix's constructor error and precedence cases, plus `scripts/check-error-data.sh`'s exact reason payloads
- **Non-claims:** a **byte and table gate**, not a theorem that every reachable error path emits the compatible payload.
- **Source:** `scripts/GATES.md`; `Blanc/LidoCircuitBreakerObservation.lean:811,817`

#### ABI-6 — Compatible behaviour of the whole public surface is established by a finite frozen matrix, not by a universally quantified theorem

- **Declarations:** no audited declaration — gate-owned row
- **Premises:** the pinned EELS oracle at its frozen commit, the locked Solidity artifact worlds, and the frozen manifest.
- **Axioms:** not applicable
- **Gate:** `scripts/check-lido-circuit-breaker-differential.sh`
- **Differential channel:** all 175 manifest rows, spanning 17 selectors plus the constructor, 144 causal history transactions, 464 resource boundaries, and 82 Solidity call traces
- **Non-claims:** **the matrix is not universal closure**, and its finiteness is asymmetric in places the observation report enumerates — for instance, non-canonical return words are measured at exactly one value, and two outcomes are measured only at exactly 32 bytes. Finite differential evidence is corroboration and is never a Lean premise.
- **Source:** `reports/lido-circuit-breaker-observation.md:196-215`; `scripts/GATES.md`

---

## Pillar — Operational monitoring

#### MON-1 — A successful `setPauser` kernel execution emits exactly one `PauserSet` log, after the stable Registry writes, carrying target, previous pauser, and new pauser

- **Declarations:** `Blanc.LidoCircuitBreaker.pauserSet_local_transition`
- **Premises:** REG-4's exact-execution premise set.
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **Gate:** `scripts/check-lido-circuit-breaker-enumeration.sh`
- **Differential channel:** `register-fresh#1:action`, `register-absent-to-zero#1:action`, `register-same-pauser#2:action`
- **Non-claims:** a **raw local** event fact — raw logs can exist inside a frame whose containing message later fails. The event is deliberately unconditional on whether the assignment actually changed: a proposed strengthening requiring a changed assignment is rejected fail-closed, because it would wrongly exclude the zero-to-zero and same-pauser executions the source really performs.
- **Source:** `reports/lido-circuit-breaker-enumeration-observability-completion.md:63,125-126,145-151`; `Blanc/LidoCircuitBreakerEnumeration.lean:1973`

#### MON-2 — A successful register continuation reaches the source-model post-witness and retains the `PauserSet` log in the terminal raw frame

- **Declarations:** `Blanc.LidoCircuitBreaker.pauserSet_register_success`
- **Premises:** MON-1's, with the register continuation word.
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **Gate:** `scripts/check-lido-circuit-breaker-enumeration.sh`
- **Differential channel:** `register-fresh#1:action`
- **Non-claims:** raw frame, pre-settlement. What follows the event is bounded only as "an optional log suffix"; the suffix is not enumerated.
- **Source:** `reports/lido-circuit-breaker-enumeration-observability-completion.md:66`; `Blanc/LidoCircuitBreakerEnumeration.lean:2113`

#### MON-3 — Cleanly settled, that same run retains both the event and the matching Registry witness in the settled state

- **Declarations:** `Blanc.LidoCircuitBreaker.pauserSet_register_success_committed`
- **Premises:** MON-2's, plus the exact direct-register message shape and a clean successful `ProcessMessage`.
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **Gate:** `scripts/check-lido-circuit-breaker-enumeration.sh`
- **Differential channel:** `register-fresh#1:action`
- **Non-claims:** clean-success settlement only; the error boundary is MON-4.
- **Source:** `reports/lido-circuit-breaker-enumeration-observability-completion.md:67`; `Blanc/LidoCircuitBreakerEnumeration.lean:2175`

#### MON-4 — A monitor sees neither a rolled-back event nor a rolled-back registry: exact direct messages that settle with an error have empty logs and restore the input witness

- **Declarations:** `Blanc.LidoCircuitBreaker.pauserSet_settled_error_not_observable`, `Blanc.LidoCircuitBreaker.pauserSet_target_zero_no_success`, `Blanc.LidoCircuitBreaker.pauserSet_target_zero_error_logs_unchanged`
- **Premises:** the exact direct-message shape and an erroring settlement; the two target-zero auxiliaries additionally take the explicit target-zero revert construction.
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **Gate:** `scripts/check-lido-circuit-breaker-enumeration.sh`
- **Differential channel:** `register-zero-target-before-write#1:action`, `pause-eoa#2:action`
- **Non-claims:** the named direct register and pause message shapes only — not all messages, and not nested frames.
- **Source:** `reports/lido-circuit-breaker-enumeration-observability-completion.md:64,65,68`; `Blanc/LidoCircuitBreakerEnumeration.lean:2320,2237,2273`

#### MON-5 — From a committed direct register, a monitor's re-read of that same settled snapshot agrees with the event it just saw

- **Declarations:** `Blanc.LidoCircuitBreaker.registryObservation_sound`
- **Premises:** the exact message target, code address, code and zero value; the register calldata; the kernel table slot; memory well-formedness and reads; three calldata-word reads with a zero continuation; an entry witness; two `canonicalAddress` facts; owner agreement across the three view states; both scalar calldata guards and argument words; the enumeration loop slot; a successful `Exec`; a successful `ProcessMessage`; and a clean final error field.
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **Gate:** `scripts/check-lido-circuit-breaker-enumeration.sh`
- **Differential channel:** `register-fresh#1:action`, `view-get-pauser#1:action`, `view-get-count#1:action`, `view-enumeration-empty#1:action`
- **Non-claims:** **one event plus one matching stable re-read**, local to the named message and snapshot. It asserts no history, no event-stream completeness, no reorg handling, no delivery, no RPC availability, no finality, no heartbeat liveness, no access authority, no deployment correctness — and above all not that an external target is honestly paused.
- **Source:** `reports/lido-circuit-breaker-enumeration-observability-completion.md:69,127-133`; `Blanc/LidoCircuitBreakerEnumeration.lean:2452`

---

## Pillar — Access-control completeness

The axiom expectations for this pillar and the three that follow are pinned and
probed by `scripts/check-lido-circuit-breaker-access.sh`, which runs its own
`#print axioms` pass over its own pin set. Rows are **axiom-homogeneous**: where
a fact depends on no axioms at all it gets its own row rather than being averaged
into a neighbour's.

#### ACC-1 — Every raw `SSTORE` occurrence in a same-frame descendant of an exactly-invoking frame root is assigned to a unique one of twenty frozen source sites, at its own pc, carrying a permitted role with an actual earlier guard occurrence and the entry-state fact that guard establishes

- **Declarations:** `Blanc.LidoCircuitBreaker.Exec.NinstOccurrence.runtimeWriteAuthority_of_rawFrameRoot`
- **Premises:** the occurrence's instruction is an `SSTORE`; the frame root exactly invokes the emitted runtime at the contract's own address; and the occurrence lies in a same-frame parent prefix of that root. **No success, commit, settlement, or endpoint premise** — this is why the classification reaches no-op and later-reverted stores, not only the ones someone thought of.
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **Gate:** `scripts/check-lido-circuit-breaker-access.sh`
- **Differential channel:** unauthorized-call reverts are differential **support** only; the theorem itself has no oracle channel
- **Non-claims:** it does not determine which call opcode created the frame — a self-`CALLCODE` or `DELEGATECALL` form satisfying all four identity fields is deliberately not excluded. The guard is an existential over instruction **kind**, not identity. And it says nothing about who controls the admin key.
- **Source:** `reports/lido-circuit-breaker-access-temporal-authority.md`; `Blanc/LidoCircuitBreakerAccess.lean`

#### ACC-2 — The classifier is a bijection between rows and structural sites, not a cardinality match, with exact pcs and three-domain separation

- **Declarations:** `Blanc.LidoCircuitBreaker.RuntimePersistentWrite.sourceSites_exact`, `Blanc.LidoCircuitBreaker.RuntimePersistentWrite.sourceSite?_injective`, `Blanc.LidoCircuitBreaker.RuntimePersistentWrite.sourceSite?_sound`, `Blanc.LidoCircuitBreaker.RuntimePersistentWrite.sourceSite?_compiledAt`, `Blanc.LidoCircuitBreaker.runtimePersistentSourceSites_pcs`
- **Premises:** the deployment parameterisation only — none beyond the statement.
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **Gate:** `scripts/check-lido-circuit-breaker-access.sh`
- **Differential channel:** no direct oracle channel
- **Non-claims:** within-function row **order** is conventional, not certified: a permutation of two rows inside the same compiled function is caught by no theorem. Nothing scans raw `0x55` bytes, so a `0x55` inside a `PUSH` payload is excluded structurally rather than by byte-scanning.
- **Source:** `reports/lido-circuit-breaker-access-temporal-authority.md`; `Blanc/LidoCircuitBreakerSites.lean`

#### ACC-3 — The persistent-write inventories are exact — including that the constructor writes exactly two persistent cells — and depend on no axioms at all

- **Declarations:** `Blanc.LidoCircuitBreaker.RuntimePersistentWrite.inventory_exact`, `Blanc.LidoCircuitBreaker.RuntimePersistentWrite.all_length`, `Blanc.LidoCircuitBreaker.constructor_inventory_cardinalities`
- **Premises:** none beyond the statement — these are decision procedures over exact pc inventories.
- **Axioms:** none
- **Gate:** `scripts/check-lido-circuit-breaker-access.sh`
- **Differential channel:** no direct oracle channel
- **Non-claims:** cardinality and membership of a frozen structural inventory. Not a statement about any execution.
- **Source:** `Blanc/LidoCircuitBreakerSites.lean`, `Blanc/LidoCircuitBreakerDeploy.lean:472`; axiom expectations pinned in `scripts/check-lido-circuit-breaker-access.py`

#### ACC-4 — Every cell of the contract's own storage that differs between a message's entry state and its clean settled poststate carries owner-cell authority derived from an exact retained last writer

- **Declarations:** `Blanc.LidoCircuitBreaker.ProcessMessage.runtimeOwnerCellAuthority_of_clean_settled_ne`
- **Premises:** an execution from the frame root; `Prog.At` pinning the **installed** emitted runtime rather than assuming it; exact invocation at the contract's own address; a `ProcessMessage` settlement; a clean error field; and a cell that actually changed. Owner closure is **derived** by a separately named non-vacuous theorem, not assumed.
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **Gate:** `scripts/check-lido-circuit-breaker-access.sh`
- **Differential channel:** no direct oracle channel for the attribution itself
- **Non-claims:** transient lock cells and effects on foreign targets are **separate domains** and are not covered by owner closure. No-op and reverted occurrences stay raw and are never called survivors.
- **Source:** `reports/lido-circuit-breaker-access-temporal-authority.md`; `Blanc/LidoCircuitBreakerOwnerClosure.lean`

#### ACC-5 — Creation execution and runtime are separate domains: the transient and external-call sites are proved, by exact pc inventory, not to be persistent sites

- **Declarations:** `Blanc.LidoCircuitBreaker.runtimeTransientSourceSites_pcs`, `Blanc.LidoCircuitBreaker.runtimeExternalCallSourceSites_pcs`
- **Premises:** the deployment parameters only — these are exact pc inventories. The companion fact that the **constructor** writes exactly two persistent cells is ACC-3's `constructor_inventory_cardinalities`, not this row's; constructor byte boundaries are pinned separately by `scripts/check-lido-circuit-breaker-constructor.sh`.
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **Gate:** `scripts/check-lido-circuit-breaker-access.sh`
- **Differential channel:** the differential gate's constructor worlds
- **Non-claims:** no whole-program "this runtime contains no external call" claim is available **or true** — the `CALL` and `STATICCALL` edges sit inside `pauseAfterSet`. Immutables are not storage writes.
- **Source:** `reports/lido-circuit-breaker-access-temporal-authority.md`; `Blanc/LidoCircuitBreakerSites.lean`

#### ACC-6 — Twenty-seven of thirty permitted (site, role) pairs carry an explicit unconditional witness, and three *unpermitted* pairs are separately refuted, so the role sets are not merely sound upper bounds

- **Declarations:** `Blanc.LidoCircuitBreaker.attainable_setPauserAssignment_adminRegistry`, `Blanc.LidoCircuitBreaker.attainable_setPauserAssignment_pauseRegistry`, `Blanc.LidoCircuitBreaker.attainable_heartbeatExpiry_heartbeatExpiry`, `Blanc.LidoCircuitBreaker.attainable_pauseLastTargetExpiry_pauseExpiry`, `Blanc.LidoCircuitBreaker.not_attainable_afterOldNewCount_pauseRegistry`, `Blanc.LidoCircuitBreaker.not_attainable_setPauserAssignment_adminConfiguration`, `Blanc.LidoCircuitBreaker.not_attainable_pauseLastTargetExpiry_heartbeatExpiry`
- **Premises:** **none** — every witness is unconditional, with no deployment variable and no reachability hypothesis.
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **Gate:** `scripts/check-lido-circuit-breaker-access.sh`
- **Differential channel:** no direct oracle channel — attainability is a raw-occurrence existential
- **Non-claims:** attainability is a **raw-occurrence** predicate. The `.pauseRegistry` witnesses live in worlds that **revert**, and none of them may be paraphrased as "a pause can persist a Registry change". No witness's entry state is exhibited as reachable from genesis. The remaining three of the thirty are neither attainable nor refutable at this altitude — a stated model boundary, not unfinished work. The three refutations are of pairs the table does **not** permit, which is why 27 inhabited plus 3 unsettleable accounts for the permitted set exactly; a two-role row remains an upper bound however many witnesses land.
- **Source:** `reports/lido-circuit-breaker-access-temporal-authority.md`, `reports/lido-circuit-breaker-pause-join-completion.md`; `Blanc/LidoCircuitBreakerAttainment.lean`, `Blanc/LidoCircuitBreakerPauseAttainment.lean`, `Blanc/LidoCircuitBreakerPauseJoin.lean`

#### ACC-7 — Two role pairs that a permitted-role widening could conflate are provably distinct at a single write

- **Declarations:** `Blanc.LidoCircuitBreaker.RuntimeWriteAuthority.adminRegistry_not_adminExpiry`, `Blanc.LidoCircuitBreaker.RuntimeWriteAuthority.pauseRegistry_not_pauseExpiry`
- **Premises:** an arbitrary actual write authority at an arbitrary frame root and write. Nothing else — no deployment, execution, or reachability hypothesis. The exclusivity is derived from the disjoint source-function index sets the role constructors carry, which is why it is a theorem rather than a comparison of labels.
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **Gate:** `scripts/check-lido-circuit-breaker-access.sh`
- **Differential channel:** no direct oracle channel
- **Non-claims:** exclusivity **within** the two named pairs only. The mechanism **cannot separate two roles living in the same compiled function** — the configuration and heartbeat-expiry roles, both in the main function, are not told apart by it, and separating them would need a path-step pin. Header pinning also cannot reach inside the authority record's constructor payloads, so a guard weakened *within* a role changes no pinned header; that separate blind spot is closed by the gate's own within-role guard-strength control, not by these theorems.
- **Source:** `reports/lido-circuit-breaker-access-temporal-authority.md`; `Blanc/LidoCircuitBreakerAuthority.lean:318,342`

---

## Pillar — Temporal authority

#### TMP-1 — Liveness is exactly `timestamp < expiry`: the compiled view returns the canonical zero word at the boundary and beyond, and the canonical one word strictly below it

- **Declarations:** `Blanc.LidoCircuitBreaker.isPauserLive_runCompiled`, `Blanc.LidoCircuitBreaker.isPauserLive_runCompiled_at_expiry`, `Blanc.LidoCircuitBreaker.isPauserLive_runCompiled_of_live`, `Blanc.LidoCircuitBreaker.isPauserLive_runCompiled_of_later`
- **Premises:** the compiled-dispatch premises — calldata length, zero value, selector, code-address agreement, exact code, the argument word, `canonicalAddress pauser`, and the expiry read — **plus a warm-slot premise**: the pauser's expiry slot is already in `accessedStorageKeys`.
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **Gate:** `scripts/check-lido-circuit-breaker-access.sh`
- **Differential channel:** the heartbeat boundary rows at `expiry-1`, `expiry`, and `expiry+1`
- **Non-claims:** **warm-slot only.** The liveness, expiry, and interval views all carry the warm premise; nothing suggests the word differs cold, it is simply unproven. And `isPauserLive` never consults the Registry, so **"live" does not imply "registered"**.
- **Source:** `reports/lido-circuit-breaker-access-temporal-authority.md`; `Blanc/LidoCircuitBreakerAccess.lean`

#### TMP-2 — Expired authority cannot revive itself: a zero-count caller errors with `SenderNotPauser` before any liveness test, and an expired caller errors, both without moving storage

- **Declarations:** `Blanc.LidoCircuitBreaker.heartbeat_runCompiledTo_error_of_count_zero`, `Blanc.LidoCircuitBreaker.heartbeat_runCompiledTo_error_of_expired`
- **Premises:** the compiled-dispatch premises — calldata length, zero value, selector, code-address agreement, exact code, and the caller's entry count read — **plus warm-slot premises on the caller's count and expiry cells**. Error **precedence** is proved, not assumed.
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **Gate:** `scripts/check-lido-circuit-breaker-access.sh`
- **Differential channel:** the heartbeat family — unregistered caller, expired caller, and the three boundary rows
- **Non-claims:** the two entry facts — registered, and strictly live — are **independent**, and neither implies the other. A callee re-entering during a pause callback can observe zero assignments and a live expiry at the same instant. Nothing here may be read as "live implies registered".
- **Source:** `reports/lido-circuit-breaker-access-temporal-authority.md`; `Blanc/LidoCircuitBreakerAccess.lean`

#### TMP-3 — Heartbeat extension is checked: success requires the checked-extension fact, and a wrapping sum reverts with a source-exact `Panic(0x11)` and restores owner state

- **Declarations:** `Blanc.LidoCircuitBreaker.heartbeat_runCompiledTo_of_checkedExtension`, `Blanc.LidoCircuitBreaker.heartbeat_runCompiledTo_error_of_add_wrap`
- **Premises:** the compiled-dispatch premises; **warm-slot premises on the caller's count, expiry, and interval cells**; that the current frame is **not static**; the caller's **strict entry liveness** and a nonzero, actually-changing prior expiry; the original-storage expiry read; and the checked-extension fact on the success arm. These are more than "the compiled-dispatch premises": the state-changing heartbeat paths are proved warm and live, not cold and unconditional.
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **Gate:** `scripts/check-lido-circuit-breaker-access.sh`
- **Differential channel:** the heartbeat overflow rows, and their pause-side siblings for post-callback count and interval change
- **Non-claims:** it does not claim overflow is **reachable** in any deployed configuration. The panic body's byte identity is a separate fact owned by `scripts/check-lido-circuit-breaker-runtime-errors.sh`, not by this theorem.
- **Source:** `reports/lido-circuit-breaker-access-temporal-authority.md`; `Blanc/LidoCircuitBreakerAccess.lean`

Every registration chronology below shares a settlement shape that each row's own field does not repeat, and the shape is **not uniform** — where a premise is carried by some chronologies and not others, that is said here rather than glossed.

**All six** take the exact message target, owner, code address, production code, zero value, and register calldata; an exact entry-gas equation; an **admin** caller; a **non-static** frame; `nonzeroCanonicalAddress` on the target; and the settlement triple — a successful `ProcessMessage`, a filled execution slot, and a clean error field as an antecedent rather than a discharged fact.

**Five of six** — all but the fresh-registration chronology — additionally take a residual-gas stipend inequality.

**Four of six** — all but the two *replacement* chronologies, which reach their state through the retained-assignment kernel instead — additionally take the entry `RegistryWitness` together with the found-or-not-found path selector that picks the chronology.

**All six** additionally take **warm**-slot premises: positive `accessedStorageKeys` membership on the cells that chronology writes, between one and six of them each, eighteen in total across the family. Every one of these theorems is therefore unavailable at a state where its own cells are still cold. Each row below names its warm cells. Separately and in the **opposite** direction, three of the six also take **cold** premises — *negative* membership, requiring a named cell to be **absent** from `accessedStorageKeys` — and those are named per row too. The two polarities are different conditions and neither implies the other.

A row's own **Premises** field names what that row adds to this shape. Reading a field without this paragraph understates the hypotheses; reading this paragraph as uniform overstates them.

#### TMP-4 — Admin re-registration may revive an expired pauser: the replacement chronology takes the new pauser's entry expiry as an arbitrary word and overwrites it, with no liveness premise

- **Declarations:** `Blanc.LidoCircuitBreaker.registerPauser_retainedNonzero_success_settled_effects`
- **Premises:** the shared registration shape above, plus `nonzeroCanonicalAddress` on the **new** pauser and on the **old** pauser; the checked-extension fact; a **warm** premise on the new pauser's expiry cell; a **cold** premise requiring the heartbeat-interval cell to be **absent** from `accessedStorageKeys`; and — the row's real scope — that the old pauser **retains at least one other assignment**. That last premise is the discriminator against TMP-6's last-assignment chronology, which writes the same fresh expiry by a different route, so this row does **not** cover the last-assignment replacement. The new pauser's entry expiry is bound to a free variable, so it may be any word including a past one. **No prior-liveness premise:** nothing asks whether that expiry had passed, and that absence is the claim.
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **Gate:** `scripts/check-lido-circuit-breaker-access.sh`
- **Differential channel:** `register-distinct-pauser#2:action`; admin-driven revival in the heartbeat family
- **Non-claims:** this is the **replacement** chronology specifically — the target is already registered to another pauser. It is not a general theorem over all registration paths, and the sibling chronologies below cannot carry it: the fresh path requires the expiry cell to be zero, and the absent path writes no expiry at all.
- **Source:** `reports/lido-circuit-breaker-access-temporal-authority.md`; `Blanc/LidoCircuitBreakerReplacementRegistration.lean:1358`

#### TMP-5 — A first registration writes a checked expiry into a cell required to be zero on entry

- **Declarations:** `Blanc.LidoCircuitBreaker.registerPauser_freshNonzero_success_settled_effects`
- **Premises:** the shared registration shape above, plus `nonzeroCanonicalAddress` on the new pauser; the checked-extension fact; that the new pauser's expiry cell **and** its original-storage value are both **zero** at entry; that the checked expiry it writes is itself **nonzero**, which excludes the degenerate world where timestamp and interval are both zero; the array-length and count non-wrap word equations; **warm** premises on the array, index, and new-pauser expiry cells; and **two cold** premises requiring the new pauser's count cell and the heartbeat-interval cell to be absent from `accessedStorageKeys`.
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **Gate:** `scripts/check-lido-circuit-breaker-access.sh`
- **Differential channel:** `register-fresh#1:action`
- **Non-claims:** because the entry cell is pinned to zero, this row says nothing about revival — there is nothing to revive. Revival is TMP-4.
- **Source:** `reports/lido-circuit-breaker-access-temporal-authority.md`; `Blanc/LidoCircuitBreakerFreshRegistration.lean:1649`

#### TMP-6 — When an assignment change leaves the old pauser with no assignments its expiry cell is cleared — unless the old and new pauser are the same address, in which case it carries the fresh expiry — and every other canonical pauser's is preserved

- **Declarations:** `Blanc.LidoCircuitBreaker.registerPauser_oldLastNonzero_success_settled_effects`, `Blanc.LidoCircuitBreaker.registerPauser_foundZeroOldLast_success_settled_effects`, `Blanc.LidoCircuitBreaker.registerPauser_foundZeroOldLastSwapPop_success_settled_effects`
- **Premises:** the shared registration shape above, plus `nonzeroCanonicalAddress` on the old pauser and the original-storage expiry reads. The first declaration is a **replacement**, and additionally takes a nonzero new pauser, **warm** premises on the old- and new-pauser expiry cells, a **cold** heartbeat-interval premise, and the checked-extension fact — which is what makes the `expiry` in the conditional below a checked timestamp-plus-interval sum rather than an arbitrary word. The other two are **removals**, distinguished by the mechanism the Cyfrin comparison turns on: one is the remove-the-tail case, taking a last-position premise, with **warm** premises on the array, index, length, and expiry cells; the other is the **swap-and-pop** case, taking a not-last premise, with six warm premises covering the vacated hole, the moved element's index, the dead tail, the target's index, the array length, and the expiry cell.
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **Gate:** `scripts/check-lido-circuit-breaker-access.sh`
- **Differential channel:** the old- and new-pauser last-assignment expiry-cleanup rows; `register-same-pauser#2:action`; unregister first, middle, and last
- **Non-claims:** **the clearing is conditional on the replacement path.** Re-registering the *same* pauser leaves that cell holding the fresh expiry rather than zero — the replacement chronology's conclusion is literally `if oldPauser = newPauser then expiry else 0`, and `register-same-pauser#2:action` is exactly that measured coordinate. The two removal chronologies clear unconditionally. This is proved on named chronologies, not over arbitrary removals, and it says nothing about callback-time coherence.
- **Source:** `reports/lido-circuit-breaker-access-temporal-authority.md`; `Blanc/LidoCircuitBreakerReplacementRegistration.lean:2143`, `Blanc/LidoCircuitBreakerUnregisterRegistration.lean:3963,5310`

#### TMP-7 — The absent-target, zero-pauser registration is a no-op on every expiry cell

- **Declarations:** `Blanc.LidoCircuitBreaker.registerPauser_absentZero_success_settled_effects`
- **Premises:** the shared registration shape above, plus **warm** premises on the array and index cells. It takes **no** timestamp, interval, expiry variable, or checked-extension fact, because it writes no expiry — but that negative list is about the expiry machinery only, and is not an exhaustive premise list.
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **Gate:** `scripts/check-lido-circuit-breaker-access.sh`
- **Differential channel:** `register-absent-to-zero#1:action`
- **Non-claims:** a preservation result — every canonical pauser's expiry cell equals its entry value, and one `PauserSet` log is emitted. It is the negation in direction of a revival fact and must never be cited for one.
- **Source:** `reports/lido-circuit-breaker-access-temporal-authority.md`; `Blanc/LidoCircuitBreakerAbsentRegistration.lean:1665`

#### TMP-8 — One fully concrete unregistration world settles end to end, exhibiting the whole path rather than quantifying over it

- **Declarations:** `Blanc.LidoCircuitBreaker.unregisterWorld_settles`
- **Premises:** **none.** The theorem takes no hypotheses at all: it is a closed statement about one hard-coded world.
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **Gate:** `scripts/check-lido-circuit-breaker-access.sh`
- **Differential channel:** the unregister rows of the Registry family
- **Non-claims:** **this is one concrete world**, with a single-entry registry, a fixed target address and a fixed pauser address. Nothing is quantified over targets, pausers, entry lists, gas, or worlds, and no genesis reachability is claimed. It exhibits that the unregistration path really settles; the general statements are TMP-4 through TMP-7, and this row must never be read as one of them.
- **Source:** `reports/lido-circuit-breaker-access-temporal-authority.md`; `Blanc/LidoCircuitBreakerUnregisterWorld.lean:1038`

#### TMP-9 — An interval update moves no existing expiry: every canonical pauser's expiry cell is byte-identical afterwards, and the new interval governs only the next successful registration or heartbeat

- **Declarations:** `Blanc.LidoCircuitBreaker.setHeartbeatInterval_success_settled_effects`
- **Premises:** the exact message target, owner, code address, code, zero value, and interval calldata; an **exact entry-gas equation**; that the caller **is the admin**; that the new interval lies within the configured minimum and maximum; that the frame is **not static**; and a filled execution slot, with a clean error field as an antecedent rather than a discharged fact.
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **Gate:** `scripts/check-lido-circuit-breaker-access.sh`
- **Differential channel:** the admin interval-change callback row, and "interval change before renewal" in the heartbeat family
- **Non-claims:** the log list is pinned **exactly** as the entry list extended, not as a containment. Nothing here is stated at transaction altitude.
- **Source:** `reports/lido-circuit-breaker-access-temporal-authority.md`; `Blanc/LidoCircuitBreakerAccess.lean`

#### TMP-10 — Emitted record order is pinned exactly, not as a containment

- **Declarations:** `Blanc.LidoCircuitBreaker.heartbeat_success_settled_effects`
- **Premises:** **not TMP-9's**, and the difference is the point: the interval setter requires the caller to be the **admin**, while this one requires the caller to be a **registered, strictly live pauser** — a nonzero entry count, a strictly future prior expiry, and the checked-extension fact — on top of the exact message shape, an exact entry-gas equation, a non-static frame, and the settlement triple. **No warm-slot premise:** unlike TMP-3's raw-run forms, this settled result carries no access-list hypothesis at all, and its gas conclusion is stated on the **cold**-`SLOAD` schedule.
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **Gate:** `scripts/check-lido-circuit-breaker-access.sh`
- **Differential channel:** the ordered-log rows pinning `PauserSet`, `PauseTriggered`, and `HeartbeatUpdated`
- **Non-claims:** raw frame logs after settlement are **not** falsely erased on error. Empty *observable* receipt logs are a different theorem at a different altitude, not a general erasure of raw logs.
- **Source:** `reports/lido-circuit-breaker-access-temporal-authority.md`; `Blanc/LidoCircuitBreakerAccess.lean`

---

## Pillar — Single-use pause

#### PAU-1 — At the moment an arbitrary target first receives control, its assignment cell is already zero and the reentrancy lock is held, and nothing is written between `pauseAfterSet` entry and the `CALL`

- **Declarations:** `Blanc.LidoCircuitBreaker.pauseAfterSetEntry_assignment`, `Blanc.LidoCircuitBreaker.pauseCallEntry_assignment_and_lock`, `Blanc.LidoCircuitBreaker.pauseCallEntry_frame`, `Blanc.LidoCircuitBreaker.removeTarget_pauseAfterSet_runCompiled`
- **Premises:** the module's **only** code hypotheses identify the CircuitBreaker's own runtime — its code and code address. **No hypothesis constrains the code at the paused target**, which is what makes the row a hostile-world result rather than a friendly-double one.
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **Gate:** `scripts/check-lido-circuit-breaker-access.sh`
- **Differential channel:** `pause-return-true` (the unregister-before-call channel); the reentry and interference family
- **Non-claims:** the span stops at the `CALL`'s **pre-state**. No blanket invariance across the `CALL` is stated, and none could hold of an arbitrary callee. Nothing here says the pause completes, succeeds, or reaches its expiry write, and the composition from the public entry into a single checked object was not performed.
- **Source:** `reports/lido-circuit-breaker-pre-control.md`; `Blanc/LidoCircuitBreakerPreControl.lean`

#### PAU-2 — A `pause` re-entered from the state at which the target holds control cannot pass the transient lock: it takes the refusal arm, reverts with the reentrancy payload, and writes nothing

- **Declarations:** `Blanc.LidoCircuitBreaker.pause_body_runCompiledTo_error_of_locked`, `Blanc.LidoCircuitBreaker.pause_runCompiledTo_error_of_locked`
- **Premises:** three hypotheses identifying the CircuitBreaker's own runtime, and the lock being held.
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **Gate:** `scripts/check-lido-circuit-breaker-access.sh`
- **Differential channel:** the reentry and interference family — same-target and different-target nested pause
- **Non-claims:** this is the **protected pause entry only**. It is not a general "no descendant does anything" claim, and it says nothing about unprotected entries or about what the callee does.
- **Source:** `reports/lido-circuit-breaker-pre-control.md`; `Blanc/LidoCircuitBreakerPauseGuards.lean`

#### PAU-3 — Every reached success walk over arbitrary target bytecode either commits an exact result or takes the storage-silent arithmetic-panic arm

- **Declarations:** `Blanc.LidoCircuitBreaker.pauseSuccess_outcome`, `Blanc.LidoCircuitBreaker.pauseSuccess_pauseTriggered_prefix`
- **Premises:** **one** function-table slot premise — the arithmetic-panic slot — together with `PauseSuccessInputs` and a supplied compiled walk. `PauseSuccessInputs` is four conjuncts: two frame-local memory windows carrying the staged target and duration, and two **non-restrictive** storage reads that merely name the entry count and heartbeat interval. So: no target-code, returndata, transient, gas, or output premise, and **no restrictive storage premise** — but the field does not pretend there are no storage hypotheses at all, because a reader checking the Lean will find two. The four-slot premise set belongs to the committed-outcome theorems of HOSTILE-2, not here. The commit and panic shapes are the definitions `PauseSuccessCommit` and `PauseSuccessPanic`, outside every pin authority and named here as vocabulary, not cited as evidence.
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **Gate:** `scripts/check-lido-circuit-breaker-access.sh`
- **Differential channel:** `pause-return-true`, `pause-last-assignment-zero-expiry-no-add`, `next-transaction-after-success`, and the ordered-log rows
- **Non-claims:** it classifies derivations that **reach** a terminal result; it asserts nothing about whether any arm is reachable in any particular world. Accepting a canonical `1` is evidence that the target **reported** success, never that it really paused. Three of its claims — the terminal transient-lock cell, the raw whole-account storage equality, and the identity of the expiry word with the emitted heartbeat log's data word — have **no direct oracle channel**. Jaune's `STOP` preserves the active frame's incoming output, so the empty-output corollary routes through an honest enclosing-frame premise rather than asserting emptiness outright.
- **Source:** `reports/lido-circuit-breaker-success.md`; `Blanc/LidoCircuitBreakerSuccess.lean`

#### PAU-4 — At two concrete cooperative-callee worlds the successful pause message survives settlement, with exactly the stated cells, logs, and non-interference

- **Declarations:** `Blanc.LidoCircuitBreaker.pauseLastWorld_settles`, `Blanc.LidoCircuitBreaker.pauseRetainedWorld_settles`, `Blanc.LidoCircuitBreaker.pauseLastWorld_effects`, `Blanc.LidoCircuitBreaker.pauseRetainedWorld_effects`, `Blanc.LidoCircuitBreaker.pauseWorld_projectionAgrees`
- **Premises:** **premise-free** — the clean-error hypothesis the settlement template carries was discharged here, not carried forward.
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **Gate:** `scripts/check-lido-circuit-breaker-access.sh`
- **Differential channel:** `pause-return-true`, `next-transaction-after-success`
- **Non-claims:** this must **not** be paraphrased as "a pause leaves the Registry clean". These are two concrete two-account worlds; nothing is quantified over callees, gas, entry lists, or worlds, and no genesis reachability is claimed. The cooperating callee is witness **content**, not a smuggled hypothesis. The Registry projections are **model-side by necessity**: a poststate witness would need a universal storage frame the walk does not export, so model and run meet only at the slots the trace actually touches.
- **Source:** `reports/lido-circuit-breaker-pause-settlement-completion.md`, `reports/lido-circuit-breaker-pause-join-completion.md`; `Blanc/LidoCircuitBreakerPauseSettlement.lean`, `Blanc/LidoCircuitBreakerPauseJoin.lean`

#### PAU-5 — The reached expiry write obeys the source's own zero test, and the only way an entered success walk misses that write is a checked-addition overflow

- **Declarations:** `Blanc.LidoCircuitBreaker.pauseSuccess_expiryWrite_dichotomy`, `Blanc.LidoCircuitBreaker.pauseSuccess_expiryWrite_of_reached`, `Blanc.LidoCircuitBreaker.pauseSuccess_expiryWrite_stores_zero_iff`
- **Premises:** a supplied compiled success walk. The dichotomy itself is otherwise unconditional, but **both reached forms carry a no-wrap antecedent** — that a nonzero count implies the checked addition of timestamp and interval does not overflow — and the zero-store characterisation additionally excludes the doubly-degenerate case where timestamp and interval are both zero. The governing law is the theorem `PauseExpiryValue.eq_zero_iff`, which is outside every pin authority and named here as vocabulary.
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **Gate:** `scripts/check-lido-circuit-breaker-access.sh`
- **Differential channel:** `pause-last-assignment-zero-expiry-no-add`
- **Non-claims:** the exact law is that the stored value is zero **iff the count is zero or both timestamp and interval are zero** — the shorter phrasing "stores zero iff the post-callback count read is zero", which an earlier report used, is literally false and is corrected here. The result does not identify the zero count with a stable last-assignment fact, does not construct the callback, does not prove terminal success, and does not assert final-state noninterference. It joins the access family only at the two concrete worlds of PAU-4, not universally.
- **Source:** `reports/lido-circuit-breaker-pause-join-completion.md`; `Blanc/LidoCircuitBreakerPauseSuffix.lean:429,561,586`

---

## Pillar — External-call honesty

#### CALL-1 — At its external boundary the contract sends exactly two messages to the named target: a valueless `pauseFor` carrying its own configured duration, then — only on success — an `isPaused` static query, with the callee running under the parent's transient storage

- **Declarations:** `Blanc.LidoCircuitBreaker.pauseCall_boundary`, `Blanc.LidoCircuitBreaker.pauseStat_boundary`, `Blanc.LidoCircuitBreaker.pause_externalBoundary`
- **Premises:** **none about the callee** — that is the claim, and it survives. But the count is larger than the reports say. `pauseCall_boundary` takes the exact operand stack, the exact 36-byte argument window holding `pauseFor` calldata, a nonzero frame depth, the honest enclosing-frame premise that the current frame is **not static**, and the compiled run. `pause_externalBoundary` takes eight, discharging the operand and window premises from the CircuitBreaker's own straight-line staging rather than assuming them — which is the honest version of the reports' "three about our own frame" phrasing. Gas sufficiency is **derived**, not assumed: the insufficient branch is an out-of-gas halt the derivation refutes. The boundary relations themselves are `def`s outside every pin authority, which is why the gate carries a dedicated arbitrary-target-code control for them.
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **Gate:** `scripts/check-lido-circuit-breaker-access.sh`
- **Differential channel:** the 82 Solidity call and static-call traces in the differential gate; `pause-return-true`
- **Non-claims:** nothing about what the target does with either message, what it returns, or whether it honours the duration. **The static flag is a fact about the message the CircuitBreaker builds, not a no-write theorem** — a static-context no-write result over arbitrary code exists nowhere in Jaune or Blanc and is not built here. No claim that either edge is reached in any particular run. These relations remain **implications at exact reached states**; composition from the public `pause` entry is deferred and recorded in the successor register.
- **Source:** `reports/lido-circuit-breaker-call-boundary.md`; `Blanc/LidoCircuitBreakerCallBoundary.lean`

#### CALL-2 — The staged target and duration words survive arbitrary callee execution

- **Declarations:** `Blanc.LidoCircuitBreaker.pauseCall_targetWord_survives`
- **Premises:** the boundary relation. There is **no memory-unchanged assumption anywhere in the module**: survival is derived from the `CALL` requesting a zero-byte return window, so the resume writes nothing.
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **Gate:** `scripts/check-lido-circuit-breaker-access.sh`
- **Differential channel:** no direct oracle channel
- **Non-claims:** transport of two frame-local words only. Nothing about the rest of memory.
- **Source:** `reports/lido-circuit-breaker-call-boundary.md`; `Blanc/LidoCircuitBreakerCallBoundary.lean`

#### CALL-3 — The branch flag takes exactly two values and inverts the callee's error; the failure arm cannot commit, and any successful walk past the branch forces the `pauseFor` call to have succeeded

- **Declarations:** `Blanc.LidoCircuitBreaker.pauseCall_flag_dichotomy`, `Blanc.LidoCircuitBreaker.pauseAfterCall_arms`, `Blanc.LidoCircuitBreaker.pauseCall_failureArm_bubbles`, `Blanc.LidoCircuitBreaker.pauseCall_failureArm_neverCommits`, `Blanc.LidoCircuitBreaker.pauseCall_successArm_reachesStatcall`, `Blanc.LidoCircuitBreaker.pauseAfterCall_ok_forces_callSuccess`
- **Premises:** as CALL-1.
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **Gate:** `scripts/check-lido-circuit-breaker-access.sh`
- **Differential channel:** the pause-failure family — target revert, query revert, fewer than 32 query bytes, a first word other than 0 or 1, and a first word of 0
- **Non-claims:** **the failure arm's payload is a two-leg disjunction, not an unconditional claim.** The out-of-gas leg is not removable: without the memory-alignment premise the revert's own expansion charge is not provably zero.
- **Source:** `reports/lido-circuit-breaker-call-boundary.md`; `Blanc/LidoCircuitBreakerCallBoundary.lean`

#### CALL-4 — The compiled program accepts only the source-compatible return shape, routing short returns, `false`, and non-canonical first words to their exact payloads, while accepting a canonical `1` with trailing bytes

- **Declarations:** `Blanc.LidoCircuitBreaker.pauseDecode_arms`, `Blanc.LidoCircuitBreaker.pauseDecode_accepts_one`, `Blanc.LidoCircuitBreaker.pauseDecode_accepts_one_withTail`, `Blanc.LidoCircuitBreaker.pauseObservation_arms`, `Blanc.LidoCircuitBreaker.pauseObservation_outcomes`, `Blanc.LidoCircuitBreaker.pauseAfterSet_outcomes`
- **Premises:** the function-table slot premises, and the static-boundary relation at the exact reached states.
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **Gate:** `scripts/check-lido-circuit-breaker-access.sh`
- **Differential channel:** the pause-failure family, plus an independent shape schema validating the exact successful 32-byte output window, the absence of successful-tail copying, complete short and large return coverage, and full failed-child bubbling
- **Non-claims:** **accepting a canonical `1` is evidence only that the target reported success — never that the target is really paused.** End-to-end pause correctness would need a separately verified target and a composition theorem, recorded in the successor register.
- **Source:** `reports/lido-circuit-breaker-observation.md`; `Blanc/LidoCircuitBreakerObservation.lean`

---

## Pillar — Hostile-world results (Stage 6)

Reentrancy refusal is PAU-2 and rollback is PAU-3; they are not restated here. These
five rows carry what is specific to the hostile-world closure: how universality is
kept falsifiable, where the one assumption sits, which uncomfortable state is
deliberately permitted, and how the same family lifts to the public pause entry.

#### HOSTILE-1 — Universality over callee bytecode is made failable, not merely asserted, by dedicated controls verified non-vacuous under live mutation

- **Declarations:** no audited declaration — gate-owned row
- **Premises:** each control instantiates its family at a universally quantified byte array, arbitrary join body, or arbitrary run-frame content, and carries that same arbitrary code across the guard and the call staging.
- **Axioms:** not applicable
- **Gate:** `scripts/check-lido-circuit-breaker-access.sh`
- **Differential channel:** no direct oracle channel — these are anti-vacuity controls, not behavioural claims
- **Non-claims:** a control proves the pins cannot be gutted silently; it is **not itself an assurance claim**. Two gate limits are recorded rather than hidden: the mutation set re-runs header pinning and never compiles the mutant, so a definition-body weakening cannot be expressed there; and header pins reach neither the authority record's constructor payloads nor the interiors of the boundary and expiry-value `def`s, which is why the bespoke controls exist at all.
- **Source:** `reports/lido-circuit-breaker-pre-control.md`, `reports/lido-circuit-breaker-call-boundary.md`; `scripts/LidoCircuitBreakerAccessControls.lean`

#### HOSTILE-2 — The exact final state of one successful pause rests on an explicitly assumed noninterference premise, and two measured rows prove that assumption is not idle

- **Declarations:** `Blanc.LidoCircuitBreaker.pauseObservation_committed_outcomes`, `Blanc.LidoCircuitBreaker.pauseAfterSet_committed_outcomes`
- **Premises:** `PauseSuccessNoninterference` — a definition whose own docstring opens "Assumed, not derived" — universally quantified over successful pre-states on both classification theorems. It requires the caller's post-callback assignment count and heartbeat interval each to equal their value at `pauseAfterSet` entry. It enters exactly when the result is restated against `pauseAfterSet` entry storage; the underlying `pauseSuccess_outcome` (PAU-3) does **not** carry it.
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **Gate:** `scripts/check-lido-circuit-breaker-access.sh`
- **Differential channel:** `overflow-pause-post-callback-count-positive` and `overflow-pause-post-callback-interval-change`, both cited in the module header and in the assumption's own docstring; supplemented by the admin-interval, admin-reassign, and callback-heartbeat rows
- **Non-claims:** arbitrary target code **can** re-enter and make either equality false — that is the measured content of those two rows, not a hypothetical. A no-write theorem for the relevant calls, or an authorization invariant strong enough to exclude the writes, would derive the premise instead of assuming it; **neither exists**. Registry coherence across histories carries no such premise, and this row must never be generalised into one that does.
- **Source:** `reports/lido-circuit-breaker-success.md`; `Blanc/LidoCircuitBreakerSuccess.lean`

#### HOSTILE-3 — The zero-count, live-expiry mid-call state is reachable and deliberately permitted, not a defect the proofs paper over

- **Declarations:** no audited declaration — gate-owned row
- **Premises:** the source's own definition: liveness is `timestamp < expiry` and never consults the Registry. So between the target's unregistration and the callback's return, an address with no registration reports live.
- **Axioms:** not applicable
- **Gate:** `scripts/check-lido-circuit-breaker-differential.sh`
- **Differential channel:** `callback-midcall-liveness`, `callback-heartbeat`
- **Non-claims:** this is real source behaviour at an internal state, pinned as a live differential coordinate. It is **why** no callback-time count/expiry coherence is claimed anywhere in this register, and why a settled-boundary invariant — which could hold — is recorded as a successor rather than asserted here.
- **Source:** `reports/lido-circuit-breaker-access-temporal-authority.md`; `Blanc/LidoCircuitBreaker.lean:176`

#### HOSTILE-4 — A production public `pause(address)` execution reaches the exact Stage 6 `pauseAfterSet` state at every terminal polarity

- **Declarations:** `Blanc.LidoCircuitBreaker.publicPause_reaches_pauseAfterSet`
- **Premises:** `PublicPauseEntryPremises` states the production runtime bytes, owner/code-address agreement, zero value, dynamic non-root frame, exact pause calldata and selector, canonical nonzero target and caller, unlocked entry, installed target code, live assignment, the duration/index/length/last registry reads, every named storage-key separation, and a memory image; plus the actual `Prog.RunCompiledTo` execution. Count preservation across removal is derived from those separations by `PublicPauseEntryPremises.removePreservesCount`; it is not an entry premise. None of these premises states or selects the terminal result.
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **Gate:** `scripts/check-lido-circuit-breaker-access.sh`
- **Differential channel:** the public pause success/failure family exercises the same production selector and registry preconditions finitely
- **Non-claims:** this row strengthens altitude only. It chooses no terminal polarity, constrains no arbitrary target behaviour beyond the separately named installed bytes, and says neither that the target reports `true` nor that it is really paused.
- **Source:** `Blanc/LidoCircuitBreakerPublicPause.lean`; `Blanc/LidoCircuitBreakerPublicPauseControl.lean`

#### HOSTILE-5 — The CALL and STATICCALL boundaries and complete settled Stage 6 outcome family hold from the public pause entry

- **Declarations:** `Blanc.LidoCircuitBreaker.pauseAfterSet_boundary_committed_outcomes`, `Blanc.LidoCircuitBreaker.publicPause_committed_outcomes`
- **Premises:** at the reached state, the four exact function-table slots, the transported target and duration words, non-root dynamic frame facts, the actual `pauseAfterSet` continuation, and `PauseSuccessNoninterference` only for successful pre-states that reach `pauseSuccess`; at public altitude, the full HOSTILE-4 entry premises and execution plus that same named noninterference condition scoped to the exact extracted state. No result-equivalent premise appears.
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **Gate:** `scripts/check-lido-circuit-breaker-access.sh`
- **Differential channel:** the pause success/failure family, including target revert, query revert, short return, canonical false, non-canonical word, canonical true, and the two post-callback overflow rows
- **Non-claims:** **accepting a canonical `1` is evidence only that the target reported success — never that the target is really paused.** Arbitrary target code can still re-enter and falsify `PauseSuccessNoninterference`; the public theorem assumes that named premise exactly where the reached-state family does and does not derive it for arbitrary targets. No liveness, universal-gas, target-honesty, or end-to-end paused-state claim is made.
- **Source:** `Blanc/LidoCircuitBreakerPublicPause.lean`; `Blanc/LidoCircuitBreakerSuccess.lean`

---

## Pillar — Deployment and history

This pillar has two layers that must not be confused. The **history** layer is
conditional: *if* the contract is in good order at some checkpoint, it stays in
good order at every state reachable from there. The **deployment** layer
discharges that "if" — for exactly one official direct deployment, and for
nothing else. Read either layer without the other and the result is an
overclaim in one direction or an understatement in the other.

Deployment rows are audited by `scripts/check.sh --no-build`; history rows are
pinned and probed by `scripts/check-lido-circuit-breaker-history.sh`, which
requires every public theorem in the family to report exactly the standard three
axioms and admits no exception table.

#### DEP-1 — For the exact official constructor input, a successful configured Prague-only transition over the strict singleton envelope establishes the deployment root

- **Declarations:** `Blanc.LidoCircuitBreaker.canonicalDeploymentStep_establishes_root`
- **Premises:** exactly three. **(1)** a canonical deployment base — seventeen pre-execution fields including that the target address is the address computed from the sender and its nonce, and four system-code equalities. **(2)** the canonical official envelope — the block's transaction list is the single transaction, no ommers, no withdrawals, a type-2 transaction on this chain, zero value, data exactly the official full CREATE input, with recovered, validated, and checked sender and the gas and funding bounds. **(3)** `hstep`, the successful configured Prague-only transition — **the theorem's only premise about the named deployed chain**. Everything else — the prepared message, the collision check, the constructor, message and transaction results, receipt success, poststate, installed code, witness, and stability — is **derived, not assumed**. The root record itself is a structure outside the axiom audit and is named here as vocabulary.
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **Gate:** `scripts/check-lido-circuit-breaker-deployment.sh`
- **Differential channel:** no direct oracle channel for the theorem. The gate carries a **separate** finite replay — one temporary strict singleton Prague block through pinned EELS with 18 positive assertions and 26 live finite mutants — which is feasibility and cross-evaluator evidence only and is **never** a Lean premise.
- **Non-claims:** not the deployed Solidity bytecode at `0x6019CB557978296BA3C08a7B73225C0975DFB2F7`; no signature, propagation, or inclusion claim; **not parameter-generic**; no co-block, clone, factory, proxy, or CREATE2 path; no nonzero endowment; no arbitrary fork; no universal patch or gas claim. It does not strengthen the history theorem and does not remove its reach bound.
- **Source:** `reports/lido-circuit-breaker-deployment-root.md`; `Blanc/LidoCircuitBreakerDeploymentRoot.lean:49-58`

#### DEP-2 — The official transaction runs end to end through the real pipeline to a receipt whose own success bit is set, with three ordered logs, no requests, and a singleton receipt key

- **Declarations:** `Blanc.LidoCircuitBreaker.canonicalDeploymentTransaction_succeeds`
- **Premises:** the canonical base, the official envelope, and a prepared deployment context.
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **Gate:** `scripts/check-lido-circuit-breaker-deployment.sh`
- **Differential channel:** no direct oracle channel — the differential campaign has no receipts at all; it compares slot readings, status, returndata, logs, and call traces, and never builds a block or a receipt
- **Non-claims:** it does not claim the three logs parse as deposit requests. The opposite is proved: the parsed request list is empty.
- **Source:** `reports/lido-circuit-breaker-deployment-root.md`, `reports/lido-circuit-breaker-history-h12.md:20-22`; `Blanc/LidoCircuitBreakerDeploymentTransaction.lean`

#### DEP-3 — Both checked Prague request-system suffix calls return empty request bytes and preserve state and output, and the whole block body composes to the deployed state

- **Declarations:** `Blanc.LidoCircuitBreaker.canonicalDeploymentSuffix_succeeds`, `Blanc.LidoCircuitBreaker.canonicalDeploymentApplyBody_succeeds`
- **Premises:** the prepared context and the transaction result.
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **Gate:** `scripts/check-lido-circuit-breaker-deployment.sh`
- **Differential channel:** the finite replay's empty-requests and system-program assertions; no direct oracle channel for the Lean statement
- **Non-claims:** **Prague-only.** The withdrawal- and consolidation-request predeploy addresses are pinned to the system program's code as a *base premise*, not proved.
- **Source:** `reports/lido-circuit-breaker-deployment-root.md`; `Blanc/LidoCircuitBreakerDeploymentBlock.lean`

#### DEP-4 — The fresh-frame constructor execution is walked in full: source-ordered validation, all twelve untaken error arms, the runtime copy and its twelve patches, exactly two configuration stores, three ordered logs, and a terminal return under a named sufficient gas

- **Declarations:** `Blanc.LidoCircuitBreaker.officialConstructorExecutionTrace_fresh`, `Blanc.LidoCircuitBreaker.officialConstructorProgram_runCompiled_fresh`, `Blanc.LidoCircuitBreaker.officialConstructor_exec_fresh`
- **Premises:** the fresh-frame entry conditions — fresh zero storage at the target address, and the exact appended official input.
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **Gate:** `scripts/check-lido-circuit-breaker-deployment.sh`
- **Differential channel:** the five constructor-success rows and the eight named constructor-reject rows, including both zero and above-maximum bounds for each duration and the two precedence cases
- **Non-claims:** the walk is for the **official** full CREATE input only. **No universal constructor-patch theorem is claimed.**
- **Source:** `reports/lido-circuit-breaker-deployment-root.md`, `reports/lido-circuit-breaker-artifact-conformance-completion.md`; `Blanc/LidoCircuitBreakerDeploymentTrace.lean`

#### DEP-5 — The empty Registry witness at the constructor poststate is read out of the actual two-write storage through region separation, not assumed from a synthetic world

- **Declarations:** `Blanc.LidoCircuitBreaker.officialConstructorPost_emptyRegistryWitness`, `Blanc.LidoCircuitBreaker.officialConstructorPost_registryCoherent`, `Blanc.LidoCircuitBreaker.processCreateMessage_establishes_officialRegistryStable`, `Blanc.LidoCircuitBreaker.processMessageCall_establishes_officialRegistryStable`
- **Premises:** the fresh constructor poststate, and disjointness of the two configuration slots from the Registry regions.
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **Gate:** `scripts/check-lido-circuit-breaker-deployment.sh`
- **Differential channel:** no direct oracle channel for the witness — the invariant's entry list is a Lean-side object with no image in a manifest that compares slot readings
- **Non-claims:** **the synthetic stable world receives no deployment credit.** The gate's second compiled control starts from that world, obtains only stability plus reflexive reach, and provably *cannot* manufacture the execution or receipt witness.
- **Source:** `reports/lido-circuit-breaker-deployment-root.md`, `reports/lido-circuit-breaker-history-h12.md:67-69`; `Blanc/LidoCircuitBreakerDeploymentMessage.lean:346`

#### DEP-6 — Every configured reachable future of the root keeps the exact runtime, admits some Registry witness, satisfies membership and index equivalence at any canonical target, and conserves the global count

- **Declarations:** `Blanc.LidoCircuitBreaker.DeploymentRoot.reflReach`, `Blanc.LidoCircuitBreaker.DeploymentRoot.reachable_registryStable`, `Blanc.LidoCircuitBreaker.DeploymentRoot.reachable_code`, `Blanc.LidoCircuitBreaker.DeploymentRoot.reachable_installedCode`, `Blanc.LidoCircuitBreaker.DeploymentRoot.reachable_witness`, `Blanc.LidoCircuitBreaker.DeploymentRoot.reachable_membership`, `Blanc.LidoCircuitBreaker.DeploymentRoot.reachable_countConservation`
- **Premises:** a deployment root, and configured reachability from it. **The total-wei-plus-withdrawals bound is inherited at every step and is not discharged here.**
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **Gate:** `scripts/check-lido-circuit-breaker-deployment.sh`
- **Differential channel:** no direct oracle channel, and unreachable in principle by any campaign — there is no artifact a chain-reachability claim could be checked against
- **Non-claims:** the witness is **existential**, not the checkpoint's list. No gas claim, no liveness, and nothing about any callee.
- **Source:** `reports/lido-circuit-breaker-deployment-root.md`; `Blanc/LidoCircuitBreakerDeploymentRoot.lean`

#### HIST-1 — From a checkpoint with the exact runtime installed and coherent storage, every reachable state is still stable — over arbitrary callee bytecode, arbitrary depth including same-instance re-entry, and arbitrary finite chains

- **Declarations:** `Blanc.LidoCircuitBreaker.chainUsing_preserves_registryStable`, `Blanc.LidoCircuitBreaker.chain_preserves_registryStable`
- **Premises:** reachability from the checkpoint (carrying the wei bound at each step), and stability at the checkpoint. What is **absent** is the claim: no premise about bytecode at any other address, no non-reentrancy condition, no direct-call-only restriction, no target honesty, no `PauseSuccessNoninterference`, no identification of the post-callback entry list with the checkpoint's, no count or interval coherence assumption, and no memory premise.
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **Gate:** `scripts/check-lido-circuit-breaker-history.sh`
- **Differential channel:** no direct oracle channel
- **Non-claims:** **not a deployment claim** — the checkpoint is a hypothesis, discharged for exactly one shape by DEP-1. Not a same-list claim, not liveness, not count/expiry coherence, and it says nothing about the callee.
- **Source:** `reports/lido-circuit-breaker-history.md`; `Blanc/LidoCircuitBreakerHistoryChain.lean`

#### HIST-2 — Endpoint coverage is a typed obligation quantified over the production dispatch list itself, so omitting an endpoint cannot typecheck

- **Declarations:** `Blanc.LidoCircuitBreaker.registrySpec_sound`, `Blanc.LidoCircuitBreaker.registrySpec_preserves`, `Blanc.LidoCircuitBreaker.registerPauser_funcSound`, `Blanc.LidoCircuitBreaker.pause_funcSound`
- **Premises:** two discharged endpoint obligations plus membership in the production function list. The pause endpoint visibly consumes its deeper-frame induction hypothesis and hands it on; the register endpoint does not take one, and that is a measured fact about the route rather than an oversight.
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **Gate:** `scripts/check-lido-circuit-breaker-history.sh`
- **Differential channel:** the views, non-payability, and ABI-boundary rows exercise the same dispatch surface finitely, but **do not corroborate the typed quantifier**
- **Non-claims:** soundness and preservation are **safety** properties. Nothing says any endpoint is reachable.
- **Source:** `reports/lido-circuit-breaker-history.md`; `Blanc/LidoCircuitBreakerHistory.lean`

#### HIST-3 — Coherence is transported across an arbitrary external call and across the pause route, which completes swap-and-pop unregistration *before* yielding to an arbitrary callee

- **Declarations:** `Blanc.LidoCircuitBreaker.coherent_of_call`, `Blanc.LidoCircuitBreaker.coherent_of_statcall`, `Blanc.LidoCircuitBreaker.coherent_pause`
- **Premises:** a depth-indexed induction hypothesis at the deeper frame. **No callee-code premise.**
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **Gate:** `scripts/check-lido-circuit-breaker-history.sh`
- **Differential channel:** five callback programs at depth two against one instance — same-target caught and bubbled, different-target caught and bubbled, and the clone-namespace row
- **Non-claims:** the clone-namespace rows show that selected clone worlds use **distinct storage owners**. They establish no clone constructor root, no joint root, no factory, proxy, or CREATE2 route, and no universal two-instance theorem.
- **Source:** `reports/lido-circuit-breaker-history.md`, `reports/lido-circuit-breaker-history-h12.md`; `Blanc/LidoCircuitBreakerHistoryChain.lean`

#### HIST-4 — The ladder from a single message call up to a whole chain preserves stability at every rung

- **Declarations:** `Blanc.LidoCircuitBreaker.processMessageCall_preserves_registryStable`, `Blanc.LidoCircuitBreaker.stateTransition_preserves_registryStable`
- **Premises:** the block rungs each take the wei bound explicitly; the transaction wrapper keeps the generic balance-sum and not-freshly-created premises where the ladder honestly needs them. Its result covers both successful and reverted inner execution and **never** equates outer successful processing with receipt success.
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **Gate:** `scripts/check-lido-circuit-breaker-history.sh`
- **Differential channel:** no direct oracle channel above the message-call rung — the campaign has no block, no receipt, no nonce or fee settlement, and no chain. The message-call level is corroborated by the 175 rows.
- **Non-claims:** these are inductions over the landed **generic** ladder, not a hand-written shadow transaction semantics.
- **Source:** `reports/lido-circuit-breaker-history.md`; `Blanc/LidoCircuitBreakerHistoryChain.lean`

#### HIST-5 — Both reachability relations are held open by compile-time controls that extend a reach chain by a block of which nothing whatever is assumed

- **Declarations:** `Blanc.LidoCircuitBreaker.reachUsing_extends_by_arbitrary_block`, `Blanc.LidoCircuitBreaker.reach_extends_by_arbitrary_block`
- **Premises:** reachability, the wei bound, and the step; the block is universally quantified.
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **Gate:** `scripts/check-lido-circuit-breaker-history.sh`
- **Differential channel:** no direct oracle channel, and unreachable in principle — the absence of a hypothesis is a property of a statement, and no fixture can witness it
- **Non-claims:** these are **controls, not results**. They assert nothing about the Registry; their job is that an additive narrowing of either reach constructor stops them elaborating, which no re-pinning can paper over.
- **Source:** `reports/lido-circuit-breaker-history.md`; `Blanc/LidoCircuitBreakerHistoryChain.lean`

#### HIST-6 — The family has models: the empty registry world satisfies stability, and the arbitrary-future consequences read fields inside the invariant rather than restating a header

- **Declarations:** `Blanc.LidoCircuitBreaker.emptyRegistryWorld_witness`, `Blanc.LidoCircuitBreaker.emptyRegistryWorld_registryStable`
- **Premises:** none beyond the statements.
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **Gate:** `scripts/check-lido-circuit-breaker-history.sh`
- **Differential channel:** no direct oracle channel
- **Non-claims:** the exhibit shows the theorems are not vacuous. **It is not a deployment and must never be reported as one.**
- **Source:** `reports/lido-circuit-breaker-history.md`; `Blanc/LidoCircuitBreakerHistoryEndpoints.lean`

#### HIST-7 — The differential campaign and the history family are non-overlapping evidence; neither subsumes the other

- **Declarations:** no audited declaration — gate-owned row
- **Premises:** the H12 reconciliation, which enumerates what each channel can and cannot see.
- **Axioms:** not applicable
- **Gate:** `scripts/check-lido-circuit-breaker-differential.sh`
- **Differential channel:** the full 175-row manifest, considered as a channel rather than as a set of cases
- **Non-claims:** three things are **unreachable in principle** by the campaign, not merely unmeasured: unbounded chain reachability, the invariant's entry list, and the absence of a hypothesis. Conversely the campaign sees things no theorem states, notably byte-level oracle agreement. Neither channel is evidence for the other's claims.
- **Source:** `reports/lido-circuit-breaker-history-h12.md`

---

## Pillar — Artifact conformance and cost

#### ART-1 — The Solidity reference is content-address-locked at v1.0.0 and reconstructed offline from vendored inputs

- **Declarations:** no audited declaration — gate-owned row
- **Premises:** the vendored source at the pinned release commit, and the schema-versioned reference lock. The mainnet deployment record is **evidence about the lock**, not a verification target.
- **Axioms:** not applicable
- **Gate:** `scripts/check-lido-circuit-breaker-reference.sh`
- **Differential channel:** the lock is the differential campaign's own oracle basis
- **Non-claims:** locking a source blob is not verifying a deployed artifact. The mainnet address, transaction, and block establish importance and provenance and nothing else.
- **Source:** `reports/lido-circuit-breaker-artifact-conformance-completion.md`; `scripts/lido-circuit-breaker-reference.json`

#### ART-2 — For arbitrary deployment parameters the production program compiles to the generated runtime bytes, and the official world's byte lengths and immutable offsets are exact

- **Declarations:** `Blanc.LidoCircuitBreaker.lidoCircuitBreakerCode_compile`, `Blanc.LidoCircuitBreaker.runtimeTemplateCode_length_exact`, `Blanc.LidoCircuitBreaker.officialFullCreateInput_length_exact`, `Blanc.LidoCircuitBreaker.officialFullCreateInput_eq_layout`, `Blanc.LidoCircuitBreaker.constructor_immutable_word_offsets_exact`
- **Premises:** the deployment parameters only.
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **Gate:** `scripts/check-lido-circuit-breaker-artifact-profile.sh`, `scripts/check.sh`
- **Differential channel:** the deployment axis of the differential campaign — constructor and runtime extraction and representative calls in deployed worlds
- **Non-claims:** compilation identity between Blanc's own program and Blanc's own emitted bytes. It says nothing about the Solidity compiler's output.
- **Source:** `reports/lido-circuit-breaker-artifact-optimization-completion.md`; `Blanc/LidoCircuitBreakerCode.lean`

#### ART-3 — On the finite resource vector the Blanc artifact is cheaper on every adequate boundary, with the declared out-of-gas controls equal

- **Declarations:** no audited declaration — gate-owned row
- **Premises:** the frozen 464-boundary vector and the pinned oracle.
- **Axioms:** not applicable
- **Gate:** `scripts/check-lido-circuit-breaker-differential.sh`
- **Differential channel:** the 464 resource boundaries and the 33 exact completion-threshold searches
- **Non-claims:** **this is a finite manifest-bound result and not a universal gas theorem.** Blanc's mandatory `.branch` control-flow representation can carry a small intrinsic dispatch overhead relative to a direct-jump implementation, so a universal dominance claim would be false rather than merely unproved. Any future positive row is admissible only through an explicit independent architecture-evidence rule.
- **Source:** `reports/lido-circuit-breaker-artifact-optimization-completion.md`; `plans/lido-circuit-breaker-program.md`

#### ART-4 — Compatibility is complete and fail-closed: no accepted behavioural deviation, no pending row, no unknown-mismatch allowlist, and no architecture exception

- **Declarations:** no audited declaration — gate-owned row
- **Premises:** the compatibility and deviation surfaces, checked against the locked reference.
- **Axioms:** not applicable
- **Gate:** `scripts/check-lido-circuit-breaker-reference.sh`
- **Differential channel:** the full manifest, whose green verdict is what makes an empty deviation registry meaningful rather than merely empty
- **Non-claims:** an empty deviation registry records that no deviation was **accepted**, not that none could exist outside the finite matrix. Storage representation may still differ from the original by design; `PORTING.md` owns that boundary.
- **Source:** `LIDO_CIRCUIT_BREAKER_COMPATIBILITY.md`, `LIDO_CIRCUIT_BREAKER_DEVIATIONS.md`

---

## Pillar — Pinned-target composition (entry 3)

This pillar is about two contracts at once, and it is the only pillar that is.
Everything above describes the CircuitBreaker alone; the rows below describe
what happens when the exact compiled Blanc **Triggerable Withdrawals Gateway**
runtime is the account the CircuitBreaker pauses.

Read the boundary carefully. The CircuitBreaker's own public pause family
(HOSTILE-5) is explicit that accepting a canonical `1` is evidence the target
*reported* success and never that the target is really paused — for an
arbitrary target that limit stands unchanged. These rows do not weaken it. They
replace the arbitrary target with one whose behaviour is separately proved, and
the pausedness in TWG-2's conclusion comes from the gateway family's own
account-level bundle, not from the CircuitBreaker's observation of returndata.

The two CircuitBreaker cells are likewise preserved by the gateway's proved
semantic descendant-write noninterference, not by an assumed callback equality:
`PauseSuccessNoninterference` is **discharged** here rather than assumed.

#### TWG-1 — The two families are connected by exact ABI agreement and one bundle specialization, with neither family importing the other

- **Declarations:** `Blanc.Composition.LidoCircuitBreakerTwg.pauseForCalldata_eq`, `Blanc.Composition.LidoCircuitBreakerTwg.isPausedCalldata_eq`, `Blanc.Composition.LidoCircuitBreakerTwg.gateway_lidoPinnedPauseTarget`
- **Premises:** for the ABI rows, none — both encoders are closed terms and the equalities are kernel-decided. For the specialization, the gateway's own quantified bundle theorem and the two accounts being distinct. The gateway bundle's four clauses are consumed whole; none is re-proved, restated or unfolded in the composition stratum.
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **Gate:** `scripts/check-layering.sh`, `scripts/check.sh`
- **Differential channel:** not applicable — this row is an interface identity, not an execution claim
- **Non-claims:** the ABI agreement is between *Blanc's* CircuitBreaker encoders and *Blanc's* gateway selector census. It is not a claim about any deployed Solidity contract's ABI, and `PORTING.md` owns that boundary. The specialization fixes the cell list `[countSlot pauser, heartbeatIntervalSlot]` and says nothing about any other storage cell.
- **Source:** `Blanc/Composition/LidoCircuitBreakerTriggerableWithdrawalsGateway.lean`

#### TWG-2 — A successful public pause of the directly installed gateway leaves it paused at the exact shared projection, sentinel included, with both CircuitBreaker cells preserved

- **Declarations:** `Blanc.Composition.LidoCircuitBreakerTwg.publicPause_gatewayPinnedTarget`, `Blanc.Composition.LidoCircuitBreakerTwg.gatewayBoundaryExecutions_of_afterSet_ok`, `Blanc.LidoCircuitBreaker.directBoundaryExecutions_of_afterSet_ok`
- **Premises:** the ordinary `PublicPauseEntryPremises` entry bundle naming the exact compiled gateway runtime as the installed target code; target/CircuitBreaker distinctness; the target account is not a precompile; the production `Prog.RunCompiledTo`; and a successful terminal polarity. There is **no code-shape premise at all**: non-delegation and a nonempty byte list follow from the compiler witness via `Blanc.not_delegation_of_compile` and `Prog.compile_ne_nil`, and nonzero installed width follows from the successful polarity via `pauseAfterSet_codeGuard_arms_windows`, whose zero-`EXTCODESIZE` arm reverts. There is **no** bundle premise, **no** program-occurrence premise, **no** accepted-query premise, **no** callback-noninterference premise, and **no** paused-result premise: both `MessageExecutesProgram` occurrences and the CALL/STATICCALL linkage are derived from the walk's own spawns.
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **Gate:** `scripts/check-claims.sh`, `scripts/check.sh`
- **Differential channel:** the gateway family's own differential manifest, which is what makes "the exact compiled runtime" a statement about the ported artifact rather than about an arbitrary program
- **Non-claims:** direct installation is the account shape proved here. A target behind a proxy is a **different instantiation** and is not licensed by this row; the later three-party convergence remains a separate unscheduled successor. This row says nothing about Lido's deployed Solidity, current mainnet code or role membership, liveness, gas sufficiency, or a second transaction. In particular it is **not** a sequential theorem that `triggerFullWithdrawals` reverts after this pause: the gateway family's protected-surface law is the exact boundary and is a statement about a paused entry projection, not about a history following this run.
- **Source:** `Blanc/Composition/LidoCircuitBreakerTriggerableWithdrawalsGateway.lean`; `Blanc/LidoCircuitBreakerPinnedTargetComposition.lean`

#### TWG-3 — The entry-3 premise bundle is satisfied by a concrete world holding the compiler's own gateway output, and its code premises are refuted by named mutants

- **Declarations:** `Blanc.Composition.LidoCircuitBreakerTwg.gatewayPauseWorld_publicPausePremises`, `Blanc.Composition.LidoCircuitBreakerTwg.gatewayPauseWorld_closedPremises`
- **Premises:** one concrete world installing the production CircuitBreaker runtime at its account and the exact compiled gateway runtime at the pause target, with only the explicit role, Registry, time and storage configuration. No code fact is restated in the world, because entry 3 asks for none. No literal byte string and no evaluator output is reflected into a theorem.
- **Axioms:** `propext`, `Classical.choice`, `Quot.sound`
- **Gate:** `scripts/check.sh`
- **Differential channel:** not applicable — this row is a satisfiability exhibit for TWG-2's premises
- **Non-claims:** **this row does not establish that the world's public pause run terminates successfully.** `gatewayPauseWorld_closedPremises` discharges every entry-3 premise *except* reachability, so it yields TWG-2's conclusion only when handed a successful production run of that world. A gateway-side compiled walk and its gas schedule are required to close that last premise, and are not part of this row; the finite-versus-sentinel duration arms are covered only by whichever run is eventually supplied. There is deliberately no code mutant: a mutant needs a hypothesis to falsify, and entry 3 has no code-shape hypothesis left. The ABI agreement remains falsifiable and is controlled.
- **Source:** `Blanc/Composition/LidoCircuitBreakerTriggerableWithdrawalsGatewayControl.lean`
