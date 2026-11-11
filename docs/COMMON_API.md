# Blanc common API registry

This is an inert, need-first map of contract-neutral Blanc APIs. Start at the
root question, follow the narrower branch, and inspect the named declarations
before writing a contract-local helper. It is deliberately a registry rather
than a tutorial: declaration types and module documentation remain the source
of truth.

For goal-sensitive advice, also run `blanc_suggest`. Its generated recipes now
print their validated registered symbols. For ordinary Lean search, use
`exact?`, `apply?`, `library_search`, and editor declaration search after this
registry has identified the likely vocabulary.

**Method-entry template (rule from 2026-11-01).** Most entries name
declarations. An entry that instead prescribes a *method* (how to discharge a
class of goals: a tactic route, a kernel decision, a chunking or batching
scheme, a generator option) must carry four lines, so that a wrong method
cannot stand unmeasured the way the hand-chunked Keccak recipe that produced
37k lines did:

```
- Probe: <the smallest goal or module the method was tried on, by path>
- Measured cost: <elaboration seconds and lines on that probe; kernel or heap if relevant; host>
- Simplest alternative tried: <the plainer route, e.g. one `decide +kernel` or an existing lemma, and its measured cost or why it fails>
- Date: <YYYY-MM-DD of the measurement>
```

A new or changed method entry without these lines is unmeasured guidance and
should not be added; recipes in `scripts/proof-recipes.toml` follow the same
rule in their `preferred_path` or `boundary` text. Existing entries gain the
lines when next changed or relied on, not by a wholesale rewrite.

## Root: what are you trying to do?

- Construct or analyze execution: go to [E — execution](#e--execution).
- Prove that an observation survives execution: go to
  [I — invariance and noninterference](#i--invariance-and-noninterference).
- Simplify or relate machine states: go to
  [S — state and machine updates](#s--state-and-machine-updates).
- Reason about bytes or EVM memory: go to
  [M — bytes and memory](#m--bytes-and-memory).
- Bind a block to its hash, check a trie root in the kernel, or state a hash
  premise: go to
  [M4](#m4-i-need-a-blocks-trie-root-its-header-hash-or-a-finite-hash-separation-premise).
- Reason about the integer exponential loop and its iteration count: go to
  [S9](#s9-i-need-the-integer-exponential-recurrence-or-a-finite-loop-witness).
- Relate raw execution to message/frame settlement: go to
  [T — settlement](#t--settlement).
- Relate source programs, compiled code, and deployed artifacts: go to
  [C — compilation and deployment](#c--compilation-and-deployment).
- Verify bytecode Blanc did not compile (a deployed contract's runtime
  bytes): go straight to
  [C9](#c9-i-need-to-verify-deployed-bytecode-blanc-did-not-compile), whose
  route map names its need-shaped sub-branches C9.1 onward.
- None matches: search public declarations in `Blanc/CommonCore.lean`,
  the eight `Blanc/CommonProofs/*.lean` pieces (`Base`, `Frames`, `MemImage`,
  `Messages`, `Walk`, `Hinv`, `NoDel`, `Balance`; import the piece you use), and the ladder (`Blanc/LadderBase.lean`,
  `Blanc/LadderSem.lean`, and `Blanc/Ladder.lean`, which states
  `ContractSpec` over them); a helper found only in a
  contract module is a hoisting candidate, not a cross-contract import target.
- Looking for a *definition* rather than a lemma: the compiled-program language
  (`Func`, `Prog`, `Line`, `Ninst`, `Linst`, `Stack`) lives in
  [`Blanc/Semantics.lean`](../Blanc/Semantics.lean). The EVM-generic
  execution layer is **Jaune's**, not Blanc's: the canonical `Exec` relation,
  its inversions and adequacy (`exec_iff_exec_eq`), the frame/step relations
  and `*.At` decode predicates, derivations (`Exec.Deriv`, `□p`, `≺`, `→p`),
  settlement (`Frame.settlementCommits`, `Exec.descendantFrames`,
  `Exec.committedFrames`), raw/retained chronology (`Exec.rawNodes`,
  `Exec.retainedNodes`, `ParentStep`/`ParentPrefix`) and message execution
  are declared under `Jaune.*` in the pinned Jaune package's
  `Jaune/ExecFrame.lean`, `Jaune/Exec.lean`, `Jaune/ExecDeriv.lean`,
  `Jaune/ExecSettlement.lean`, `Jaune/ExecChronology.lean` and
  `Jaune/MessageExecution.lean`. Blanc imports them through
  `Blanc/Semantics.lean`, `Blanc/CommonCore.lean`,
  `Blanc/ExecutionSettlement.lean`, `Blanc/ExecutionOccurrence.lean` and
  `Blanc/MessageExecution.lean`, and every Blanc module `open`s `Jaune`, so
  the short names below resolve to the Jaune declarations. Blanc keeps its
  own theory about them (for example the `Blanc.Exec.*` occurrence,
  source-cursor and replay lemmas), which is where the branches below
  point; a new EVM-generic execution fact belongs in Jaune (Jaune's `API.md`
  maps its supported surface; section 6 lists the lemma families for
  downstream proof libraries), and
  `scripts/check-extraction-ownership.sh` fails if Blanc redeclares a
  relocated declaration. Blanc's own list
  prefix/split algebra (`Split`, `Pref`, `Frel`) lives in
  [`Blanc/Basic.lean`](../Blanc/Basic.lean). Both are the substrate the
  branches below are stated over, so read the declaration and its module
  documentation there rather than expecting a need-first branch for it.
- Extend a tail-recursive fold by one final input:
  [`Blanc/ListFold.lean`](../Blanc/ListFold.lean)'s `fold_snoc_of_equations`
  derives the snoc equation from the supplied empty-list and cons equations,
  for arbitrary input and state types.
- Exact byte-pattern offsets: [`Blanc/BytePattern.lean`](../Blanc/BytePattern.lean)'s
  `BytePattern.occurrences` scans successive suffixes in increasing order.
  Empty patterns yield no offsets. Every byte offset is
  considered, including instruction immediates; these facts alone say nothing
  about parsing or execution.
- Fork coverage: `CoveredFork f` (`f ∈ coveredForks`) in `Blanc/Semantics.lean`.
  Consume it only through `CoveredFork.stateGas_none`, `bal_none`,
  `rules_stateGas_none`, `rules_bal_none`, `rules_access`, `rules_push0`,
  `rules_shifts`, `rules_touchedSweep`, `rules_refundQuotient`, `rules_dataNonZero`,
  `rules_calldataFloor`, `rules_sstore`, `requests_eq`,
  `beaconRoots_not_precompile`, `historyStorage_not_precompile`, `of_eq` and,
  where a per-fork case split is unavoidable, `CoveredFork.cases`. Discharge a
  schedule premise with a concrete config lemma. `mainnetChainConfig_covered` takes both the
  real block number and timestamp and requires
  `mainnetPragueTimestamp ≤ timestamp`; it does not cover historical mainnet
  selections before Prague.
  For such a schedule, preserve an invariant along a configured chain with
  [`Blanc/LadderReached.lean`](../Blanc/LadderReached.lean):
  `ContractSpec.chainUsing_preserves_inv_of_reached` asks coverage only at or
  after a timestamp floor and a starting tip at or past it, and
  `stateTransitionUsing_reachedStep` gives the strictly-later block and new tip
  of one accepted step. `BlockChain.ReachUsing.tip_floor` carries the tip's
  floor along a reach, `stateTransitionUsing_covered_of_reached` covers one
  floored step, `ExecutionTrace.exists_configuredHistoryTrace_of_reachUsing_of_reached`
  builds a configured history over a floored segment, and
  `mainnetChainConfig_pragueTimestamp_le_of_covered` is the converse of
  `mainnetChainConfig_covered` (a covered mainnet selection is at or after
  Prague), which turns a covered deployment block into the floor's start.
  To move an execution *between* covered forks, use
  [`Blanc/ForkUniform.lean`](../Blanc/ForkUniform.lean): `withFork` replaces the fork on
  `Sevm`/`Evm`/`Msg`/`Frame`; `evm_step_withFork` (one step commutes at an
  `InstNeutralAt` node: not `CLZ`, and `BLOBBASEFEE` only at zero excess blob gas),
  `frame_enter_withFork` (a `Frame.PrecompNeutral` frame: no `MODEXP`/`P256VERIFY`),
  `settle_withFork`, `Exec.withFork` (an `ExecNeutral` derivation, node for node) and
  `exec_withFork`, `exec_out_withFork`, `runFrame_withFork`, `processMessage_withFork`,
  `processCreateMessage_withFork` (same outcome). A closed `*_deploy` instance needs none of
  this when its general `*_create` already quantifies `CoveredFork`.
  The lower `genericCall_step_withFork`, `spawn_ofCreate_withFork`, and
  `executePrecomp_withFork` helpers also require both source and destination
  coverage: inherited deletion snapshots and BN254 gas are historical rule
  reads. `settleMsg_withFork` requires coverage of both saved messages as
  well as the destination. These are covered-fork transports, with no claim
  of equality across arbitrary historical forks.
- For the forks from Shanghai on (rule facts and
  `CoveredFork`'s coercions into the domain and the `CALL` family's `CallEra`), use
  [`Blanc/ShanghaiOnwards.lean`](../Blanc/ShanghaiOnwards.lean).
- Historical extraction uses the separate `HistFork` / `histForks` domain in
  [`Blanc/HistoricalFork.lean`](../Blanc/HistoricalFork.lean): exactly Byzantium through
  BPO2, including synthetic Constantinople and excluding Amsterdam.
  `HistFork.stateGas_none`, `bal_none`, and `neutral` supply the two
  `NeutralFork` projections. `HistFork.requests_covered` derives existing
  `CoveredFork` coverage only when the selected fork enables requests;
  `CoveredFork.histFork` embeds modern coverage. `mainnet_histFork` applies to
  an actual successful lookup at both number and timestamp, without asserting
  a selection below the schedule's floor. These facts retain historical runs;
  they supply no opcode, gas-price, settlement, invariant or reward-free law.
- Build a configured block *forward* from proof-produced evidence about its
  parts (a reachable history, a counterexample, a liveness witness): go to
  [T7](#t7-i-must-construct-a-configured-block-forward-from-its-parts).

## E — execution

### E1. I need to construct a source or compiled execution term

- Stack/gas frame composition in
  [`Blanc/CommonCore.lean`](../Blanc/CommonCore.lean):
  `Devm.popBurn_of_pop_of_burn`, `pushBurn_cons_popBurn_cons`,
  `burn_of_popBurn_nil`, `burn_of_pushBurn_nil`, `burn_trans`,
  `popBurn_of_burn_of_popBurn`, and `popBurn_of_popBurn_of_pop` retain
  every canonical `Devm.Rel` field, including `touchedAccounts`.
  `push_of_pushAt` inverts a successful execution at a retained PUSH;
  the invalid-PUSH0 availability branch cannot be that execution.
  Choose the composition by its premises; a shared `Devm.Rel` conclusion
  alone does not distinguish these routes.
- Ordinary source `Func.Run` walk:
  `func_execute`, `func_execute_with`, and the split lemmas in
  [`Blanc/Tactics.lean`](../Blanc/Tactics.lean).
- A compiled walk that pushes a closed hash word (or a word hidden behind a `Line`): `func_run` evaluates the PUSH cost (and any `rfl`
  value obligation) by `whnf` before it scans local equations, so unfold the
  `Line`, prove `pushCost w.toBytes.sig = gVerylow` once by
  `pushCost_of_ne_zero (by decide +kernel)`, and
  `generalize hq : w = v at hcost ⊢` *before* `apply Func.execSat_segment` (its
  end-state metavariable must be created inside the generalized context);
  `subst hq` once the segment is closed. Three more depth causes recur in
  the same walks: a dead inner `setMach` left by a lemma step (`simp only
  [Devm.setMach_setMach, Devm.stateGas_setMach]`, or `rw [addLog_setMach,
  Devm.setMach_setMach]` after a `LOG`); a stuck `rfl` on a comparison value
  obligation such as `Nat.toB256 len <? 32 = 0` (state the hypothesis in the
  walk's exact form so the syntactic local check takes it first); and a
  `cases r <;> first | rfl | …` over `Rinst` whose failing `rfl` branch runs
  first (put the cheap refuting branch first, `Rinst.runCore_pc_irrel`).
- Constructive opcode helpers in [`Blanc/Forward.lean`](../Blanc/Forward.lean)
  expose their actual rule requirements: an empty PUSH immediate requires
  `rules.op.push0`, while nonempty immediates do not; the cold/warm SLOAD and
  SSTORE helpers require EIP-2929 access, and SSTORE additionally requires the
  net-metering/stipend-sentry regime. EXTCODESIZE names its zero surcharge and
  cold-price field where needed. SSTORE retains the actual gas record in its
  refund formula, including Berlin's refund schedule. State-gas absence alone
  supplies none of those activation or access facts.
  For existing covered consumers, use `CoveredFork.rules_access`,
  `rules_push0`, `rules_sstore` and
  `BenvStat.gas_eq_prague_of_covered`; the latter replaces the invalid inference
  from state-gas absence to Prague gas prices. Its EXTCODESIZE projections are
  `CoveredFork.rules_codeReadSurcharge` and `CoveredFork.rules_coldAccountAccess`,
  and the selected transient-storage, `CHAINID` and `BASEFEE` flags are
  `CoveredFork.rules_transient`, `rules_chainId` and `rules_baseFee` (all in
  [`Blanc/Forward.lean`](../Blanc/Forward.lean)).
- For flat account-access pricing, `Ninst.runCompiled_extcodesize_flat` in
  [`Blanc/ForwardFlatAccess.lean`](../Blanc/ForwardFlatAccess.lean) constructs
  the exact EXTCODESIZE step from `rules.access = .flat prices`,
  `rules.bal = none`, the actual stack, exact entry gas
  `G + prices.extCode + rules.gas.codeReadSurcharge`, and stack room.
  It returns the actual pre-state code-size word, preserves `d.stateGas`,
  and needs no covered-fork, staticness or selected code-size premise.
- For the loose gas-free walk prefix reaching an intermediate cut of a
  successful source run, with source-path accumulation, use
  [`Blanc/RunPrefix.lean`](../Blanc/RunPrefix.lean).
  `Func.RunPrefix` ends at an explicit target path, state, and body rather
  than a terminal result, and every crossed instruction carries a
  `Ninst.gasFree` certificate. `RunPrefix.line` builds a prefix across a
  gas-free line, `RunPrefix.trans` composes prefixes, `Func.Run.of_prefix`
  splices a completion run back onto a prefix, and the `of_run_prepend`,
  `of_run_branch`, and `of_run_call` twins expose the prefix alongside the
  corresponding elimination. `Func.RunPrefix.getBal_eq` shows a prefix moves no ETH (every
  crossed instruction is gas-free). Paths accumulate exactly as in
  `Func.sourceSites`, with the extended path in the premise so elimination
  never reduces paths. A prefix into a line is unconstructible without that
  line's gas-free certificate. Registered triggers were checked: the
  `implication-premise:Func.Run` tag advises splitting a run hypothesis
  rather than constructing or consuming a prefix, and no goal-head or
  goal-shape trigger names the prefix conclusion, so discovery remains in
  this registry.
- For a successful source branch whose selected arm calls a known
  nonreturning auxiliary, use `of_run_branch_call_of_not_run` in
  [`Blanc/CommonProofs/Balance.lean`](../Blanc/CommonProofs/Balance.lean).  Its shared
  specializations `of_run_branch_call_revert`,
  `of_run_branch_call_revertWith`, and
  `of_run_branch_call_revertReturnData` cover the standard empty,
  constant-payload, and returndata-bubbling reverters.
- Known stack steps without a tactic arm: `prefix_of_mul`, `prefix_of_div`,
  `prefix_of_timestamp`, `prefix_of_xor` and `prefix_of_extcodesize_val` in
  [`Blanc/CommonProofs/Walk.lean`](../Blanc/CommonProofs/Walk.lean), and
  `prefix_of_argCheckNonAddress` in
  [`Blanc/CommonProofs/Balance.lean`](../Blanc/CommonProofs/Balance.lean).
  The `EXTCODESIZE` helper pins the exact code-size word from the instruction's
  input state and carries unchanged memory across address warming.
- Peel the shared `nonpayable` entry wrapper on a source run with
  `run_body_of_run_nonpayable_frame` (in
  [`Blanc/CommonProofs/Hinv.lean`](../Blanc/CommonProofs/Hinv.lean)); it derives zero call value.
- Ordinary compiled success walk (`Func.RunCompiled`): `func_run` and the
  opcode constructors in [`Blanc/Forward.lean`](../Blanc/Forward.lean).
  `MSTORE` and `MSTORE8` each consume the next numeric memory-expansion hint;
  the hint remains checked by the instruction's exact `Devm.extCost` premise.
  `SHL`/`SHR`/`SAR` step through `Rinst.runCore_{shl,shr,sar}_of_shifts`, whose
  selected-shift premise comes from a local hypothesis or from
  `CoveredFork.rules_shifts` (in [`Blanc/Semantics.lean`](../Blanc/Semantics.lean));
  a nonempty `PUSH` closes its PUSH0 guard by `B256.toBytes_sig_ne_nil`, or by
  `push0_guard_of_pushCost_verylow` from a `pushCost … = gVerylow` premise.
  `CHAINID` and `BASEFEE` step the same way through
  `Rinst.runCore_{chainid_of_chainId,basefee_of_baseFee}`.
- Compiled walk with an arbitrary terminal outcome (`Func.RunCompiledTo`):
  [`Blanc/Reverts.lean`](../Blanc/Reverts.lean).
- Storage access on a fork with a `StateGasRules` record, under any meter: `rx_sstoreS` over
  `sstoreTotalA` (execution gas plus `sstoreSpillA`, the state gas the reservoir cannot cover) and
  `sstoreRepayA` (a credit against an earlier spill), inverted by `ri_sstoreA`, `ri_sstore_nonstaticA`
  and `ri_sloadA`; `rx_sstoreA` over `sstoreCostA` / `afterSstoreA` is its no-spill projection (with
  `sstoreChargeA`, `sstoreCreditA`, `sstoreMeterA`, `chargeStateGas_of_le`, `chargeStateGas_spill`,
  `chargeStateGas_ok_inv`, `chargeGas_ok_of_eq`, `sstoreAmsterdamRefund_ge` and the
  `afterSstoreA_*` observers), `Ready` and `rx_sstoreR` for a frame's stores, `readsBase` and `readsGas`
  for a list of reads, `rx_sloadV` naming the value read, and `rx_sloadA` over `sloadCost` / `afterSloadA` are in
  [`Blanc/Lift/AmsterdamWalk.lean`](../Blanc/Lift/AmsterdamWalk.lean), stated against the record, not
  literal prices. `Ninst.runCompiled_sloadA` (`Blanc/ForwardCall.lean`) needs only EIP-2929 access;
  `Ninst.runCompiled_sload_selected` is it where the read record vanishes.
- Selected storage access uses the neutral `sloadCost` / `afterSload` and
  `sstoreCost` / `afterSstore` carriers in
  [`Blanc/ForwardStorageAccess.lean`](../Blanc/ForwardStorageAccess.lean).
  Its projection API includes unchanged storage on a non-target account,
  code, addresses, logs, account-deletion set, output, and error; the
  target-storage, refund-counter, and key-set equations expose the selected
  write, refund update, and warm/cold access update.  The lower
  whole-machine transport uses `afterSload_setMach`, `afterSstore_setMach`
  and `addLog_setMach` from
  [`Blanc/ForwardCall.lean`](../Blanc/ForwardCall.lean). They commute each
  selected world update with `Devm.setMach`, preserving warm keys, refunds and
  logs while a caller changes stack, memory and gas. Apply them over a symbolic
  base before substituting a concrete machine image. The existing recipe
  `devm-common-update-law` matches exposed `memWrite`, `addAccessedStorageKey`
  or `setStorVal`, not these whole carrier equalities; discovery stays here
  instead of broadening that trigger or unfolding a concrete state tower. The lower
  one-write primitive is `setStorVal_getStor_ne` in
  [`Blanc/CommonProofs/Base.lean`](../Blanc/CommonProofs/Base.lean).
- Read-through laws of a selected `SLOAD`, also in
  [`Blanc/ForwardStorageAccess.lean`](../Blanc/ForwardStorageAccess.lean):
  `afterSload_getStorVal` / `afterSload_getOrigStorVal` /
  `afterSload_getTransVal` (reads pass through), `afterSload_warm` (the read
  key is warm after), `afterSload_preserves_warm` and `not_mem_afterSload` /
  `afterSload_preserves_cold` (other keys keep their status),
  `afterSload_cold_keys` (a cold read inserts exactly its key),
  `afterSload_accessedStorageKeys_addLog`, `sloadCost_congr` (the charge reads
  only the key set) and the `Std.HashSet` helper `not_mem_hashSet_insert`.
- For exact ordered SLOAD accounting, `SloadSchedule` retains the incoming
  state and key at each read. `sloadScheduleCost_eq` separates the warm base
  cost from the cold surcharge, and `sloadColdCount_le` /
  `sloadScheduleCost_le` bound that schedule in
  [`Blanc/StorageAccessGas.lean`](../Blanc/StorageAccessGas.lean).
  The same module bounds an SSTORE: `sstoreCost_le_value` (cold access plus the
  value charge), `sstoreValueCost_le` (at most a fresh set) and
  `sstoreValueCost_of_ne` (a dirty slot costs the warm charge).
- Jaune prices `SSTORE` from the machine original read `Devm.getOrigStorVal`,
  which is `0` at an account created in this transaction and the snapshot
  otherwise. In [`Blanc/ForwardStorageAccess.lean`](../Blanc/ForwardStorageAccess.lean),
  `afterSload_createdAccounts` / `afterSstore_createdAccounts` carry the
  created-account set across the selected steps (`Devm.addLog_createdAccounts`
  in `Blanc/CommonProofs/Messages.lean` across a log), `getOrigStorVal_congr_created`
  transports the read between machines with equal created sets,
  `getOrigStorVal_of_not_created` reduces it to the snapshot at an uncreated
  owner, `actualOrigStorVal_eq_zero_of_raw` turns a zero snapshot into a zero
  machine read, and `addAccessedStorageKey_getOrigStorVal` crosses key
  warming. Keep a snapshot premise and convert it with these rather than
  restating a theorem on the snapshot read.
- `sstoreNewRefundCounter_ge_of_original_eq_current` proves an SSTORE whose
  original and current slot values agree cannot decrease an arbitrary refund
  counter; `afterSstore_refundCounter_ge_of_original_eq_current` carries this
  to the selected warm/cold SSTORE state for checked-message settlement; more
  generally `RefundSafe orig cur` (original equals current, original zero, or
  current nonzero) rules out the clearing-reversal branch:
  `sstoreNewRefundCounter_ge_of_safe` / `afterSstore_refundCounter_ge_of_safe` in
  [`Blanc/StorageRefund.lean`](../Blanc/StorageRefund.lean).
  `refundSafe_of_snapshot_eq` derives `RefundSafe` at the machine original read
  from a snapshot-equals-current premise, and `sstoreValueCost_zero_le_of_safe`
  bounds the charge at a zero (created-account) original by the charge at a
  `RefundSafe` snapshot original, so a snapshot-priced bound remains an upper
  bound.
- `ShaCallPost`
  (precompile calls) keeps the refund counter (`ShaCallPost.refund`).
- Invert an existing arbitrary-outcome compiled walk:
  [`Blanc/CompiledWalkInversion.lean`](../Blanc/CompiledWalkInversion.lean).
  Use `runCompiledTo_next_inv`, `runCompiledTo_branch_inv`,
  `runCompiledTo_call_inv`, and `runCompiledTo_prepend_inv` for structural
  nodes; `runCompiledTo_last_inv`, `runCompiledTo_revert_inv`, and
  `runCompiledTo_revertSelector_inv` for terminal/revert nodes.  The shared
  `iszero_stack_inv` also transports the unchanged memory and return data.
  Known impossible successful terminals/calls use `Linst.not_run_revert_ok`,
  `Func.RunCompiledTo.not_ok_revertData`,
  `Func.RunCompiledTo.not_ok_call_revertData`,
  `Func.RunCompiledTo.not_ok_call_revert`, and
  `Func.RunCompiledTo.not_ok_call_revertSelector`; successful `STOP` identity is
  `Func.RunCompiledTo.stop_eq`.  For exact constant-data revert payloads and
  their persistent/transient/log frame, use
  `runCompiledTo_revertData_frame_inv`; when the reverter is reached through a
  known auxiliary call, use `runCompiledTo_call_revertData_frame_inv` so the
  payload conclusion remains tied to that call walk.  For a known branch-head prefix use
  `Func.RunCompiledTo.zero_branch_of_prefix` or
  `Func.RunCompiledTo.succ_branch_of_prefix`, both outcome-polymorphic.  A
  successful branch whose jumped arm is a fixed empty-data reverter can be
  collapsed directly with `Func.RunCompiledTo.zero_branch_of_ok_call_revert`;
  it returns the fall-through walk and branch pop.  Use the neighboring
  `_of_prefix` form when the forced zero head and preserved known tail are
  also needed.  For any separately established nonreturning right arm, use
  `Func.RunCompiledTo.zero_branch_of_ok_of_right_not_ok` and its prefix form
  instead of adding a reverter-specific branch lemma.  A
  successful shared `nonpayable` wrapper is peeled by
  `Func.RunCompiledTo.nonpayable_body_of_ok`, which also derives zero value and
  preserves the known stack tail and storage.  If zero value is already known
  but the terminal outcome is arbitrary, use
  `Func.RunCompiledTo.nonpayable_body_of_value_zero`.
  To invert the rejecting arm instead, use
  `Func.RunCompiledTo.nonpayable_revert_of_value_nonzero`: a nonzero call
  value forces the wrapper's empty-revert path before any premise about the
  protected body is needed.
  This remains COMMON_API-only: the same `Func.RunCompiledTo` head is also the
  reliable trigger for construction recipes, so an automatic recipe would
  conflate constructing and inverting a walk.
- Carry an observable through a successful compiled walk with a fixed
  function table using `Func.CompiledInv` in
  [`Blanc/CompiledFixedInvariance.lean`](../Blanc/CompiledFixedInvariance.lean).
  Its `call` rule requires both the exact table lookup and the callee
  invariant, closing the soundness gap that makes table-polymorphic
  `func_inv` refuse `Func.call`.  `compiled_inv` walks ordinary lines,
  instructions, branches, and terminals and consumes an already-proved exact
  call invariant at each tail jump.  The same module completes the opt-in
  `LogOutputHinv` scope for ordinary arithmetic (`MUL`, `SUB`, `DIV`, `MOD`,
  `ADDMOD`, `MULMOD`, `XOR`, `RETURNDATASIZE`, and `MLOAD`) and exposes
  generic branch/call burn preservation, so contract modules do not redeclare
  those instances privately.
- **Solidity address-slot reads and writes.** `Blanc.loadAddressWordAt` and
  `Blanc.storeAddressWordAt` in
  [`Blanc/AddressSlot.lean`](../Blanc/AddressSlot.lean) implements the raw storage
  behavior of an `address`-typed storage reference: loads discard the raw
  upper 96 bits, while assignments preserve those bits and replace only the
  low 160 bits.  Use `addressSlotReadWord` and `addressSlotWriteWord` for the
  matching pure word projections; `addressSlotReadWord_eq_toAdr_toB256` ties
  the low-word projection to the ordinary address conversion, and
  `addressSlotReadWord_write_of_clean` gives the public read after a packed
  write of an address-shaped word; `addressSlotReadWord_get_set_packed`
  frames that read through a concrete storage update.  `addressMask_and_eq_zero_of_lt`
  gives the mask fact directly from a `word.toNat < 2 ^ 160` bound (the
  contract-neutral address-width fact), and
  `addressSlotReadWord_eq_self_of_lt` is its corollary for a value already
  known to read back clean, without a second word or
  `addressSlotReadWord_write_of_clean`.  The
  value-carrying inversions
  `of_loadAddressWordAt_val` and `of_storeAddressWordAt_val` live in
  [`Blanc/AddressSlotProofs.lean`](../Blanc/AddressSlotProofs.lean), with the
  `PUSH20 0xff..ff` literal as the mask (`ff20_eq`, `ff20_and_word`,
  `ff20_and_and`) and `addressMask_and_write_of_clean` (a packed
  write of a clean word keeps the raw upper ninety-six bits).
  Use it when delegated code can make a nominal address slot raw-dirty; a plain
  full-word `SSTORE` is observably different in that state.
- Calls, delegate calls, or child-frame resumption: go to E2.
- A predicate must hold for every entered child root: go to E3.
- Only the terminal RETURN/REVERT remains: go to E4.

### E2. The walk crosses a child frame

- Value-call initialization and memory projections:
  `Blanc/Lift/CallMessageFacts.lean` owns the `vcsm_*`
  projections, `mem_read_fst`, `callSpawnParent_memory_data` and
  `addAccessedAddress_setMach_memory` in `Blanc.Lift`.

Use [`Blanc/ForwardCall.lean`](../Blanc/ForwardCall.lean):

- `Func.ExecWitness` / `Prog.ExecWitness` package raw call outcomes.
- `Prog.ExecWitness.intro` pays the compiled program's leading `JUMPDEST` for
  a caller-named success or fatal-error witness; use
  `Func.ExecWitness.prepend_fsig` and `fsigCost` to construct the shared
  four-instruction selector prefix before the residual function. The prefix
  requires the actual `rules.op.push0 = true` flag; its SHR availability is
  derived from that flag under the named fork rules.
- `Func.runCompiledTo_mstoreAt` keeps the continuation over an abstract memory
  image. Its availability premise is conditional on the actual
  `(word * 32).toBytes.sig` immediate being empty; nonempty pushes need no
  PUSH0 flag. Derive the flag from the actual rules or
  `CoveredFork.rules_push0`, rather than from state-gas absence.
- `Func.ExecSat` / `Prog.ExecSat` package predicates over outcomes.
- `Func.execSat_sload_step_with_nonce`,
  `Func.execSat_sstore_warm_step_with_nonce`, and
  `Func.execSat_log_step_with_nonce` also pass equality of every account nonce
  to the continuation, immediately after code equality. Use them when a walk
  must transport nonce-based account protection. The original step helpers
  retain their signatures as wrappers that discard this additional fact.
- For one external call with a gas-independent exact debit and canonical
  successor, use `ExactCallProfile` in
  [`Blanc/Lift/ExactCallProfile.lean`](../Blanc/Lift/ExactCallProfile.lean).
  Its `entry_gas` identifies the metered input gas; `congr` fixes the debit
  and every successor column except gas, including returndata and access
  sets. `sound` keeps the exact debit equation. `runExact`, `runEx`, and
  `runExact_residual` prepend the call while retaining that equation and
  successor for the continuation. Headroom is a separate `Ready` condition.
  `allGasStaticCallEntry`, `allGasZeroCallEntry`, `CallWindowReady`,
  `StaticWordCallProfile`, and `MutableCallProfile` specialize this interface
  to all-gas word-reply windows, preserving world transitions, result-stack
  room, and identity-precompile readiness. These are per-call premises;
  constructing a profile still requires the callee's exact run and stability.
- The `Ninst.runCompiled_*call*` family constructs concrete call crossings.
- When the walk already holds the callee's own exact run, use
  [`Blanc/Lift/ExactWalkCallChild.lean`](../Blanc/Lift/ExactWalkCallChild.lean):
  `Ninst.runCompiled_call_nonzero_child` resumes a nonzero-value `CALL` into a
  non-precompile callee from `exec (initEvm (callChildMsg …)) = .ok cpost` with
  `cpost.error = none`, the child message being the parent-built message over
  the debited world with empty-caller storage writes cleared and the callee
  credited; the parent lands in `callChildPost` (child world and
  warm sets adopted, gas returned, flag `1` pushed, output copied), and
  `callChildPost_facts` projects every field when the child returned nothing.
  A lifted callee supplies `exec … = .ok _` through `exec_iff_exec_eq` from its
  `Exec` derivation; a code-free callee is `Ninst.runCompiled_call_nonzero_codeFree`.
  `adrSet_union_isEmpty` carries an empty deletion set through the resumed
  parent's `accountsToDelete` union.
  The zero-value sibling is `Ninst.runCompiled_call_zero_child` (child message
  `callChildMsg … 0 …` keeps the entry environment and ignores `stmid`);
  `callChildPost_facts_zero` projects the resumed parent
  when the output window is empty, whatever the child returned.
- For an exact fixed-width word writer over a real zero-value CALL, use
  [`Blanc/Lift/SystemWordWriter.lean`](../Blanc/Lift/SystemWordWriter.lean):
  `program_compile` identifies the 65-byte PUSH32/MSTORE/CALL/STOP runtime,
  `childMsg_data` identifies its full word input, and `exec` consumes the actual
  parent-built child execution equation and clean child error under `CoveredFork`
  and its explicit CALL admission premises. `post_facts`, `post_code` and
  `post_storage` expose the settled child effects and status one. The child law
  and a closed kept-history control remain separate obligations.
- `accessDelegation_worldMeta` carries transient storage and the storage-access
  warm set through the exact delegation-resolution equation;
  `accessDelegation_createdAccounts` carries the created-account set.
- `state_subBal_stor` preserves every account's storage across a successful
  balance subtraction in call settlement.
- `hashSetPair_mem_union_right` transports a known `(Adr × B256)` membership
  into the right side of a warm-key union without unfolding concrete hashes.
- `Ninst.ChildlessRunCompiled` strengthens one compiled instruction with a
  definitionally empty recursive slot; `.toRunCompiled` forgets that fact,
  while `childlessRunCompiled_exec_doneFrame` and
  `childlessRunCompiled_staticcall_doneFrame` construct it for synchronously
  resolved frames.
- `Func.exec_of_runCompiledTo` and its program bridge recover an `Exec`
  derivation from a completed arbitrary-outcome compiled walk.
- When a frame invariant must retain block statics across a child spawn, use
  `genericCall.step_spawn_benvStat`, `genericCreate.step_spawn_benvStat`, or
  the instruction-neutral `Xinst.step_spawn_benvStat` (Jaune's
  `Jaune/Exec.lean`), then combine it with
  `Frame.enter_run_benvStat` or `RunFrame.benvStat_eq` after entry. When the
  spawn runs under Amsterdam state-gas rules, use the
  `genericCallAmsterdam`/`genericCreateAmsterdam` `step_spawn_depth` and
  `step_spawn_benvStat` mirrors instead; `Xinst.step` selects them on
  `stateGas`.

For an exact `DELEGATECALL` boundary, use
[`Blanc/DelegatecallEnvelope.lean`](../Blanc/DelegatecallEnvelope.lean).
`DelegatecallSpawnDescriptor` records the real stack, memory-extension,
delegation-resolution, access-charge, EIP-150 split, depth, and precompile
equations; its `parent`, `child`, and `resume` are the actual Jaune constructors,
`.afterAccess_memory` records that delegation resolution preserves the call
memory, `.step` recovers the exact `.delegatecall` spawn, `.child_data` exposes the
exact input-memory window, and `.crossing` discharges the entered child frame.  A
`DelegatedChildCertificate` retains the recursive child trace without assuming
an outer result; `.process` recovers its relational `ProcessMessage` witness and
`.result` recovers the exact total `processMessage` equation.  When the proof
starts from an already-successful compiled `DELEGATECALL` step,
`DelegatecallSpawnDescriptor.certificate_of_runCompiled` inverts that step into
the arbitrary retained child outcome and the exact resume equation instead of
requiring the consumer to reconstruct the recursive slot.  For a compiled step
being constructed from an already-retained child trace, use
`DelegatecallSpawnDescriptor.runCompiled_of_certificate`; it combines the
certificate with the exact resume equation and derives the actual compiled
`.delegatecall` step for the descriptor's own child.  For a compiled step
that has already settled back into an ordinary parent state,
`DelegatecallSpawnDescriptor.settled_of_runCompiled` packages the retained
child as a `DelegatecallSettledBoundary`, including the exact returndata,
status-word stack, state, transient-storage, and log equations.  Its `.memory`
theorem exposes the exact resumed output write; for calls with a zero output
window, use `.memory_eq_parent_of_outputSize_zero` or the stronger
`.memory_image_of_outputSize_zero` to carry `Mem.Wf` and `Mem.Reads` across the
parent extension and empty resume write.  On its failure arm,
`DelegatedChildCertificate.rollback_of_error` recovers the child-entry
state and transient storage before the caller classifies or bubbles the payload.
Keep direct-call
comparison separate through
`DirectToDelegatedContext` and the implementation-specific
`DirectTargetTransport`; this interface explicitly exposes gas, depth, access,
transfer, code-address, and storage-owner changes.

To invert an existing source `Ninst.Run` over a direct call whose operands are
already known, use the shared inversion pair in
[`Blanc/LadderBase.lean`](../Blanc/LadderBase.lean) — do not re-derive the
spawn/resume equations at the consumer:

- `of_run_call_val_with_depth_frame`: from a known 7-operand stack prefix
  (`g :: c :: v :: ii :: is :: oi :: os :: xs`) and
  `Ninst.Run sevm s Ninst.call sf`, either the failed arm (flag `0` plus
  `Devm.WorldEq s sf`) or the entered arm (`Ninst.StepRun`, `0 < depth`, exact
  parent stack/state/memory/logs/output, both delegation-resolution arms,
  `Xlot.Filled`, the exact `ProcessMessage (callMsg …)` child with a clean
  result, the exact `Resume.call` equation, and the `sf` state/returndata/
  memory/stack projections). The compat projections `of_run_call_val_with_depth`
  and `of_run_call_val` drop the step/logs/output and then the depth fact for
  consumers that do not need them.
- `of_step_call_val_with_depth_frame`: when the actual pc, recursive slot,
  `Xlot.Filled` and `Ninst.StepRun` are supplied, preserve that same CALL
  boundary, including its exact spawn, message/process and resume equations.
  The original run-based theorem projects this selected-step interface.
- `Ninst.step_call_spawn_exact` in
  [`Blanc/CallSpawnExact.lean`](../Blanc/CallSpawnExact.lean): the same exact
  CALL frame one level lower, when the proof holds only the step equation
  `Ninst.step ⟨pc, sevm, s⟩ Ninst.call = .spawn f rsm pc'` and the 7-operand
  stack (`g :: c :: v :: ii :: is :: oi :: os :: rest`), not an `Ninst.Run`.
  It returns the parent `Devm` (stack, state and memory extension over the
  input and output windows), `0 < depth`, both delegation-resolution arms,
  `f = Frame.ofCall (callMsg …)` with the EIP-150/stipend gas term, and
  `rsm = .call parent oi.toNat os.toNat`.  It says nothing about the child's
  outcome or the resumed parent; take those from the retained slot. Import `Blanc.CallSpawnExact` (it imports
  only `Blanc.Ladder`).
- `of_run_staticcall_val_with_depth_cause`: the 6-operand
  (`g :: t :: ii :: is :: oi :: os :: xs`) STATICCALL analogue over
  `Ninst.staticcall`, whose failed arm additionally carries a
  `StatcallFailureCause` witness; compat projection
  `of_run_staticcall_val_with_depth`. Opcode honesty is load-bearing: CALL (7
  operands, value, stipend) and STATICCALL (6 operands, forced static) already
  have separate statements — select by the operand count actually on the stack,
  never by analogy, and keep DELEGATECALL on its envelope above.
- `of_step_staticcall_val_with_depth_frame_cause`: when the proof already
  holds the actual pc, recursive slot, `Xlot.Filled` and successful
  `Ninst.StepRun`, preserve that supplied slot directly. Its success arm also
  gives the exact `Ninst.step` spawn of the resolved `Frame.ofCall`, parent
  `Resume.call` and successor pc. The existing run-level cause theorem is a
  compatibility projection of this single inversion. The supplied-slot form
  retains occurrence provenance; it does not establish child order or root
  commitment.
- For arbitrary-result STATICCALL occurrences, use
  [`Blanc/StaticcallObservation.lean`](../Blanc/StaticcallObservation.lean).
  `Ninst.staticcall_observation` consumes the actual `Ninst.StepRun` and its
  filled slot; `Exec.NinstOccurrence.staticcall_observation` takes these from
  the supplied occurrence. `StaticcallObservation` distinguishes direct
  completion without a spawn from the exact spawned message, original slot,
  unrestricted settlement and resume. `StaticcallRouting` retains either
  the interpreted child's actual `Exec` or the enabled native address,
  `executePrecomp` result and settlement with slot `.none`, including native
  OOG. `Xinst.step_staticcall_spawn_frame_zero` and
  `staticcall_routing_of_process` establish the call frame and zero-value
  transfer before native classification. These facts require no
  `CoveredFork`, success flag or nonempty output. The payload is the actual
  message's data; contract-wide relevance, ordering and historical commitment
  are separate obligations.
- Consumption pattern: Blanc's compiled callers branch on the pushed flag, so a
  caller holding the success guard dismisses the failed arm with the trailing
  `iszero`+guard.

For the entered child's code and code address at the `Xinst`-step level — from a
spawn equation without operand knowledge — use the spawn-source family in
[`Blanc/CommonProofs/Messages.lean`](../Blanc/CommonProofs/Messages.lean):

- `Xinst.step_spawn_source`: the trichotomy over any
  `Xinst.step sevm devm x = .spawn f rsm` — empty target code, same target as
  the parent, or code identity under `¬ isValidDelegation`. Its second disjunct
  (`f.inner.currentTarget = sevm.currentTarget`) remains open for an arbitrary
  instruction. For an actual STATICCALL spawn,
  `Xinst.step_staticcall_sameTarget_code` in
  [`Blanc/ExecutionDirectCode.lean`](../Blanc/ExecutionDirectCode.lean) gives
  direct-code identity from same-target and nondelegation evidence. It is the
  shared owner of the proof. Message-level resolution with
  the callee word known goes through `not_delegation_of_compile`.
- `Xinst.step_spawn_codeAddress_eq_currentTarget`: away-from-parent child
  code-address identity, from the spawn equation plus `≠`, nonempty target code,
  and no-delegation evidence.
- `Evm.step_spawn_child`: the `Evm.step` packaging — child `pc = 0`, preserved
  `getCode`, and the same away-case code identity.

Direction honesty: this family inverts an existing run or spawn; it never
manufactures liveness from a stack prefix. To construct a call crossing, use the
`Ninst.runCompiled_*call*` family above. Note the asymmetry: entered-frame CALL
has `runCompiled_call_zero_value` / `runCompiled_call_nonzero`, while
entered-frame STATICCALL has no `runCompiled` constructor — assemble those
crossings per consumer from `Xinst.step_staticcall_spawn` composed with
`Ninst.runCompiled_exec_run`.

When the walk must name the frame's **exact ordered direct children** (an environment or
call list read off `Exec.childFrames`), walk the actual derivation instead of a lifted run:
[`Blanc/Lift/FrameWalk.lean`](../Blanc/Lift/FrameWalk.lean) gives the walk state
`XAt sevm post pc d L` (a derivation from `d` at `pc` whose remaining children are `L`, gas a
word) and the spawning steps `xa_call`/`xa_staticcall`, which peel the next
child as `ChildOf` (target, calldata, value, static flag, output, logs, storage and code at
entry and exit, warm growth) unless the target is an undelegated precompile.
[`Blanc/Lift/FrameWalkKit.lean`](../Blanc/Lift/FrameWalkKit.lean) carries memory as a byte
image (`xa_call_img`, `xa_staticcall_img`, `xa_identity_img`) and states image facts as
`WordAt`/`Region` with the `wchain` tactic.

If the property concerns which child roots were entered rather than only the
terminal result, continue to E3.

### E3. I must carry a predicate over all entered child roots

- For a warm fixed-width SHA-256 precompile crossing, use
  `Ninst.childlessRunCompiled_staticcall_sha256_64_warm_ext` in
  [`Blanc/ForwardSha256.lean`](../Blanc/ForwardSha256.lean); the ordinary
  `runCompiled_*` projection intentionally forgets the empty child slot. Use
  `Ninst.childlessRunCompiled_staticcall_sha256_64_warm_ext_full` when later
  transaction settlement also needs the crossing's exact refund preservation,
  account-deletion-set emptiness preservation, or the unchanged
  created-account set (which an exact later `SSTORE` price depends on).

To identify the caller and target of settlement-committed frames, use
[`Blanc/Lift/CallerProvenance.lean`](../Blanc/Lift/CallerProvenance.lean).
`Exec.childFrames run` lists a frame's direct settlement-committed children;
`Evm.step_spawn_child_caller` says each child either receives the parent's
current target as caller or keeps the parent's target. `CallerTarget p ca Q`
states the desired property of frames at `ca` called by `p`. `settledRoots`
is defined at every trace layer, with `settledFrames_eq : settledFrames =
rootFrames settledRoots`. For the parent-to-child fold consuming this
vocabulary, use `ConfiguredHistoryTrace.settledFrames_callerTarget_of_children`
in `Blanc/Lift/CallChildren.lean`, described below.

To show that every direct child of a frame is called by the frame's own current
target, use
[`Blanc/Lift/CallChildren.lean`](../Blanc/Lift/CallChildren.lean):
`Exec.childFrames_caller_of_callKinds` concludes it from the frame's
CALL/STATICCALL-only restriction along its chain (a checked certificate's
`SpawnKinds`), via `Xinst.step_call_spawn_caller` and
`Xinst.step_staticcall_spawn_caller`. `Exec.childFrames_isStatic` says a static
frame has only static children. For the caller fold of
`Blanc/Lift/CallerProvenance.lean` with the weaker obligation that every direct
child of a frame at `p` or `ca` satisfies the target property (`CallerChildren`),
use `ConfiguredHistoryTrace.settledFrames_callerTarget_of_children`.
The fold's root case needs that `ca` enters no settled message root itself.
The per-wrapper root-caller forms (`ProcessMessageTrace`,
`MessageCallTrace`, `SystemMessageTrace`, `RequestsTrace` `.settledRoots_caller`)
are in [`Blanc/ExecutionTraceRootCallers.lean`](../Blanc/ExecutionTraceRootCallers.lean).
For an address whose checkpoint code `C` is nonempty and not an EIP-7702
designator, with no contract invariant to carry, use
[`Blanc/ExecutionSettledOwnCode.lean`](../Blanc/ExecutionSettledOwnCode.lean):
`Exec.descendantFrames_ownCode` gives `OwnCodeAt` at every committed
descendant frame, provided frames running `C` at `ca` spawn only by `CALL`,
`STATICCALL` or `CREATE2` (`OwnSpawns`), and
`Xinst.step_create2_spawn_unprotected` says a `CREATE2` child targets
an address with no code. A code image equal to
`some C.toList` pins the bytes by `ExecutionTrace.bytes_eq_of_image`
([`Blanc/ExecutionImmutableCode.lean`](../Blanc/ExecutionImmutableCode.lean)).
For every *raw* frame, rolled back or not, [`Blanc/ExecutionRawFramesCodeImage.lean`](../Blanc/ExecutionRawFramesCodeImage.lean):
`*.rawFrames_codeImage` per wrapper carries a `ContractSpecSem`'s image (from the
`*.stateInv_admitted_sem` message invariant) with `Exec.rawFrameRoots_codePreserve`
inside each message. For the In-carrier (`StagedBodyTrace` / `ConfiguredBlockTraceIn` /
`ConfiguredHistoryTraceIn`), [`Blanc/ExecutionInCodeImage.lean`](../Blanc/ExecutionInCodeImage.lean):
`…rawFrames_codeImageIn` per wrapper (and `_of_installedIn` for staged bodies,
In-blocks and In-histories) carries the image through the In-rungs
(`*.stateInv_admitted_semIn`, with the installed certificate and image
identification the In-rungs demand; message and transaction levels are
fork-free and reused). `ConfiguredHistoryTraceIn.settled_codeImageIn` follows
through the settled-to-raw bridge; `…settledRoots` / `…settledFrames_eq` bridge
In settled frames to `rootFrames`, giving `settledFrames_contigIn` and the
forest `settledFrames_parentIn`. `MidHistoryTraceIn.rawFrames_codeImageIn`
starts at a genuine mid-history `Benv`, using the actual transaction suffix
and later whole blocks. `MidHistoryTraceIn.settled_codeImageIn` specializes
this to a certified image installed at that start and preserves each retained
frame's original entry code; it requires no fabricated block checkpoint or
storage replay invariant. The original and mid proofs share the withdrawal
invariant fragment. No recipe is registered: use this branch and the named theorem.
When no installed certificate exists (a proxy runtime that `DELEGATECALL`s),
[`Blanc/ExecutionInCodeImageSafe.lean`](../Blanc/ExecutionInCodeImageSafe.lean):
`…codeImage_of_safe` per wrapper (message, transaction) threads each entry world's `getCode wa = C`
with the `…_of_safe` chain of `ExecutionNoDelSafeHistory` (same
`SafeRawFrames wa` premise, plus `C.toList ≠ []` and `¬ isValidDelegation C`)
and keeps it at every raw root by `Exec.rawFrameRoots_codePreserve`.
No recipe is registered: use this branch
and the named theorem.
For the raw-node chronology itself (every reached driver node in execution
order, independently of outcome),
[`Blanc/ExecutionInRawNodes.lean`](../Blanc/ExecutionInRawNodes.lean):
per-level `…rawNodes` mirroring the `…rawFrames` chains with `Exec.rawNodes`
in place of `Exec.rawFrameRoots`; `…mem_rawNodes_iff_rawFrame_parentPrefix`
(node membership is exactly `ParentPrefix` under some listed root);
`…rawNodes_of_mem_rawFrames` (nodes of a listed root's own run);
`…safeRawFrames_of_rawNodes` (per-node safety into `SafeRawFrames`); and
`ConfiguredHistoryTraceIn.exists_rawNodes_split_of_mem_rawFrames`
(positional split of a listed root). No recipe is registered: use this branch
and the named theorem.
For the actual decoded instruction and stack operands of a raw recognized
successful store, use `Exec.Deriv.successfulSstore?_decoded` in
[`Blanc/ExecutionOccurrence.lean`](../Blanc/ExecutionOccurrence.lean).
It projects `Ninst.At` and the same recognized key/value at the top of the
node's stack directly from `successfulSstore? = some`; it requires no retained
membership, fork coverage or final frame success. No recipe is registered: use the recognizer equation.
For storage-cell provenance along the raw chronology,
[`Blanc/ExecutionCellProvenance.lean`](../Blanc/ExecutionCellProvenance.lean):
`CellProv wa k init nodes v` (entry value kept or a listed successful
`SSTORE` of `v`); `CellProv.mono_left` / `mono_right` / `trans` (assembly
across concatenations); `CellProv.of_replayCell` (retained-write replay is
provenance); `Evm.step_cont_getStor_get_noStateGas` and
`Evm.step_spawn_enter_getStor_noStateGas` (state-gas-absence twins of the
covered-fork per-step facts); `Exec.Deriv.successfulSstore?_sound_raw`
(recognizer soundness at raw nodes); storage twins
`sweepTouchedAccounts_getStor_of_nonempty`, `payRewards_getStor`,
`ExecutionTrace.messageCallExecutionMessage_getStor`; and the level-zero
`Exec.rawNodes_getCode`, `Exec.rawNodes_cellProv_noStateGas` (per-run,
by induction). No recipe is registered: use this branch and the named theorem.
For cell provenance at message and transaction level (L1-L2), each relative
to an arbitrary entry world,
[`Blanc/ExecutionInCellProvenance.lean`](../Blanc/ExecutionInCellProvenance.lean):
`RetainedXlot.cellProv_at` (frame-generic, with the entry cell equation);
`ProcessMessageTrace.cellProv_at` / `cellProv_post` and
`ProcessCreateMessageTrace.cellProv_at` / `cellProv_post` (call/create cores
via settlement replay); `MessageCallTrace.cellProv_at` / `cellProv_post`
(collision/create/call arms); `TransactionTrace.cellProv_at` /
`cellProv_post` (debit plus gas-credit, deletion-fold and sweep settlement);
plus the entry bridges `Frame.enter_run_getStor`, `createEntry_getStor`,
`delegation_keeps_code_entry`, `execMsg_cell_eq`,
`not_protected_target_of_noCollision`, `prepareMessage_own_entry` and the
settlement storage facts `addBal_getStor_of_codenonempty`,
`foldl_destroyAccount_getStor`, `CellProv.of_replay_nodes`. No recipe is
registered: use this branch and the named theorem.
For unconditional root cell equality, use
[`Blanc/ExecutionCommittedCell.lean`](../Blanc/ExecutionCommittedCell.lean):
the call/create/message/transaction `cell_eq_of_settledRoots` lifts and
`MessageCallTrace.code_eq` preserve the same installed nonempty,
nondesignator code and actual selected cell. Failed settlement uses rollback;
the transaction layer keeps actual output deletion exclusion explicit.
[`Blanc/ExecutionHistoryCommittedCell.lean`](../Blanc/ExecutionHistoryCommittedCell.lean)
lifts these laws through transaction lists, enabled or skipped system stages,
withdrawals, requests, rewards and configured histories. `OutputNotDeleted`
records actual transaction outputs. `SystemStagesDisabled` and its root/log
equations apply only when the actual selected rule bits disable those stages.
For mainnet, [`Blanc/ExecutionHistoryInEraBounds.lean`](../Blanc/ExecutionHistoryInEraBounds.lean)
derives those bits from the actual schedule selection:
`mainnetChainConfig_preCancun_of_timestamp_lt` identifies its era,
`ConfiguredBlockTraceIn.systemStagesDisabled_of_mainnet_timestamp_lt` handles
one block, and `ConfiguredHistoryTraceIn.systemStagesDisabled_of_mainnet_tip_before_cancun`
uses the final tip's timestamp and accepted-header chronology for every block
in the original history. The `mainnet-pre-cancun-stages` recipe recognizes the
staged-body and configured-history predicate heads. Mainnet configuration and
the actual timestamp bound remain necessary; block numbers alone do not bound
a mixed block/time schedule.
The same layers expose `cell_property_of_settledRoots`: an actual entry
`P cell` plus each complete-settlement root's conditional `P pre → P post`
produces the endpoint property, preserving the same code, state-gas and actual
deletion obligations. `cell_rel_of_settledRoots` accepts an explicit reflexive,
transitive relation and each actual root's `rel pre post`; transitivity
composes `rel origin pre` with that root law. Its output is `rel origin endpoint`.
Equality API signatures are preserved as predicate instances, sharing the
settlement proofs. `ConfiguredHistoryTraceIn.cell_zero_of_settledRoots`
instantiates `P value := value = 0`, requiring only an actual initial zero
and each root's conditional zero preservation, never all root entries zero.
List/history `outputNotDeleted_iff_noDelScheduled` connects existing
`ExecutionNoDelSafeHistory` deletion producers to the unchanged
`OutputNotDeleted` obligations; no new raw-world or code-family premise is added.
For a coupled cell/deletion law, use
[`Blanc/ExecutionSettledRootEntry.lean`](../Blanc/ExecutionSettledRootEntry.lean).
`RetainedXlot.settledRoots_entry_getCode_getStor` and the CALL/CREATE variants
derive protected code and storage at the actual outer root entry.
`MessageCallTrace.settledRoots_entry_code_cell` and the transaction variant
carry those facts through authorization, code resolution and nonce/fee debit.
`TransactionTrace.cell_noDel_of_settledRoots` and
`ApplyTransactionsTrace.cell_noDel_of_settledRoots` provide the root callback
with derived entry code and cell property before asking for deletion and cell
preservation. The ordered fold returns actual deletion exclusions, endpoint code
and property, and every original settled root's entry facts. Descendant entries
are not identified with the transaction input. Failed settlement supplies no retained root.
Use this explicit trace/cell
branch directly; there is no distinct reliable single goal-head recipe trigger.
For exact transaction-position cuts, use
[`Blanc/ExecutionHistoryCommittedCuts.lean`](../Blanc/ExecutionHistoryCommittedCuts.lean):
`ApplyTransactionsTrace.splitAt_settledRoots_eq`, `splitAt_rootLogs_eq` and
`splitAt_outputNotDeleted_iff` follow the canonical list cut, including empty
root lists. `MidHistoryTraceIn.cell_eq_before_txSplit` transports a settled-after
origin to a later before-transaction endpoint using only intervening roots and
deletion exclusions. The actual decoded transaction identity and concrete
rootwise cell laws remain inputs. Use this trace/boundary branch directly;
an expanded cell equality alone does not select the intended chronology.
The before endpoint is
the cut's `benv`; settled-after is `afterBenv`. Empty root lists do not
identify a transaction position, so retain the indexed cut witness.
The predicate/relational siblings are `splitAt_cell_property_boundaries`,
`splitAt_cell_rel_boundaries`, `MidHistoryTraceIn.cell_property_of_settledRoots`,
`cell_rel_of_settledRoots`, and the block/mid-history
`cell_property_before_txSplit` / `cell_rel_before_txSplit`.
The post-transaction siblings are
`StagedBodyTrace.cell_property_after_transactions_of_settledRoots` and
`cell_rel_after_transactions_of_settledRoots`.
For the code and the `(wa, k)` storage cell at every raw node of an
In-history on any selected fork (no `CoveredFork`, no delegation or access
premise; safety of the strictly earlier raw nodes only),
[`Blanc/ExecutionHistoryCellProvenance.lean`](../Blanc/ExecutionHistoryCellProvenance.lean):
`ConfiguredHistoryTraceIn.rawNode_cellProvenance` (checkpoint value or an
earlier attributed raw successful `SSTORE`), its invariant forms
`ConfiguredHistoryTraceIn.rawNode_cellInv` and
`ConfiguredHistoryTraceIn.rawFrame_entryCellInv`; the per-level `cellProv_at`
/ `cellProv_post` lifts for `ApplyTransactionsTrace`, `SystemMessageTrace`,
`RequestsTrace`, the beacon, history and request stages, `StagedBodyTrace`,
`ConfiguredBlockTraceIn` and `ConfiguredHistoryTraceIn`; and the helpers
`msgNode_code`, `txNode_code`, `StagedBodyTrace.withdrawalCell_of_code`,
`StagedBodyTrace.withdrawalCode_of_code`, `successfulSstore?_node_owner`.
No recipe is registered: use this branch and the named theorem.
For how each raw node of an In-history is reached (a message root running the
code installed at its own target, a successor of an earlier node of its frame,
or the root of a frame an earlier node spawned), with no premise beyond the
trace, [`Blanc/ExecutionInRawNodeOrigin.lean`](../Blanc/ExecutionInRawNodeOrigin.lean):
`ConfiguredHistoryTraceIn.rawNodes_origin` (`OriginList`, `RawOrigin`,
`RootOwnCode`, `Exec.Deriv.SpawnedAt`), the level-zero
`Exec.rawNodes_split_origin`, the per-level `…rawNodes_origin` lifts, and the
message facts `MsgRootCode`, `MsgOwn`, `messageCallDelegation_own`,
`messageCallExecutionMessage_rootCode`. It is the positional input of a strong
induction over `rawNodes` that bounds the codes run in a storage context.
No recipe is registered: use this branch and the named theorem.
For the own-code fact at an actual settled outer root, use
[`Blanc/ExecutionInRootOwnCode.lean`](../Blanc/ExecutionInRootOwnCode.lean):
the per-level `…settledRoots_rootOwnCode` derives `RootOwnCode`
for that root's `rootDeriv` directly from message entry, authorization and
CREATE collision handling. It needs no installed-world invariant or extra
stage capability. The per-level `…settledRoots_rootOwnEntry`
retains both code equality and `codeAddress = some target` under the same
nonempty, non-designating installed-code condition. `RootOwnEntry.code`
projects the old `RootOwnCode` fact. The message producer `MsgRootEntry`,
`Frame.enter_run_rootOwnEntry`, `processCreateMessage_msg_rootEntry` and
`messageCallExecutionMessage_rootEntry` retain that address through entry,
CREATE collision exclusion, authorization and code resolution; the
per-level `settledRoots_rootOwnEntry` transports preserve the same actual
roots. This applies to outer message roots; delegated descendants still need
the positional origin classification above.

For the same provenance restarted at a committed boundary inside the
history (a block-body start or the boundary after any transaction, e.g. for
a contract deployed after the checkpoint; safety only of the raw nodes
between the boundary and the node),
[`Blanc/ExecutionHistoryCellProvenanceFrom.lean`](../Blanc/ExecutionHistoryCellProvenanceFrom.lean):
the boundary predicates `BoundaryAt s pre` on `ApplyTransactionsTrace`,
`StagedBodyTrace`, `ConfiguredBlockTraceIn` and `ConfiguredHistoryTraceIn`,
with `ConfiguredHistoryTraceIn.boundaryAt_checkpoint` and the per-level
`BoundaryAt.prefix`; `ConfiguredHistoryTraceIn.rawNode_cellProvenance_from`
(boundary value or an attributed raw successful `SSTORE` between),
`rawNode_cellInv_from`, `rawFrame_entryCellInv_from`, the endpoint form
`ConfiguredHistoryTraceIn.cellProv_post_from`; the per-level `cellProv_at_from`
/ `cellProv_post_from` lifts, `ApplyTransactionsTrace.BoundaryAt.suffix`,
`StagedBodyTrace.requests_cellProv_at` / `requests_cellProv_post` and
`ConfiguredHistoryTraceIn.cellProv_attribution`. The checkpoint statement is
the instance `boundaryAt_checkpoint`, `pre = []`. No recipe is registered:
use this branch and the named theorem.
For installed code at settled frames of an In-history on a historical fork
(where `CoveredFork` cannot hold),
[`Blanc/ExecutionInOwnCode.lean`](../Blanc/ExecutionInOwnCode.lean):
`OwnCodeAtIn F ca C` (installed at start, pc `0`, selected domain `F`, no
state gas, runs `C` at `ca`); per-level `…settledRoots_ownCodeIn` concluding
it at every settled root with no cover premise (roots need no spawn
classification); `OwnSpawnsIn` (fork-free spawn contract: state-gas absence
in place of coverage) with `Exec.descendantFrames_ownCodeIn` (child `F`/gas
via `step_spawn_child_benvStat`; create2 arm split on `op.create2`); and
per-level `…settledFrames_ownCodeIn` ending in
`ConfiguredHistoryTraceIn.settled_ownCodeIn` at every settled frame, no
cover premise. No recipe is registered: use this branch and the named theorem.

For a committed-replay history that takes one step per *outermost* settled,
non-static frame at an address (a re-entered frame consumed inside its
ancestor), use [`Blanc/Lift/OutermostFrames.lean`](../Blanc/Lift/OutermostFrames.lean):
`Exec.Frame.obsAt` / `Exec.Frame.subtreeAt`, `ConfiguredHistoryTrace.committedFramesAt` (all
settled non-static frames at `ca`, in trace order) and
`ConfiguredHistoryTrace.outermostFramesAt` (the outermost ones, via
`Exec.outermostDescAt` / `Exec.Frame.outermostAt`). Facts:
`mem_outermostFramesAt` (settled, at `ca`, non-static),
`outermostFramesAt_sublist` (trace order), `outermostFramesAt_partition`
(non-nesting: the outermost frames' subtrees flatten to exactly
`committedFramesAt`), `eq_outermostFramesAt_of_partition` (any non-static `ca`
frame list with that partition, e.g. a ladder's step frames, *is* the outermost
list), and `outermostFramesAt_step` / `committedFramesAt_step`. The generic
list facts behind them are `List.sublist_flatMap_of_headed` and
`List.eq_of_flatMap_headed` (in namespace `Blanc`).

To show that every direct child of a certified frame comes from one of a few
call sites, use [`Blanc/Lift/CallSiteChildren.lean`](../Blanc/Lift/CallSiteChildren.lean)
with the vocabulary of [`Blanc/Lift/CallSite.lean`](../Blanc/Lift/CallSite.lean).
Name a site inside a generated
tree's straight prefix with `SFunc.lineDrop n t` (`SFunc.lineSuffix_lineDrop`).
`Xinst.step_call_spawn_selector` equates a CALL child's selector with
`CallInputSelector`'s reading of the parent's input window;
`ChainMemoryBelow R bound` is the memory bound such content facts take.

### E4. I need a common terminal walk


For general offsets, sizes, stack tails, or payloads, use
`Func.runCompiledTo_return_word` in `ForwardCall` or
`Func.runCompiledTo_revert` / `Func.runCompiledTo_revert_of` in `Reverts`.
For a primitive gas charge, `chargeGas_eq_ok` in
[`Blanc/Compiled.lean`](../Blanc/Compiled.lean) exposes the exact successful
decrement, while `chargeGas_eq_outOfGas` in
[`Blanc/ChargeGas.lean`](../Blanc/ChargeGas.lean) exposes the unchanged-state
out-of-gas result without pulling compiled-execution infrastructure into a
small consumer.

For a nonzero branch flag that tail-calls an empty-revert auxiliary, use
`emptyRevertGuardCost` and `Func.runCompiledTo_emptyRevertGuard` in
[`Blanc/Reverts.lean`](../Blanc/Reverts.lean). Both this guard helper and
`Func.runCompiledTo_revert_func` require the actual
`sevm.benvStat.rules.op.push0 = true` flag for their two zero pushes;
state-gas absence alone does not enable PUSH0.

For a nonzero branch flag that tail-calls a constant `Error(string)`
auxiliary, use `errorBodyCost`, `errorCallCost`, `errorGuardCost`, and
`Func.runCompiledTo_errorGuard` in
[`Blanc/RevertPayload.lean`](../Blanc/RevertPayload.lean), with the actual
`sevm.benvStat.rules.op.push0 = true` availability flag for its zero pushes.
The cost remains a function of the entry state, so arbitrary aligned prior memory and its exact
expansion charge are retained.  When an existential carrier exposes a
different entry state with the same memory size, transport the exact cost with
`errorGuardCost_congr_memory_size`.

For a source-level `mstoreAt 0 +++ returnMemoryRange 0 32` tail, use
`ReturnsWord`, `of_storeReturnWord`, or the memory-side-condition-free
`returnsWord_of_storeReturn` in
[`Blanc/LadderBase.lean`](../Blanc/LadderBase.lean).

### E5. I need to inspect what happened in an `Exec`

- Complete settled prefixes at an arbitrary non-static target:
  `Blanc/ExecutionTargetPrefix.lean` owns `ExecutionTrace.TargetClosed`
  with `.nil`, `.append`, `.gap`, `.committed`, `settledFrames_targetClosed`
  and `before_targetClosed`. The last retains the actual split and no-enclosing
  target-frame premise.

- For operand-stack safety at every reached same-frame node, use
  [`Blanc/CompiledStackSafety.lean`](../Blanc/CompiledStackSafety.lean).
  `CompiledStackSafety.Certificate` carries local actual-decoder step and height
  proofs; `Certificate.parentStep`, `parentPrefix`, and `at_parentPrefix`
  transport them over the existing raw `Exec.Deriv.ParentPrefix`, including
  failing outcomes and repeated loops. The entry invariant must be proved for
  the exact execution root. `call_resumes_of_room` constructs a status-word
  resume from parent headroom; `resume_call_safe` distinguishes a newly generated
  parent operand-stack fault from an inherited child-settlement error. This
  interface does not synthesize an opcode or concrete-program certificate.
  Its exact `StepSafe` goal-head advice lives in the core `proofRecipeTriggerMatches`
  dispatch, shared with the generalized certificate recipe, while the `ResumeSafe`
  arm stays leaf-only in `proofRecipeLeafTriggerMatches` in `ProofRecipeTactic`,
  reusing the shared raw-head helper. Unmatched triggers retain the original matcher;
  the generator validates both fixed inventories and rejects duplicate owners.
- Forward primitive stack safety, including failure arms, is in
  [`Blanc/AbstractStackSafety.lean`](../Blanc/AbstractStackSafety.lean).
  `AbstractStackSafety.Matches` matches the entire operand stack against
  exact literals or arbitrary words; `Matches.length`, `getElem?`, `set`,
  and `swap` preserve its structural information. `SafeResult` permits
  non-stack errors while requiring the supplied successful postcondition.
  Compose it with `SafeResult.bind` and `mono`. `chargeGas_safe`, `push_safe`,
  `pop_safe`, `pushItem_safe`, `applyUnary_safe`, `applyBinary_safe`,
  `dup_safe`, and `swap_safe` cover the named actual primitive semantics.
  `WordMatches.eq_of_some` recovers an exact concrete operand.
  `ninst_push_safe` includes exact next-PC equality; `step_ofExecution_safe`,
  `step_ofJump_safe`, and `call_resume_safe` connect to the existing
  `StepSafe`/`ResumeSafe` obligations. None requires sufficient gas or a
  successful terminal outcome. These lemmas do not construct a concrete
  program certificate. The generic `SafeResult` head alone does not identify
  an instruction or transfer, so this primitive inventory is registry-only
  until that selection interface exists.
- Forward stack safety for concrete regular and control-flow opcodes, proved
  against the actual `Rinst.runCore` and `Jinst.runCore` implementations
  including every raw error arm, is in
  [`Blanc/AbstractStackTransfer.lean`](../Blanc/AbstractStackTransfer.lean).
  `regularTransfer` is the decidable abstract transfer for the regular opcodes
  a row can carry. `regularTransfer_safe` proves every accepted transfer
  against actual `Rinst.run`, from exact full-stack matching and an input
  length at most eight; `ninst_regularTransfer_safe` lifts it to `Ninst.step`
  with the exact fall-through PC. Both include every error arm, without a
  successful-run or adequate-gas premise. Unsupported opcodes and insufficient
  operand shapes are rejected by the existing check. The individual
  `gas_safe`, `calldataload_safe`, `mload_safe`, `mstore_safe`, `sload_safe`,
  `sstore_safe`, and `ninst_pop_safe` remain available for direct composition.
  `SafeResult.map`, `SafeResult.pure_bind`, `assert_safe` (any decidable
  proposition), `assert_true_safe`, and `assertDynamic_safe` are the
  composition helpers they use. `SafeResult.noStackFault` and
  `xstep_ofExcept_safe` connect terminal/external outcomes to `StepSafe`;
  the `Matches` update lemmas for output, return data, gas, memory extension,
  accessed addresses, and delegation resolution preserve the complete stack
  through CALL staging. `jumpTransfer`, `jumpiTransfer`, and
  `jumpdestTransfer` are universal decidable transfers for the exact-destination
  `JUMP`, exact-destination/arbitrary-condition `JUMPI`, and stack-preserving
  `JUMPDEST` shapes. Their `_safe` theorems expose the actual taken target,
  `JUMPI` one-byte fall-through, and successful `jumpable` check while allowing
  gas and invalid-target failures as non-stack errors. The `jinst_*Transfer_safe`
  wrappers lift those facts to the actual `Step.ofJump (Jinst.run ...)` step.
  `terminalTransfer` covers `STOP`, `RETURN`, and `REVERT` through actual
  `Linst.run`; `terminalTransfer_safe` retains the successful RETURN tail and
  all non-stack error arms, while `linst_terminalTransfer_safe` is the actual
  halted dispatcher path. `callTransfer` removes CALL's seven operands and
  prepends its eventual status word. `callTransfer_safe` follows actual
  `Xinst.step` through access/delegation, gas, static, insufficient-balance,
  depth-zero, child-spawn and resumption behavior, and
  `ninst_callTransfer_safe` fixes the actual one-byte parent continuation PC.
  `genericCall_step_safe` makes the caller/callee boundary explicit: it proves
  the caller's status-word continuation for arbitrary child settlement and
  does not assert operand-stack safety of arbitrary callee code. Decoded-table
  validation and a concrete program certificate remain separate obligations.
  The existing stack-certificate recipe advises the `StepSafe` head; selecting
  a transfer wrapper additionally needs the exact instruction and successful
  check, so discovery remains in this registry.
- For per-instruction equality modulo gas over the same opcode family minus
  `gas`, see I1 and
  [`Blanc/GasErasure.lean`](../Blanc/GasErasure.lean).
- Raw nodes (`Exec.rawNodes`, Jaune's `Jaune/ExecChronology.lean`), raw frame
  roots, and instruction occurrence:
  [`Blanc/ExecutionOccurrence.lean`](../Blanc/ExecutionOccurrence.lean).
- `Prog.SourceSite.pcs` projects a source inventory to compiled counters;
  `Prog.SourceSite.coordinates` keeps each counter coupled to its owning
  function-table index for role-preserving finite inventory checks.
- `Exec.StorageWrite.effectTriple` erases only the derivation node from a
  successful write, and `Exec.retainedStorageEffectTriples` is the canonical
  settlement-retained `(owner, key, value)` chronology.
- For an actual target-directed source route, use
  `Exec.Deriv.SourceCursor.Toward.chronology`,
  `next_of_instruction_ne`, `rebase`, `dropLineRun`,
  `selectBranchZero`, and `selectBranchSucc`.  The supporting
  `ParentPrefix.trans`, `advance_pushToward`, `advance_jumpToward`,
  `SourceCursor.branchFlagToward`, and `ninstRun_of_nextEdge` retain the exact
  same-frame chronology and stack effects across compiler glue; they do not
  assert liveness or a final execution outcome.
- Every actual same-frame continuation edge preserves nonempty code:
  `Exec.Deriv.ParentStep.codePreserve` in
  [`Blanc/ExecutionNoninterference.lean`](../Blanc/ExecutionNoninterference.lean),
  beside `ParentStep.sevm_eq`; it covers the plain step, the immediately
  completed spawn, and the resumed child.
- For a loose gas-free walk prefix with source-path accumulation, see E1 and
  [`Blanc/RunPrefix.lean`](../Blanc/RunPrefix.lean).
- To place the cut of a loose gas-free `Func.RunPrefix` on the *actual*
  execution, use `Exec.Deriv.SourceCursor.ofRunPrefix` in
  [`Blanc/PrefixTransport.lean`](../Blanc/PrefixTransport.lean). From a source
  cursor of a successful frame (`root.exn = .ok post`) whose state agrees with
  the loose start under `Devm.EqModGas`, it returns the source cursor at the
  prefix's target path and body, its state again equal modulo `gasLeft`, and a
  same-frame `ParentPrefix` from the starting node. The forward cursor duals
  `SourceCursor.mainForward`, `nextForward`, `branchForward`, and
  `callForward` advance without a nominated target (`mainForward` needs only
  the entry counter and the compiled bytes), `SourceCursor.ninstAt` decodes
  the instruction under a `.next` cursor, and
  `ParentStep.exists_of_ninstAt_ok`, `exists_of_pushAt_ok`, and
  `exists_of_jinstAt_ok` supply the underlying continuation edges. They need
  the successful outcome; for an arbitrary-outcome frame use the
  target-directed `*Toward` family above. A word read from `gasLeft` is not
  transported: stop the prefix before `gas` and cross it on the actual node.
- To show that such a walk spawns no child frame, use the spine lemma
  `Exec.Deriv.SourceCursor.ofRunPrefix_sameFrame_gasFree` in the same module.
  It returns `Exec.Deriv.ExecFreeUntil cursor.node cursor'.node`: every
  same-frame node from the start lies at or after the landing node or decodes
  no `Xinst`. `mainForwardFree`, `branchForwardFree`, and `callForwardFree`
  are the matching duals (the plain forms are their projections). Compose
  spans with `ExecFreeUntil.trans`; when the walk lands on a `.last` cursor
  (`Linst.at_of_slice cursor.codeSlice`), `ExecFreeUntil.noExec_of_linstAt`
  covers the whole frame and `Exec.descendantFrames_eq_nil_of_no_sameFrame_xinstAt`
  concludes `Exec.descendantFrames run = []`. For a span that ends at a
  spawning node instead, `ExecFreeUntil.descendantFrames_eq` moves the
  descendant frames from its start to its end. A straight-line gas-free
  function body (`Func.straightGasFree`, no table call) turns any successful
  `Func.Run` into such a walk to a terminal instruction with
  `Func.RunPrefix.toLast_of_run`.
- To name the *nodes* of every derivation from a concrete machine (not only a
  `Nonempty (Exec …)`), use [`Blanc/Lift/NodeWalk.lean`](../Blanc/Lift/NodeWalk.lean).
  `pwalkH` is a kernel-evaluable pc-level walk over a `CodeTries` of the code with the
  witness engine's shadows and a hash policy `HashPol` (`.refuse`: stop at
  `KECCAK256`; `.avoid slot`: run it through `keccakStep` and refuse a digest equal to
  `slot`); `pwalk` is the `.refuse` walk. The `SELFBALANCE` shadow step requires the selected
  `op.selfBalance` capability as well as absence of a balance access list; it refuses
  the step when the opcode is unavailable.
  To decide many closed walk equalities in one kernel check (each boundary evaluated once, not
  once per equality), close a conjunction of them with `kernel_rfl_and`
  ([`Blanc/Lift/KernelBatch.lean`](../Blanc/Lift/KernelBatch.lean)).
- To consume a call-family child whose code is a lifted certificate *without* walking it by the
  kernel — the child's inputs symbolic, its run built forward as `SProg.RunExact` with
  `Blanc/Lift/ExactWalk.lean` — use [`Blanc/Lift/ExactLeaf.lean`](../Blanc/Lift/ExactLeaf.lean).
  `ChildAgree.afterSload` moves the witness
  engine's shadows across the selected-access base `afterSload`
  over an `St`, so an explicit post state has explicit shadows;
  `sloadCost_shadow` (`sloadCostS`) and
  `afterSload_shadow` (`afterSloadS`) restate charges
  and bases on the shadows without inspecting the accessed-key hash set.
- To state a closed walk witness under every covered fork rather than the one its machine
  fixes, transport its kernel facts with
  [`Blanc/Lift/NodeWalkFork.lean`](../Blanc/Lift/NodeWalkFork.lean). The message-level layer
  underneath is [`Blanc/ForkUniform.lean`](../Blanc/ForkUniform.lean) (see the root's
  *Fork coverage* entry).
- When a closed walk's message runs over a world whose evaluation is expensive (a settled world
  of earlier messages: every `SSTORE` charge reads the transaction-original storage), evaluate
  the kernel facts under a cheap original state and transport them with
  [`Blanc/Lift/NodeWalkOrig.lean`](../Blanc/Lift/NodeWalkOrig.lean): `origOf l` is the closed
  world holding exactly the storage the shadow `l` reads; the `*_withOrig` lemmas are the
  original-state layer alone.
  `Jaune.Sevm.withOrig_code` and `Blanc.ForkUniform.Sevm.withFork_code` transport the code projection
  by named equalities, keeping a concrete source machine out of kernel conversion.
  The interpreter's `SSTORE` arm reads the original value through
  `Blanc.Lift.Witness.origReadK` (WitnessArms), not `Devm.getOrigStorVal` directly:
  `Std.HashSet` membership in `createdAccounts` does not reduce in the kernel (the
  bucket index goes through the opaque `System.Platform.numBits`), while the set's
  `size` field does, so an empty created set is decided by size. A proof that
  unfolds `sstoreStep` rewrites with `origReadK_eq` to recover the machine read.
  A concrete witness whose created set is nonempty still cannot be kernel-evaluated
  through an `SSTORE` that needs the original value.
  Use `resumeCallB_re` to preserve the parent and output window of a transformed call preparation,
  and `CallPrep.re_adrs` for its accessed-address shadow at the resumed configuration.
  The `changed-frame-projection` recipe recognizes direct equality goals exposing
  `Sevm.code` over `Sevm.withOrig`, `CallPrep.adrs` over `CallPrep.re`, or
  `resumeCallB` with all three parent/window projections from the same `CallPrep.re`.
  Its fully qualified helpers are `Jaune.Sevm.withOrig_code`,
  `Blanc.Lift.Witness.CallPrep.re_adrs`, and `Blanc.Lift.NodeWalk.resumeCallB_re`.
  If an alias hides the update or projection, unfold only that local binding and
  run `blanc_suggest` again; the advice never normalizes a concrete machine.
- `kernel_forall_rfl_and`
  ([`Blanc/Lift/KernelBatchForall.lean`](../Blanc/Lift/KernelBatchForall.lean)) decides a
  universally quantified conjunction of equalities in one kernel check. Its shared builder
  imports `Lean.Elab.Tactic.ElabTerm` for the tactic elaboration support. Over a free world,
  compare computed values by `decide` (or against literal boundaries), never
  as terms.
- To make a kernel-checked witness quantify over **every world that agrees on finitely many
  entries** (a checkpoint predicate as a genuine finite read-set agreement, not a world pinned
  everywhere): [`Blanc/Lift/ShadowTail.lean`](../Blanc/Lift/ShadowTail.lean).
  `Boundary.cfgOfT` is the boundary kit with a tail (prefixes decided, tails
  compared as terms). Read the unextended prefixes with
  `Boundary.cfgOf1_acs`, and read the complete prefix-plus-tail shadows with
  `Boundary.cfgOfT_acs`; use these projection lemmas over symbolic
  boundaries before substituting a concrete machine image.
- Pre-EIP-155 legacy transactions (`.zero` type, `v = 27` or `v = 28`, no chain id) for any `Tx`:
  [`Blanc/Lift/LegacyRecover.lean`](../Blanc/Lift/LegacyRecover.lean). `signingHash_pre155` evaluates
  `Tx.signingHash` to its six-field payload (encode it with `RlpConcrete.encode_list_at_last`, the
  data field kept abstract); `recoverSender_pre155`
  gives `recoverSender cid tx = .ok a` at every `cid` from the signing hash, the `r`/`s` range facts
  and one `secp256k1.recover h (tx.v - 27).toBool r s = some a` fact, each a closed `decide +kernel`
  goal once the fields are substituted; `legacy_decode_pre155` runs the strict nine-field
  `BLT.toExLegacyTx` from the per-field scalar decoder equations without reducing the data field, and
  yields `Tx.WireWellFormed`.
- Determinism of execution witnesses:
  [`Blanc/ExecDeterminism.lean`](../Blanc/ExecDeterminism.lean).
- Identifying an execution's descendant frames across one step (`Exec.descendantFrames_eq_of_nextNone`, `_of_jump`,
  `_nil_of_last`, `_flatMap_of_nextSome`, `Exec.Deriv.descendantFrames_eq_of_stepRun`):
  [`Blanc/ExecIdentification.lean`](../Blanc/ExecIdentification.lean).

For settlement-retained wrappers, stable call-tree paths, or an exact ordered
world-state replay, continue to E6, E7, or E8 respectively.  To rule out an
operand-stack fault along that same-frame chronology rather than inspect it, go
to E9.

### E6. I need the exact successful wrapper trace, not only its final result

Use [`Blanc/ExecutionTrace.lean`](../Blanc/ExecutionTrace.lean). Its carrier
and constructor families cover every modelled wrapper layer:

- `ExecutionTrace.RetainedXlot`, `.toFilled`, and
  `ExecutionTrace.exists_retainedXlot_of_filled` retain the concrete recursive
  `Exec` selected by a filled slot.
- `ExecutionTrace.ProcessMessageTrace`, `ProcessCreateMessageTrace`, and
  `MessageCallTrace`, with their `exists_*Trace` theorems, retain raw message,
  CREATE, and message-call execution. `ProcessMessageTrace.result`,
  `ProcessCreateMessageTrace.result`, and `MessageCallTrace.result` recover the
  exact deterministic wrapper equations retained by those carriers.
- `ExecutionTrace.messageCreateCollision`, `messageCallDelegation`, and
  `messageCallExecutionMessage` name the three message-call routing cuts.
  Authorization and resolution use Jaune's actual fork-gated helpers rather
  than an unconditional EIP-7702 lookup.
- `ExecutionTrace.transactionPreludeBout`, `transactionBlobGasFee`, and
  `transactionTenv` expose transaction preparation;
  `TransactionTrace`, `exists_transactionTrace`, and
  `TransactionTrace.exists_finalStateForm` retain the whole transaction.
  `transactionTenv` follows the selected rules' coinbase-warming flag;
  `TransactionTrace.exists_selectedFinalStateForm` is the selected inversion
  beside `exists_finalStateForm`: it runs under the actual
  `stateGas = none` antecedent, routes the gas/refund/coinbase expressions
  through the semantic `settleTransactionGas`, and keeps the touched sweep
  symbolic. The older form's covered-fork premise supplies refund quotient 5
  and the absence of a touched-account sweep.
- [`Blanc/ExecutionSettledReceiptLogs.lean`](../Blanc/ExecutionSettledReceiptLogs.lean)
  provides `MessageCallTrace.logs_eq_settledRoots`: the actual message output
  contains each completely settled root's logs exactly once, including CREATE
  code-deposit failure filtering. Its receipt APIs retain actual status and gas,
  and preserve the encoded receipt key through later transaction indices and
  final body stages.
- [`Blanc/ExecutionTraceSettledOrigin.lean`](../Blanc/ExecutionTraceSettledOrigin.lean)
  exposes `MessageCallTrace.mem_rawFrames_of_mem_settledFrames` for the same
  occurrence's entry facts.
- `ExecutionTrace.ApplyTransactionsTrace`, `SystemMessageTrace`,
  `RequestsTrace`, and `AppliedBodyTrace`, together with their `exists_*Trace`
  theorems, retain transaction lists, system messages, requests, and the full
  block body. `ApplyTransactionsTrace.run`, beside its carrier in
  `ExecutionTrace.lean`, recovers the exact fold equation from the supplied
  retained transaction evidence. `RequestsTrace.state_eq_consolidationState` identifies the final
  request state, and `AppliedBodyTrace.decodedTxs_nil` / `AppliedBodyTrace.decodedTxs_of_mapM`
  decode `trace.decodedTxs` from empty or mapped
  `txs.mapM (decodeTx benv.stat.rules)` runs. The body carrier retains its
  explicit ommer input. Its existing constructor theorem requires
  `CoveredFork`: the beacon/history calls, withdrawals and requests are on,
  and proof-of-work rewards are absent under that premise. This does not
  give unconditional system-call traces or reward-free bodies on historical
  forks. These retained wrappers are selected by their replay equations;
  the broad `Nonempty` conclusion alone is not a reliable recipe trigger.

For successful wrapper extraction under the actual selected rule condition
`stateGas = none`, use `ExecutionTrace.exists_messageCallTrace_of_stateGas_none`,
`exists_transactionTrace_of_stateGas_none`,
`exists_applyTransactionsTrace_of_stateGas_none`, and
`exists_systemMessageTrace_of_stateGas_none`, respectively for a settled
message call, a transaction, its indexed transaction-list fold, and an
unchecked system transaction. Each retains the same existing data carrier.
The original four entry points retain their exact `CoveredFork` interfaces
as compatibility wrappers. Raw process/create extraction already needs no
fork premise. The explicit state-gas condition supports retaining the actual
execution; it does not provide modern refund/touched-account equations,
no-deletion facts, request-enablement or a reward-free body.

For fork-dependent body stages, use
[`Blanc/ExecutionStagedBodyTrace.lean`](../Blanc/ExecutionStagedBodyTrace.lean):
`ExecutionTrace.BeaconStageTrace`, `HistoryStageTrace`, and `RequestStageTrace`
distinguish skipped stages from actual retained system calls. Each `result`
theorem recovers the exact wrapper equation; `disabled_endpoints` proves the
state/output or BAL-builder identities and zero direct system-message roots.
`systemRootCount` counts only these direct roots, excluding their descendants.
The called request arm reuses `RequestsTrace` and its existing ordered calls.
`ExecutionTrace.StagedBodyTrace` retains the exact decoded transaction fold,
withdrawal pair, explicit ommers, reward-state equation, final access-list
check and output. `StagedBodyTrace.state_eq_rewardState` includes PoW credits;
`state_eq_requestState_of_pow_none` requires their absence.
`withdrawals_disabled` proves the disabled withdrawal identity, and
`finalBout_of_bal_none` identifies the final empty-access-list normalization.
Successful extraction uses `exists_beaconStageTrace` and
`exists_historyStageTrace` under the actual input's `stateGas = none`,
`exists_requestStageTrace` under the conditional capability
`requestsHash = true → CoveredFork`, and `exists_stagedBodyTrace` under both
conditions. These constructors retain the actual skipped or called stage and
the successful wrapper's endpoints; state-gas absence alone does not imply
that a request pass is enabled.

State replay over a retained staged body lives in
[`Blanc/ExecutionStagedBodyStateTrace.lean`](../Blanc/ExecutionStagedBodyStateTrace.lean).
`StagedBodyStateChronology` keeps only the selected transaction-list
chronology and its `stateReplay` runs beacon, history, selected transactions,
withdrawals, requests, then rewards under `stateGas = none` alone. The
bout-only block-access-list check contributes no boundary.

For an actually covered fork, `AppliedBodyTrace.toStaged` embeds the supplied
modern body and `StagedBodyTrace.toModern` recovers the modern carrier. The
embedding's `toStaged_transactions`, `toStaged_beacon`, `toStaged_history` and
`toStaged_requests` laws retain the original transaction fold and system-call
data; `StagedBodyTrace.toModern_preserves` retains all four components on the
return path. These adapters use the supplied witnesses. They neither select a
fresh execution trace nor infer modern coverage from historical membership.
For raw or settlement-retained frames of supplied optional stages and
selected-domain block/history spines, import
[`Blanc/ExecutionStagedFrames.lean`](../Blanc/ExecutionStagedFrames.lean).
`BeaconStageTrace`, `HistoryStageTrace`, `RequestStageTrace`, `StagedBodyTrace`,
`ConfiguredBlockTraceIn` and `ConfiguredHistoryTraceIn` each expose `rawFrames`
and `settledFrames`. Skipped stages enumerate nothing; called requests keep
withdrawal before consolidation, bodies keep beacon/history/transactions/requests,
and histories append prior blocks before the next block. Withdrawals, rewards
and BAL finishing contribute no interpreter frames. The optional stages'
`rawFrames_of_disabled` / `settledFrames_of_disabled` retain their actual
disabled guard; each family's `mem_rawFrames_of_mem_settledFrames` transports
committed membership to its raw root using the existing full message/CREATE
settlement filters. Modern `toStaged`, `toModern` and `toIn` projection
equalities retain the supplied execution evidence with the adapters' existing
coverage premises. None of these supplied-carrier projections needs historical
capabilities, no-deletion or a reward budget. Raw lists include rolled-back
entries; these results prove neither occurrence uniqueness nor world-state
chronology, target survival or contract preservation. Historical balance and
contract-invariant transport remain separate obligations. These carriers do not widen
`CoveredFork` or change modern `AppliedBodyTrace`.

For entry admission on those same six supplied carrier families, import
[`Blanc/ExecutionStagedAdmission.lean`](../Blanc/ExecutionStagedAdmission.lean).
Each family's `FrameAdmitted` is equivalent, through
`frameAdmitted_iff_rawFrames`, to the entry predicate at every actual raw root
whose current target is the selected address. Optional skipped stages are
vacuous; bodies preserve beacon/history/transactions/requests order, and the
configured history predicate follows its supplied block spine. Failed and
rolled-back raw entries remain included.
`rawFrames_entered` transports an `EnteredCondition` to every raw root;
`frameAdmitted_entered` specializes that guarantee to admission.
`freshFrameAdmitted` supplies empty stack and memory, and `FrameAdmitted.and`
combines independent entry predicates on the same supplied trace.
These structural results require no historical-domain membership, coverage,
state-gas absence, code-routing certificate, deletion safety or reward budget.
They supply no world-state invariant, account survival or historical contract
preservation; those producers remain separate. Existing modern admission and
preservation APIs retain their existing meanings and coverage premises.

For the exact request bytes appended by a retained request pass, import
[`Blanc/RequestsOutput.lean`](../Blanc/RequestsOutput.lean).
`ExecutionTrace.RequestsTrace.requests_eq` preserves the arbitrary incoming
`bout.requests` and appends the optional type-0 deposit payload, type-1
withdrawal return data and type-2 consolidation return data, in that order.
`ExecutionTrace.optionalRequestEntry` contributes a singleton typed request
for a nonempty payload and no entry for an empty one;
`optionalRequestEntry_eq_nil_iff` identifies the empty case.
`append_optionalRequestEntry` is the conditional-append equation
used by the trace theorem. No premise excludes type-1 entries from the incoming
prefix or empties consolidation output. For an actual block body,
`ExecutionTrace.AppliedBodyTrace.transaction_requests_eq_nil` discharges the
empty-prefix fact: transactions start from `BlockOutput.init`, and
`ExecutionTrace.ApplyTransactionsTrace.requests_eq` proves that their fold
preserves the request list. Thus callers may omit the prefix without adding
an assumption. Payload validity, withdrawal FIFO
provenance, configured-history correspondence and contract refinement remain
separate obligations. This projected requests equality has no carrier-specific
goal head, so discovery stays here rather than in an execution recipe.

Configured transitions and histories continue in
[`Blanc/ExecutionHistory.lean`](../Blanc/ExecutionHistory.lean):
`ExecutionTrace.ConfiguredBlockTrace`,
`exists_configuredBlockTrace_of_transition`,
`ConfiguredHistoryTrace`, `ConfiguredHistoryTrace.toReachUsing`, and
`exists_configuredHistoryTrace_of_reachUsing` retain the schedule-selected
rules and body traces without hard-coding a fork.

To extend a configured history by consensus blocks, use
[`Blanc/JointHistory.lean`](../Blanc/JointHistory.lean). `JointRun cfg ccfg bls s₀`
is a snoc-shaped run of successful `JauneConsensus.jointStep`s, each carrying the
balance no-wrap bound, and `JointRun.toExec pre` extends a
`ConfiguredHistoryTrace` ending at the anchor's execution chain by the run's
engine blocks. `jointStep_engine` extracts the block's `NewPayloadRequest` and the
engine verdict from a successful step; `engineVerdict_ok` turns a verdict into the
selected covered fork, `stateTransitionUsing`, the body run and the requests
equality. `JointStepTrace` pins each step's `ConfiguredBlockTrace` block to
`payloadToBlock req` and its body requests to `req.executionRequests`.
To index a run by step, use `JointRun.steps` (each `JointRunStep` carries the step's
endpoints, signed block and the chosen `JointStepTrace`). `JointRun.extendsBy_steps`
turns steps `i ≤ j` into configured histories through them with
`ConfiguredHistoryTrace.ExtendsBy` of exactly `j - i` blocks and of the remaining
`steps.length - 1 - j` blocks to `run.toExec pre`; `JointRun.extendsBy_toExec` is
the one-step form. These are the premises `Blanc/ExecutionHistoryExtension.lean`
consumers (delivery bounds, restricted exclusion premises) take.

To run consensus blocks across the Gloas fork (ePBS: a block carries a bid, its payload arrives in an envelope and is
built upon by the next block), use [`Blanc/JointGloasHistory.lean`](../Blanc/JointGloasHistory.lean).
`GJointRun cfg ccfg bls s₀` is a snoc-shaped run of `GJointRunStep`s over `JauneConsensus.jointStepG` and the sum
state `GJointState`, of three kinds: `.pre` (`PreStepData`, a `jointStep` with its `JointStepTrace`), `.crossing`
(`CrossingData`: `crossFromFulu`, the fork state `atFork`, the slots, the FULL settlement of the `.landed` bid) and
`.gloas` (`GloasStepData`, exposing the post-slots state `postSlots`, the settlement and the built-upon block).
`GJointRun.blocks` are the built-upon execution blocks, one `KeptHistory` (`GJointRun.keptHistory`);
`GJointRun.extendsBy` splits them at a step (`payloadIndex`); `GJointRun.reach`, `reach_pre`, `reach_post`,
`reach_post_pre` over `GJointReach`. `GJointRunStep.exists_of_jointStepG` makes any successful step from a
`ParentCoherent` state a run step; `keptStep_of_engineVerdictG` turns an accepted Gloas payload into an Amsterdam
`KeptStep`. The joint-level invariants G3-09..11 (`ExecHeadIsLatestBlockHash`, `ParentPayloadCoherence`,
`ExpectedWithdrawalsLedger`, together `GJointInv`), their step preservation, the Gloas `process_block` frame of
`latest_block_hash` (`processBlock_latestBlockHash`), and the crossing's forced FULL settlement
(`crossing_parentFull`, `jointStepG_cross_ok_of_spec`) and builders (`CrossingData.buildersFar`) are in
[`Blanc/JointGloasInvariants.lean`](../Blanc/JointGloasInvariants.lean).
For the beacon side of a step, `JointRun.steps_jointStep` recovers the successful
`jointStep` of any indexed step; `jointBlockInput ccfg bls s b` is the beacon state the
step hands to `process_block` (same calls as `jointStep`), and `jointStep_processBlock`
shows a successful step ran `processBlock (jointCtx ccfg bls)` on it successfully
(`stateTransition_processBlock` is the within-fork piece). Combine with Jaune's
`Facts.processBlockWith_split`/`Facts.processOperations_split` to reach a mid-block state.
For a step's withdrawals, `jointWithdrawalsInput ccfg bls s b` is the state
`process_withdrawals` reads (after `process_block_header`), and
`jointStep_processWithdrawals` gives its `getExpectedWithdrawals` result `(ws, processed)`,
the payload withdrawals equal to `ws` (via `consensusWithdrawals_eq_of_beq`, the derived
`BEq` as equality) and the successful `process_withdrawals`; `JointStepTrace.block_wds`
identifies the step's execution block withdrawals with `payloadWithdrawals b`. For the
execution-side credit of a withdrawal list, `addBal_bal` gives a credit's effect on one
address, `processWithdrawalsState_bal_congr` says the fold's effect at an address depends only
on that address's balance, and `processWithdrawalsState_bal_filter` reduces an address's
balance after the fold to crediting only the withdrawals addressed to it.
To address a flattened per-step list (any `l.flatMap f`, e.g. the requests of all of a
run's steps) by step and offset, use
[`Blanc/ListFlatMapPosition.lean`](../Blanc/ListFlatMapPosition.lean):
`Blanc.List.exists_flatMap_position` gives every position `i` a pair `(j, k)` with
`k < (f l[j]).length` and `((l.take j).flatMap f).length + k = i`, and
`Blanc.List.flatMap_position_inj` makes that pair unique. The element there is
`Blanc.List.getElem?_flatMap_position` in
[`Blanc/ListChunks.lean`](../Blanc/ListChunks.lean), which also cuts a list into fixed-width
pieces (`Blanc.List.chunksOf`, with `Blanc.List.chunksOf_flatMap`: re-chunking blocks of exactly
`w` elements gives the blocks back, so a byte string of fixed-length records reads back as its
records) and splits a list around its one element satisfying `p`
(`Blanc.List.split_of_filter_length_one`: the split, `find? p`, and the longest prefix avoiding `p`).
The same module splits a list at an index it holds (`Blanc.List.eq_take_cons_drop`), splits a
pointwise `Forall₂` relation alike (`Blanc.List.forall₂_split`), and follows a queue entry drained
at a fixed rate along a list to where it is drained (`Blanc.List.drain_position`: entry `q` of the
queue at index `j` is entry `q % cap` of what index `j + q / cap` drains).
For a configured covered-fork pre-history followed by a joint run (`RingJoint`, with ring-contract header, timestamp and number bounds
`ObservedPreTip`, `HistoryTimestampsFit`, `HistoryNumbersFit`) or a typed request feed across a `JointRun`
(`JointFeed.stepRequests`, `JointFeed.feed`, `JointFeed.feedPosition`, `exists_feed_position`, `feedPosition_inj`),
use [`Blanc/JointFeed.lean`](../Blanc/JointFeed.lean), which also bridges `JointRun` steps directly to `KeptHistory`
(`JointRun.kept_toExec`, `kept_take_pre`, `kept_take_add`, `kept_getElem?`).
For the stable frozen ring vocabulary, use
[`Blanc/Corpus/Freeze/RingCommon.lean`](../Blanc/Corpus/Freeze/RingCommon.lean):
`Blanc.Corpus.Freeze.ring`, `keptAtAddr`, `storOf`, `frameStor`, `ObservedPreTip`,
`HistoryTimestampsFit`, `HistoryNumbersFit`, `stepTime`, `stepNumber`, `stepSlot` and
`Blanc.Corpus.Freeze.RingJoint`. This frozen carrier and `Blanc.RingJoint` are distinct nominal types;
use the carrier required by the statement rather than assuming they are interchangeable.

For consensus SSZ byte equations, use
[`Blanc/ConsensusSsz.lean`](../Blanc/ConsensusSsz.lean):
`leBytes_eight_eq_reverse_toBytes` (little-endian `uint64` bytes are Jaune's
big-endian `UInt64.toBytes` reversed), `leNat_leBytes`, `leBytes_eight_injective`,
`adr_toBytes_injective`, `toAdr?_toBytes` (an address's 20 bytes decode back to it, with
`toAdr?_append` and `uint32_ofBytes_eq_toUInt32`), `serialize_byteVector`, and
`serializeSeq_of_fixedSize`/`serialize_sszList_of_fixedSize` (a list of
fixed-size elements serializes to the concatenation of its elements). For a consensus
`WithdrawalRequest`, `serialize_withdrawalRequest` gives its serialization field by field
(source address, public key, little-endian amount), `serialize_withdrawalRequest_length`
its 76 bytes, and `serialize_withdrawalRequest_injective` its injectivity.

To turn a block's transaction or receipt trie entries into body and receipt
facts, use [`Blanc/ExecutionTrieBinding.lean`](../Blanc/ExecutionTrieBinding.lean).
`transactionsEntries` and `receiptsEntries` are the entry lists that
`getTransactionsRoot` and `getReceiptRoot` build their trie maps from
(`transactionsNTB`, `receiptsNTB`; `getTransactionsRoot_eq_trie`,
`getReceiptRoot_eq_trie` by `rfl`), with values `txTrieValue` and
`receiptTrieValue`. State a binding over these lists, not over the `NTB` tree
(structural tree equality includes shape). No Merkle–Patricia injectivity of `trie` is proved; the
entry equality is the caller's obligation.

To exclude an address using a missing log-bloom bit, use
[`Blanc/LogBloom.lean`](../Blanc/LogBloom.lean).
`LogBloom.ContainsAddress` requires all three address bits from Jaune's actual
Keccak digest; `HasIndex`, `byteIndex` and `bitMask` expose an individual bit.
`LogBloom.containsAddress_of_mem` proves that a member of `logs` has all three
bits in `logsBloom logs`; `address_ne_of_missing` is its exclusion form. OR
updates preserve existing bits, including through later logs and topics.
The index bound and bit preservation use kernel-checked natural-number and
Boolean algebra; no native bitvector decision axiom is required.
No hash injectivity or cryptographic exclusion premise is needed.
For transaction and interval membership, use `ExecutionBlockLogs` below.

To relate a configured history to a later one, use
`ExecutionTrace.ConfiguredHistoryTrace.ExtendsBy` in
[`Blanc/ExecutionHistoryExtension.lean`](../Blanc/ExecutionHistoryExtension.lean):
`base.ExtendsBy trace n` says `trace` is `base` followed by exactly `n`
configured blocks. Its lemmas `settledFrames` (base frames are a prefix),
`rawFrames_mem`, `blockCount` (`trace.blockCount = base.blockCount + n`),
`noSenderAt` and `noAuthorityAt` restrict an extension's retained frames and
caller/authority exclusion premises to the history it extends.

To concatenate two selected-domain (`In`) histories end to end, use
`ExecutionTrace.ConfiguredHistoryTraceIn.append` in
[`Blanc/ExecutionHistoryInAppend.lean`](../Blanc/ExecutionHistoryInAppend.lean):
`append first second` joins D-to-P and P-to-B into D-to-B by induction on
the second history's `.step` spine. Its lemma `rawFrames_append`
concatenates the frame lists in order, and
`NoDelScheduled_append`, `RewardCreditsFunded_append` and
`FrameAdmitted_append` split the per-block conjunction predicates across
the join. To move a history across fork domains, `ConfiguredBlockTraceIn.map`
and `ConfiguredHistoryTraceIn.map` re-predicate block and history along
`∀ f, F f → G f` (raw and settlement-retained roots are kept by
`map_rawFrames` / `map_settledFrames` at both levels); `toHistFork` at both
levels specializes the re-predication along `CoveredFork.histFork`, and
`ConfiguredHistoryTrace.toHistForkIn` chains the existing
`ConfiguredHistoryTrace.toIn` with it, so a modern suffix joins a
historical prefix through `append` with `toHistForkIn_rawFrames` /
`toHistForkIn_settledFrames` identifying the kept roots. No premise assumes
delegation, EIP-2929 access, or enabled optional passes.

To start a selected-domain history in the middle of a block (a contract
deployed by transaction `i` of block N), use
[`Blanc/ExecutionMidHistoryIn.lean`](../Blanc/ExecutionMidHistoryIn.lean).
`ExecutionTrace.ApplyTransactionsTrace.TxSplit trace i` cuts a retained
transaction fold at `i` into `before`, the actual `head : TransactionTrace`
and `after`, with `rawFrames_eq` / `settledFrames_eq`; `splitAt` builds one
for every `i < txs.length`, `TxSplit.putIndex_eq` identifies `index` and `tx`
on a decoded block list, and `afterBenv` is the boundary right after `i`.
For exact legacy-body identification,
use [`Blanc/ExecutionBodyTransactionCut.lean`](../Blanc/ExecutionBodyTransactionCut.lean).
An explicit full ordered body equality
and selected-list position identify the supplied original cut's transaction;
they supply no historical observation, sender, receipt, or state fact.
The equality head is shared by unrelated goals, so discovery remains this
manual registry route rather than a broad proof-recipe trigger.
`ConfiguredBlockTraceIn.txSplit_stat`, `txSplit_notCreated` and
`txSplit_bound` derive the selected fork, the empty created set and the
withdrawal-inclusive no-wrap bound at the cut from the block.
`MidHistoryTraceIn F cfg start future` has base `tail block cut` (the rest
of block N) and `.step` whole blocks; it carries `rawFrames`,
`settledFrames`, `FrameAdmitted` (`frameAdmitted_iff_rawFrames`),
`RewardCreditsFunded`, `rawFrames_mem_block` (every raw root lies in some
retained block, so block-level per-root facts transfer), and `append` with a
`ConfiguredHistoryTraceIn` (frames, admission and funding split across it).
`ConfiguredBlockTraceIn.rawFrames_txSplit` splits a
block's frames at the cut and `FrameAdmitted.tail` restricts block
admission to the base. Preservation: `ConfiguredBlockTraceIn.tail_stateInv_admitted_semIn`,
`MidHistoryTraceIn.stateInv_admitted_semIn` / `stateInv_admittedIn`; the
post-fold stages alone are `StagedBodyTrace.afterTransactions_stateInv_admitted_semIn`.
The accounting rungs `afterTransactionsIn`, `configuredBlockTailIn` and
`midHistoryIn` are in
[`Blanc/ExecutionAccountingMidHistoryIn.lean`](../Blanc/ExecutionAccountingMidHistoryIn.lean).
The per-root block facts already transported to a mid history are in
[`Blanc/ExecutionMidHistoryInFacts.lean`](../Blanc/ExecutionMidHistoryInFacts.lean):
`MidHistoryTraceIn.rewardCreditsFunded` (every block, the cut block included, funds its reward
credits under `BodyStageCapabilities F`) and `rawFrames_entered` (any `EnteredCondition`),
each through `rawFrames_mem_block`.

For the original retained forest and admitted queries after a transaction cut,
use [`Blanc/ExecutionMidHistoryInForest.lean`](../Blanc/ExecutionMidHistoryInForest.lean).
It imports the canonical `MidHistoryTraceIn.settledRoots` and `settledFrames_eq`
from [`Blanc/ExecutionHistoryCommittedCuts.lean`](../Blanc/ExecutionHistoryCommittedCuts.lean);
`settledFrames_parentIn` adds the actual suffix roots' parent relation.
`ApplyTransactionsTrace.TxSplit.senderQueries_after` proves the exact query drop
for any genuine cut; `senderOccurrences_tail_indexed` preserves original indices
and full transaction inputs. `senderQueries_cut_prefix`
embeds the mid history as the original full history's
ordered suffix, with membership corollaries. The query list preserves duplicates
and includes admitted transactions whose VM execution reverts.
`settledRoots_caller_ne_of_senderQueries` transfers actual sender-query exclusion
and a distinct system address to mid root callers. The start remains the cut's
actual `afterBenv`; these APIs neither create a block-chain checkpoint there nor
rebase deployment-world facts from the full history.


Fork-era schedule facts for historical extraction live in
[`Blanc/ExecutionHistoryInForkFacts.lean`](../Blanc/ExecutionHistoryInForkFacts.lean):
`BerlinOnwards`, `PrePrague`, `PreCancun`, `PragueOnwards` (fork lists in
activation order, each with a `DecidablePred` instance) and decision lemmas
over `histForks` discharging per-fork premises — `HistFork.access_eip2929_of_berlinOnwards`,
`HistFork.two_mem_precompiles`, `HistFork.delegationDisabled_of_prePrague`,
the `sys.beaconRoots` / `sys.historyStorage` / `header.requestsHash` flag
facts by era, `HistFork.preCancun_cancun_pragueOnwards`, and
`PreCancun.toPrePrague`. To show a per-fork numeric or schedule property,
follow the same `revert`-then-`cases f <;> decide` pattern (compare
`HistFork.dataNonZero_ge`).

Warmth of transaction frames along retained `In`-histories is in
[`Blanc/ExecutionHistoryInWarmth.lean`](../Blanc/ExecutionHistoryInWarmth.lean):
`ConfiguredHistoryTraceIn.txRawFrames` projects the transaction frames, and
`txRawFrames_warmIn` (with per-transaction, per-list, per-body and per-block
rungs) shows every transaction frame starts with every active precompile
warm, from the history's own `BodyStageCapabilities` plus an explicit
per-fork EIP-2929 access hypothesis and per-fork precompile membership —
flat-access forks get no claim. `txRawFrames_warm_hist` discharges both for
`0x02` on a Berlin-onwards `HistFork` domain by decision.

Empty code at one address along retained `In`-histories is in
[`Blanc/ExecutionHistoryInCodeAt.lean`](../Blanc/ExecutionHistoryInCodeAt.lean):
neutral (`stateGas = none`) twins of the interpreter core
(`Xinst.step_spawn_create_codeAddress_noStateGas`,
`Xinst.codeAt_effectRecAvoid_noStateGas`, `Evm.step_codeAt_noStateGas`,
`Exec.codeAt_avoid_noStateGas` through `Xinst.step_shapeNoStateGas` with
child environments by `Evm.step_spawn_child_benvStat`), the message and
transaction rungs, and the staged body, block and history levels.
EIP-7702 authority is a disjunct beside the no-authority premise from the
message level up (`..._noStateGas` lemmas), cased per fork at history level
from an explicit per-fork disabled-delegation hypothesis plus
`ConfiguredHistoryTraceIn.NoAuthorityAt` (new `In` definition); fully
pre-Prague histories use `codeAt_empty_prePrague` with no authority premise
at all. `sweepTouchedAccounts_getCode_empty` keeps empty code through the
sweep.

For nonce transport within settlement-retained execution, use
[`Blanc/ExecutionNonceCode.lean`](../Blanc/ExecutionNonceCode.lean).
`Evm.step_spawn_nonce_noStateGas` and
`Exec.Deriv.ParentStep.nonce_ne_zero_noStateGas` supply the instruction-level transport.
Complete child settlement determines which nodes survive; discarded children
cannot supply the starting position.

For nonzero-nonce continuity in the same retained execution, use
`Exec.retainedNodes_nonce_ne_zero_after_split_noStateGas` or
`Exec.retainedNodes_nonce_ne_zero_of_ordered_noStateGas`. They carry a nonzero
nonce observed at an actual retained position through child return and all
later retained positions, including the committed endpoint. The child-return
seam `Exec.spawn_nonce_eq_of_settlementCommits_noStateGas` preserves every raw
nonce exactly, including the CREATE target; code deposit changes no nonce.
`Exec.rawNodes_nonce_ne_zero_noStateGas` supplies entry-to-node transport.
`Exec.retainedNodes_create_ne_of_ordered_nonce_noStateGas` combines the ordered
nonce result with the actual later CREATE guard to exclude address reuse;
supply the later node's no-state-gas premise and its actual spawn/entry witness.
These APIs require the original retained-list split. They concern
one execution and do not exclude an earlier lifetime in another transaction
or prove survival through the outer transaction's deletion fold.

For the final message or transaction state, use
[`Blanc/ExecutionRetainedCodeSettlement.lean`](../Blanc/ExecutionRetainedCodeSettlement.lean).

For accounts that may have been created after root entry, use
[`Blanc/ExecutionDeletionProvenance.lean`](../Blanc/ExecutionDeletionProvenance.lean).
`Exec.retained_atd_origin_noStateGas` traces any endpoint deletion to the
initial deletion set or to a SELFDESTRUCT node in the same execution's
complete-settlement-retained chronology.
`Exec.not_mem_atd_of_retained_terminal_safe` therefore needs only initial
deletion absence and retained terminal exclusion, without installed entry
code or exclusion from the created-account set. Discarded child settlements
use the existing rollback law; successful CREATE deposits preserve the raw
child deletion set. The lower-level interfaces are
`Linst.selfdestruct_accountsToDelete_noStateGas`,
`Linst.accountsToDelete_origin_noStateGas`,
`Evm.step_cont_atd_noStateGas`, `Evm.step_halt_atd_origin_noStateGas`,
`Evm.step_spawn_enter_atd_subset_noStateGas`,
`Evm.step_spawn_resume_atd_origin_noStateGas` and
`Evm.step_doneOk_atd_subset_noStateGas`.
`GenericCreate.step_done_atd`, `GenericCall.step_done_atd`,
`Xinst.step_done_atd_noStateGas`, `Resume.create_atd_of_clean`,
`Resume.call_atd_of_clean`, `executeCode.handle_precompile_ok_atd`,
`ProcessMessage.none_ok_atd` and `ProcessCreateMessage.none_ok_atd_of_clean`
cover the synchronous and return boundaries. These membership/equality goals
do not identify the actual execution or terminal-safety certificate, so no
reliable automatic recipe trigger is registered.

For an account with empty code, such as an externally owned account or the
SYSTEM address, use
[`Blanc/ExecutionEmptyContext.lean`](../Blanc/ExecutionEmptyContext.lean).
`Exec.rawNodes_emptyContext_noStateGas` shows that every reached node whose
storage context is the account runs empty code, when the account's code is
empty at entry and no entered frame is a CREATE at it;
`Exec.rawNodes_no_selfdestruct_of_emptyContext` concludes that no such node
decodes SELFDESTRUCT. The message wrappers
(`MessageCallTrace.settledRoots_no_selfdestruct_of_emptyContext`, with the
code-free root condition `MsgEmptyEntry`) supply the terminal-safety
certificate, and `TransactionTrace.not_deleted_of_emptyContext` concludes
exclusion from the transaction's actual deletion set with no nonempty-code or
created-set premise. The premises are trace facts (empty code, CREATE
avoidance, authorization exclusion), so no automatic recipe trigger is
registered.

To conclude that an account sent no transaction from its final nonce, use
[`Blanc/ExecutionNonceKeep.lean`](../Blanc/ExecutionNonceKeep.lean). A settled
message call keeps every nonzero nonce on every arm
(`MessageCallTrace.nonce_ne_zero`, from `Exec.nonce_ne_zero_committedPost_noStateGas`
and the existing message-entry nonce lemmas), and so do system messages,
withdrawals, request calls and reward credits. Under the empty-code context
facts above, `TransactionTrace.nonce_ne_zero_of_emptyContext` keeps a nonzero
nonce through deletion and the empty-account sweep and gives the sender one.
The folds `ApplyTransactionsTrace.noSender_of_nonce_zero`,
`StagedBodyTrace.noSender_of_nonce_zero`,
`ConfiguredBlockTraceIn.noSender_of_nonce_zero` and
`MidHistoryTraceIn.noSender_of_nonce_zero_cancun` turn a zero nonce at the end
into the `NoSenderAt` premise over the whole span: a one-block nonce
observation replaces a census of senders.

For an actual transaction, the initial deletion-absence premise is derived by
`TransactionTrace.settledRoot_entry_not_deleted` in the same module. Its
`RetainedXlot`, `ProcessMessageTrace`, `ProcessCreateMessageTrace` and
`MessageCallTrace.settledRoot_entry_atd` adapters identify the selected root's
entry set with the message's inherited deletions. The existing
`messageCallExecutionMessage_inherited` helper in `ExecutionHistoricalAdmission`
is public for the delegation step; transaction preparation supplies emptiness.
`TransactionTrace.not_deleted_of_retained_terminal_safe` then supplies the
actual output exclusion. These interfaces need neither
installed entry code nor an initial not-created invariant. Terminal safety
still ranges over the actual retained nodes of the selected root; code
classification and historical installation remain consumer obligations.
Selected trace/root/node witnesses cannot be recovered from the equality or
membership goal alone, so these adapters have no automatic recipe trigger.

For whole transactions, including those with no retained interpreter root,
use `TransactionTrace.not_deleted_of_retained_terminals`. Its terminal
condition ranges over all actual settled roots; synchronous completion and
discarded outcomes are handled by the CALL, CREATE and
`MessageCallTrace.not_deleted_of_settledRoots` adapters. These require only
deletion exclusion, not the stronger installed-account `NoDel` invariant.
`TransactionTrace.code_preserved_of_retained_terminals` preserves installed
nonempty, nondesignator code and supplies the actual output deletion exclusion.
`ApplyTransactionsTrace.code_preserved_of_retained_terminals` composes that
result across the exact transaction list, also returning `NoDelScheduled`.
Both allow an account created earlier in the same block; neither assumes
exclusion from the block's created-account set. They retain stateGas-none,
actual starting installation and terminal-safety premises. No claim about
the historical origin of that installation follows. As above, a code equality
does not determine the required transaction trace or safety certificate.

When the same selected root already has a deletion-exclusion proof, use
`TransactionTrace.not_mem_accountsToDelete_of_settledRoot` to discharge the
actual output-deletion premise.
Its message-level companion is
`MessageCallTrace.not_mem_accountsToDelete_of_settledRoot`. Neither requires
installed code, a nonempty entry account, or exclusion from the initial
created-account set. `ProcessMessageTrace.settledRoot_post_atd` and
`ProcessCreateMessageTrace.settledRoot_post_atd` identify the core deletion set
with that of the actual retained root; `ProcessMessage.ok_atd_eq_committedPost`
is the raw CALL settlement projection. Successful code deposit preserves the
constructor's deletion set, while failed complete settlement supplies no root.
These adapters consume selected-root membership and cannot infer that witness
from a deletion-membership goal, so they have no automatic recipe trigger.

System frames along retained `In`-histories by fork era are in
[`Blanc/ExecutionHistoryInSystemFrames.lean`](../Blanc/ExecutionHistoryInSystemFrames.lean):
`StagedBodyTrace.systemRawFrames` and the block/history `systemRawFrames`
projections, the era-indexed `installedAt` set (`[]` before Cancun, beacon
roots only on Cancun, all four from Prague) with decision
characterizations, and per-stage target facts feeding
`StagedBodyTrace.systemRawFrames_target_of_spawnFree` (all four targets),
`ConfiguredBlockTraceIn.systemFrames_target_inEra`, and
`ConfiguredHistoryTraceIn.systemFrames_target_inEra` (each frame targets its
own block fork's installed set). State preservation is complete before
Cancun (`systemFrames_installed_preCancun`, `SystemCodeInstalledAt.of_preCancun`,
both vacuous) and through every system message
(`SystemMessageTrace.installed_keep_noStateGas`); preservation through
transactions on Cancun and later eras goes through the non-deletion chain,
stated once under `stateGas = none` plus the EIP-6780 flag with the
`CoveredFork` forms derived (`CoveredFork.rules_selfdestructOnlyCreated`): the
interpreter core (`Evm.step_effect_noStateGas`, `Exec.effect_neutralSchedule`,
`Exec.inv_noDel_noStateGas`) and message/create/call preservation
(`processMessageCall_accountsToDelete_ne_noStateGas`) in
[`Blanc/LadderBase.lean`](../Blanc/LadderBase.lean); the settlement form
(`TransactionTrace.exists_finalStateForm_noStateGas` with explicit
refund-quotient/touched-sweep hypotheses) and the transaction(-list) keeps
(`TransactionTrace.codeAt_keep_noStateGas`,
`ApplyTransactionsTrace.codeAt_keep_noStateGas`) in
[`Blanc/ExecutionTraceCodeKeep.lean`](../Blanc/ExecutionTraceCodeKeep.lean). Era schedule facts
(`CancunOnwards`, EIP-6780/refund-quotient/touched-sweep decisions,
`HistFork.pragueOnwards_covered`) are in
[`Blanc/ExecutionHistoryInForkFacts.lean`](../Blanc/ExecutionHistoryInForkFacts.lean).
Installed-code preservation through staged bodies, blocks, and histories is in
[`Blanc/ExecutionHistoryInSystemCodeKeep.lean`](../Blanc/ExecutionHistoryInSystemCodeKeep.lean):
`StagedBodyTrace.codeAt_keep_noStateGas` threads one canonical (nonempty,
non-delegating) code through beacon, history-storage, transaction,
withdrawal, request, and reward stages;
`ConfiguredBlockTraceIn.systemFrames_installed_keep` preserves each block fork's
own installed set, era-split by `HistFork.preCancun_cancunOnwards` (vacuous
before Cancun, keep from Cancun on, per-address facts via
`mem_systemContracts_of_mem_installedAt` and `systemContracts_facts`);
`ConfiguredHistoryTraceIn.codeAt_keep_of_cancunOnwards` threads one canonical
code along every all-Cancun-onwards history
(`ConfiguredHistoryTraceIn.AllCancunOnwards`), with
`ConfiguredHistoryTraceIn.beaconRootsCode_keep_of_cancunOnwards` discharging the
beacon-roots character facts once and for all.

The CREATE-avoidance premise of that keep chain is derived from the kept code itself in
[`Blanc/ExecutionHistoryInCreateAvoid.lean`](../Blanc/ExecutionHistoryInCreateAvoid.lean):
a nested CREATE spawns only after finding empty code at its new address and a top-level
creation runs only on a false `messageCreateCollision`, so nonempty code at `a` excludes every
frame without a code address targeting `a` (`Exec.createAvoid_noStateGas`, lifted through
`MessageCallTrace`, `TransactionTrace`, `ApplyTransactionsTrace`, system messages, stages and
`StagedBodyTrace.createAvoid_noStateGas` to
`ConfiguredBlockTraceIn.createAvoid_of_cancunOnwards`). Use
`ConfiguredBlockTraceIn.installedNoFrame_of_opening` /
`ConfiguredHistoryTraceIn.installedNoFrame_of_openings` for the installed-target exclusion
from actual openings, `ConfiguredHistoryTraceIn.systemCodeAtOpenings_of_cancun_present` for a
Cancun spine from one beacon anchor with no frame premise, and
`ConfiguredHistoryTrace.systemCreateAvoid` for a modern history from `SystemCodeInstalled`.
Delegation keeps the code address (`messageCallDelegation_codeAddress`).

Actual block-opening system installations and system-target exclusion for retained
historical traces are in
[`Blanc/ExecutionHistoryInSystemEnvironment.lean`](../Blanc/ExecutionHistoryInSystemEnvironment.lean).
`ConfiguredBlockTraceIn.SystemCodeAtOpening` and
`ConfiguredHistoryTraceIn.SystemCodeAtOpenings` select `installedAt` at each
actual opening state; they require no installed code before Cancun.
`ConfiguredBlockTraceIn.systemFrames_target_of_installedAt` derives the active
target set from those installations and the existing no-authority/no-CREATE
trace scopes, using reachable instruction positions (`SpawnFreeReach`) for
canonical system code. `rawFrames_system_or_tx` partitions the actual raw
frames; `not_mem_installedAt_of_size` excludes a differently sized installed
contract from the active system addresses. These are trace-level inputs for
composition; the C/P seams must supply the opening installations.
This is a registry branch rather than a proof recipe: target-set conclusions
alone do not identify the matching installed-code and trace-scope witnesses,
and a general list-membership or raw-frame trigger is not selective.

To produce those opening obligations from actual checkpoint cuts, use
[`Blanc/ExecutionHistoryInSystemOpenings.lean`](../Blanc/ExecutionHistoryInSystemOpenings.lean).
`ConfiguredHistoryTraceIn.ForksSatisfy` records a predicate of each selected
fork; `tip_fork_mono` and `forksSatisfy_between` derive actual schedule bounds
from the endpoint tips, via Jaune's `stateTransitionUsing_fork_mono` and each
retained block's exact post-state equation. `systemCodeAtOpenings_of_cancun` threads one initial beacon-roots
installation through the actual Cancun spine with the existing code-keep laws.
`NoAuthorityAt_append` composes actual
authorization predicates. These remain registry entries: the opening goal
alone does not distinguish the eras or identify the endpoint lookup and initial
code witnesses. Do not replace those witnesses by an unexplained per-block
installation premise.


### E7. I need stable paths to settlement-retained frames

Use [`Blanc/ExecutionPath.lean`](../Blanc/ExecutionPath.lean):

- `Exec.LocatedFrame` pairs a retained frame with its zero-based call-tree
  path.
- `Exec.descendantFramePaths` and `Exec.committedFramePaths` enumerate retained
  descendants and the root-inclusive committed path list.
- `Exec.committedFramePaths_map_frame` forgets paths back to the ordinary
  committed-frame list. `Exec.descendantFramePaths_map_frame` gives the same
  projection for a supplied original entering path and child counter.
- `Exec.LocatedFrame.EnteringOccurrence` is indexed by the original execution
  and preserves the exact immediate retained parent as an original
  `committedFramePaths` member, the actual child counter, its same-frame
  retained instruction occurrence, and that occurrence's exact recursive child
  slot and `runOk` equations. This keeps equal-looking frame occurrences
  distinct.
- `Exec.LocatedFrame.exists_enteringOccurrence` is the minimal consumer route:
  apply it to a non-root `committedFramePaths` member, then refine the retained
  occurrence's decoded instruction if the contract needs a particular family.
  It deliberately does not classify the root `[]`; use configured transaction
  or system-envelope provenance for that case.


For the direct children of a frame and the selection of target frames, use
[`Blanc/Lift/RetainedTargetCompleteness.lean`](../Blanc/Lift/RetainedTargetCompleteness.lean):
`Exec.childFrames_eq_nil_of_free` and `Exec.Deriv.ExecFreeUntil.childFrames_eq`
say a span of the chain that decodes no `Xinst` has no direct child;
`Exec.Deriv.ParentStep.childFrames_spawn` (and `descendantFrames_spawn_done`,
`descendantFrames_runOk`) split the retained frames at a spawning node into the
entered child's and the continuation's; `Exec.mem_descendantFrames_of_mem_childFrames`
embeds a direct child; `Exec.descendantFrames_isStatic` makes every retained
frame below a static run static; and `Exec.retainedTargetFramesFromAt_complete`
says every retained frame at `ca` lies inside one frame that
`retainedTargetFramesFromAt ca` selects (the outermost target frames).
`Xinst.step_callKind_spawn_target`/`_codeAddress` read a CALL-kind child's
target and code address.


### E8. I need an exact ordered replay of world-state changes

Start with [`Blanc/ExecutionStateTrace.lean`](../Blanc/ExecutionStateTrace.lean):

- `StateTransition` and `StateReplay` are the generic event and continuity
  carriers; `StateReplay.append`, `.mapOrigin`, and `.castPost`, plus
  `StateTransition.mapOrigin`, compose and re-label a replay.
- `Exec.StateBoundaryKind`, `Exec.StateBoundaryOrigin`, `Exec.StateBoundary`,
  `Exec.stateBoundary`, `Exec.startState`, `Exec.stateBoundariesOfCommits`, and
  `Exec.committedStateBoundaries` build the execution-level chronology;
  `Exec.committedStateReplay` proves it continuous.

The wrapper-specific chronology modules use the same vocabulary and expose
`stateBoundaries`, an `exists_stateChronology` bridge where a separate
chronology witness is needed, and a terminal `stateReplay` theorem:

- [`Blanc/ExecutionMessageStateTrace.lean`](../Blanc/ExecutionMessageStateTrace.lean)
  for `MessageStateBoundaryKind`, `MessageStateBoundaryOrigin`,
  `MessageStateBoundary`, and `MessageCallTrace`;
- [`Blanc/ExecutionTransactionStateTrace.lean`](../Blanc/ExecutionTransactionStateTrace.lean)
  for transaction refund, coinbase, deletion, and
  `TransactionStateChronology` boundaries;
- [`Blanc/ExecutionSelectedTransactionStateTrace.lean`](../Blanc/ExecutionSelectedTransactionStateTrace.lean)
  for the selected transaction refund, coinbase, deletion, and touched-sweep
  `SelectedTransactionStateChronology` boundaries under
  `stateGas = none` (selected gas/refund/tip via semantic
  `settleTransactionGas`; sweep suffix empty when the rules do not sweep);
- [`Blanc/ExecutionBodyStateTrace.lean`](../Blanc/ExecutionBodyStateTrace.lean)
  for system messages, transaction lists, direct withdrawals, requests, and
  `AppliedBodyStateChronology`;
- [`Blanc/ExecutionStagedBodyStateTrace.lean`](../Blanc/ExecutionStagedBodyStateTrace.lean)
  for the staged-body chronology under `stateGas = none`:
  `StagedBodyStateChronology` retains only the selected transaction-list
  chronology and replays beacon, history, selected transactions, withdrawals,
  requests, then rewards in `applyBody` order (withdrawals gated by the header
  switch, rewards empty under `pow = none`);
- [`Blanc/ExecutionHistoryInStateTrace.lean`](../Blanc/ExecutionHistoryInStateTrace.lean)
  for the In-block / In-history chronology: `ConfiguredBlockStateChronologyIn`
  holds the D1 staged-body chronology with an `initBenv` preparation event and
  derives `post` via `postEq`; `ConfiguredHistoryStateChronologyIn` follows
  refl/step. Per-block `stateGas = none` is discharged from the history's own
  `BodyStageCapabilities`, with the reward-suffix rule carried from D1;
- [`Blanc/ExecutionHistoryStateTrace.lean`](../Blanc/ExecutionHistoryStateTrace.lean)
  for `ConfiguredBlockStateChronology` and
  `ConfiguredHistoryStateChronology` across schedule-parametric histories.

For the actual successful LOG observations, use
[`Blanc/Lift/CommittedLogs.lean`](../Blanc/Lift/CommittedLogs.lean).
`Exec.logAt?` reads the decoded opcode, operand stack and memory;
`Exec.Deriv.successfulLog?` selects successful continued instructions, and
`Exec.Deriv.successfulLog?_sound` exposes their actual decoded step and appended
log. `Exec.boundaryOwnLogs` emits only at instruction boundaries.
`Exec.committed_logs` equates the committed endpoint log list to its incoming
prefix plus those observations in the existing retained chronology. Its
`CoveredFork` premise covers child initialization, CALL and CREATE resumption,
and complete settlement failure; failed subtrees are pruned and settlement
boundaries never duplicate child logs. For message-root receipt bridges,
`Frame.settle_logs_eq` exposes complete-settlement log preservation, including
code-deposit settlement; `Frame.settle_logs_of_ok` retains its compatibility
interface. `Frame.enter_done_clean_logs_noStateGas` proves an immediate clean
entry has no logs. These reuse the same settlement and native-entry proofs.


For inclusion from a retained frame into the root endpoint, use
`Exec.committedFrame_logs_subset_noStateGas` in
[`Blanc/Lift/CommittedFrameLogs.lean`](../Blanc/Lift/CommittedFrameLogs.lean).
It needs root commitment, `stateGas = none`, and membership in
`Exec.committedFrames`; delegation and access rules remain arbitrary. Complete
failed settlement still discards the child subtree.

For an actual same-parent LOG occurrence, use
[`Blanc/ExecutionParentLogAttribution.lean`](../Blanc/ExecutionParentLogAttribution.lean).
`Exec.Deriv.successfulLog?_mem_committedPost` puts the actual successful
instruction's entry in its committing suffix endpoint;
`Exec.Deriv.ParentPrefix.successfulLog_mem_committedPost` transports it to
the exact root endpoint using the parent prefix's unchanged outcome.
`Exec.Frame.parentLog_mem` supplies the retained-frame form.
`ExecutionTrace.TransactionTrace.log_mem_receipt_of_settledFrame` factors
endpoint-log membership through complete settlement into the original
transaction's successful receipt; `parentLog_mem_receipt` starts from the
same actual parent occurrence. `parentLog_eq_of_receipt_singleton` identifies
that emitted entry from a proved lookup and singleton log list for the same
receipt. Nested/reentrant logs need no exclusion premise. The source producer
must supply the real parent prefix, successful LOG image and actual retained
frame; these theorems neither infer an occurrence from a receipt value nor
authenticate external receipt observations. Only `stateGas = none` is needed;
delegation and access policies remain arbitrary. The membership and equality
conclusions have no sufficiently specific goal head for a proof recipe.

To regroup the retained boundaries into exact nonempty chunks and compose a
local source simulation, use
[`Blanc/Lift/SegmentedReplay.lean`](../Blanc/Lift/SegmentedReplay.lean).
`ReplayChunk` reuses `StateTransition`; `ExactChunks` retains exact flattening
and each chunk's continuous replay. `StateReplay.rechunk` derives the chunk
endpoints from the actual raw replay. `StateReplay.simulateChunks` composes
local steps and chronological observations with an explicit prefix-indexed
`Link`, so suspended source locals remain part of the incoming relation.
`Exec.StateBoundary.isOwn`, `Exec.AdmissibleChunk` and `Exec.AdmissibleCuts`
exclude decoded external instructions and child seams from own chunks, retain
one frame path and permit terminal only at the end. `Exec.simulateCommittedChunks`
applies the fold to the actual committed execution stream.
`Exec.simulateCommittedLogChunks` additionally connects the local producer's
ordered observations to the concrete endpoint logs using `Exec.committed_logs`.
`StateTransition.canonicalChunks` deterministically coalesces contiguous own
instruction prefixes under a semantic prepend policy. `StateReplay.canonicalChunks_exact`
derives exact coverage and endpoints; `Exec.committedCanonicalChunks_spec` supplies
admissibility on the actual committed stream. `Exec.simulateCanonicalLogChunks`
consumes those cuts without a supplied partition or log-endpoint premise.

For the same local fold over an existing configured-history witness, use
[`Blanc/Lift/SegmentedHistory.lean`](../Blanc/Lift/SegmentedHistory.lean):
`ExecutionTrace.ConfiguredAdmissibleChunk` preserves the original wrapper
boundaries, and `ExecutionTrace.ConfiguredHistoryStateChronology.simulateChunks`
consumes its `stateReplay`. Its `canonicalChunks`/`canonicalChunks_spec` and
`simulateCanonicalChunks` derive and consume exact admissible cuts through the
original wrappers. Local producers and a contract's model refinement remain required.

The same module's `Exec.retainedTargetTurns` selects original located frames by
storage owner and retains foreign boundaries. A selected target root stops the
outer traversal; failed ancestor settlement prunes the entire child subtree.
`retainedTargetTurns_expand` recovers the complete original chronology in order,
while `retainedTargetTurns_spec` preserves the selected frames' original ordered
sublist, ownership and foreign-boundary distinction. `retainedTargetTurns_entering`
supplies the actual entering occurrence for each selected non-root frame.
`retainedTargetTurns_cover` preserves ordered target/LOG observations.
`Exec.simulateRetainedTargetLogChunks` consumes canonical cuts of that actual
expanded queue and supplies the proven provenance to local chunk producers,
deriving the concrete committed log endpoint without a target-frame model
endpoint premise. Nested activity inside a selected frame remains in its expansion.
`Exec.retainedTargetTurnsAt` starts that same retained traversal at an original
entering path. `Exec.RetainedTargetTurn.rebase` changes only original paths, and
`retainedTargetTurnsAt_eq_map_prefix` identifies it with the ordered map of the
unprefixed traversal. It preserves child counters, duplicates, state boundaries
and complete failed-settlement pruning; it supplies no new entering occurrence
or contract-specific source queue.
`Exec.retainedTargetTurnsFrom_targets_spec` exposes the selected target-frame
projection for arbitrary entering paths and child counters.
For a structural fold over only the selected frames, use
`Exec.retainedTargetFramesFromAt`: it projects the existing traversal with
`filterMap Sum.getRight?` at the original parent path and child counter.
`Exec.retainedTargetTurnsAt_filterMap_eq` connects the entering-path wrapper
to that projection at counter zero. The `_target`, `_halt`, `_cont`, `_doneOk`
and `_runOk` equations preserve target selection and the original counters:
childless calls advance the parent counter; interpreted children use
`path ++ [counter]` and start at zero. A child contributes only when
`Frame.settlementCommits` holds, so a failed settlement removes its whole
subtree before the parent continuation is appended. These equations support
a local producer over the retained frames; they do not establish its request,
reply or contract-model correspondence.
For a fold that must also see the actual foreign LOGs in order (the turn queue of
a mutable external call), use `Exec.targetLogEventsFrom` in
[`Blanc/Lift/TargetLogEvents.lean`](../Blanc/Lift/TargetLogEvents.lean): retained
target frames interleaved with each foreign frame's successful `Exec.logAt?`.
`Exec.committedFrame_ownLogs_subset` embeds each settlement-retained frame's
canonical own-log ledger into its enclosing ledger by membership. Its proof
relates the existing tree/list projections, preserving complete-settlement
pruning, with no instruction-effect proof. `Exec.committedFrame_log_mem_noStateGas`
then places such a log in that same enclosing committed output through the
canonical log equation. These membership projections are registry-only because
a general list-membership goal does not identify this chronology reliably.
`Exec.targetLogEventsFrom_frames` proves its frame projection equals
`Exec.retainedTargetFramesFromAt`, with matching `_target`, `_halt`, `_cont`,
`_doneOk` and `_runOk` equations. The same module transports one foreign step for
arbitrary callee code: `Evm.step_done_getStor` requires a protected owner
for completed childless message settlement; `Xinst.spawn_run_getStor` and
`Evm.step_run_getStor_noStateGas` transport code-bearing storage from the settled child's
committed endpoint or rollback, pointwise. The `_noStateGas` forms take
`rules.stateGas = none`; under a covered fork apply them to
`CoveredFork.rules_stateGas_none`. The actual-step helpers
`GenericCreate.step_done_getStor` and `GenericCall.step_done_getStor`, in
[`Blanc/ExecutionMessageEffects.lean`](../Blanc/ExecutionMessageEffects.lean),
preserve every owner when the step itself returns `.done (.ok post)`. Successful CALL message transfer is a
spawn and does not satisfy that actual-step premise. The module also transports
logs (`Xinst.call_run_logs`: a CALL/STATICCALL appends exactly its committed child's
logs), the installed image (`CodeSem.At.parentStep`, `CodeSem.At.spawnChild_noStateGas`,
`CodeSem.At.callChild`, self-calls included), child entry (`Xinst.spawn_child_world`,
`Xinst.call_spawn_ofCall`, `Frame.ofCall_settle_clean`),
`Exec.retainedTargetFramesFromAt_rawFrameRoot` and `Lift.StepIn.codePreserve`.
The raw-frame-root theorem accepts an arbitrary original entering path and
child counter and retains their actual located-frame projection.
For code-free message entry, `Blanc.executeCode.enter_inr_routing` derives the
actual code address, enabled-precompile flag and fork's precompile predicate.
The module's `callMsg_none_precompile` consumes these routing facts for the
CALL/STATICCALL producers below. Pinned `Jaune.executeCode.enter_inr` instead
identifies the raw result as `executePrecomp (initEvm msg) adr`; these are
distinct projections.
For a successful nonzero-flag call with the actual recursive slot `.none`, use
`Xinst.call_none_precompile` (seven operands) or `Xinst.staticcall_none_precompile`
(six operands). They identify an enabled precompile at the original target;
the STATICCALL form preserves the supplied slot through
`of_step_staticcall_val_with_depth_frame_cause`; `Xinst.staticcall_none_precompileH` is the
STATICCALL form from `rules.stateGas = none` alone. An empty retained view queue
alone does not identify this route, since interpreted code can also retain no views.
The existing `goal-head:StateReplay` recipe selects chronology continuity;
the joint chunk/Link/observation premises are discovered through this registry.

### E9. I need to rule out an operand-stack fault over an actual walk

The common layers, bottom-up:

- [`Blanc/CompiledStackSafety.lean`](../Blanc/CompiledStackSafety.lean) states
  the local obligation. `StackFault` isolates the two operand-stack halts from
  every other `EvmError`; `NoStackFault` and `InheritedStackFault` distinguish a
  fault the parent generated from one a child settlement handed back;
  `ResumeSafe` and `StepSafe` are the per-step obligations; `Certificate` bundles
  them with a stack-height ceiling. `Certificate.parentStep`,
  `.parentPrefix` and `.at_parentPrefix` transport the invariant along the
  existing same-frame chronology, so no parallel execution relation is
  introduced.
- [`Blanc/AbstractStackSafety.lean`](../Blanc/AbstractStackSafety.lean) is the
  abstraction: a `Pattern` is a whole-stack list of `Option B256`, `none`
  forgetting a value but never an operand position, and `Matches` is exact
  rather than a prefix. `SafeResult` carries a postcondition through the success
  arm while keeping every error arm's stack-fault obligation.
- [`Blanc/AbstractStackTransfer.lean`](../Blanc/AbstractStackTransfer.lean)
  proves forward safety of `regularTransfer`, `jumpTransfer`, `jumpiTransfer`,
  `terminalTransfer` and `callTransfer` against the actual Jaune opcode
  implementations.
### Original history, caller and receipt adapters

For a caller fold over an arbitrary complete-settlement root list, use
`rootFrames_callerTarget_of_children` in
[`Blanc/Lift/CallChildren.lean`](../Blanc/Lift/CallChildren.lean).
[`Blanc/ExecutionMidHistoryCallers.lean`](../Blanc/ExecutionMidHistoryCallers.lean)
provides the selected-domain and mid-history wrappers and checked-sender exclusion.
The canonical roots and frame expansion remain in
[`Blanc/ExecutionHistoryCommittedCuts.lean`](../Blanc/ExecutionHistoryCommittedCuts.lean),
and system-stage caller facts remain in
[`Blanc/ExecutionSenderRootCallers.lean`](../Blanc/ExecutionSenderRootCallers.lean).
`ConfiguredHistoryTraceIn.append_senderQueries` and
`MidHistoryTraceIn.noSenderAt_of_senderQueries` in
[`Blanc/ExecutionMidHistoryInForest.lean`](../Blanc/ExecutionMidHistoryInForest.lean)
retain the exact original query lists, including failed transactions.

For caller exclusion over a Cancun suffix or history, use
[`Blanc/ExecutionMidHistoryInCallerExclusion.lean`](../Blanc/ExecutionMidHistoryInCallerExclusion.lean).
Its `NoSenderAt`, `AllCancun` and `BeaconCodeInstalled` record exact sender,
selected-fork and actual beacon-code duties.

The public
`messageCallExecutionMessage_code_empty` and `prepareMessage_callCode` in
[`Blanc/ExecutionTraceCallerExclusion.lean`](../Blanc/ExecutionTraceCallerExclusion.lean)
supply the actual message-code facts.


## I — invariance and noninterference

### I1. One instruction/line/function preserves an observation

- Coarse outcome-aware instruction frames in
  [`Blanc/CommonProofs/Frames.lean`](../Blanc/CommonProofs/Frames.lean):
  `processCreateMessage.chargeCodeGas_instructionFrame` covers code-deposit
  charging on both outcomes, including optional EF rejection and state-gas
  charges. `ForkRules.accessDelegation_instructionFrame` covers the activated
  facade, including disabled delegation. For exact operand-stack and memory
  projections, use `ForkRules.accessDelegation_stack` and
  `ForkRules.accessDelegation_memory` in
  [`Blanc/LadderBase.lean`](../Blanc/LadderBase.lean). Both cover enabled and
  disabled delegation without a modern-fork premise. Their equality conclusions
  have no reliable registered single goal-head trigger. The coarse frame preserves state,
  deletion and created-account sets, transient storage, and storage-write
  annotations; it leaves touched-account metadata unobserved. Exact
  `Pop`/`Burn` and Mach-only frames retain touched-account equality.
  `Rinst.sstore_runCore_stateWriteFrame` and the `of_run_sstore*` inversions
  cover the actual SSTORE regime and access schedule, including flat access;
  the SLOAD/EXTCODESIZE observation and prefix helpers cover both schedules.
  These operation-specific relations occur inside the shared outcome carrier;
  no existing registered single goal-head trigger distinguishes them, so use
  this branch and the exact operation declaration before unfolding its walk.
- For successful calls under `rules.stateGas = none`, use
  `CallEffects.call_run_effects` for seven-operand `CALL` and
  `CallEffects.call6_run_effects` for six-operand `DELEGATECALL` or `STATICCALL`
  in [`Blanc/Lift/CallEffects.lean`](../Blanc/Lift/CallEffects.lean). They give
  the exact one-word stack result and bounded output-window memory write,
  handling flat and EIP-2929 access, enabled or disabled delegation, balance
  and depth failure, and child failure as well as success. The same owner
  provides `CallEffects.genericCall_stack`, `CallEffects.genericCall_memory`,
  and the `CallEffects.Devm.pop_cons`/`popToNat_cons`/`popToAdr_cons` and
  `withStack_pop`/`withStack_popToNat`/`withStack_popToAdr` operand helpers.
  These observations prove no settlement or gas equality; their
  conjunction/equality goals have no reliable registered single goal-head
  trigger.
- For successful checked stack transfer, use `ninstTransfer_run_noStateGas`
  in [`Blanc/Lift/Transfer.lean`](../Blanc/Lift/Transfer.lean). It requires only
  `rules.stateGas = none`, handles both access schedules and delegation
  settings, and derives opcode availability from actual success where needed.
  `run_balance_stack` in the same module gives BALANCE's exact account-read
  stack result under either access schedule. The original `ninstTransfer_run`
  retains its modern statement. These stack observations have no reliable
  registered single goal-head trigger.
- `Ninst.Inv`, `Rinst.Inv`, and `Line.Inv`: use `line_inv` plus the registered
  `Ninst.Hinv` / `Rinst.Hinv` instances in `Blanc/Tactics.lean` and
  [`Blanc/CommonProofs/Hinv.lean`](../Blanc/CommonProofs/Hinv.lean).
- `Func.Inv`: use `func_inv`; it intentionally refuses arbitrary `Func.call`.
- For direct stack-prefix transport through shared line instructions, use the
  `prefix_of_*` family in [`Blanc/CommonProofs/Walk.lean`](../Blanc/CommonProofs/Walk.lean),
  including `prefix_of_mul`, `prefix_of_div`, `prefix_of_timestamp`,
  `prefix_of_xor`, and `prefix_of_argCheckNonAddress` (in
  [`Blanc/CommonProofs/Balance.lean`](../Blanc/CommonProofs/Balance.lean)). These declarations are
  also registered with the
  `stack-prefix-transport` recipe.
  - `Devm.state` is preserved by `mstore`, `mload`, `swap`, and the register
    instructions other than the two store forms — including the arithmetic,
    bitwise, and comparison instructions and `sload`, `timestamp`, `caller`,
    `gas`, and `pop` (`show_hinv_state` builds those from
    `Rinst.preserves_state`); `Devm.memory` likewise now covers the full binary
    arithmetic family. Import [`Blanc/WordArithmetic.lean`](../Blanc/WordArithmetic.lean)
    for the lower-fanout `Rinst.xor`, `Rinst.addmod`, and `Rinst.mulmod` state
    instances and the ternary arithmetic memory instances. The scoped
    `LogOutputHinv` instances cover `callvalue`, `calldatasize`, `timestamp`,
    `mul`, `div`, and `sub` beside the earlier arithmetic, stack, and
    environment instructions. A walk that tracks a single account's balance states its
  invariant as the pointwise projection `fun d => Devm.getBal d a`, for which
  `Rinst`/`Ninst` instances are registered beside the whole-family ones.
- A terminal `Linst.Inv` goal is discharged from its registered `Linst.Hinv`
  instance with `exact Linst.Hinv.inv`; `Blanc/LadderBase.lean` registers
  `Devm.getCode` preservation for both `Linst.stop` and `Linst.revert`.
- A missing contract-neutral instance belongs in a shared module below every
  consumer, not in the first contract that needs it.
- For equality of EVM states modulo `gasLeft` across two successful runs of a
  gas-free instruction or line, use
  [`Blanc/GasErasure.lean`](../Blanc/GasErasure.lean).
  `Devm.EqModGas` relates states agreeing on every `Devm.Rels` column except
  `gasLeft`, with `refl`/`symm`/`trans`, the `of_burn`, `of_pop`, `of_push`,
  `of_popBurn`, and `of_pushBurn` step adapters, update congruences
  (`of_memWrite`, `of_addAccessedStorageKey`, `of_withRefundCounter`,
  `of_setStorVal`, `of_withMemory`, `of_withStack`), and read congruences
  (`extCost_congr`, `getStorVal_congr`, `memRead_congr`, `of_popToNat`).
  `Rinst.gasFree` covers the `regularTransfer` opcode family minus `gas`, plus XOR;
  `Ninst.gasFree` adds `push` and `Line.gasFree` covers lines.
  `Rinst.run_eqModGas` replays two successful per-op runs against each other,
  `Ninst.run_eqModGas` lifts that to instructions, and `Line.run_eqModGas`
  to gas-free lines. The whitelist never contains `pc`, `gas`, or an
  `Xinst`; adding `gas` makes the instruction theorem unprovable, since two
  runs differing only in gas push different words. The identity is modulo
  exactly the columns outside `Devm.Rels` as pinned: a Jaune bump adding
  columns there widens it silently, so revisit `Devm.Rels` and the whitelist
  at any such bump. Existing suggestion facilities were checked and no
  registered trigger matches the two-run congruence goal shape, so discovery
  remains in this registry.
- `Devm.EqModGas.withGasLeft` (a state is gas-erasure equal to itself at any gas) and
  `Devm.EqModGas.output_eq` are in
  [`Blanc/Lift/GasErasureRun.lean`](../Blanc/Lift/GasErasureRun.lean).
- For literal equality after choosing a common execution-gas value, use
  `Devm.EqModGas.withGasLeft_eq` in
  [`Blanc/Lift/CallProfileTransport.lean`](../Blanc/Lift/CallProfileTransport.lean).
  `of_normalized_eq` proves the converse relation from equality at gas zero;
  `.st`, `.addAccessedAddress`, `.callSpawnParent`, and `.callChildPost`
  transport every column except execution gas through caller preparation and
  clean child resumption. The resume theorem needs both parent and child
  agreement, and retains returndata, access sets, refunds, state-gas and read/
  write metadata. These lemmas do not assert equal debit or callee liveness.
- To change only a frame's initial-gas environment coordinate while retaining
  the complete dynamic machine and outcome, use
  [`Blanc/Lift/StaticGasTransport.lean`](../Blanc/Lift/StaticGasTransport.lean).
  `ExactCallProfile.withStaticGas` preserves the literal debit and successor
  functions. `sloadCost_withStaticGas`,
  `sstoreCost_withStaticGas`, `afterSload_withStaticGas` and
  `dataWord_withStaticGas` (all `rfl`) are the storage-charge, post-world and calldata-word
  facts an exact schedule's cost transport unfolds to. These theorems update
  `Sevm.gas`, leaving dynamic `Devm.gasLeft` unchanged.
- To state a frame theorem (given at an arbitrary static machine and entry
  `St pre [] Mem.empty G`) for a message entered with an execution grant, use
  [`Blanc/Lift/StaticGasMessage.lean`](../Blanc/Lift/StaticGasMessage.lean): `Msg.withGas`,
  `initSevm_withGas` (`{initSevm msg with gas := G}`), `initDevm_withGas`
  (`St (initDevm msg) [] Mem.empty G`). Fix the cost at the base
  message, instantiate the frame theorem at a fresh gas variable `F` with the premises transported
  by `*.withStaticGas F`, rewrite the cost back with the schedule's `*_withStaticGas`, and only
  then relate `F` to `R + c` (rewriting `← hF` rather than substituting, so no definitional check
  unfolds the closed cost).
  Existing recipe triggers cannot distinguish this static-coordinate update
  from ordinary run construction, so discovery remains in this registry.
- For the canonical successor of a value-0 identity-precompile copy (a gas-normalized
  data form of the resumed caller, at the copy's explicit stack tail, memory and windows),
  use `identityCallNext` in
  [`Blanc/Lift/IdentityCall.lean`](../Blanc/Lift/IdentityCall.lean), with its literal
  `_memory`/`_stack`/`_returnData`/`_gasLeft` facts and `identityCallNext_withStaticGas`.
  `call_identity_step_canonical` / `rxc_call_identity_canonical` and the `RunExCut` twin
  `rxce_call_identity_canonical` in [`Blanc/Lift/RunEx.lean`](../Blanc/Lift/RunEx.lean) add
  `Devm.EqModGas b' (identityCallNext …)` to the old step's post; the old statements are
  their projections. For Vyper's `raw_call` join and tail, `rawJoinBaseNext` (explicit clamped
  length `n`) and `rawTailBaseNext` (the original base's clamped return-data length) in
  [`Blanc/Lift/VyperRawCall.lean`](../Blanc/Lift/VyperRawCall.lean) name the copy's canonical
  base, with static-gas lemmas; `rxc_vyRawCallJoin_canonical` /
  `rxc_vyRawCallTail_canonical` and their `RunExCut` twins `rxce_vyRawCallJoin_canonical` /
  `rxce_vyRawCallTail_canonical` hand it to the continuation, keeping the literal `vyRawMem`
  memory and the exact charge. These carry no new charge, world premise or gas quantifier.
  No registered trigger distinguishes these from the bounded steps, so discovery remains in
  this registry.

`Linst.selfdestruct_preserves_code_created` and `Linst.selfdestruct_balance_effect`
cover the actual beneficiary credit and refund hooks across historical rules.
The `Linst.selfdestruct_preserves_noDel`, `Linst.run_noDel` and
`Linst.inv_noDel` helpers instead require
`rules.settle.selfdestructOnlyCreated = true`: before that activation, an
existing coded account can schedule itself for deletion. These helpers do not
assert a historical-uniform NoDel invariant.

For a weaker actual step condition,
`Linst.selfdestruct_preserves_noDel_of_onlyCreated_or_foreign` in
`Blanc/CommonProofs/NoDel.lean` accepts the modern creation restriction **or**
`sevm.currentTarget ≠ wa`. SELFDESTRUCT schedules its executing storage target,
not its beneficiary. `Linst.run_noDel_of_safe` handles an actual terminal run
when that target is foreign or the decoded terminal is not SELFDESTRUCT.
Both preserve `Execution.NoDel`, including live error payloads, from the input
`Devm.NoDel`; they do not require a successful outcome or establish safety of
a protected target executing arbitrary code.

### I2. The property concerns a complete execution or child frames

For an account that already has nonempty code, use
[`Blanc/ExecutionExistingAccount.lean`](../Blanc/ExecutionExistingAccount.lean).
`Exec.not_created_of_installedCode` preserves its exclusion from
`createdAccounts` through both raw outcome channels, with no commitment,
terminal-safety, deletion-set or fork-capability premise. `Exec.accountPreserve`
composes the common `Devm.AccountPreserve` relation through the existing
execution-effect traversal. The `true` mode carries code equality and
created-account exclusion; the `false` mode supplies the unchanged code-only
compatibility APIs. Message/CREATE handling uses the actual collision guard.
This does not exclude scheduling deletion: retained deletion safety still
needs the terminal and complete-settlement argument. Use the named theorem;
a bare set-membership goal does not identify this execution-specific route.

- `Evm.step_effect_noStateGas` and `Exec.effect_neutralSchedule` in
  `Blanc/CommonProofs/Messages.lean` compose neutral per-instruction effects
  under `stateGas = none` and the EIP-6780 flag, transporting the schedule to
  children by the exact spawn environment; `Exec.inv_noDel_noStateGas` in
  `Blanc/LadderBase.lean` consumes them.
- `Xinst.inv_noDel_noStateGas` and `Ninst.inv_noDel_noStateGas` in
  `Blanc/LadderBase.lean` preserve NoDel through actual instruction steps under
  `sevm.benvStat.rules.stateGas = none`. Their explicit `Xlot.InvNoDel` premise
  is the selected child's recursive preservation obligation; it must be proved
  for that child, not supplied as an environment or endpoint survival axiom.
  The original `Xinst.inv_noDel_gen` and `Ninst.inv_noDel_gen` remain modern
  compatibility wrappers. The core uses the actual ordinary done/create/call
  shape, retaining unavailable-opcode errors and actual inherited/collision
  guards. These are step facts, not historical `Exec.inv_noDel`, raw-tree
  routing, whole-message safety or contract/history preservation. There is no
  reliable single goal-head recipe distinguishing these premise-specific NoDel
  routes; use this branch and the named step declaration. The existing
  `xinst-step-shape` recipe selects only the decomposition donor.
- Raw-certificate no-deletion over the driver tree:
  [`Blanc/ExecutionDeletionSafety.lean`](../Blanc/ExecutionDeletionSafety.lean).
  `Exec.inv_noDel_of_raw_terminal_safe` concludes `Execution.NoDel` for a
  complete `Exec` run from the input `Devm.NoDel`, `stateGas = none`, and a
  decoded terminal exclusion at every actual reached node in the executing
  storage context (`node.sevm.currentTarget = wa → ¬ Linst.At ... .selfdestruct`
  over `Exec.rawNodes`). The certificate is indexed by the selected run's own
  reached nodes, never by retained or committed nodes; the six-constructor
  induction builds the child `Xlot.InvNoDel` obligation instead of assuming a
  recursive oracle. It needs no fresh-entry, successful-outcome, modern
  `CoveredFork`, actual/world code equality, or new opcode-availability premise.
  The concrete protected-runtime or routing producer of the `safe` certificate
  is a mandatory separate obligation, as are message/inherited-deletion
  closure, historical contract/history invariants, and global candidate
  readiness. No recipe is registered: the reducible NoDel conclusion does not
  uniquely distinguish this route, so use this branch and the named theorem.
- Retained-certificate no-deletion over the same actual driver tree:
  [`Blanc/ExecutionRetainedDeletionSafety.lean`](../Blanc/ExecutionRetainedDeletionSafety.lean).
  `Evm.step_spawn_resume_atd_of_discarded_noStateGas` proves that an actual spawn,
  discarded COMPLETE `frame.settle raw`, and successful same-resume equation
  preserve the parent's deletion set. `Resume.create_atd_of_error` and
  `Resume.call_atd_of_error` expose its ordinary flagged-resume components.
  These laws assume no safety for discarded raw nodes, global code/routing
  condition, or final no-deletion fact. Concrete retained terminal safety,
  incoming no-deletion, message/root settlement and historical consumers remain
  separate obligations. No recipe is registered: the reducible NoDel and
  deletion-set equality goals do not reliably identify this premise-specific
  route; use this branch and its named declarations.
- Producer of that `safe` certificate from an installed checked runtime:
  [`Blanc/ExecutionNoDelProducer.lean`](../Blanc/ExecutionNoDelProducer.lean).
  `Exec.safe_of_installedCert` takes `Cert.check C c`, `c.callOnly`,
  `c.noSelfdestruct`, `¬ isValidDelegation C`, nonempty `C`, the actual
  installed code `pre.getCode wa = C`, `stateGas = none`, and pc-zero entry of
  `C` when the root owns `wa`'s storage; it proves the decoded SELFDESTRUCT
  exclusion at every raw node owning `wa`'s storage, every outcome, no fork
  premise. The cross-frame argument covers reentrant `CALL`/`STATICCALL` into
  `wa`, foreign `DELEGATECALL`/`CALLCODE` (they keep the caller's account) and
  `CREATE`/`CREATE2` (cannot enter an account with code).
  `Exec.inv_noDel_of_installedCert` composes it with
  `Exec.inv_noDel_of_raw_terminal_safe`. Message/inherited-deletion and
  transaction-level closure remain separate.
  The low-level guard lives in
  [`Blanc/ExecutionCreateGuard.lean`](../Blanc/ExecutionCreateGuard.lean):
  `Xinst.step_create_isCreate_noStateGas` identifies actual CREATE-family
  frames, and `Evm.step_spawn_create_unprotected_noStateGas` excludes a
  protected target from the actual collision guard. These lemmas need only
  state-gas absence, not modern fork coverage. No separate recipe: choose
  the named producer from the available certificate restriction.
- Message and selected-transaction closure of that producer:
  [`Blanc/ExecutionNoDelTransaction.lean`](../Blanc/ExecutionNoDelTransaction.lean).
  `RunFrame.invNoDel_of_installedCert` produces the slot `Xlot.InvNoDel`
  obligation, so the fork-neutral `ProcessMessage.inv_noDel` /
  `ProcessCreateMessage.inv_noDel` give `ProcessMessage.inv_noDel_of_installedCert`
  / `ProcessCreateMessage.inv_noDel_of_installedCert` (every outcome, error
  payloads and rollback snapshots) and the executable
  `processMessage_preserves_noDel_of_installedCert` /
  `processCreateMessage_preserves_noDel_of_installedCert`, with no fork
  premise. `ExecutionTrace.MessageCallTrace.noDel_of_installedCert` covers the
  settled wrapper (collision, CREATE at coded `wa` excluded, EIP-7702
  authorization and code resolution). Generic helpers: `Xlot.invGetCode_of_filled`
  (fork-free slot code preservation) and
  `sweepTouchedAccounts_getCode_of_nonempty` (the sweep never erases an
  account with nonempty code). It needs `wa ∉ benv.createdAccounts`.
- Installed-runtime transport uses `InstalledRuntimeSafety C`
  in [`Blanc/ExecutionNoDelProducer.lean`](../Blanc/ExecutionNoDelProducer.lean).
  Its `of_cert` constructor derives all-outcome raw
  safety from checked certificates. The
  `safeRawFrames_of_runtimeSafety` bridges in `ExecutionNoDelSafeHistory`
  carry this producer through messages, transactions, stages and histories.
  The matching `noDel_of_runtimeSafety` / `code_of_runtimeSafety` wrappers in
  `ExecutionNoDelHistory` derive code preservation without a supplied
  `SafeRawFrames` oracle. `InstalledCert.runtimeSafety` preserves the old
  call-only APIs. `ExecutionInstalledCertCuts` exposes
  `ConfiguredBlockTraceIn.code_after_txSplit_of_runtimeSafety`,
  `code_before_txSplit_of_runtimeSafety`, and their `MidHistoryTraceIn`
  compositions on the original transaction cuts. The installed source code
  and history are explicit inputs; these lemmas authenticate neither.
- History closure of that producer:
  [`Blanc/ExecutionNoDelHistory.lean`](../Blanc/ExecutionNoDelHistory.lean).
  `InstalledCert C` bundles the actual runtime facts (certificate check,
  `callOnly`, `noSelfdestruct`, no designator, nonempty). Stage lemmas
  `SystemMessageTrace`/`RequestsTrace.noDel_of_installedCert` (system calls,
  including a system target equal to `wa`), `Beacon`/`History`/`RequestStageTrace.code_of_installedCert`,
  `ApplyTransactionsTrace.noDel_of_installedCert`, `StagedBodyTrace.noDel_of_installedCert` and
  `ConfiguredHistoryTraceIn.noDel_of_installedCert` carry `getCode wa = C` from
  the checkpoint to the history's endpoint state (by induction, every
  checkpoint of its spine) and prove the recursive `…NoDelScheduled wa` (no
  selected transaction schedules `wa` for deletion). No `CoveredFork`;
  per-block `stateGas = none` from `BodyStageCapabilities F`; no premise that
  `wa` is never targeted; block-level `createdAccounts` is empty at
  `initBenv`. Also `payRewards_getCode`.
  Every `…_of_installedCert` above is a wrapper over the safe-parametric chain
  below, via its trace's `safeRawFrames_of_installedCert` bridge.
- Installed-certificate code survival across actual transaction cuts:
  [`Blanc/ExecutionInstalledCertCuts.lean`](../Blanc/ExecutionInstalledCertCuts.lean).
  `ConfiguredBlockTraceIn.code_after_txSplit_of_installedCert` starts at the
  selected transaction's `cut.afterBenv`, carries its code through the actual
  remaining transactions, withdrawals, requests and rewards, and ends at the
  block endpoint. `MidHistoryTraceIn.code_of_installedCert` extends that
  remainder through the existing whole-block spine.
  `ConfiguredBlockTraceIn.code_before_txSplit_of_installedCert` carries code
  from a target block's prestate through its actual beacon/history stages and
  `cut.before` to `cut.benv`. Only `InstalledCert`, the selected
  domain's `BodyStageCapabilities`, and source-cut installed code are needed;
  safety/deletion exclusions are derived, and no balance/reward budget or
  source-block-prestate installation is required. The starting installed code
  remains a producer output; transport alone authenticates no historical
  constructor or anchor. As with the installed-cert history route, the
  reducible code-equality goal does not reliably distinguish this route's
  specific premises, so use these named APIs rather than a goal-head recipe.
- Safe-parametric no-deletion and code survival across configured In-histories:
  [`Blanc/ExecutionNoDelSafeHistory.lean`](../Blanc/ExecutionNoDelSafeHistory.lean).
  `ExecutionTrace.SafeRawFrames wa trace.rawFrames` says every node of every
  listed frame's own execution (`Exec.rawNodes` of each `Exec.Deriv` in the
  trace's own `rawFrames` enumeration) excludes decoded SELFDESTRUCT in the
  executing storage context `wa`. The `…_of_safe` chain
  (`RunFrame.invNoDel_of_safe`, `ProcessMessage` /
  `ProcessCreateMessage.inv_noDel_of_safe`, the retained-trace
  `ProcessMessageTrace` / `ProcessCreateMessageTrace.inv_noDel_of_safe`,
  `MessageCallTrace.noDel_of_safe`, `TransactionTrace.noDel_of_safe`, system /
  request stages, `StagedBodyTrace.noDel_of_safe`,
  `ConfiguredBlockTraceIn.noDel_of_safe`,
  `ConfiguredHistoryTraceIn.noDel_of_safe`) concludes what the installed-cert
  version concludes (`…NoDelScheduled wa`, `getCode wa = C`) from that premise
  plus the code facts the proofs actually use (`C.toList ≠ []`,
  `¬ isValidDelegation C`); raw levels take an explicit retained run with its
  slot equation instead. `Exec.safeNodes_of_installedCert` turns the
  installed-cert producer into per-frame safety (`Exec.rawNodes` of a listed
  frame sit inside the whole run's `Exec.rawNodes`). No recipe is registered:
  use this branch and the named theorem.
- Complete-settlement-root no-deletion transport for actual message/transaction traces:
  [`Blanc/ExecutionRetainedNoDelTransaction.lean`](../Blanc/ExecutionRetainedNoDelTransaction.lean).
  `ProcessMessageTrace.noDel_of_settledRoots` and
  `ProcessCreateMessageTrace.noDel_of_settledRoots` consume conditional NoDel
  preservation at only their own complete-settlement roots, for an actual clean
  settled core. The existing CALL/CREATE engines construct each callback's actual
  incoming NoDel; `Execution.noDel_of_committedPost` supplies the indexed outcome
  projection. `MessageCallTrace.noDel_of_settledRoots` requires no core law when
  complete settlement is flagged: its real output deletion set is empty, including
  CREATE deposit failure. `TransactionTrace.noDel_of_settledRoots` retains genuine
  prepared-message/inherited/created exclusions and selected final-state code;
  `ApplyTransactionsTrace.noDel_of_settledRoots` composes the same list's actual
  output exclusions (`NoDelScheduled`) and code survival. The shared
  `processMessageCall_createRun_noDel_of_clean` /
  `processMessageCall_callRun_noDel_of_clean` projections and unchanged
  `messageCallDelegation_installed` / `prepareMessage_own` entry donors live in
  `Blanc/ExecutionNoDelSafeHistory.lean`; old raw-safe APIs keep their signatures.
  No raw/discarded-child safety, global-apart or final-output survival premise is
  supplied. Message input NoDel, inherited deletion exclusion, installed code,
  transaction created-account exclusion and actual root preservation remain explicit.
  System-stage/history/exact-cut composition remains separate. No reliable single
  goal-head distinguishes these premise-specific routes; use this branch by name.
- Enabled stages and configured-history no-deletion from those same settled-root laws:
  [`Blanc/ExecutionRetainedNoDelHistory.lean`](../Blanc/ExecutionRetainedNoDelHistory.lean).
  `SystemMessageTrace.noDel_of_settledRoots` and `RequestsTrace.noDel_of_settledRoots`
  preserve the actual system/request outputs; `BeaconStageTrace`, `HistoryStageTrace`
  and `RequestStageTrace.code_of_settledRoots` keep real enabled invocations and skipped
  branches. `StagedBodyTrace`, `ConfiguredBlockTraceIn` and
  `ConfiguredHistoryTraceIn.noDel_of_settledRoots` compose actual transaction output
  exclusions and installed code. `ConfiguredHistoryTraceIn.outputNotDeleted_of_settledRoots`
  returns the cell-history output predicate on that same history. Withdrawals, requests,
  rewards and finalization reuse the registered cell-property/code transports.
  Installed code, actual fork capabilities, and conditional root NoDel preservation
  remain explicit; no raw-safe or discarded-child obligation is manufactured.
- Uniqueness of actual retained message/transaction traces and transaction-spine
  reassembly: [`Blanc/ExecutionTraceDeterminism.lean`](../Blanc/ExecutionTraceDeterminism.lean).
  `RetainedXlot.eq_of_same` / `index_eq_of_runFrame`,
  `ProcessMessageTrace.eq_of_same`, `ProcessCreateMessageTrace.eq_of_same`,
  `MessageCallTrace.eq_of_same` / `index_eq_and_heq_of_same_input`,
  `TransactionTrace.eq_of_same` / `index_eq_and_heq_of_same_input` and
  `ApplyTransactionsTrace.eq_of_same` / `index_eq_of_same_input` use deterministic
  input/wrapper equations and `Exec.unique`. `ApplyTransactionsTrace.toRun` exposes
  the exact fold equation; `ApplyTransactionsTrace.append` reassembles actual spines.
  Use these named APIs when identifying an arbitrary supplied cut; equality of
  flattened committed frames alone is not outer-root equality. No reliable selective
  goal-head identifies these input-specific equality routes.
- For actual transaction output deletion exclusions after a genuine cut, use
  [`Blanc/ExecutionMidHistoryInNoDel.lean`](../Blanc/ExecutionMidHistoryInNoDel.lean).
  For conditional preservation at the same original complete-settlement roots,
  use `ConfiguredBlockTraceIn.outputNotDeleted_after_txSplit_of_settledRoots` and
  `MidHistoryTraceIn.outputNotDeleted_of_full_settledRoots`. These preserve the
  supplied arbitrary `TxSplit` and actual suffix/later history, with no deletion
  premise at the cut. `ApplyTransactionsTrace.TxSplit.settledRoots_eq` derives
  that cut's exact outer-root split by deterministic before/head/after reassembly;
  `ApplyTransactionsTrace.append_settledRoots`, `settledRoots_cast` and
  `ConfiguredHistoryTraceIn.append_settledRoots` keep the index/list transports
  explicit. No canonical-cut substitution or flattened-frame root inference occurs.
  These list membership/equality goals have no selective recipe head.
  `ApplyTransactionsTrace.noDelScheduled_iff_outputNotDeleted` and its
  `ConfiguredHistoryTraceIn` counterpart identify the safety and complete-settlement
  predicates on the same outputs. `ConfiguredBlockTraceIn.outputNotDeleted_after_txSplit_of_safe`
  transports installed code through the actual opening system calls, before-trace
  and selected transaction to prove the arbitrary `TxSplit` suffix exclusion.
  `ConfiguredBlockTraceIn.code_and_outputNotDeleted_after_txSplit_of_safe` also
  returns the proxy-independent installed code at the exact after-cut state;
  `MidHistoryTraceIn.code_and_outputNotDeleted_of_full_safe` pairs that code
  with the actual suffix/later deletion exclusion. The original deletion-only
  APIs are projections with unchanged premises. These routes depend jointly on
  the supplied full chronology, cut and safety carrier, so discovery remains
  through this named registry branch rather than a general code-equality recipe.
  `MidHistoryTraceIn.outputNotDeleted_append` splits the actual suffix and later
  blocks; `outputNotDeleted_of_full_safe` derives their exclusions from the
  original full history's safety and checkpoint code. No cut-local deletion or
  installed-code oracle, canonical-cut replacement, cell law or initial zero is
  supplied. Use this chronology branch directly; the expanded output predicate
  alone does not choose an intended cut, so no goal recipe is registered.
- `ExecuteCode.inv_noDel`, `ProcessMessage.inv_noDel`,
  `ProcessCreateMessage.inv_noDel` and the whole-message no-deletion helpers
  in `Blanc/LadderBase.lean` require `wa ∉ msg.inheritedDeletions` at the
  arbitrary-message boundary. CALL and CREATE derive the child exclusion
  from the parent's `Devm.NoDel.atd` in both snapshot branches.
- Message-entry projections: `processMessage_entry_facts` carries the code,
  target, calldata, time, storage and `Mem.Wf` facts, with `pre.stack = []` and
  `pre.memory = Mem.empty` kept separate as `processMessage_entry_stack` and
  `processMessage_entry_memory` so a walk that reads scratch words can take the
  image rather than only well-formedness. The storage projection requires
  zero message value or `State.Protected` at the selected owner;
  `processMessage_entry_frame_facts` gives every other conjunct with no
  storage premise.
- Generic execution noninterference:
  [`Blanc/ExecutionNoninterference.lean`](../Blanc/ExecutionNoninterference.lean).
  For `Exec.NoRetainedWriteTo`, first split on `Execution.commits out = true`:
  `Exec.noRetainedWriteTo_of_not_commits` closes the rollback arm;
  `Exec.noRetainedWriteTo_of_no_execOccurrence`,
  `Exec.noRetainedWriteTo_of_sourceSites_no_exec`, and
  `Exec.noRetainedWriteTo_of_frame_owners_ne` are the committing routes.
  To conclude cell preservation with `Exec.committedCell_eq_of_noRetainedWriteTo`,
  also supply nonempty entry code at the observed owner. Its
  `Exec.committedCell_eq_of_noRetainedWriteTo_noStateGas` generalization needs
  only the actual selected rules' state-gas absence; the covered theorem is
  its compatibility wrapper.
  For the storage at one account under any rule record, Amsterdam included, with no statement about a
  frame that did not commit, use the kept-frames layer.
  [`Blanc/ExecutionKeptFrames.lean`](../Blanc/ExecutionKeptFrames.lean): `Exec.keptAt`, `Exec.keptAt_chain`, the one
  fold; `Exec.retained_induction`, the recursor on committing runs; `Xinst.step_spawn_form`, every spawn shape at once.
  [`Blanc/ExecutionKeptFacts.lean`](../Blanc/ExecutionKeptFacts.lean): `Exec.keptAt_entry`, `Exec.keptAccount`,
  `Exec.descendantFrames_caller_excluded_neutral`.
  [`Blanc/ExecutionKeptTop.lean`](../Blanc/ExecutionKeptTop.lean): `MessageRoots`, both lanes of `processMessageCall`.
  [`Blanc/ExecutionKeptChain.lean`](../Blanc/ExecutionKeptChain.lean): `TransactionRoots`, `BodyRoots`, `KeptHistory`.
  For empty entry stack and memory on the actual kept carrier, use
  [`Blanc/ExecutionKeptFresh.lean`](../Blanc/ExecutionKeptFresh.lean):
  `Root.keptAt_fresh` transports a supplied fresh root to every kept frame;
  `BodyRoots.roots_fresh` derives freshness of actual body roots, and
  `KeptHistory.fresh` derives it for every frame kept at a selected address,
  without a code, fork or budget premise. Entry output has its separate API below.
  For installed runtime transport on the original kept transaction carrier, use
  [`Blanc/ExecutionKeptRuntime.lean`](../Blanc/ExecutionKeptRuntime.lean):
  `MessageRoots.runtime_entry` retains pc zero, target, installed nonempty nondelegating code,
  actual message stat and `Exec.FreshEntry`, from the actual routed message.
  `TransactionRoots.runtime_of_runtimeSafety` and `TransactionsRoots.runtime_of_runtimeSafety`
  use `InstalledRuntimeSafety`, installed code, `rules.stateGas = none` and
  `rules.settle.touchedSweep = false`; they preserve the installed code through settlement
  and give pc zero, target, code, fork and actual fresh-entry facts for every kept target frame.
  The target may already belong to the created-account set; no calldata-size bound is required.
  At an arbitrary message boundary, `MessageRoots.not_deleted_of_runtimeSafety` additionally
  requires the target absent from `msg.inheritedDeletions`; the transaction producer derives
  this opening exclusion from the actual preparation. It does not erase inherited deletions.
  For cleared entry output in a covered-fork kept history, use
  [`Blanc/ExecutionKeptEntered.lean`](../Blanc/ExecutionKeptEntered.lean):
  `KeptHistory.keptAt_output` gives `f.pre.output = []` for every frame actually kept at the selected address.
  Its top-level `MessageRoots`, transaction, request and body lemmas require `rules.stateGas = none`;
  the history theorem discharges that from its covered-fork premise. Its history scope excludes Amsterdam.
  The per-block SYSTEM_ADDRESS premises a request-contract history theorem takes (no sender, no authority, no
  creation there) are one structure, [`Blanc/ExecutionKeptClean.lean`](../Blanc/ExecutionKeptClean.lean):
  `HistoryClean`, stated by the EIP-8282 builder and EIP-7251 public history headlines.
  For the balance at one account across a committed run of a frame elsewhere, kept frames only, under any rule
  record: [`Blanc/ExecutionKeptValue.lean`](../Blanc/ExecutionKeptValue.lean): `Exec.kept_bal_ge_keptPaid` (at least
  the balance plus every kept frame's value, `Exec.keptPaid`), `Exec.kept_bal_neverFalls`; the spawn balance facts
  `Xinst.step_spawn_bal_neutral`, `Evm.step_spawn_enter_bal`, `Evm.step_spawn_settled_getBal`,
  `Evm.step_spawn_rolled_getBal`. Up the levels of a kept history: `MessageRoots.bal_covers`,
  `TransactionRoots.bal_covers`, `BodyRoots.bal_covers`, `KeptHistory.bal_covers` (premises `HistoryRootsFit`,
  `HistoryCreditsFit`).
  `ConfiguredBlockTraceIn` has no Amsterdam inhabitant, since its request stage fixes two contracts: use `KeptHistory`.
  To carry a covered-fork `ConfiguredHistoryTrace` onto `KeptHistory`, and splice it with later (Amsterdam) kept
  steps: [`Blanc/ExecutionKeptConfigured.lean`](../Blanc/ExecutionKeptConfigured.lean): `ConfiguredHistoryTrace.kept`
  (same parents, blocks, forks and outputs), `ConfiguredHistoryTrace.keptHistory`, `ConfiguredHistoryTrace.splice`,
  `KeptHistory.append`; the kept carrier is determined by its start and blocks (`KeptStep.unique`,
  `KeptHistory.unique`, `ConfiguredHistoryTrace.kept_unique`), so frames read off it do not depend on the derivation.
  For the pre-execution system calls of a kept step (EIP-4788 beacon roots and EIP-2935 history storage, header
  parent/number/timestamp/block-hash links, and prefix/suffix/tip/step splits of `KeptHistory`), use
  [`Blanc/ExecutionKeptPreCalls.lean`](../Blanc/ExecutionKeptPreCalls.lean) (`KeptStep.beaconRoots_frames`,
  `KeptStep.beaconRoots_stor`, `KeptStep.historyStorage_frames`, `KeptStep.historyStorage_stor`,
  `KeptStep.lastBlockHash`, `KeptStep.parentBeaconRoot`, `KeptHistory.split_at`, `KeptHistory.tip_snoc`,
  `KeptHistory.step_adj`, `KeptHistory.number_add`, `KeptHistory.timestamp_lt`); `KeptHistory.mainnet_covered` in
  [`Blanc/ExecutionKeptClean.lean`](../Blanc/ExecutionKeptClean.lean) supplies `CoveredFork` along a `mainnetConfig`
  kept history from Prague activation.
- Reentrancy-lock exclusion over the all-outcome frame tree:
  [`Blanc/LockExclusion.lean`](../Blanc/LockExclusion.lean).
  `LockSpec.locked_core` keeps the lock cell fixed, slot-addressed owner
  `SSTORE`s absent and `NoRetainedWriteTo` true below any locked node.  It
  takes nonempty entry world code at the observed owner, the per-code
  `LockSpec.Dominance` and per-world `OwnerDiscipline`/`HashAvoidIn` hypotheses.
  The latter definitions constrain interpreted code and hashes; they do not
  imply world-code protection. Reusable step facts there:
  `Evm.step_cont_getStor_get` preserves one cell across an actual continuing
  step unless an owner `SSTORE` hits its key; it needs no owner protection.
  `Evm.step_doneOk_getStor_eq`, `Evm.step_spawn_enter_getStor` (entered child
  storage), and `Ninst.none_getStor_eq_of_ne_sstore` require `State.Protected`
  at the observed owner because their execution relations include message
  settlement. The actual-step helpers in `ExecutionMessageEffects` distinguish
  immediate opcode completion from completed childless message settlement.
  `Exec.Deriv.ParentPrefix.codePreserve` transports code along a same-frame
  prefix, and `Exec.rawFrameRoots_codePreserve` does so to every raw frame root,
  for owners with nonempty entry code. Also available:
  `Exec.rawFrameDescendants_entry` (pc 0 and covered fork for every raw
  descendant root) and `Exec.Deriv.ParentPrefix.antisymm`.
- Storage-owner discipline from world premises:
  [`Blanc/OwnerDiscipline.lean`](../Blanc/OwnerDiscipline.lean).
  `ForwarderShape K I` is the decidable forwarder shape (`forwarderCode`
  template; `forwarderShape_6326` by `decide`), `noSstore_of_scan`
  proves `NoSstore` by a finite scan.  Reusable spawn facts there:
  `Xinst.step_delegatecall_spawn_code` (child code = code at the popped
  address), `Xinst.step_create_spawn_fresh` (`CREATE*` only enters a codeless
  account) and `Jinst.runCore_ok_pc`; the direct-call facts
  `Xinst.step_call_spawn_code`, `Xinst.step_staticcall_spawn_code` and
  `Xinst.step_directCall_spawn_code` (`CALL`/`STATICCALL`, including a call
  back into the current account) live in
  [`Blanc/ExecutionDirectCode.lean`](../Blanc/ExecutionDirectCode.lean).
- Storage-owner discipline for a code family closed under delegation, any number of levels
  deep: [`Blanc/OwnerClosure.lean`](../Blanc/OwnerClosure.lean). `Exec.DelegationClosed S` says every committed frame
  owning `P`'s storage that runs a code of `S` decodes no `CALLCODE` and `DELEGATECALL`s only
  undelegated accounts holding a code of `S`; `Exec.ownerCode_of_closed` then says every committed
  frame owning `P`'s storage runs a code of `S`, given that `P` holds one, the root runs one when it
  owns `P`, and the codes of `S` are nonempty and no EIP-7702 designators. The induction is over
  committed frames (`Exec.descendantFrames`), so a reverted subtree is never entered;
  `Xinst.step_delegatecall_spawn_stack` is the stack a spawning `DELEGATECALL` leaves.
  [`Blanc/OwnerClosureControl.lean`](../Blanc/OwnerClosureControl.lean) shows the closure is not vacuous on a two-code toy family
  (`toy_ownerCode`: an EIP-1167 forwarder and a one-byte `STOP` leaf). Worked use:
  `Blanc/ExecutionOwnerFamily.lean` (the multi-code owner ladder, T2c).
- Persistent-storage silence of static execution:
  [`Blanc/StaticStorage.lean`](../Blanc/StaticStorage.lean).  `Devm.storageView`
  is the extensional `Stor.get` observation the contract invariants use.  The
  module supplies its `PopBurn.Inv`, `Burn.Inv`, and lifts the existing generic
  `Linst.Hinv` / `Ninst.Hinv` facts to that observation; it deliberately does
  not manufacture a universal `STATICCALL` `Hinv`.
  `Exec.rawNodes_isStatic_of_static` and
  `Exec.retainedStorageWrites_eq_nil_of_static` propagate the static flag and
  exclude successful `SSTORE`. Storage can also change through normalized
  balance transfer, so `Exec.storageView_committedPost_eq_of_static`
  requires a protected entry current
  target or empty interpreter code. Actual `STATICCALL` routing supplies this
  condition internally; both instruction-level APIs keep their statements.
  For an arbitrary static root, use
  `Exec.getStor_committedPost_eq_of_static_protected` at a protected owner and
  `Exec.protected_committedPost_of_static` to transport that protection.
  `Msg.protected_of_benvAfterTransfer` transports protection through entry;
  `Msg.getStor_eq_of_safeTransfer` gives global storage equality for disabled
  transfer, zero value, or self-transfer at a protected account. These facts
  say nothing about transient storage, logs, balances or gas.
  For an actual historical or modern run whose selected rules satisfy
  `sevm.benvStat.rules.stateGas = none`, use
  `Exec.getStor_committedPost_eq_of_static_noStateGas`,
  `Exec.storageView_committedPost_eq_of_static_noStateGas`,
  `Exec.getStor_committedPost_eq_of_static_protected_noStateGas`, and
  `Exec.protected_committedPost_of_static_noStateGas` with the same static,
  committed and protected-target-or-empty-code premises as their modern
  wrappers. `Ninst.staticcall_getStor_eq_noStateGas` and
  `Ninst.staticcall_inv_getStor_noStateGas` derive readiness from actual
  STATICCALL routing, including flat/EIP-2929 access and disabled/enabled
  delegation. These equality conclusions do not identify a unique proof
  route by goal head; select the theorem with its actual-run premises here.
- Representation-exact storage silence of static execution:
  [`Blanc/StaticCallStorage.lean`](../Blanc/StaticCallStorage.lean).  Use it
  when the boundary is the `Stor` tree itself (a replay carrier that meets at
  *equal* storages) rather than the extensional `Devm.storageView`.
  The shared raw-storage proof now lives in `Blanc.StaticStorage`.
  `Ninst.staticcall_inv_getStor_exact` exposes the same equality for one
  successful `STATICCALL` on a fork named by `CoveredFork` (Prague, Osaka,
  BPO1 and BPO2; Amsterdam is excluded), with no new caller premise.
  Its capability-level counterpart is
  `Ninst.staticcall_inv_getStor_exact_noStateGas`: it needs only the selected
  rules' state-gas absence and the actual successful STATICCALL. It inherits
  the same raw-storage equality without supplying opcode availability,
  child commitment, gas equality or any other modern fork capability.
  For a recursive source walk at one covered `Sevm`, use
  `Func.SilentAt`, `Func.SilentIn.toSilentAt`, and
  `Func.observe_eq_of_run_silentAt`: ordinary instruction leaves still use
  their generic invariants, while the `STATICCALL` leaf consumes the covered
  theorem directly. Import
  `Blanc.StaticCallStorage` (it imports only `Blanc.StaticStorage`).  Like its
  parent it says nothing about transient storage, logs, balances or gas.
- Transient-state invariance and settlement:
  [`Blanc/TransientInvariance.lean`](../Blanc/TransientInvariance.lean) and
  [`Blanc/TransientSettlement.lean`](../Blanc/TransientSettlement.lean).
- If the invariant is specifically over entered raw frame roots, return to E3.

### I3. A foreign or childless frame must preserve a contract precondition

Use the generic frame lemmas in [`Blanc/LadderBase.lean`](../Blanc/LadderBase.lean)
(the `ContractSpec.*` forms in [`Blanc/Ladder.lean`](../Blanc/Ladder.lean)):

- `ProcessMessage.none_ok_state_eq_entry_of_clean` identifies a clean,
  childless settlement with its transferred entry state.
- The `targetBalanceMono_of_none` family on `ProcessMessage`,
  `ProcessCreateMessage`, `GenericCall`, `GenericCreate`, `Xinst`, and `Ninst`
  proves pointwise balance monotonicity at foreign execution boundaries;
  `Linst.targetBalanceMono_of_foreign` lifts it through a line.
- `Ninst.foreignNone_getStor_eq` is the matching persistent-storage fact.
- `Xinst.step_spawn_caller_eq_parent_or_target_eq_parent` and
  `Xinst.step_spawn_caller_ne_of_target_eq` classify the caller of a spawned
  child.
- `ContractSpec.Post.of_state_eq`, `ContractSpec.Pre.child_of_outbound_transfer`,
  and `ContractSpec.Ninst.none_preserves_precond` transport the generic
  contract conditions through state equality, outbound transfer, and a
  successful nonrecursive instruction.

**A token frame's foreign world.**

- [`Blanc/Lift/ForeignKeep.lean`](../Blanc/Lift/ForeignKeep.lean): the tactics `rstepN`, `rbranchE`, `rdispE` walk a dispatcher into a decided exec-free set.
- [`Blanc/Lift/ReachKinds.lean`](../Blanc/Lift/ReachKinds.lean): `ExecsSet`, `Reach.execs_of_set`: which external instructions a closed region of a certificate decodes.

## S — state and machine updates

### S1. I need a projection through one update

Use Jaune's update-first laws named `Devm.<update>_<projection>` before
unfolding a concrete state tower. Examples include:

- `Jaune.DevmProjections` (in the pinned Jaune package) holds the J1
  pairs `Devm.<update>_<projection>` and
  `addAccessed{Address,StorageKey}_<projection>` (`addLog`, `setStorVal`,
  `setTransVal`, `withRefundCounter`, `memWrite`, `memExtends`, `setCode`,
  `withGasLeft`, `withStack`, `withReturnData`, `withOutput`, `incrNonce`,
  `setBal`, `setMach`); search it before restating a projection.
- `Devm.setMach_stack`, `Devm.setMach_memory`,
  `Devm.setMach_accessedStorageKeys`, and the other `setMach` projections.
- `Devm.withOutput_state`, `Devm.withOutput_logs`,
  `Devm.withOutput_transientStorage`, and sibling projections.
- `Devm.memWrite_gasLeft`, `Devm.memWrite_memory` and `Devm.memWrite_stack`,
  all in Jaune.

- `Devm.creditBeneficiary_getCode` and `Devm.creditBeneficiary_delSets` in
  `Blanc/CommonProofs/Frames.lean` preserve code and the deletion sets under either
  presence-preserving historical credits or ordinary credits.
  `Devm.creditBeneficiary_getBal` compares their balance maps with `addBal`;
  it does not equate account presence or storage-write annotations.
  `Devm.creditBeneficiary_getStor_of_protected` preserves a protected owner's
  storage, and `State.Protected.creditBeneficiary` preserves that protection.
  `creditSelfdestructRefund_getCode` and `creditSelfdestructRefund_delSets`
  isolate the refund hook's unchanged observations;
  `creditSelfdestructRefund_state` preserves its persistent state.
  `sweepTouchedAccounts_bal` preserves every balance because it erases only
  empty accounts; it does not assert equality of raw account presence.
- For persistent storage setters, use Jaune's
  `State.setStorVal_get_self` / `State.setStorVal_get_ne`, which handle the
  existing-account `setPresent` branch, Blanc's `setStorVal_getStor_self`
  projection, and Jaune's `Devm.setStorVal_getStorVal_self`. A `State`-level write leaves every
  account's code alone by `State.getCode_setStorVal` in
  [`Blanc/SystemCallForward.lean`](../Blanc/SystemCallForward.lean) (the `Devm` form is Jaune's
  `Devm.setStorVal_getCode`).

For equality of whole dynamic machines, `Devm.eq_of_proj` in
[`Blanc/Compiled.lean`](../Blanc/Compiled.lean) requires all nineteen exact
projections, including `a.meta.touchedAccounts = b.meta.touchedAccounts`.
Supply that equality from the actual frame's `touchedAccounts` field or from
an update that preserves the metadata. Equality of persistent state alone
does not determine the touched set.

If several updates form a familiar semantic post-state, continue to S2.

### S2. I need a reusable composite projection cut

`Devm.subBal_state` in
[`Blanc/MachineDataFacts.lean`](../Blanc/MachineDataFacts.lean) projects a
successful machine debit to the corresponding successful account-state debit.
For an `Option.toExcept` success, first use Jaune's `Option.toExcept_eq_ok`.
Neither result proves sufficient funds or equality of the whole machine;
use them to avoid unfolding machine records through repeated option cases.

For the entire storage map at one address across account-state equality, use
`getStor_eq_of_state_eq` in `Blanc/LadderBase.lean`.

Use [`Blanc/CommonProofs/Base.lean`](../Blanc/CommonProofs/Base.lean):

- `Stor.get_set_ite` exposes a single storage-map update as the equality
  branch at an arbitrary observed key.
- `Devm.addAccessedStorageKey_setMach_setMach` cancels an obsolete machine
  component across an access-key update followed by the final `setMach`.
- `of_run_sload_logs` exposes the log silence of a successful `SLOAD`,
  including its cold access-list
  warming path.  Use it instead of widening the global `Ninst.Hinv`
  instance set: access metadata changes even though this projection does not.
- Jaune's `Devm.setStorVal_getStorVal_self` is persistent storage read-after-write.
- Jaune's `Devm.setStorVal_getCode` carries account code across a persistent
  storage write, and Jaune's `Devm.setCode_getStor` storage across code
  installation. Jaune's `Devm.withRefundCounter_getStor`,
  `Devm.withRefundCounter_getCode`, `Devm.withRefundCounter_getBal`, and
  `Devm.withRefundCounter_createdAccounts` cut through the refund-counter
  update of an SSTORE post; `Devm.setStorVal_createdAccounts` carries the
  created-account set across the storage write itself. Rewrite with these
  before unfolding a concrete write tower instead of a `change` or a local
  `rfl` restatement. Jaune's `Devm.setCode_logs`,
  `Devm.setCode_output`, `Devm.setCode_error`,
  `Devm.setCode_refundCounter`, and `Devm.setCode_accountsToDelete` carry the
  persistent storage and frame observations that code installation does not
  modify.
- `Devm.returnPost_world`, `Devm.returnPost_getStorVal`,
  `Devm.returnPost_transientStorage`, and
  `Devm.returnPost_accessedStorageKeys` project through the common
  `setMach`/`memRead`/`withOutput` return post.
- `Devm.sstoreBase_state`, `Devm.sstoreBase_error`,
  `Devm.sstoreBase_transientStorage`, `Devm.sstoreBase_logs`, and
  `Devm.sstoreBase_accessedStorageKeys` project the common
  warm/refund/storage-write post; `Devm.sstoreWarmBase_accessedStorageKeys`
  is the corresponding already-warm key-set projection.
- `State.set_bal`, `State.setStor_bal`, `State.incrNonce_bal`, and
  `State.setCode_bal` (Jaune's `Jaune/ExecSettlement.lean`, imported by
  [`Blanc/ExecutionSettlement.lean`](../Blanc/ExecutionSettlement.lean))
  preserve the complete world-balance map across balance-neutral account
  updates. `genericCreate_prepared_bal`, `genericCreate_prepared_getStor`, and
  `processCreateMessage_msg_bal_eq` package the corresponding CREATE
  preparation cuts. `genericCreate_prepared_getStor` requires the creator
  nonce increment to be nonzero. For an actual recursive spawn, use
  `genericCreate_step_spawn_nonce_ne_max` from `Blanc/LadderBase.lean` and
  `UInt64.add_one_ne_zero_of_ne_max` to discharge it.
  `genericCreate_step_spawn_prepared_target_unprotected` exposes the actual
  collision check after that creator increment: the new target has zero nonce
  and empty code in the prepared state. Constructor setup therefore starts its
  nonce at one. The original `genericCreate_step_spawn_target_unprotected`
  derives the corresponding pre-increment fact from the same extraction.
- `State.setBal_current_of_protected`, `State.addBal_zero_of_protected`, and
  `State.subBal_zero_of_protected` (in `Blanc/CommonProofs/NoDel.lean`) are exact
  world equalities: a zero credit, zero debit, or current-balance rewrite at a
  `State.Protected` owner returns the identical raw world. Their tree step is
  `treeMap_insert_same` (over `treeMapImpl_insert_same`), an exact structural
  identity for inserting a key at its current value, not map extensionality.
  Without protection the zero write can normalize an empty account to absent
  and erase its storage, so the premise is necessary.
- `State.Protected.of_compile` (an account carrying `Prog.compile p` is
  protected) sits beside `State.Protected.of_image` and `.of_code_ne_nil` in
  `Blanc/CommonProofs/NoDel.lean`. `selfPayment_entry_clears_storage` is the
  mechanism that makes protection necessary across message entry: a
  full-balance self-payment empties a codeless, nonce-zero account, and the entry
  deletes it with its storage.
- `Acct.clearIfEmpty_of_not_empty`, `Acct.clearIfEmpty_withBal_of_code`,
  `Acct.clearIfEmpty_withBal_of_nonce` (with `Acct.withBal_nonce`/`_code`) in
  `Blanc/CommonProofs/NoDel.lean` remove the normalization of a nonempty account or
  of a balance write at a coded or nonce-carrying account. Rewrite with the
  `withBal` forms rather than closing the branch by `exact`: at a concrete
  literal credit the unifier otherwise unfolds word arithmetic.
- `Acct.clearIfEmpty_of_code_toList_ne_nil` (in `Blanc/CommonProofs/NoDel.lean`) is
  the account-level form: `setAccount` normalization is the identity on an
  account whose code is a nonempty byte list, so a code installation followed
  by `State.setAccount_get_self` returns the written account exactly. Jaune's
  `Acct.clearIfEmpty_bal`, `_nonce`, `_code`, and `_stor` project single fields
  without any premise.

### S3. I need state-relation or write-frame composition

Use `Devm.StateWriteFrame` and its reflexive/transitive/composition lemmas in
`Blanc/CommonProofs/Frames.lean`, then inspect higher-level relation combinators in
[`Blanc/LadderBase.lean`](../Blanc/LadderBase.lean).

If the fact is about which holder's balance moved rather than how states
compose, continue to S5.

### S5. I need the address-shaped storage rows a token ledger sums over

`Stor.rest` in [`Blanc/CommonCore.lean`](../Blanc/CommonCore.lean) is the
holder-keyed view of persistent storage — exactly the domain `balSum` sums
over — and it is the right vocabulary for "who moved, and by how much".  Its
laws live in [`Blanc/LadderBase.lean`](../Blanc/LadderBase.lean):

- `Stor.rest_set_self` and `Stor.rest_set_ne` are read-after-write on one row:
  a holder-keyed write is visible at its own row and nowhere else.  Reach for
  these when a proof books an exact per-row movement of its own.
- `Stor.increase_set` and `Stor.decrease_set` package the same write as the
  `Increase` / `Decrease` relations the `Σ` lemmas consume; `Stor.AgreeOffAdr`
  is the complementary half, saying nothing outside the address-shaped keys
  moved.
- `le_sum` bounds one row by the sum, and `add_le_sum_of_ne` bounds two
  distinct rows together — the two facts needed to turn "the actor's own row
  covers the move" into "the rest of the ledger is untouched and still fits".
- `sum_add_assoc` and `sum_sub_assoc` move `Σ` across an `Increase`/`Decrease`.
  `sum_eq_add_of_row_add` and `sum_eq_sub_of_row_sub` are their `Nat`-level
  readings, for a caller holding an exact per-row `Nat` equation plus "no other
  row moved" instead of a `B256`-valued relation; neither asks for an overflow
  side condition, because the post row is itself a word.
- A write at a fixed non-address slot is invisible here; each contract states
  that separately because the slot is the contract's own.
- When the credit itself is unchecked and may wrap, use
  [`Blanc/BalanceAlgebra.lean`](../Blanc/BalanceAlgebra.lean) rather than
  assuming `B256.Nof`: `B256.toNat_add_le` bounds a wrapped sum by the
  mathematical one, `sumBelow_increase_le` and `sum_increase_le` bound the
  growth of an address-prefix sum by the value credited including the wrapping
  case, and `transfer_does_not_increase_sum` is the paired-movement form.
  These are upper bounds; they do not establish that no wrap occurred.
- For a *pure* token model whose ledger is a function `Adr → B256` rather
  than storage, use [`Blanc/LedgerUpdate.lean`](../Blanc/LedgerUpdate.lean).
  `ledgerDebit`/`ledgerCredit` are the one-row `Function.update` movements.
- For an exact observation of a finite coalition, import
  [`Blanc/LedgerConservation.lean`](../Blanc/LedgerConservation.lean) and use
  `ledgerSumOn`. `ledgerSumOn_congr` transports pointwise agreement;
  `ledgerSumOn_increase` needs the credited row's `B256.Nof`,
  `ledgerSumOn_decrease` needs debit cover, and `ledgerSumOn_transfer` needs
  pre-state `SumNof`. The transfer law already covers a self transfer and all
  coalition-membership overlaps. These are local equations only: they neither
  supply those guard facts nor establish an execution path or history. The
  `finite-coalition-ledger` recipe reaches this branch from a target containing
  `ledgerSumOn`.
- For a pure ledger read over a *finite key footprint* (a history observes only
  the rows it touches), import
  [`Blanc/Lift/LedgerFootprint.lean`](../Blanc/Lift/LedgerFootprint.lean).
  `footprintSum keys balances` sums the rows a key list names and
  `FootprintCovers keys balances` says the list names every nonzero row;
  `footprintSum_eq_sum` equates a duplicate-free covering footprint's sum with
  the full address `sum` (via `sum_eq_ledgerSumOn` for any covering
  coalition), so a conservation law proved over `sum` (packaged as
  `SumBacked balances supply`) is read over any covering footprint.
  `FootprintCovers.extend` extends a footprint by the keys a step touches, and
  `footprintSum_dup_ne_sum` is the statement control: a repeated nonzero key
  breaks the equation.
- The hashed slot term itself, `mapSlot key base` (solc's mapping slot; Vyper's
  with the arguments swapped), is in
  [`Blanc/Lift/MapSlot.lean`](../Blanc/Lift/MapSlot.lean); write locality at
  one owner's rows of a lifted contract's two-level mapping is under
  [C9.5](#c95-i-need-hashed-storage-slots-write-locality-or-demanded-zero-cells).

### S6. I need a basic EVM-word identity

For EVM exponentiation, use Jaune's `B256.bexp_zero` and `B256.bexp_eq`
from its pinned `Jaune.Basic` API. The latter exposes `x.toNat ^ y.toNat`
modulo `2^256`; the zero-exponent theorem covers every word, including zero.
Rewrite small word-to-Nat conversions explicitly before closed arithmetic.
Do not unfold `Nat.powMod` or rely on its implementation helpers: Lean4.35
also has a root `Nat.powMod`, while Jaune's wrapper preserves its own
`m ≤ 1` convention. The shared `Lift.bexp_256_32` in
[`Blanc/Lift/PackedSha.lean`](../Blanc/Lift/PackedSha.lean) covers the packed
word-copy special case. The leaf advice tactic recognizes direct `bexp`
equalities without normalizing a concrete state or memory expression.



For the integer Newton loops of a three-coin StableSwap pool (Curve Vyper
0.2.4 `get_D`, `get_y`, `get_y_D`), use
[`Blanc/Lift/StableSwapNewton/Defs.lean`](../Blanc/Lift/StableSwapNewton/Defs.lean),
namespace `Blanc.StableSwapNewton`. `dP`, `bodyD`, `loopD`, `getD`, `bodyY`,
`loopY`, `cOf`, `bOf`, `getY` and `getYD` are the unbounded `Nat` arithmetic
in the source's order of operations, with fuel and stopping tolerance as
parameters; the `Chk` variants return `Option Nat` and revert (`none`) exactly
where the source's checked `uint256` arithmetic does (`chkAdd`, `chkSub`,
`chkMul`, `chkDiv`). `aboveRoot`, `floorRoot` and `rootQ` name the exact roots
the loops approximate, for statements only.
[`Blanc/Lift/StableSwapNewton/Root.lean`](../Blanc/Lift/StableSwapNewton/Root.lean)
pins `floorRoot` by one point (`floorRoot_eq`).
[`Blanc/Lift/StableSwapNewton/D.lean`](../Blanc/Lift/StableSwapNewton/D.lean)
bridges the checked `get_D` to the plain one (`getDChk_some`) and proves
`getD_lower`: for positive balances and `A ≥ 1`, `getD` is
never below `⌊D*⌋`, at every tolerance, stopped or capped; it also holds the cap,
non-monotonicity and ceil-mutation witnesses.
[`Blanc/Lift/StableSwapNewton/Y.lean`](../Blanc/Lift/StableSwapNewton/Y.lean)
bridges `get_y` / `get_y_D` (`getYChk_some`, `getYDChk_some`) and proves the
tolerance-1 `y` loop returns exactly `rootQ` (`loopY_eq_rootQ`,
`loopY_eq_rootQ_of_le` with its `k + 1`-body bound, `loopY_eq_rootQ_of_lt` for a
start below the root, `getY_eq_rootQ`, `getYD_eq_rootQ`) under the
non-degeneracy `rootGap`. Without it the loop returns `rootOrSucc`: the floor
root, or one above it only when `rootGap` fails (`loopY_rootOrSucc_of_le`,
`loopY_rootOrSucc_of_lt`, `loopY_rootOrSucc`). For every non-reverting checked
call, with no start premise, use `getYChk_rootOrSucc` and
`getYDChk_rootOrSucc`; `getY_start_below_root` and `getYD_start_below_root`
show reachable calls start below the root.

Use the primitive word facts in
[`Blanc/MachineDataFacts.lean`](../Blanc/MachineDataFacts.lean) before
destructing a `B256`: `B256.mul_comm` covers word multiplication, including
wrapping products. This owner imports `Jaune.WordFacts`, whose
`B256.not_lt_of_ltCheck_eq_zero` turns a zero unsigned comparison flag into
the negated strict comparison (it does not assert that arithmetic producing
either operand was overflow-free). Import this owner directly; CommonProofs
and Ladder do not reexport it.
For every other comparison flag (`eqCheck`, `ltCheck`, `gtCheck`, in either
direction, including flags discharged from `toNat` bounds at a solc range
check), import Jaune's `Jaune.WordFacts` and use its `B256.eq_of_eqCheck_ne_zero`,
`B256.lt_of_ltCheck_ne_zero`, `B256.lt_of_gtCheck_ne_zero`,
`B256.ltCheck_eq_zero_of_toNat_le`, `B256.gtCheck_eq_zero_of_toNat_le` and the
`B256.{eq,lt,gt}Check_{ne,eq}_zero_iff` family; do not restate them.
For a logical shift right that never grows its shifted operand, use
`B256.shr_toNat_le` in
[`Blanc/Lift/FreePtrFacts.lean`](../Blanc/Lift/FreePtrFacts.lean).

Use the fixed-width arithmetic declarations in
[`Blanc/WordArithmetic.lean`](../Blanc/WordArithmetic.lean) and the basic word
identities in [`Blanc/CommonProofs/Walk.lean`](../Blanc/CommonProofs/Walk.lean) before
destructing a `B256` (`B256.or_comm` is in
[`Blanc/AddressSlotProofs.lean`](../Blanc/AddressSlotProofs.lean)). `wordModulusN`, `maxWordN`, `wordModulusN_pos`,
`maxWordN_lt_wordModulusN`, and `maxWord_toNat` name the standard `2^256`
bounds. `div_two_div_pow`, `div_pow_div_two`,
`one_and_toB256_eq_mod_two`, and `toB256_shiftRight_one` bridge recurring
natural-number calculations to exact word operations. `Nat.xor_or_shiftLeft`,
`B128.toNat_xor`, and `B256.toNat_xor` expose `xor`, while
`Nat.or_or_shiftLeft`, `B128.toNat_or`, and `B256.toNat_or` expose `or`
through the nested word representation. In `CommonProofs/Walk`,
`B256.and_comm` and `B256.xor_comm` provide the shared commutativity facts for
bitwise conjunction and exclusive-or, while `B256.and_idem_right` removes a
repeated identical mask.

For a low-bit field of an EVM word, use
[`Blanc/Lift/PackedWord.lean`](../Blanc/Lift/PackedWord.lean).
`Lift.PackedWord.lowMask_toNat` identifies the low `k` bits with the natural
residue modulo `2^k` for `k ≤ 256`; `lowMask_eq_self_of_lt` removes that mask
from a bounded word. `lowMask_sub_toNat` identifies masked word subtraction
with subtraction modulo the field width when the right operand is below
`2^k`, including full-word borrowing. These facts preserve wraparound and
require no timestamp ordering. Discovery remains
in this registry: the field width and caller's desired word/natural form
must be chosen before applying these lemmas.

For exact two-word multiplication, `productLowWord`, `productScratchWord`,
`productHighBeforeBorrowWord`, `productBorrowWord`, and `productHighWord` name
the standard `MUL`/`MULMOD` staging and carry correction, while
`productLowWord_toNat`, `productHighWord_toNat`, and
`productHighWord_mul_add_productLowWord_toNat` recover the exact unbounded
product without a single-word magnitude premise;
`wideNumeratorN_productWords` packages the same fact through the shared
high/low numerator representation. `productHighWord_eq_toB256_div_wordModulus`,
`productLowWord_eq_zero_iff`, and
`roundedProductHighWord_eq_toB256_ceilDiv` provide the floor and ceiling
bridges for division by exactly `2^256`.

For the first stage of exact two-word division,
`wordModulusFactorWord` represents `2^256 mod denominator` and
`wideRemainderWord` computes the remainder of `high * 2^256 + low` using
`ADDMOD`/`MULMOD`; their corresponding `_toNat` theorems expose the exact
natural-number values under only a nonzero-denominator premise.
`wideNumeratorN`, `wideBorrowWord`, `wideSubLowWord`, and `wideSubHighWord`
name the generic two-word subtraction stage;
`wideSubWords_reconstruct` and
`wideNumerator_sub_remainder_mod_eq_zero` recover its exact unbounded value
and divisibility.

For the factor-and-fold stage of full-width division, `Nat.lowestSetBit` and
`Nat.lowestSetBit_spec` isolate the largest power of two dividing any nonzero
bounded natural. `lowestSetBitWord`, `removeLowestSetBitWord`, and
`wordModulusDivFactorWord` are the corresponding word operations; their
`_toNat`, `_spec`, `_ne_zero`, and `_odd` theorems expose the positivity,
divisibility, and odd-denominator facts needed downstream.
`Nat.sub_mod_eq_div_mul`, `Nat.sub_mod_div_factor`, and
`Nat.two_word_div_lt_modulus` provide the generic remainder-removal,
factor-removal, and fitting quotient-width bounds;
`Nat.pow_le_two_word_div_of_le_high` is the overflow-side companion when the
denominator is no larger than the high word. `toB256_maxWordN` identifies the
re-embedded largest natural word with `B256.max`.
`wordAdd_eq_toB256_add` identifies
wrapped word addition with natural addition re-embedded modulo `2^256`, while
`wordSub_eq_toB256_sub_of_le` identifies non-underflowing word subtraction
with the re-embedded natural difference. `wordAdd_lt_left_iff` is the
companion overflow test: a compiled unsigned addition guarded by comparing its
stored sum with one summand wraps exactly when the natural sum leaves the word
domain. `wordDiv_eq_toB256_div` identifies
ordinary EVM word division with re-embedded natural division, including the
zero-divisor convention, while `wordMod_eq_zero_iff` identifies its exact-
division test. `toB256_add_one` records the unconditional modular
successor bridge; `toB256_add_one_of_lt` retains the bounded compatibility
name used by older callers. `roundedQuotientWord_eq_toB256_ceilDiv` turns any
staged floor quotient/remainder pair with the correct zero test into the
re-embedded natural ceiling quotient. Under a positive dividend,
`ceilPredQuotientWord_eq_toB256` similarly turns the capacity finisher into
`ceilDiv - 1`, while `ceilDiv_sub_one_le_div` records its generic floor bound.
`ceilDiv_lt_wordModulusN_of_floor_lt` upgrades a fitting floor quotient to a
fitting ceiling quotient from the exact guard that forbids rounding the
largest word upward.
`minWord_eq_toB256_min` turns a word-level smaller-candidate branch into exact
natural-number `min` when the natural candidate fits in one word.
The generic
`Nat.fold_divided_words` identity and `foldDividedWords_toNat` justify folding
a divided high/low pair back into one word. `wideReducedLowWord`,
`wideReducedHighWord`, `wideReducedNumeratorN`, and
`wideFoldedDividendWord` compose that machinery with remainder subtraction;
`wideReducedWords_reconstruct`, `denominator_dvd_wideReducedNumerator`,
`lowestSetBitWord_dvd_wideReducedLow`, and
`wideFoldedDividendWord_toNat` provide the exact reconstruction and
divisibility interface. `wideRemainderWord_eq_zero_iff` exposes the analogous
exact-division test for a two-word numerator.

For modular inverses, `inverseSeedWord`, `inverseNewtonStepWord`, and
`inverseNewtonIter` name the standard seed and word-ring refinement.
`newtonStep_modEq_square` is its unbounded algebraic core;
`b256_mul_modEq_wordModulus`, `b256_sub_modEq_wordModulus`, and
`inverseNewtonStepWord_modEq_wordModulus` bridge wrapped word operations to
`Int.ModEq`; `inverseNewtonStepWord_modEq_square` lifts one known inverse; and
`inverseNewtonIter_six_modEq` turns any proved four-bit seed into an inverse
modulo the full word modulus. For an odd denominator,
`inverseSeedWord_modEq_sixteen` proves the standard seed correct and
`inverseNewtonIter_six_seed_modEq_wordModulus` closes the complete refinement.
Finally, `wideQuotientWord` composes reduction, folding, and refinement, while
`wideQuotientWord_toNat` proves its exact floor-division result from the
standard `high < denominator` branch guard, with no extra magnitude premise;
`wideQuotientWord_eq_toB256` gives the corresponding word equality directly.
These declarations are COMMON_API-only: an `Int.ModEq` goal is not reliably
Newton-specific enough for an automatic proof recipe.

For the halving and low-bit steps a compiled loop performs, use
[`Blanc/WordArithmetic.lean`](../Blanc/WordArithmetic.lean): `div_two_div_pow`
and `div_pow_div_two` collapse iterated `Nat` halving into one power,
`one_and_toB256_eq_mod_two` identifies the low-bit mask with `% 2`,
`toB256_add_one_of_lt` is the non-wrapping increment, and
`toUInt64_shiftRight_one`, `toB128_shiftRight_one` and `toB256_shiftRight_one`
are the fixed-width halving bridges at the three widths.  Each carries its own
`< 2 ^ 64` or `< 2 ^ 256` bound as a hypothesis; none of them establishes that
bound for a caller.

For three-operand word instructions, `applyTernary_def` and
`Devm.diffBurn_of_applyTernary` expose the generic execution shape,
`prefix_of_diffBurn_three` transports a known stack prefix, and
`prefix_of_addmod` / `prefix_of_mulmod` are the direct compiled-instruction
bridges. The latter two are registered with the `stack-prefix-transport`
recipe.



### S7. I need a token-ledger conservation invariant

A token contract that keeps balances at address-shaped keys and a total
supply at one reserved non-address key satisfies one invariant: the word at
the supply slot is exactly the sum of the balances.  That invariant is
`LedgerConserved` in
[`Blanc/LedgerConservation.lean`](../Blanc/LedgerConservation.lean), and
everything it needs rests on the single bit fact `¬ ValidAdr slot`:
`toB256_ne_of_not_validAdr` is the fact in the form the storage lemmas want,
`rest_set_slot` says a supply write cannot move the sum, `get_slot_set` says
a balance write cannot move the supply, and `rest_set_of_not_validAdr` says a
write at any other non-address key is invisible to the balances.
`transfer_of_debit_credit` is the two-`set` transfer step, and
`LedgerConserved.transfer`/`mint`/`burn` (with the `mint_set`/`burn_set`
`Stor.set` forms) carry the invariant across a booked movement.
`LedgerConserved.sumNof` says the sum never overflows (it *is* a word),
`le_supply` bounds every balance by the supply, and `of_empty`, `of_eq`,
`of_get_eq`, and `of_rest_eq` seed and transport the invariant.  Nothing here
names a contract.

A ledger keyed by *hashed* slots (a Solidity or Vyper mapping) cannot claim "every key's slot holds
its value": two keys may share a slot, and a history touches a tiny fraction of the key space.  State
the ledger over a set `K` of **tracked keys** instead, with
[`Blanc/SlotFootprint.lean`](../Blanc/SlotFootprint.lean): `Support` (every nonzero word is at a fixed
slot or a tracked key's slot), `Inj`/`Apart` (tracked slots pairwise distinct and off the fixed slots),
`Fresh`/`FreshKeys`/`extendBy` (a frame's or trace's touched keys are tracked or on slots in no use, and
extend the footprint).
The key type, its slot function and the fixed slots are parameters.
For an explicit query list and write list, `checkFaithfulOn slot observed written`
checks that a written key shares its raw slot only with itself among the requested
observations; `checkFaithfulOn_eq_true` gives its exact finite soundness statement.
`checkApartOn slot observed foreign` and `checkApartOn_eq_true` check raw foreign
slots against those same explicit observations. These require neither a
`Support` premise nor zero values for keys outside the observation list.
To read a footprint ledger off raw storage words, use [`Blanc/SlotFootprintWord.lean`](../Blanc/SlotFootprintWord.lean):
`trackedWord slot K s k` is the word at a tracked key's slot and `0` at an untracked key.

To establish such a footprint at a concrete checkpoint world, decide it with
[`Blanc/Lift/FiniteCheckpoint.lean`](../Blanc/Lift/FiniteCheckpoint.lean): for a finite row list
`rows : List (κ × B256)` (each key with its precomputed slot word; the tracked set is `rowKeys rows`),
`checkRows slot fixed rows s` checks that every word is its key's slot, the words ascend strictly
(`ascending`, so distinct), no word is a fixed slot, and every nonzero entry of the storage tree is a
fixed slot or a listed word (`covered`, a merge walk). `checkSumNof w` decides `SumNof w.bal` by summing the
world's actual accounts (`sum_bal_eq_worldBalSum`, `checkSumNof_sound`).

For what a token's **address** answers along a configured history, with no storage layout, use the
token interface core in [`Blanc/Lift/Token/Core.lean`](../Blanc/Lift/Token/Core.lean): a pure `Book`
(ledger, step per entered frame, decoded `Op`, balances, allowances, well-formedness), the `BookLaws`
a composition consumes, and `Core T B`, which ties a book to the settled frames of a history
(`IsEntry`, `replayAt`, `replayEnd`, the `balanceOf`/`transfer` answers), with the facet
`TransferLive`. [`Blanc/Lift/Token/Holder.lean`](../Blanc/Lift/Token/Holder.lean) gives
`Book.run_append`, `entryAsks_append`, the holder argument `BookLaws.run_holder` and the positional
segment `Core.segment`. Further facets are separate structures in their own files:
`Erc20Abi` ([`Blanc/Lift/Token/Abi.lean`](../Blanc/Lift/Token/Abi.lean)) and `SelfCaller`
([`Blanc/Lift/Token/SelfCaller.lean`](../Blanc/Lift/Token/SelfCaller.lean)).
For a token with a privileged minter, the minter/supply facet `SupplyFacet B`
([`Blanc/Lift/Token/Supply.lean`](../Blanc/Lift/Token/Supply.lean)) reads a book's supply and minter
and classifies mint and burn messages (zero amounts included); `SupplyFacet.run_supply` says that
along an accepted run whose minter-sent messages keep the minter (`KeepsMinter`), the minter persists
and the final supply plus `burned` equals the initial supply plus `minted`.

When the token's positional replay law holds only at settled positions outside its own writers (a
proxy token observed at the entry of a frame inside a `DELEGATECALL` chain), use the
writer-shadowed core `CoreW` in [`Blanc/Lift/Token/CoreW.lean`](../Blanc/Lift/Token/CoreW.lean): `Core` with the replay law
required only at positions that are not `Shadowed` (a judgment on the position, the settled frames
before it and its frame, not on a frame value) plus the two shadow laws the generic walk needs;
`WholeBlocks` places a direct child at the end of a run of whole committed blocks; `Core.weak` and
`SelfCaller.weak` keep every `Core` a `CoreW` (`SelfCallerW`); `CoreW.good_along` and
`CoreW.run_holder_segment` are the `Along.lean` facts over it. The walk consumes the
holder-indexed laws of [`Blanc/Lift/Token/HolderLaws.lean`](../Blanc/Lift/Token/HolderLaws.lean) (`AskLaws B h a`, the per-message
laws of one holder, `AskLaws.run_holder`, the trace-local `HolderLaws T B`, and
`BookLaws.holderLaws` from the universal laws) rather than `BookLaws` directly, so a token whose
book admits a third authorizer fits: [`Blanc/Lift/Token/Signed.lean`](../Blanc/Lift/Token/Signed.lean) gives `BookS` (a book
with a signer), `BookLawsS` (a holder's balance or allowance may also move on the holder's own
signature), the trace-local facet `NeverSigner T S` (the holder never signs a booked entry) and the
bridge `BookLawsS.holderLaws`; `Book.unsigned`, `BookLaws.unsigned` and `neverSigner_unsigned` read
a plain book as a signature book with no signer. [`Blanc/Lift/Token/SignedControl.lean`](../Blanc/Lift/Token/SignedControl.lean) is the
kernel counterexample showing that `NeverSigner` is needed (`control_signer_breaks_holder`). The
transfer-liveness facet conditioned on a gas budget rather than on the consumed cost plus the
stipend (a proxy forwards only 63/64 of its gas) is `TransferLiveBudget` in
[`Blanc/Lift/Token/TransferLiveBudget.lean`](../Blanc/Lift/Token/TransferLiveBudget.lean), with `TransferLive.toBudget`.


### S9. I need the integer exponential recurrence or a finite loop witness

The canonical natural-number definitions already live in the pinned Jaune
package's `Jaune/Machine.lean`: `Jaune.fakeExpAux` uses a well-founded
lexicographic measure `(numerator + 1 - i, accumulator)`, and `Jaune.fakeExp`
starts at index 1 with accumulator `factor * denominator`, then divides the
sum by the denominator. Consume `Jaune.fakeExpAux_zero`,
`Jaune.fakeExpAux_succ`, `Jaune.FakeExpSpec`, `Jaune.fakeExpAux_spec` and
`Jaune.fakeExpAux_spec_unique`; do not duplicate the recurrence or give it a
guessed fuel bound.

[`Blanc/FakeExponential.lean`](../Blanc/FakeExponential.lean) adds
`Blanc.FakeExponential.Run`, a finite recurrence trace carrying the iteration
count and series output. `Run.output_eq` identifies every trace's output with
the canonical series.
`accumulator_le` and `factor_le` provide lower bounds; the latter requires a
positive denominator. `accumulator_zero_numerator` and `value_zero_numerator`
give the exact zero-numerator boundary, with positivity required for the
final division. The withdrawal-request model consumes these for positive
fees and the zero-excess fee, and its later fee-loop/gas refinement can consume
the finite trace. These statements establish no finite-word no-overflow,
bytecode refinement, gas cost or history property. This is a theorem-directed
numeric interface; it has no execution-goal recipe.

[`Blanc/FakeExponentialEval.lean`](../Blanc/FakeExponentialEval.lean) provides
`Blanc.FakeExponentialEval.runFuel` and `fakeExpFuel`, an explicit Option-valued
Nat evaluator. `run_iff_runFuel` relates a finite Nat trace to sufficient fuel,
and `fakeExpFuel_eq_fakeExp` identifies a completed evaluation with Jaune's
total `fakeExp`.

For a symbolic lower bound from a finite growing prefix, use
[`Blanc/FakeExponentialGrowth.lean`](../Blanc/FakeExponentialGrowth.lean).
`Blanc.FakeExponential.accumulator_mul_pow_le` bounds the canonical series
below by `accumulator * q^n` when a positive denominator and counter satisfy
`denominator * (counter + n) * q ≤ numerator`.
`factor_mul_pow_le` consumes that bound at canonical initialization and final
division, giving `factor * q^n ≤ fakeExp factor numerator denominator`.
These are necessary-bound tools for downstream arithmetic domains; they do
not establish finite-word equality or reachable-state admission. The interface
uses named arithmetic theorems and has no execution-goal recipe.

For the unsigned B256 recurrence, use
[`Blanc/WordFakeExponential.lean`](../Blanc/WordFakeExponential.lean).
`Blanc.WordFakeExponential.Run` carries the initial output prefix, active-body
count and final word sum. `run_exists` supplies a finite run bounded by
`measure`; `Run.deterministic` identifies both its count and output, and
`run_exists_unique` packages the unique pair. Termination uses the counter's
countdown to zero and unsigned division by zero, for arbitrary word numerator
and denominator. These theorems establish no equality with the Nat recurrence,
bytecode refinement, gas bound or history property. This interface has no
execution-goal recipe.

[`Blanc/WordFakeExponentialEval.lean`](../Blanc/WordFakeExponentialEval.lean)
spells out the word recurrence as a Nat evaluator: `nextNat` and `addNat`
apply `% 2^256` at each word operation. `runFuel_of_run` transports an
existing word trace through Jaune's `B256.toNat` bridges, while
`run_of_runFuel` reifies a completed Nat evaluation as a word trace; closed
computations using this evaluator never evaluate B256 limb arithmetic in the
kernel.

For a shorter word-run bound under a sufficiently large eventual divisor, use
[`Blanc/WordFakeExponentialBound.lean`](../Blanc/WordFakeExponentialBound.lean).
`WordFakeExponential.Run.iterations_le_of_halving_horizon` allows an arbitrary
warm-up of `H` steps and bounds the remaining active steps by the word width,
256. It takes positive Nat counter/denominator, an exact-divisor margin through
`counter + H + 256`, and `2 * numerator.toNat ≤ denominator * (counter + H)`.
The numerator products and output sums may wrap; the proof uses modular
reduction decreasing the quotient, then repeated halving. This is an arithmetic
run-length bound, with no execution or gas premise.

For a sufficient domain relating these two recurrences, use
[`Blanc/FakeExponentialWordCorrespondence.lean`](../Blanc/FakeExponentialWordCorrespondence.lean).
`NoWrap` is indexed by an existing `FakeExponential.Run` and its initial sum
prefix. It bounds each active prefixed sum, accumulator product and divisor
product, plus the stopped prefix. `NoWrap.final_sum_lt` gives the final sum
width; `NoWrap.to_word_run` constructs the word run with the same count;
`NoWrap.word_result` identifies any word run's count and canonical prefixed
Nat sum. `NoWrap.fakeExp_eq` gives the canonical value after final division
under an explicit denominator width. Cast counter increment needs no extra
width premise. These APIs establish neither a maximal equality domain nor
reachability, bytecode, gas or history properties. Their namespace is
`Blanc.FakeExponentialWordCorrespondence`; they have no execution-goal recipe.

For the converse on a bounded executed word trace, use
[`Blanc/FakeExponentialWordDomain.lean`](../Blanc/FakeExponentialWordDomain.lean).
`FakeExponentialWordDomain.Run.quotient_eq_iff_noWrap` takes positive Nat
counter `c` and denominator `d`, zero initial output, and
`d * d * (c + iterations) ≤ 2 ^ 256`. Equality of the final quotient with the
canonical Nat recurrence is then equivalent to an existing Nat run of the
same length with `NoWrap` at prefix zero. The margin makes active divisors
exact and each overflowing product lose enough to affect final division;
extra Nat terms after early word termination are included. This is an exact
arithmetic domain within that window, with no reachable-history claim.
`FakeExponentialWordDomain.Run.quotient_le` takes the same bounded window and
proves that the word quotient is at most the Nat quotient, without any
no-wrap premise. It supports sufficient-payment liveness without requiring
fee equality; it does not turn a successful word-fee guard into Nat payment.

For the request contracts' quote at factor 1 and fraction 17, use
[`Blanc/RequestFeeWord.lean`](../Blanc/RequestFeeWord.lean), which states those
windows' results over the excess word alone, with no queue model.
`RequestFeeWord.word_fee_le` bounds an executed word quotient by
`fakeExp 1 excess.toNat 17` everywhere; `word_fee_eq_iff` is equality exactly on
`NoWrapDomain`; `NoWrapDomain.word_result` identifies count and quotient;
`natFeeExcessCeiling`, `NoWrapDomain.excess_lt`, `excess_lt_of_paid` and
`word_fee_lt_of_large_excess` separate the two fees above the growth ceiling.

## M — bytes and memory

For concrete RLP encoding and parsing, use
[`Blanc/RlpConcrete.lean`](../Blanc/RlpConcrete.lean).
`RlpConcrete.nat_bytes_roundtrip` recovers the entire natural from Jaune's
variable-width encoding.
To decode a concrete encoding, prove the encoding first and invert it:
[`Blanc/RlpRoundTrip.lean`](../Blanc/RlpRoundTrip.lean) provides
`RlpConcrete.toBLT?_toBytes` (`Bytes.toBLT? b.toBytes = some b` for every `BLT`
encoded in fewer than `2 ^ 64` bytes), with fuel-explicit `decode_encode` and
`parse_encode` for items inside a larger buffer. Payload bytes stay abstract, so a
signed creation transaction decodes from its canonical-encoding theorem
(`tx.toBLT.toBytes = raw`) in three lines; no field-by-field parse chain is needed. When every
byte is concrete and small (a few thousand bytes), `rw [Bytes.toBLT?_eq_toBLTS];
decide +kernel` from `Jaune/RlpEval.lean` is shorter still.
`RlpConcrete.splitAt_append` retains an arbitrary payload and suffix;
`encode_bytes_many` selects the ordinary length-prefixed byte encoder;
`decode_bytes_short`, `decode_bytes_long`, `decode_list_short`, and `decode_list_long`
apply Jaune's actual parser equations while keeping payload bytes abstract.
On the encoder side, [`Blanc/RlpListEncode.lean`](../Blanc/RlpListEncode.lean)
provides `RlpConcrete.encode_list_at` (and `encode_list_at_last`, core
`encode_list_mid`): a list of closed items with one long abstract byte item
`data` at index `i` encodes as `hdr ++ data ++ tl`, where the closed header and
tail are `decide +kernel` side conditions over `longHeaderS` and Jaune's
structural `BLTs.toBytesJoinS`; the abstract item is never reduced. State the
expected bytes as `prefix ++ code.toList ++ suffix` and a creation envelope or
signing payload is one term, e.g.
`encode_list_at 5 rfl code_toList_length (by decide) (by decide +kernel) (by decide +kernel)`. For several abstract items use
`encode_bytes_long` / `encode_list_long` (long header over an abstract payload or
a known joint body) with `toBytesJoin_append`, and close each closed
`longHeaderS` by `decide +kernel` instead of a `norm_num` header computation.
`encode_bytes_nil` and `toBytesPack_of_pos` (`Blanc/RlpBytesInjective.lean`) are
the shared one-line encoder facts.
For unbounded encoder and receipt-index separation, use
[`Blanc/RlpReceiptKeys.lean`](../Blanc/RlpReceiptKeys.lean):
`RlpConcrete.encode_bytes_injective`, `receipt_key_injective` and `receipt_key_ne`
cover arbitrary byte payloads and every natural index, including zero and indices
at or above 128. These are encoder/key facts, not a decoder-validity or receipt-lookup premise.
`decode_byte` and `decode_empty_bytes` cover the one-byte headers; `parse_cons`
composes the actual first-item and remaining-list equations.
`decode_hash` proves the fixed-width header-word roundtrip, including leading
zero bytes. `header21_roundtrip` keeps the requests commitment and requires
explicit present base fee, withdrawals root, both blob-gas fields and parent
beacon root, plus the scalar decoder equations. Absent access-list hash and
slot number delimit the 21-field shape; partial optional tails are not covered.
The list lemma requires the actual recursive child parse. These
equations do not assert whole-envelope canonicality or strict transaction acceptance.
Select by the known header and payload length; the common equality head also
covers unrelated encode/decode goals, so this remains a manual registry route.

### M1. The goal is a `sliceD` normalization

- Bounded natural-number parser reads in
  [`Blanc/BytesSliceNat.lean`](../Blanc/BytesSliceNat.lean): `Bytes.sliceToNat_of_le` identifies
  `data.sliceToNat start width` with `Bytes.toNat (data.sliceD start width 0)` when
  `start + width ≤ data.length`.
- Read a fixed-size ABI `bytes4` head word with `argBytes4` in
  [`Blanc/CommonCore.lean`](../Blanc/CommonCore.lean).  It right-aligns the
  ABI's left-aligned four significant bytes before an integer comparison;
  use ordinary `arg` for integer/address head words.
- Full source from offset zero: `Bytes.sliceD_zero_length` in
  `Blanc/CommonProofs/MemImage.lean`.
- Normalize arbitrary, including 0–3-byte, calldata with
  `Sevm.selector_eq_toB256_takeD_four`: it identifies the selector with the
  first four bytes padded on the right with zeros.  Its limb bridge is
  `shiftRight_224_eq_toB256_take_four`.
- Reassemble adjacent padded windows with `List.sliceD_split`.  For the common
  two-word event window, `Mem.read_two_word_writes` directly proves that stores
  at offsets 0 and 32 read back as the exact 64-byte concatenation;
  `Bytes.read_two_word_writes_at` and `Mem.read_two_word_writes_at` provide the
  same fact at an arbitrary starting offset.
- Compose exact fixed-layout byte images with the shared laws in
  [`Blanc/BytesWrite.lean`](../Blanc/BytesWrite.lean): `Bytes.length_writeAt`,
  `List.sliceD_add`, `Bytes.sliceD_stagedPair`,
  `Bytes.sliceD_append_middle`, `Bytes.getD_sliceD_of_lt`,
  `Bytes.sliceD_sliceD_of_le`, `Bytes.sliceD_of_sliceD_eq`,
  `Bytes.sliceD_of_sliceD_zero_eq`, and
  `Bytes.writeAt_append_middle_at`.
- Compose more than one write with the ordered staging API in
  [`Blanc/MemoryLayout.lean`](../Blanc/MemoryLayout.lean). `MemoryStage` keeps
  exact `(offset, payload)` entries in execution order, `applyImage` folds
  actual `Bytes.writeAt`, and `footprint` records the corresponding byte
  spans. Use the decidable `avoids` or `avoidsAll` guard with
  `applyImage_sliceD_of_avoids` or `applyImage_slices_of_avoidsAll` for
  preserved padded windows. `read_written` requires only the later suffix to
  miss the selected write, so an earlier overlap and an intentional later
  replacement retain ordinary last-write-wins behavior.
  Checked authoring examples demonstrating ordered staging, allocation rounding,
  symbolic and machine readback, boundary guards, and memory-shape preservation
  live in [`scripts/ProofRecipeSuggestions.lean`](../scripts/ProofRecipeSuggestions.lean)
  (`intended_staged_windows`, `intended_staged_allocation`,
  `intended_final_word_image_readback`, `intended_final_word_machine_readback`,
  `intended_overlap_guard_rejected`, `intended_empty_write_inside_observation`,
  `intended_empty_observation_inside_write`,
  `intended_relation_with_memory_shape`).
- To read a window of a stage's image: [`Blanc/MemoryWindows.lean`](../Blanc/MemoryWindows.lean), where
  `window_at` reads a window inside one write no later write touches, `sliceD_sliceD` and `sliceD_self`
  reduce it, and `avoids_tac` closes the side condition over literal offsets.
- For the selected gas of those ordered primitive writes, use
  [`Blanc/MemoryStageGas.lean`](../Blanc/MemoryStageGas.lean).
  `MemoryStage.selectedGas_eq` telescopes the actual expansion charges into
  the per-write base charge plus the final-minus-initial memory cost, given
  word-aligned initial allocation. `applyMemory_aligned` preserves that
  alignment; `memExtsSize_le` and `memExtsSize_ge_window` bound the actual
  allocation from the access windows. Empty writes retain their base charge.
- Decode an exact word without losing bytes with
  `Bytes.toBytes_toB256_of_length`; shorten a padded read with
  `List.take_takeD_of_le`. The limb-level codec proofs are private
  implementation details of the public round-trip theorem.
- Whole-word byte images and the low-byte mask live in
  [`Blanc/Lift/WordImage.lean`](../Blanc/Lift/WordImage.lean).
  `Bytes.sliceD_writeAt_word_last` appends a word written exactly at
  a window's end, so consecutive word stores (an ABI encoding, a recovery
  request) read back as their concatenation, peeled from the right.
  `Bytes.sliceD_writeAt_short` reads a short write (a call reply prefix of at
  most 32 bytes) at the head of a word window followed by the old image, and
  `B256.zero_toBytes_sliceD` reads zeros from any tail of the zero word.
  `B256.and_ff_eq_toUInt8` and `UInt8.toB256_and_ff` identify `AND 0xff` with
  the low byte as a `UInt8`, as a `uint8` ABI decoder masks it. Discovery is
  manual; no trigger is registered.
- The ECRECOVER precompile on arbitrary calldata lives in
  [`Blanc/Lift/Ecrecover.lean`](../Blanc/Lift/Ecrecover.lean).
  `ecrecoverOutput data` is the precompile's own success output (empty for a
  malformed `v`, zero or out-of-range scalars, or failed recovery; otherwise the
  recovered address as one word), defined through Jaune's `executeEcrecover`;
  `executeEcrecover_eq` states it for any machine that can pay the fixed charge.
  `ecrecoverOutput_spectrum` proves for arbitrary calldata, without premises,
  that this output is empty or a canonical address word.
  `ecrecover_output_of_processMessage_clean` turns a clean synchronous
  non-delegated address-1 child (the `ProcessMessage` a `StaticAnswered` witness
  exhibits) into `gasEcrecover ≤ gas` and that output, and `ecrecover_active`
  discharges activation of address 1 on every covered fork by `CoveredFork.cases`.
  It identifies the executed answer; it never asserts that recovery succeeds or
  that signatures are unforgeable. Discovery is manual.
  The checked request-and-return engine lives in
  [`Blanc/Lift/EcrecoverCall.lean`](../Blanc/Lift/EcrecoverCall.lean).
  `EcrecoverCall.entry` exposes its exact source calling convention through
  `ReturnLayout`; `ReturnChecks` records the four structural return checks.
  `EcrecoverCall.consumes_effective` takes direct-routing readiness at the
  actual entry rules, `rules.delegatedCodeAddress(code1) = none`. Disabled
  delegation needs no code-byte restriction; enabled delegation still needs
  an actual readiness producer. The existing `EcrecoverCall.consumes` projects
  pure nondelegation to that same engine and takes the actual code/certificate, source cursor,
  entry registers, pointer, nondelegation, successful execution and a
  `NeutralFork` (no state gas, no block access list: every `HistFork`). It derives
  the real query, native call and paid gas, canonical nonzero answer, original
  slot and return continuation. Each version must prove its exact source
  equality and structural checks against its own certificate. The call PC is
  relative to the actual entry; the theorem assumes no desired answer or gas
  budget. Direct `ReturnChecks` goals use the `ecrecover-return-layout` recipe;
  the existential semantic consumer is found here by name.
  Shared signed-query fragments live in
  [`Blanc/Lift/SolcSignedQuery.lean`](../Blanc/Lift/SolcSignedQuery.lean).
  Its line inversions cover the prologue, calldata size, seven-argument permit
  and nine-argument authorization decoders, pause and mapped-byte reads,
  nonce update, six- and seven-word struct buffers,
  typed-data encoding and signature guards. Source destinations, nonce base,
  type hash and return tags are parameters where supported by the actual
  instruction sequence. `recovery_epilogue` derives the returned answer and
  owner stack from the compiler's shuffle. Consumers still prove exact source
  equality and follow their own certificate and cursor route. Every fork premise
  here is `NeutralFork` (no state gas, no block access list), so the storage
  lines state their successor over `afterSloadH`/`afterSstoreH` under the
  frame's actual access schedule.
  `nonce_head_line` exposes the exact key and increment operands immediately
  before SSTORE; its source is `nonceLine.dropLast`, with the original literal
  and complete `nonce_line` interface preserved.
  `mapped_byte_read_line` takes the actual indexed stack equality and proves
  the mapping read for that depth; the original `blacklist_read_line` is its
  permit specialization. `wrapper_line`, `selector_line`, `compare_gt_line`
  and `compare_eq_line` derive the ABI wrapper and selector-test stacks.
  `masked_owner_line` inverts the four-instruction
  address-mask/equality prefix using the canonical returned address word;
  successful owner equality still requires the consumer's actual branch proof.
  `seven_word_head_line`, `seven_word_body_line` and `seven_word_tail_line`
  invert the actual authorization builder; its source tag, domain slot and
  return destination remain explicit parameters.
  `struct_hash_line_at`, `typed_words_line_at`, `typed_length_line_at` and
  `typed_hash_line_at` use the actual pointer, length and read bounds.
  Consumers must derive every
  buffer fact and actual source route. Use the existing `line-run-split`
  recipe for line inversions. The
  helpers do not establish a whole selector path or historical occurrence.
- For an exact eight-byte big-endian limb, use
  [`Blanc/WordByteRoundtrip.lean`](../Blanc/WordByteRoundtrip.lean):
  `Blanc.Bytes.toBytes_toUInt64_of_length` proves that decoding and encoding
  preserves every byte under the length-eight premise. It derives the result
  from the public complete-word codec and needs no execution-goal recipe.
- For fixed-width shift and mask byte images, use
  [`Blanc/WordByteCodecs.lean`](../Blanc/WordByteCodecs.lean), namespace
  `Blanc.WordByteCodecs`. `high128_mask_bytes` identifies the first sixteen
  bytes followed by sixteen zeros; `shift96_take20_toAdr_bytes` identifies
  the leading address bytes after left alignment;
  `shift64_low_bytes_reverse_slice16` identifies ascending low-byte shifts
  with the reversed eight-byte lane at offsets 16 through 23. These pure
  word conversions have no execution-goal recipe.
- Fixed or padded memory windows: use `Mem.Wf` and `Mem.Reads` before adding a
  local take/drop proof.

### M2. The goal is an EVM memory update or read

- Jaune's `Devm.memWrite_memory`, `Devm.memWrite_stack`, and
  `Devm.memWrite_gasLeft` describe the primitive update.
- For source inversion of primitive word and byte stores, use
  `of_run_mstore_val` / `prefix_of_mstore_val` and
  `of_run_mstore8_val`. The byte-store result is the exact low-byte singleton write.
- `Mem.size_write_of_le`, `Mem.size_read_snd_of_le`, and related extension
  lemmas live in [`Blanc/ForwardCall.lean`](../Blanc/ForwardCall.lean).
- For a finite layout, `MemoryStage.applyMemory` folds actual `Mem.write` in
  the same order as `applyImage`. `MemoryStage.wf_reads` carries the exact
  `Mem.Wf`/`Mem.Reads` correspondence; `applyMemory_size` computes allocation
  through `memExtsSize`, including empty writes and 32-byte rounding;
  `applyMemory_size_of_covered` preserves an existing allocation only from an
  explicit fit premise. Use `words` for fixed word stores. These declarations live in
  [`Blanc/MemoryLayout.lean`](../Blanc/MemoryLayout.lean).
- For construction, `Ninst.runCompiled_mstore8_of` retains the exact singleton
  low-byte write and names its dynamic expansion charge. `func_run` uses the
  same rule for every supported compiled relation; pass that charge as the
  next numeric hint. `Func.runCompiledTo_mstore_step` covers word stores that
  need an exhibited outcome-general continuation.
- When only one long-lived word must survive unrelated scratch traffic, import
  [`Blanc/MemoryImage.lean`](../Blanc/MemoryImage.lean) and carry `MemWordAt`
  instead of exposing the whole byte image. `MemWordAt.writeMiss`,
  `.writeMissBytes`, `.extendsWrite`, `.acrossLine`, `.acrossLoadWord`, and
  `.acrossMstoreAt` are the basic frame transports (including CALL-family
  resume memory); `.acrossStaticcall` and `.acrossSuccessfulCall` cross an
  external call whose selected word lies at or above the end of its output
  window, the latter under an explicit status-one premise that rules out the
  failing branch; `Bytes.WordFrameFrom` composes the untouched suffix of exact
  trace images, `.slice_eq`, `.of_preserved_memImage`, and `.of_wordFrame`
  bridge those images, and `prefix_of_loadWord_window` reads the selected word
  back.
- `Blanc.WordArithmetic.minWord_eq_toB256_min` bridges a compiled comparison
  between a fitting natural and a word to natural-number `min`;
  `toNat_toB256_min_maxWord` is the matching exact round-trip for results
  saturated at `B256.max`.
- For creation-code guards, `of_run_codesize` exposes the complete code-image
  length pushed by `CODESIZE`.
- For creation-code copies, use `of_run_codecopy_mem`.

A scratch-word walk that writes several fixed slots and reads them back needs
three window cases.  `Bytes.sliceD_writeAt_inside` projects a subwindow wholly
inside the payload just written, while `Bytes.sliceD_writeAt_before` and
`Bytes.sliceD_writeAt_after` skip a write that lands wholly above or wholly
below the read window; `Bytes.sliceD_writeAt` remains the exact whole-payload
readback.  For a copied padded window, `Bytes.getD_sliceD_of_lt` projects one
in-range byte and `Bytes.sliceD_sliceD_of_le` projects any wholly contained
subwindow back to the original image.  At whole-word granularity prefer
`Bytes.readWord_writeAt_self` and `Bytes.readWord_writeAt_of_disjoint`, which
fix the 32-byte width and take the disjointness as a single `≤`-disjunction.

### M3. The goal is carrying a known memory word across execution

Use the shared carriers in
[`Blanc/MemoryImage.lean`](../Blanc/MemoryImage.lean) rather than declaring a
contract-local "this word survives that line" predicate.  Import it directly
with `import Blanc.MemoryImage`; it is contract-neutral and its own only
import is `Blanc.Ladder`.

- `MemImage devm img` is the whole-image carrier: it keeps `Mem.Wf` beside the
  reader image so the write algebra never re-derives it.  `MemImage.write`
  advances it across a byte write; `MemImage.of_memory_eq` moves it across a
  memory-preserving step.
- `MemWordAt devm offset w` is the one-window carrier: the backing image
  becomes existential, which keeps a large scratch region out of downstream
  goals.  Move between the two with `MemWordAt.of_memImage` and
  `MemWordAt.memImage`.
- Establish a window by storing (`MemWordAt.of_write`, `of_run_mstoreAt_mem`).
  Eliminate it to a direct memory-read equality with `MemWordAt.readWord`, or
  read it back onto the stack with `prefix_of_loadWord_window`.
- Carry a window across a write that misses it with `MemWordAt.writeMiss`
  (whole-word) or `MemWordAt.writeMissBytes` (arbitrary span); across logical
  extension with `MemWordAt.extend` and `MemWordAt.extends`; across the
  combined CALL-resume shape with `MemWordAt.extendsWrite`.
- Cross whole instructions and lines with `MemWordAt.acrossLine`,
  `acrossNinst`, `acrossMload`, `acrossLoadWord`, `acrossMstoreAt` and
  `acrossLogWith`; cross a call boundary with `MemWordAt.acrossStaticcall` or
  `MemWordAt.acrossSuccessfulCall`, whose only memory premise is
  `outputOffset + outputSize ≤ offset`.
- For a scratch trace whose writes are confined below a fixed boundary,
  `Bytes.WordFrameFrom` is the compositional frame relation. It quantifies
  every byte offset, so use `writeBefore` to compose a write whose end is at or
  below the boundary and `sliceD` to observe any padded width in the preserved
  suffix. Use `refl` and `trans` to compose frames, then
  `MemWordAt.of_wordFrame` when only a 32-byte machine window remains.
- For a finite ordered trace, import
  [`Blanc/MemoryLayout.lean`](../Blanc/MemoryLayout.lean) and use
  `MemImage.applyStage` to advance the whole proof image,
  `MemWordAt.applyStage` with one checked window guard, or
  `MemoryStage.wordFrameFrom` when every write ends below a suffix boundary.


Boundary: `Bytes.WordFrameFrom.writeBefore` requires the explicit layout fact
`n + ys.length ≤ start`; it does not support a write crossing the suffix. Every
theorem here is frame-shaped — it carries an already-known
window and proves nothing about what the step computed.  The disjointness side
condition is always the caller's explicit premise; this module never infers
that a contract's scratch region sits below a window, and it supplies no
multi-region layout, footprint or staging algebra.  For goals about the
primitive update itself, stay in
[M2](#m2-the-goal-is-an-evm-memory-update-or-read).

### M4. I need a block's trie root, its header hash, or a finite hash-separation premise

- A hash or trie premise: state it with `Blanc.Separated f xs` from
  [`Blanc/Separated.lean`](../Blanc/Separated.lean) over the finitely many values the trace computes
  (typically `[traceValue, recordedValue]`), never as universal injectivity (false by pigeonhole,
  so vacuous). `Separated.pair_eq` is the binding step, `Separated.pair_self` shows it satisfiable,
  `Separated.pair_iff` shows that in context it is exactly the equation it delivers (the gain is
  epistemic: it fails only under a collision). HASH-T's footprint premise is an instance:
  `SlotFootprint.FreshKeys.separated`, `SlotFootprint.freshKeys_iff`.
- A kernel-reducible trie encoding: [`Blanc/TrieKernel.lean`](../Blanc/TrieKernel.lean) holds
  the structural node encoders `nodeCompS`/`structCompS` and their hash-parametric twins
  `nodeCompH`/`structCompH`.

## T — settlement

### T1. I have `exec (initEvm msg)` and need `processMessage msg`

For a clean no-code-address execution whose target touch must remain in the
settled machine, use `processMessage_ok_touch_of_exec` in
[`Blanc/DeploymentTouch.lean`](../Blanc/DeploymentTouch.lean); the composed
CREATE adapter and its charge obligation are indexed in [C2](#c2-i-need-deploymentmessage-correspondence).

Use Jaune's `Jaune/MessageExecution.lean`, imported by
[`Blanc/MessageExecution.lean`](../Blanc/MessageExecution.lean):

- `MessageExecution.processMessage_eq_settle_exec_of_enter` exposes the generic
  frame-settlement boundary from an exact successful `Frame.enter` equation;
  use it for delegated children and any other retained entry.
  `frameEnter_eq_run_afterTransfer_of_notPrecompile` derives that entry from a
  successful transfer, exact code address, and fork-relative non-precompile
  fact without requiring `disablePrecompiles = true`; its settlement-level
  companion is
  `processMessage_eq_settle_exec_afterTransfer_of_notPrecompile`.
- For payable calls that already retain the exact interpreter entry, use
  `processMessage_eq_settle_exec_afterTransfer_of_codeEntry` and
  `processMessage_clean_of_exec_afterTransfer_of_codeEntry`. Derive ordinary
  non-precompile entry with
  `executeCode_enter_of_codeAddress_not_precompile`; this covers normal
  `disablePrecompiles = false` messages. Use
  `processMessage_eq_settle_exec_afterTransfer_of_noCodeAddress` for creation
  code with no separate address.
- `processMessage_eq_settle_exec_afterTransfer` names the actual environment
  produced by value transfer when precompiles are explicitly disabled, and
  `processMessage_eq_settle_exec` is its identity-entry specialization.
- `processMessage_clean_of_exec_afterTransfer`,
  `processMessage_revert_of_exec_afterTransfer`, and
  `processMessage_halt_of_exec_afterTransfer` cover the three raw outcomes from
  that actual entry environment. The unsuffixed adapters specialize them to
  entry-state identity.
- `settledRevert` and `settledHalt`, with their projection lemmas, name the
  canonical settled error machines.
- `Frame.settle` is `settleMsg` after the rules-selected error handler: use
  `Frame.settle_eq_settleMsg_handleErrorWith` (Jaune's `Jaune/ExecFrame.lean`)
  to expose it, then identify
  the selected handler with `executeCode.handleErrorWith_none` (the legacy
  `handleError`), `executeCode.handleErrorWith_some` (Amsterdam
  `handleErrorAmsterdam`), or `executeCode.handleErrorWith_ok` (either handler
  is the identity on clean results).
- For the inversion direction, use
  [`Blanc/MessageExecutionInversion.lean`](../Blanc/MessageExecutionInversion.lean):
  `processMessage_clean_rawPost` recovers a clean successful raw post, while
  `processMessage_entry_facts` recovers code, target, calldata, timestamp,
  entry storage, and memory well-formedness from the actual retained frame,
  given zero value or protection of the selected storage owner;
  `processMessage_entry_stack` separately recovers its empty operand stack
  and `processMessage_entry_memory` its empty memory, without changing the
  established conjunction returned by the former.
- For an already-retained zero-value static-precompile child, use
  [`Blanc/StaticPrecompileMessage.lean`](../Blanc/StaticPrecompileMessage.lean):
  `stor_of_processMessage_staticPrecomp` exposes the all-account storage frame
  under the positive enabled-precompile premise.  At address `0x2`,
  `gasSha25664_le_of_processMessage_clean` rules out an underfunded clean
  child, `output_of_processMessage_sha256_64_clean` identifies the exact
  64-byte SHA-256 result, and `frame_of_processMessage_sha256_64_clean`
  packages both conclusions.  None of these facts bypasses delegation
  resolution: the caller must first establish that the actual call selected
  the ordinary address-2 precompile route.
- `Msg.initDevm_*` and `Msg.initSevm_*` (Jaune's
  `Jaune/MessageExecution.lean`) expose canonical message-entry fields.

`Msg.NoDel.initDevm` in `Blanc/CommonProofs/NoDel.lean` requires the exact additional
fact `wa ∉ msg.inheritedDeletions`; message NoDel alone constrains code and the
created-account set, not the inherited deletion snapshot. Derive this fact
from the actual message producer. It is not a default-empty assumption.

For a whole successful `processMessageCall`, use
`ContractSpecSem.processMessageCall_preserves_stateInv` in
[`Blanc/LadderSem.lean`](../Blanc/LadderSem.lean), or the thin
`ContractSpec.processMessageCall_preserves_stateInv` wrapper in
[`Blanc/Ladder.lean`](../Blanc/Ladder.lean), when only `StateInv` is needed.
These retain the actual `MsgInv`, covered fork and contract preservation
premises, and require no inherited-deletion exclusion. The conjunction theorem
`processMessageCall_preserves_inv` additionally requires
`wa ∉ msg.inheritedDeletions` and preserves both `StateInv` and exclusion of
`wa` from the output deletion set. Transaction and system-message rungs derive
that exclusion from their actual message constructors; they do not add a
blanket hypothesis to their public signatures. This is contract-invariant
preservation over the existing wrapper, not a generic historical NoDel claim
or a raw interpreter-to-settlement equality recipe.

The same two owners' `applyBody_preserves_inv` theorem takes the actual
`ommers : List Header` before withdrawals. It keeps `CoveredFork` and the
existing balance and environment-invariant premises; covered modern rules
have no proof-of-work reward pass, so this is not a historical reward
preservation theorem. The static transition rung passes `block.ommers`.
Configured transition and import rungs reuse Jaune's
`stateTransitionScheduledE_of_pow_none`, deriving its no-reward premise from
`CoveredFork`, rather than assuming that scheduled ommer validation always
matches a fixed fork.

### T2. I need to know which child effects survive settlement

Use Jaune's `Jaune/ExecSettlement.lean` and `Jaune/ExecChronology.lean`
(imported by [`Blanc/ExecutionSettlement.lean`](../Blanc/ExecutionSettlement.lean)
and [`Blanc/ExecutionOccurrence.lean`](../Blanc/ExecutionOccurrence.lean)) and
Blanc's [`Blanc/ExecutionOccurrence.lean`](../Blanc/ExecutionOccurrence.lean):

- `processMessage.settle_ok_cases` in `Blanc/CommonProofs/Balance.lean` retains the
  actual `Devm.recordTouch` wrapper on both clean and rolled-back machines.
  Use its exact machine equations, then project unchanged observations.
  Rollback restores entry state, transient storage and storage-write
  annotations before recording the rules-selected touch.
- `Execution.commits` and `Frame.settlementCommits` distinguish raw success
  from complete frame settlement.
- `Exec.storageReplay_committedPost` supplies `Exec.StorageReplay`: at each
  owner whose entry code is nonempty, code is preserved and persistent storage
  equals replay of the retained SSTOREs. Use its second conjunct with the
  owner's code fact to obtain a cell equality; `Exec.StorageReplay.append`
  transports that code fact through composition. Account normalization and
  CREATE preparation can erase storage at code-empty owners, so this is not
  an all-account storage frame.
- `Exec.exists_lastRetainedSstore_of_getStor_ne` takes the same entry-code
  premise when locating the final retained write responsible for a changed
  cell. Derive it from the contract's existing code invariant.
- `Exec.descendantFrames`, `Exec.committedFrames`, and retained-node APIs
  traverse only effects that survive the relevant settlement boundary.
- `Exec.retainedStorageEffectTriples_cont`,
  `Exec.retainedStorageEffectTriples_doneOk`, and
  `Exec.retainedStorageEffectTriples_halt` compose the proof-erased retained
  `(owner, key, value)` chronology across ordinary, synchronously childless,
  and terminal execution nodes.
- `ProcessMessage.clean_input_state_of_settle` exposes the clean raw input and
  exact state retained by a successful settlement.
- `ProcessCreateMessage.ok_state_eq_inner_of_no_error` exposes the
  balance-neutral CREATE settlement seam; `processCheckedSystemTransaction_to_unchecked`
  recovers the unchecked successful system-message result.
- [`Blanc/MessageResult.lean`](../Blanc/MessageResult.lean) supplies the
  contract-neutral `MessageResult`, pointwise persistent/transient storage
  projections, and `ChildToWrapperSettledAt`.  The latter states the exact
  delegated-child-to-wrapper status normalization, complete output copy, and
  log rule: clean-child logs commit, while failed-child logs are discarded.
  Gas and warm-access bookkeeping are intentionally outside that relation.
- For exact retained wrapper carriers continue to E6; for their ordered state
  chronology continue to E8.

For a gas budget on retained frame multiplicity, use
[`Blanc/ExecutionCommittedGas.lean`](../Blanc/ExecutionCommittedGas.lean).
`Blanc.Exec.descendantFrames_settledGas` bounds the descendant count plus
returned gas after error handling by the actual execution's entry gas measure.
`Blanc.Exec.committedFrames_length_gas_le` includes the root with one extra
unit: a root may execute a free STOP. Child settlement determines which
descendants survive; this is a count of list occurrences, not distinct frames.
The bound itself needs no code-identity or successful-child premise.
For message wrappers, use
[`Blanc/ExecutionMessageGas.lean`](../Blanc/ExecutionMessageGas.lean):
`ExecutionTrace.MessageCallTrace.settledFrames_length_gas_le` bounds retained
frame occurrences plus returned execution gas by the message grant plus one
on covered forks. Its `ProcessMessageTrace` and `ProcessCreateMessageTrace`
companions use the settled machine's gas measure. The call wrapper follows
delegation and the create wrapper includes code-deposit settlement.
For the memory/gas potential along synthetic runs, use
[`Blanc/Lift/MemPotential.lean`](../Blanc/Lift/MemPotential.lean): `Pot`
(the gas measure plus the memory cost already paid is below one word) and
`memCap` (the word-size allowance).

### T2a. I need a frame invariant under trace-local entry premises

Before lifting through a wrapper, an invariant may need a positive condition
only at the roots of target frames actually entered by one concrete execution.
Use [`Blanc/ExecutionFrames.lean`](../Blanc/ExecutionFrames.lean),
[`Blanc/ExecutionFrameEntry.lean`](../Blanc/ExecutionFrameEntry.lean),
[`Blanc/ExecutionAdmission.lean`](../Blanc/ExecutionAdmission.lean), and
[`Blanc/ContractAdmission.lean`](../Blanc/ContractAdmission.lean) for the raw
execution layer, then the matching `Execution*Admission` module for retained
message, transaction, body, block, and history carriers —
[`Blanc/ExecutionMessageAdmission.lean`](../Blanc/ExecutionMessageAdmission.lean)
for `RetainedXlot`, `ProcessMessageTrace`, `ProcessCreateMessageTrace` and
`MessageCallTrace`,
[`Blanc/ExecutionTransactionAdmission.lean`](../Blanc/ExecutionTransactionAdmission.lean)
for `TransactionTrace` and `ApplyTransactionsTrace`,
[`Blanc/ExecutionBodyAdmission.lean`](../Blanc/ExecutionBodyAdmission.lean)
for `SystemMessageTrace`, `RequestsTrace` and `AppliedBodyTrace`, and
[`Blanc/ExecutionHistoryAdmission.lean`](../Blanc/ExecutionHistoryAdmission.lean)
for `ConfiguredBlockTrace` and `ConfiguredHistoryTrace`.  Each module owns only
the `FrameAdmitted` predicate of its own carriers and the transport theorem
through them; withdrawals and other direct state steps keep their ordinary
invariant proofs. For the exact boundary before request processing, use
[`Blanc/ExecutionBodyPrefixAdmission.lean`](../Blanc/ExecutionBodyPrefixAdmission.lean):
`AppliedBodyTrace.requestBenv` names the transaction-plus-withdrawals environment;
`requestBenv_covered` transports the fork and `requestBenvInv_admitted_sem`
transports the invariant using the existing admission and opening balance bound.
Neither request-call outcome is consumed by this prefix proof. For an arbitrary
normal-transaction position after the two actual opening system calls, use
[`Blanc/ExecutionTransactionPrefix.lean`](../Blanc/ExecutionTransactionPrefix.lean):
`ApplyTransactionsTrace.splitPrefix` returns `PrefixSplit n`, whose `before`
and `suffix` are the original indexed list's take/drop traces, with the exact
intermediate `benv` and `bout` and `rawFrames_eq`. `zero_boundary` and
`full_boundary` identify both edge cases; `next_result` recovers the actual
remaining head's `processTransaction` result and continuation trace.
[`Blanc/ExecutionTransactionPrefixAdmission.lean`](../Blanc/ExecutionTransactionPrefixAdmission.lean)
proves `indexedTransactions_length` and the exact full decoded-list boundary
with `transactionPrefix_full_boundary`, names opening-plus-prefix raw roots
with `transactionPrefixFrames`, preserves
the fork with `transactionPrefix_covered`, and transports an arbitrary
`ContractSpecSem.BenvInv` with `transactionPrefix_benvInv_admitted_sem` from
body entry. Admission ranges over exactly those raw roots, including rollback;
no withdrawal or request outcome is consumed. The take/drop structure is a
reliable named carrier; a bare `BenvInv` goal does not identify this boundary,
so discovery uses this branch and the existing trace-admission recipe. Import
[`Blanc/ExecutionTraceFresh.lean`](../Blanc/ExecutionTraceFresh.lean) when the
consumer needs canonical interpreter ingress as one conjunct:

- `Exec.rawFrameDescendants` and `Exec.rawFrameRoots` are the unfiltered
  entered-frame traversal below both the invariant ladder and the richer
  occurrence APIs. `Exec.mem_rawFrameDescendants_of_mem_descendantFrames` and
  `Exec.mem_rawFrameRoots_of_mem_committedFrames` carry a retained committed
  invocation root back to that traversal; they do not supply same-frame
  prefix/suffix or full storage chronology.
- For a retained trace carrier rather than a single `Exec`, the raw entered
  roots are projected by
  [`Blanc/ExecutionTraceFrames.lean`](../Blanc/ExecutionTraceFrames.lean):
  `ExecutionTrace.RetainedXlot.rawFrames` and the `rawFrames` of
  `ProcessMessageTrace`, `ProcessCreateMessageTrace`, `MessageCallTrace`,
  `TransactionTrace`, `ApplyTransactionsTrace`, `SystemMessageTrace`,
  `RequestsTrace`, `AppliedBodyTrace`, `ConfiguredBlockTrace` and
  `ConfiguredHistoryTrace` (whose `.step prior block` case is
  `prior.rawFrames ++ block.rawFrames`). No settlement or commitment filter is
  applied: a frame whose effects were later rolled back is still listed, so a
  predicate required over the whole list is a stronger premise than one over
  retained frames. The same module closes the traversal: `Exec.rawFrameRoots_trans`
  says a raw root of a raw root is a raw root, and
  `Exec.mem_rawFrameDescendants_of_parentStep` and
  `Exec.mem_rawFrameDescendants_of_parentPrefix` carry membership up an
  `Exec.Deriv.ParentStep` or `ParentPrefix` to its root.
  `Exec.rawFrameDescendants_sub_of_stepNone`, `_of_stepSome` and `_of_jump`
  include a successful continuation's raw descendants, and a filled child's
  raw roots, in the whole run's. Membership goals over
  these lists have no distinguishing head, so there is no recipe.
- When every raw root of a trace must satisfy a fact that `Frame.enter` establishes
  (empty stack and memory, an empty output buffer), import
  [`Blanc/ExecutionTraceEntered.lean`](../Blanc/ExecutionTraceEntered.lean):
  `EnteredCondition E` says every entered child's initial machine satisfies `E`;
  `enteredCondition_fresh` and `enteredCondition_output` are instances;
  `Exec.rawFrameDescendants_entered` and the carrier rungs up to
  `ExecutionTrace.ConfiguredHistoryTrace.rawFrames_entered` carry it to every raw root;
  `ConfiguredHistoryTrace.frameAdmitted_entered` / `frameAdmitted_output` give the
  admission. Pass `(E := …)` explicitly: `EnteredCondition`'s binders are implicit.
- When a retained trace consumer needs only frames whose message roots and
  descendants survive settlement, import
  [`Blanc/ExecutionTraceSettledFrames.lean`](../Blanc/ExecutionTraceSettledFrames.lean)
  and use its `settledFrames` projections instead of `rawFrames`; it mirrors
  the same trace-carrier route and concatenation order while applying the
  message and CREATE settlement tests at their roots.
  `ApplyTransactionsTrace.settledFrames_nil` shows an empty transaction fold
  settles no frames, while `ApplyTransactionsTrace.head_of_cons` and
  `ApplyTransactionsTrace.single_head` place the head transaction's settled
  frames among the fold's.
- To apply a property of raw transaction roots to a settlement-committed
  transaction frame, import
  [`Blanc/ExecutionTraceSettledOrigin.lean`](../Blanc/ExecutionTraceSettledOrigin.lean).
  `ApplyTransactionsTrace.mem_rawFrames_of_mem_settledFrames` places the
  frame's `Exec.Frame.rootDeriv` in the transaction traversal's `rawFrames`.
  It preserves the outer message and CREATE settlement filters and proves
  membership only, not uniqueness or a full chronology. The withdrawal
  `block_settled_transaction_caller_ne_system` consumes it with the existing
  trace-level caller-exclusion theorem.
  `SystemMessageTrace.mem_rawFrames_of_mem_settledFrames` supplies the same
  membership transport for a protocol system invocation.
- To place the entered top-level root frame of a committed message or call transaction among settled frames, import [`Blanc/ExecutionTraceRootFrame.lean`](../Blanc/ExecutionTraceRootFrame.lean).
  The shared `callRun_logs_error` helper in
  [`Blanc/ExecutionSettledReceiptLogs.lean`](../Blanc/ExecutionSettledReceiptLogs.lean)
  exposes the wrapper-to-core error and log equality.
  `TransactionTrace.root_frame_of_call_value_with_message` additionally preserves
  the exact identity `msg = trace.msg`, so execution facts carried by its relation
  can be applied to the retained transaction message. The original helper keeps
  its exact interface as a projection of that variant.
- To preserve fixed nonempty, nondelegating code across a configured history
  and the next block's protocol boundaries, import
  [`Blanc/ExecutionImmutableCode.lean`](../Blanc/ExecutionImmutableCode.lean).
  `ConfiguredHistoryTrace.block_code_boundaries` gives exact code identity at
  the opening, after beacon processing, before requests and after withdrawal
  processing. It uses the actual trace's admission and resource facts; it
  requires no address exclusions or contract-specific frame-entry premise.
- [`Blanc/ExecutionFrameTime.lean`](../Blanc/ExecutionFrameTime.lean) fixes
  the new chain tip (`ConfiguredBlockTrace.post_blocks_getLast`).
  For the *settled* frames of a block or history, import
  [`Blanc/ExecutionHistoryFrameTime.lean`](../Blanc/ExecutionHistoryFrameTime.lean):
  `ConfiguredHistoryTrace.blockFrames` (settled
  frames in trace order, each paired with its retaining block).
- `Exec.FrameAdmitted ca entry run` requires `entry` exactly at those roots
  whose `currentTarget = ca`. Its `root`, `mono`, `cont_of_ne`,
  `doneOk_of_ne`, `runErr_child`, `runOk_child`, and `runOk_next_of_ne`
  theorems are the supported restriction interface; do not reconstruct list
  membership inside a contract proof.
- `RootEntryIn F` in
  [`Blanc/ExecutionTraceEntry.lean`](../Blanc/ExecutionTraceEntry.lean) says a raw frame
  root starts at program counter zero on a selected fork. Each wrapper from
  `ProcessMessageTrace` through `AppliedBodyTrace` derives it (`.rootEntryIn`).
- `Exec.FreshEntry sevm pre` records only `pre.stack = []` and
  `pre.memory = Mem.empty`. `Exec.FrameAdmitted.fresh_of_enter` derives it
  from one actual frame entry, and `Exec.FrameAdmitted.and` combines it with
  an independently established contract-specific condition.
  `Frame.enter_run_output_empty` derives the independent `pre.output = []`
  fact from the same genuine entry; it is not part of `Exec.FreshEntry`.
- `ForallSubExecAdmitted`, `lift_admitted`, and `lift_inv_admitted` are the
  arbitrary-`Exec` eliminators. Unlike `RootedExecution`'s forward compiled
  construction, they keep the selected execution proof in the induction
  motive and therefore can consume trace-local evidence.
- State a contract obligation as `ContractSpec.SoundAdmitted ca entry` and
  close the frame theorem with `ContractSpec.preserves_inv_admitted`, yielding
  `ContractSpec.PreservesAdmitted ca entry`. `preserves_lift_admitted` is the
  lower transport seam for a custom frame invariant.
- `ExecutionTrace.MessageCallTrace.stateInv_admitted`,
  `TransactionTrace.benvInv_admitted`, `AppliedBodyTrace.stateInv_admitted`,
  and `ConfiguredHistoryTrace.stateInv_admitted` thread that same preservation
  theorem through their exact retained wrappers.  Each carrier has a matching
  `FrameAdmitted` predicate, so admission is required only for interpreter
  frames that the concrete trace actually entered.
  The whole-call `MessageCallTrace.stateInv_admitted_sem` and
  `MessageCallTrace.stateInv_admitted` conjunctions additionally require
  `ca ∉ msg.inheritedDeletions`. Admission constrains actual interpreter
  roots; it does not constrain an arbitrary incoming deletion set. Keep both
  the state-invariant and output-deletion conclusions. Prepared transaction
  callers derive this premise from `trace.prepared` and the actual fresh
  message constructor; raw/create state-only transports keep their existing
  signatures.
- Historical (fork-domain) counterpart:
  [`Blanc/ExecutionHistoricalAdmission.lean`](../Blanc/ExecutionHistoricalAdmission.lean).
  `ContractSpecSem`/`ContractSpec.SoundAdmittedIn F` and `PreservesAdmittedIn F`
  replace each `CoveredFork` frame position by a selected domain `F`
  (`PreservesAdmitted.toIn` is the `CoveredFork` instance, `PreservesAdmittedIn.mono`
  restricts). `ProcessMessageTrace`/`ProcessCreateMessageTrace`/`MessageCallTrace.stateInv_admitted_semIn`,
  `TransactionTrace`/`ApplyTransactionsTrace.benvInv_admitted_semIn` and the
  `ContractSpec` forms `…_admittedIn` split `hfork` into `F fork` (routing)
  and `stateGas = none` (settlement); deletion exclusion of `ca` comes from an
  installed checked runtime (`InstalledCert C`, `c.sem.image = some C.toList`)
  via `MessageCallTrace.accountsToDelete_ne_of_installedCert`, and the touched
  sweep from `StateInv.sweepTouchedAccounts` (never erases nonempty code; no
  sweep-off assumption). Also `stateGas = none` output twins
  `processMessageCall_{createCollision,createRun,callRun}_out_noStateGas` and
  `StateInv.getCode_eq_of_image`. The historical frame ladder that produces
  `PreservesAdmittedIn F` from `SoundAdmittedIn F` is the next bullet.
  The same owner carries the body and history: `SystemMessageTrace`/`RequestsTrace`/
  `Beacon`/`History`/`RequestStageTrace.stateInv_and_sum_le_admitted_semIn`
  (skipped stages are the identity), `StagedBodyTrace.stateInv_admitted_semIn`
  (D1 stage order; withdrawals via `benvInv_processWithdrawalsState_sem`;
  rewards via `StateInv.payRewards`, one `StateInv.addBal` per credit),
  `ConfiguredBlockTraceIn`/`ConfiguredHistoryTraceIn.stateInv_admitted_semIn`
  (per-block `F`/`stateGas = none` from `forkIn` + `BodyStageCapabilities F`,
  withdrawal funding from the retained `bound`, post via `postEq`) and the
  `ContractSpec` forms `…_admittedIn`. Reward funding is the explicit premise
  `RewardCreditsFunded` / `OmmerCreditsFunded` (lifted as
  `StagedBodyTrace`/`ConfiguredBlockTraceIn`/`ConfiguredHistoryTraceIn.RewardCreditsFunded`),
  which the Mac-owned reward budget discharges; no reward arithmetic is
  proved there. Also `ApplyTransactionsTrace.sum_le_noStateGas`.
- Historical frame ladder:
  [`Blanc/ExecutionHistoricalLadder.lean`](../Blanc/ExecutionHistoricalLadder.lean).
  `ContractSpecSem.preserves_lift_admitted_semIn F hF` and
  `ContractSpecSem`/`ContractSpec.preserves_inv_admittedIn F hF` turn
  `SoundAdmittedIn F` into `PreservesAdmittedIn F` for any domain with
  `hF : ∀ {f}, F f → f.ruleSet.stateGas = none`; `…_histFork` instantiate
  `HistFork` (`HistFork.stateGas_none`), and `preserves_inv_admitted_viaIn`
  recovers the modern theorem at `CoveredFork`. Step twins
  `Xinst.{none,some}_preserves_precond_noStateGas` and
  `Linst.inv_postcond_noStateGas` take only `stateGas = none` (selfdestruct reads
  the fork's actual access, beneficiary-credit and deletion rules);
  `Xinst.Run.some_child_forkIn` transports any `F` to an entered child.

- To derive structural admission directly from an independently checked predicate
  over the actual raw entries, use `ConfiguredHistoryTrace.frameAdmitted_iff_rawFrames`
  in [`Blanc/ExecutionTraceAdmission.lean`](../Blanc/ExecutionTraceAdmission.lean).
  The same equivalence is available for every carrier from `RetainedXlot` through
  configured history. It selects only roots targeting the named address and
  keeps failed and later rolled-back entries; it neither supplies an invariant
  nor filters by settlement.
- To derive per-frame environment facts from trace-level premises instead of
  demanding them per frame: `Exec.rawFrameRoots_warm`
  ([`Blanc/ExecutionWarmth.lean`](../Blanc/ExecutionWarmth.lean),
  [`Blanc/ExecutionTraceWarmth.lean`](../Blanc/ExecutionTraceWarmth.lean)) shows an
  address warm in every transaction-entered frame, including reverted subtrees,
  when it is a precompile of every covered fork (the accessed set only grows).
  `Exec.codeAt_avoid` and `ConfiguredHistoryTrace.codeAt_empty`
  ([`Blanc/ExecutionCodeAt.lean`](../Blanc/ExecutionCodeAt.lean),
  [`Blanc/ExecutionTraceCodeAt.lean`](../Blanc/ExecutionTraceCodeAt.lean)) keep the
  code at an address empty through a trace given no CREATE frame targets it and no
  authorization recovers to it (`NoAuthorityAt`). A machine update that keeps the
  error field is a `Devm.ErrKeep` walk in
  [`Blanc/ExecutionErrorKeep.lean`](../Blanc/ExecutionErrorKeep.lean). For transaction caller
  exclusion, `Exec.rawFrameRoots_caller_excluded_noStateGas` in
  [`Blanc/ExecutionCallerExclusion.lean`](../Blanc/ExecutionCallerExclusion.lean)
  tracks actual CALL/CREATE/DELEGATECALL callers and empty executing code from
  selected `rules.stateGas = none`. Its public spawn steps are
  `Xinst.step_create_spawn_codeAddress_noStateGas` and
  `Evm.step_spawn_caller_excluded_noStateGas`; entered children retain the selected
  capability through their actual block-environment equality. The original
  `Exec.rawFrameRoots_caller_excluded`, `Xinst.step_create_spawn_codeAddress` and
  `Evm.step_spawn_caller_excluded` retain their modern `CoveredFork` signatures.
  `RetainedXlot.caller_excluded_of_runFrame_noStateGas`,
  `MessageCallTrace.caller_excluded_noStateGas`,
  `TransactionTrace.caller_excluded_noStateGas` and
  `ApplyTransactionsTrace.caller_excluded_noStateGas` in
  [`Blanc/ExecutionTraceCallerExclusion.lean`](../Blanc/ExecutionTraceCallerExclusion.lean)
  carry that selected-rule fact through actual retained frames, message delegation,
  checked senders and transaction lists. They require actual empty-code and CREATE
  avoidance witnesses; they derive no such environmental restrictions from deployment.
  `TransactionTrace.caller_excluded` keeps its modern compatibility signature.
  `ConfiguredHistoryTrace.txRawFrames_caller_excluded` in
  [`Blanc/ExecutionTraceCallerExclusion.lean`](../Blanc/ExecutionTraceCallerExclusion.lean)
  derives that exclusion from initially empty code, retained `NoSenderAt`,
  `NoAuthorityAt`, and trace-local CREATE avoidance (`ApplyTransactionsTrace.noSender_nil`
  supplies `NoSenderAt a` vacuously for an empty transaction list). Calls to the empty-code
  address remain allowed; system frames are outside the conclusion.
  The same shared proofs expose `Exec.rawFrameRoots_caller_excluded_noStateGas`,
  `TransactionTrace.caller_excluded_noStateGas` and
  `ApplyTransactionsTrace.caller_excluded_noStateGas`; existing covered-fork
  interfaces are compatibility wrappers.
  This is transaction-frame coverage, with no system-frame or exact partial-cut
  scope claim. These quantified context-dependent conclusions have no reliable
  automatic recipe trigger; use this branch to choose the required carrier.
  For a Cancun prefix starting after a transaction, use
  `MidHistoryTraceIn.frameAdmitted_caller_ne_cancun` in
  [`Blanc/ExecutionMidHistoryInCallerExclusion.lean`](../Blanc/ExecutionMidHistoryInCallerExclusion.lean).
  Its `AllCancun` reads the cut block and every later block's actual selected fork;
  `NoSenderAt` reads only the suffix's and later blocks' checked senders.
  From initially empty code at the excluded address and actual raw CREATE avoidance,
  `callers_and_code_empty_cancun` derives target-restricted caller exclusion and
  empty endpoint code. There is no authority premise because Cancun disables delegation.
  `BeaconCodeInstalled` is a separate residual code-installation condition at each
  later whole-block opening; the cut's remaining stages have no beacon call.
  The protected target must differ from the beacon-roots address. Actual canonical
  beacon code confines protocol frames through `BeaconStageTrace.rawFrames_target_of_code`
  and `SpawnFreeReach`; disabled history/request stages contribute no invented calls.
  The standalone block and suffix producers are
  `ConfiguredBlockTraceIn.callers_and_code_empty_cancun` and
  `ConfiguredBlockTraceIn.tail_callers_and_code_empty_cancun`.
  `StagedBodyTrace.afterTransactions_codeAt_noStateGas` keeps code through actual
  withdrawals, request calls and rewards from the transaction-fold boundary, with
  request CREATE avoidance; `requests_rawFrames_empty_cancun` supplies the selected
  disabled-request fact. Deployment does not establish the empty-code, checked-sender,
  CREATE-avoidance or beacon-installation environmental premises.
  `SpawnFree` and
  `ConfiguredHistoryTrace.systemRawFrames_target_of_spawnFree`
  ([`Blanc/ExecutionTraceSystem.lean`](../Blanc/ExecutionTraceSystem.lean)) confine
  system-message frames to the four system addresses when their code spawns
  nothing.
  `SpawnFree` decodes at every offset, so it is false of the canonical EIP-7002
  code (`0xF4` bytes inside `PUSH` data): for real system code use
  `SpawnFreeReach` (no spawning instruction at a position an execution reaches;
  `Evm.step_cont_noPush` shows every executed pc is one no `PUSH` immediate covers,
  `Exec.rawFrameDescendants_eq_nil_of_reach`) and decide it for concrete bytes with
  `spawnFreeReach_of_check` over the linear walk `spawnFreeCheck`
  ([`Blanc/ExecutionReachable.lean`](../Blanc/ExecutionReachable.lean)). The four
  canonical system contracts, their checked `SpawnFreeReach`, and
  `SystemCodeInstalled` are in
  [`Blanc/SystemContracts.lean`](../Blanc/SystemContracts.lean).
  `ApplyTransactionsTrace.codeAt_keep`
  ([`Blanc/ExecutionTraceCodeKeep.lean`](../Blanc/ExecutionTraceCodeKeep.lean)) keeps
  *nonempty* non-delegating code through transactions (the empty-code
  `codeAt_empty` cannot), and `ConfiguredHistoryTrace.systemFrames_of_installed`
  ([`Blanc/ExecutionTraceSystemCode.lean`](../Blanc/ExecutionTraceSystemCode.lean))
  shows that with the canonical code installed at the checkpoint every system
  message enters no frame but its own.
- To discharge the creation-avoidance premise
  `∀ root ∈ trace.rawFrames, root.sevm.codeAddress = none → root.sevm.currentTarget ≠ a`
  for a concrete witness whose code makes calls (so `SpawnFreeReach` fails): show the world is
  call-only, `CodesCallOnly` (every installed code reaches only `CALL` at positions no `PUSH`
  immediate covers, `CallOnlyReach`, and none is a delegation designator), and that the
  block's transactions are calls without authorizations. `Exec.callOnly_roots` gives every raw
  frame a code address for one derivation, and `ConfiguredBlockTrace.callOnly` lifts it through
  the message, transaction, system-call, request and body traces, returning the post-chain
  world call-only again ([`Blanc/ExecutionTraceCallOnly.lean`](../Blanc/ExecutionTraceCallOnly.lean)).
  Decide `CallOnlyReach` for concrete bytes with `callOnlyReach_of_check`
  (`callOnlyCheck`, the linear walk), and get it from `SpawnFreeReach` with
  `callOnlyReach_of_spawnFreeReach`. `Xinst.step_call_spawn` is the per-`CALL` fact: the child
  has a code address and runs the callee's own code when it holds no designator.
  `Lift.WithdrawalRequest.FeeCounterexample.blockOk_of` is the worked consumer.
- To discharge the frame walks' entry premise `pre.gasMeasure < 2 ^ 256` for every raw frame of
  a configured history with no premise at all: `ConfiguredHistoryTrace.gas_bound` (`< 2 ^ 64`)
  and `ConfiguredHistoryTrace.frameAdmitted_gas`
  ([`Blanc/ExecutionTraceFrameEnv.lean`](../Blanc/ExecutionTraceFrameEnv.lean)).
  `Exec.rawFrameRoots_gas_le` is the execution-level fact (no entered frame starts with more gas
  than the execution's root); message roots start with the message grant
  (`MessageCallTrace.rawFrames_gas_le`, which uses the now-public `messageCallDelegation_gas` and
  `messageCallExecutionMessage_gas` of `Blanc/ExecutionMessageGas.lean`), transaction grants are
  below the block gas limit (`TransactionTrace.rawFrames_gas_lt`).
- To discharge the same per-frame gas/entry premises over a selected-domain
  (`In`) carrier instead of a modern one: with `BodyStageCapabilities F`,
  `ConfiguredHistoryTraceIn.rootEntryIn` (`root.pc = 0 ∧ F root.sevm.benvStat.fork`),
  `ConfiguredHistoryTraceIn.gas_bound` (`< 2 ^ 64`),
  `ConfiguredHistoryTraceIn.frameAdmitted_gas` and `ConfiguredHistoryTraceIn.rawFrame_gas`
  ([`Blanc/ExecutionStagedFrameEnv.lean`](../Blanc/ExecutionStagedFrameEnv.lean)).
  The entry chain is predicate-parametric (`RootEntryIn F`, every transport
  rewrites a `benvStat` equality, no rule fact needed); the gas chain runs on
  the `stateGas = none` twins (`TransactionTrace.msg_gas_noStateGas`,
  `gas_le_remaining_noStateGas`, the `rawFrames_gasMeasure_le_noStateGas`
  family, `header_gasLimit_lt_of_transition`, the modern statements unchanged
  as wrappers). Bounds needing a numerical rule value arrive as explicit
  fork-class hypotheses instead: `ConfiguredHistoryTraceIn.calldata_bound` (and staged/block
  forms) takes
  `hdata : ∀ f, F f → 16 ≤ (Fork.ruleSet f).txr.dataNonZero`, and the strict
  `rawFrames_gas_lt` chain (`TransactionTrace.msg_gas_succ_le_noStateGas`,
  `intrinsicGas_bounds_noStateGas`, staged/block forms) takes
  `hbase : ∀ f, F f → (Fork.ruleSet f).gas.txBase = 21000`; the `_hist`
  corollaries discharge both for `HistFork` (`HistFork.dataNonZero_ge`,
  `HistFork.txBase_eq`, each proved by `cases f <;> decide`).
- To discharge the per-frame premise `sevm.data.length < 2 ^ 256` for every raw
  frame of a configured history with no premise at all:
  `ConfiguredHistoryTrace.calldata_bound` and
  `ConfiguredHistoryTrace.frameAdmitted_calldata`
  ([`Blanc/ExecutionTraceCalldata.lean`](../Blanc/ExecutionTraceCalldata.lean)).
  Transaction roots satisfy `4 * data.length ≤ tx.gas` (intrinsic gas) and
  `tx.gas ≤ blockGasLimit < 2 ^ 63` (`checkTransaction`, `checkGasLimit` via
  `ConfiguredBlockTrace.header_gasLimit_lt`); child frames carry a memory slice
  sized by a popped word (`Evm.step_spawn_child_data`), and system messages
  fixed data. Before child entry, including synchronous precompile entry,
  `ExecutionTrace.Xinst.step_spawn_inner_data_length_lt` derives
  `frame.inner.data.length < 2 ^ 256` directly from an actual `Xinst.step` spawn
  and `stateGas = none`; it needs no entered-child witness or bounded-output
  premise. The entered-child theorem consumes this same opcode proof.
  `Exec.rawFrameRoots_data_bound` is the execution-level form.
- Every retained carrier from `ProcessMessageTrace` through
  `ConfiguredHistoryTrace` has `freshFrameAdmitted`; its matching
  `FrameAdmitted.and` combines that trace-derived fact with another admission
  over the same retained roots.

This layer does not manufacture environment, storage, routing, delegation, or
precompile facts, constrain an execution's result, or filter by settlement.
A consumer must derive every independent admission from its actual trace and
use the retained/committed APIs when rollback matters.

#### I need an ordinary execution output bound

Use [`Blanc/Lift/ReturnDataBound.lean`](../Blanc/Lift/ReturnDataBound.lean).
`Lift.ReturnDataBound.exec_output` proves, on both success and error outcomes,
that `Exec` leaves the enclosing output equal to its initial value or produces
an output of length less than `2 ^ 256`, assuming `stateGas = none`.
`OutputProvenance` states that disjunction explicitly: arbitrary seeded
execution does not imply a bounded output. Regular instructions and jumps
preserve output; RETURN/REVERT use a popped word for their full output size;
normal CREATE/CALL resumption preserves the enclosing output across either
child outcome. The theorem composes those facts over the actual interpreter.
For the actual call-level bound, use `call_returnData_length_lt` or
`staticcall_returnData_length_lt` on a real `Ninst.Run` and `CoveredFork`.
Both bound the complete post-state returndata, independently of the requested
output-copy window, including normally settled REVERT and exceptional-halt
children. `call_step_returnData_length_lt` is the `StepRun`/`Filled` interface;
`processMessage_output` is the message/settlement interface with actual bounded
input and `stateGas = none`. These consume actual initialized output seeds,
precompile producers and child-input bounds; no bounded-callee-output ENV
hypothesis is needed. Ordinary arbitrary-seed `exec_output` retains its explicit
disjunction above.

When rounded allocations need stronger headroom, the pinned Jaune's
`Jaune/MemoryAccounting.lean` provides
`Jaune.call_step_returnData_length_lt_two_pow_160` on actual `StepRun` plus
`Filled`, and `Jaune.call_returnData_length_lt_two_pow_160` on actual
`Ninst.Run` CALL. Both bound the complete reply below `2^160`, including
failed children and native callees, from legacy state gas and parent gas
measure plus charged-memory cost below `2^256`. The value stipend is covered.
`Jaune.Exec.memory_accounting_output` preserves the paid memory potential
across recursive execution and settlement on either outcome. Consumers must
derive the parent potential from their initialized/reachable execution;
it is an intermediate producer obligation, not a new bounded-callee-output
or no-wrap environmental premise. A generic inequality goal alone does not
identify this producer, so discovery remains in this registry.


#### I need a bound on actual precompile output

Use [`Blanc/Lift/PrecompileOutputBound.lean`](../Blanc/Lift/PrecompileOutputBound.lean).
`PrecompileOutputBound.precompile_run_output` follows all implemented producer
branches and bounds successful output length by `2 ^ 256`. Identity consumes
the actual input-length bound; MODEXP consumes its 32-byte modulus-length
header; the other producers use their fixed output serializers.
`PrecompileOutputBound.executePrecomp_output` gives the bound on both outcome
channels when actual input and incoming output seed are short. Errors preserve
the seed. Derive those premises from the real frame entry; this API does not
supply a separate environmental assumption about precompile output.
The immediate consumer is actual-entry composition in `Lift.ReturnDataBound`.

### T2b. I need a contract's own ledger replay across retained settlement

A contract that reads one account and reports an *ordered* replay of the moves
it saw meets four obstacles that are about EVM settlement, not about its
ledger.  Use
[`Blanc/ExecutionAccountingReplay.lean`](../Blanc/ExecutionAccountingReplay.lean)
rather than restating them:

- `ExecutionAccountingReplay.ReplayCarrier ca` supplies local `silent` and
  `credit` laws. Its `readsStorage` flag makes the storage premise of `silent`
  conditional. `ReplayCarrier.toSettlementCarrier` observes only `ca` when
  that flag is true, and no storage when false. A false flag therefore requires
  proving balance-only silence; it is not an assumption of storage independence.
  The local entry and positive-credit laws keep their original statements.
- `ReplayCarrier.processMessage_of_body` retains its original premises.
  The settlement-level CALL engine additionally takes `EntryStorageSafe`.
  Generic CREATE body seams use exclusion of the CREATE target from observed
  storage owners, replacing the old target-storage-empty premise. The local
  form requires target inequality only when `readsStorage = true`; rollback
  remains exact world restoration.
- `ReplayCarrier.xinstForeignSome` requires owner protection only when it
  reads storage. The general settlement form requires protection at every
  footprint owner, deriving CREATE target exclusion from actual target
  unprotectedness. Balance-only instances discharge the conditional premise
  without acquiring a code hypothesis.
- `ExecutionAccountingReplay.benvAfterTransfer_getStor_eq_of_safe` proves
  owner-local entry storage equality from successful transfer, the existing
  world-sum bound, and guarded caller-disjoint-or-Protected safety. The sum
  bound rules out a positive recipient credit wrapping to zero. Use it for
  true local carrier entry laws without adding a protection premise.
- `ReplayCarrier.ofStorageEqBalanceMono` is the endpoint classifier: a
  transition that fixes the account's storage and cannot lower its balance is
  one positive credit or no step at all.  A foreign-opcode proof should expose
  those two facts rather than restate the four-way split.
- `ReplayCarrier.nilOfEq` and `ReplayCarrier.silentReplay` are the small
  derived forms the seams themselves use.
- `ExecutionAccountingReplay.balanceCarrier` is a second, deliberately
  un-ledger-shaped instantiation whose boundary is a bare `Nat`; it reads no
  storage and records no provenance.  `balanceEntry_eq_ofState`,
  `ProcessMessage.targetBalanceCredits_of_body` and
  `targetBalanceCredits_of_balance_mono` are its restated seams, and they are
  what keeps the interface from quietly acquiring a ledger-shaped premise.
- `signedBalanceCarrier` retains exact message values with an `Int` entry
  boundary, avoiding a raw-frame value≤balance premise. `SignedBalanceCredit`
  distinguishes message-frame credits from incidental credits;
  `signedBalanceEntry_eq_ofState` connects that boundary to actual value transfer
  and `signedBalanceCarrier_append` composes replay. `SignedBalanceCredit.frames`
  observes message frames; `signedBalanceCredit_frames_sum_le` bounds their
  total values by the total recorded credits.
  [`Blanc/ExecutionAccountingSignedBalance.lean`](../Blanc/ExecutionAccountingSignedBalance.lean).
- `storageFoldCarrier` records a pure storage update for each event, with
  message transfers and incidental balance credits silent.
  `GuardedStorageReplay` checks each event's guard against the incoming storage
  at that occurrence, before applying its update; `.append` composes connected
  segments and `.fold_eq` gives the exact final storage. The contract supplies
  the update, guard and event observation; the carrier imposes no queue model.
  [`Blanc/ExecutionAccountingStorageFold.lean`](../Blanc/ExecutionAccountingStorageFold.lean).
  For the inverse decomposition at an exact list boundary, import
  [`Blanc/ExecutionAccountingStoragePrefix.lean`](../Blanc/ExecutionAccountingStoragePrefix.lean).
  `GuardedStorageReplay.split` retains both guarded segments at the computed
  prefix storage; `.head_guard` exposes the first event's incoming guard.
  The registered recipe triggers do not recognize this custom relation or
  carrier-construction need, so discovery remains in this branch.


### T2c. I need that ledger replay on every wrapper up to a whole configured history

Once a contract has a `ReplayCarrier` (T2b) and the replay of one committed
message root, the rest of the wrapper ladder is not about its ledger.  Use
[`Blanc/ExecutionAccountingLadder.lean`](../Blanc/ExecutionAccountingLadder.lean)
rather than climbing it again:

- `ExecutionAccountingReplay.AccountingLadder S ca` is the whole contract
  obligation, five fields: `carrier` (a `ReplayCarrier ca`), `append` (replays
  compose at a shared boundary), `tag` (the provenance a ladder-produced credit
  step carries, from block and transaction position), `root` (a committed
  retained execution at `initEvm` of a run-ready, non-self-call message below
  the word bound replays from `frameEntry` to its committed post-state — the
  shape of a contract's `lift_core` instance), and `preserves`
  (`S.Preserves ca`).
- Its rungs, each `∃ steps, L.carrier.Replay (ofState pre) steps (ofState
  post)` over the matching retained trace: `processMessage`,
  `processCreateMessage`, `messageCall`, `transactionMessage`, `transaction`,
  `transactionList`, `systemMessage`, `requests`, `directWithdrawal`, `body`,
  `configuredBlock`, `configuredHistory`.  The world word bound
  (`sum … bal < 2 ^ 256`) is an explicit premise up to `requests` and is derived
  inside the ladder above it; it stays explicit below because a general
  `ContractSpec.Side` need not be `SumNof`.
- `AccountingLadder.TraceRealizes L cfg root steps future` is the
  block-structured history carrier: one retained `ConfiguredBlockTrace` per
  imported block, each with its own replay segment.  `.toReplay` concatenates
  it, `.toReachUsing` projects configured reachability (given the root's
  reflexive reach), and `of_configuredHistoryTrace` / `exists_of_reachUsing`
  realize every retained history or reach from an `S.StateInv` root.
- Small additions it needed: `ReplayCarrier.ofAddBal_observed` (a direct balance credit
  is one positive credit at `ca` or no step, requiring
  `C.readsStorage = true → State.Protected pre ca`) and the word-bound transports
  `ExecutionTrace.TransactionTrace.msg_sum_nof` and
  `ExecutionTrace.processWithdrawalsState_sum_nof`.  Four more wrapper facts
  live beside them for ladders that do not fit this one:
  `ExecutionTrace.TransactionTrace.msg_caller` (the prepared message's caller
  is the checked sender), `ExecutionTrace.ApplyTransactionsTrace.stat_eq` (a
  transaction list changes the block environment only through state),
  `ExecutionTrace.processWithdrawalsState_getStor_eq` (direct withdrawals preserve
  storage at each `State.Protected` owner) and `ExecutionTrace.AppliedBodyTrace.transactionBound` (the
  withdrawal word bound survives the body prefix).



When the consumer must also know which executed frames the steps came from,
import
[`Blanc/ExecutionAccountingObserved.lean`](../Blanc/ExecutionAccountingObserved.lean):

- `ExecutionAccountingReplay.ReplayObservation C` reads a carrier's step lists
  homomorphically (`obs`, `obs_nil`, `obs_append`), says what one settled frame
  contributes (`frameObs`), and restates the carrier's credit law with the
  produced steps observed as nothing (`credit`).
- `AccountingLadder.Observed L` adds the root law: a committed root's replay
  observes exactly `(Exec.committedFrames run).flatMap view.frameObs`.
- Every rung has an observed twin, `AccountingLadder.Observed.processMessage`
  … `configuredBlock`, with the original's hypotheses and the extra conclusion
  `O.view.obs steps = trace.settledFrames.flatMap O.view.frameObs`
  (`directWithdrawal`: `= []`); the history headlines are
  `Observed.configuredHistory` and
  `Observed.traceRealizes_of_configuredHistoryTrace`.
- Seam twins take a `V : ReplayObservation C`:
  `ReplayCarrier.processMessage_of_body_observed`,
  `processCreateMessage_of_body_observed`, `xinstForeignSome_observed` (the
  child segment of a foreign CALL/CREATE slot), `silentReplay_observed`,
  `ofStorageEqBalanceMono_observed` and `ofAddBal_observed`. The raw CREATE
  twin requires `C.readsStorage = true → msg.currentTarget ≠ ca`; the actual
  foreign-slot twin requires conditional owner protection and derives CREATE
  exclusion internally. The local CALL twin keeps its original premises.

The observed statements are the proofs: `ReplayObservation`, the
`SettlementCarrier.*_observed` engines, `ofStorageEqBalanceMono_observed` and
`ofAddBal_observed` live in the replay and ladder modules, whose unobserved
seams and rungs are the observed ones read through `ReplayObservation.trivial`
and `Observed.trivial` (observing nothing).  Do not restate an unobserved rung
to carry a projection; instantiate an observation.

For deployed bytecode or a proof needing actual-frame entry premises, use
[`Blanc/ExecutionAccountingAdmission.lean`](../Blanc/ExecutionAccountingAdmission.lean):
`ExecutionAccountingReplay.AccountingLadderAdmitted c ca entry` takes a
`ContractSpecSem`, admitted preservation, and one observed root law. The law
relates replay steps to exactly `Exec.committedFrames run` and receives
`Exec.FrameAdmitted` for that same run. Its wrapper rungs carry the corresponding
trace admission through message creation, transactions, system messages,
requests, withdrawals, blocks and histories. `configuredHistory` concludes
replay and equality to `history.settledFrames.flatMap view.frameObs`; it derives
fork coverage from each retained block. Admission remains an entry premise,
never a supplied storage chain or endpoint condition. The legacy
`AccountingLadder.Observed.toAdmitted` adapter derives fresh entry from retained
traces and preserves the existing compiled API. Shared wrapper bounds and
`ReplayCarrier.ofAddBal_observed` now lives in the admitted module;
the old ladder reexports them by import. Raw `directWithdrawal` rungs in the
admitted ladder and both legacy twins require
`carrier.readsStorage = true → State.Protected pre ca`. Zero credits can
normalize an unprotected storage-only account; positive credits use the existing
sum bound to preserve storage. Transaction and body rungs derive protection
from installed-code invariants and retain their statements. The admitted
`processCreateMessage` needs no separate fresh-storage premise because its
existing `targetNe` suffices; legacy CREATE signatures retain that premise.

The single-execution bridge is
[`Blanc/ExecutionAccountingCore.lean`](../Blanc/ExecutionAccountingCore.lean).
`Exec.CoreAccounting` combines empty observations for static runs with exact
observed replay under the world word bound. `Exec.coreAccounting` lifts a
semantic target handler using the existing interpreter and settlement seams;
foreign frames must observe nothing, and foreign entry snapshots must equal
`ofState`. Its target handler receives only the already-derived lower-depth
core. Static observation emptiness is independent of the balance bound.
`Exec.CoreAccounting.messageRoot_facts` derives the semantic entry location and
entry balance bound from an actual transferred, run-ready message. Neither
bridge supplies a contract-specific deposit classification or entry premise.

Over a selected historical fork domain `F` instead of `CoveredFork`, use the
In twins: [`Blanc/ExecutionAccountingStepsIn.lean`](../Blanc/ExecutionAccountingStepsIn.lean)
(`Xinst.targetBalanceMono_of_none_noStateGas`,
`Ninst.targetBalanceMono_of_none_noStateGas`, the fork-free
`Ninst.foreignNone_getStor_eq'`, and
`xinstForeignSome_observed_noStateGas` at both carrier levels, all taking only
`sevm.benvStat.rules.stateGas = none`) and
[`Blanc/ExecutionAccountingCoreIn.lean`](../Blanc/ExecutionAccountingCoreIn.lean)
(`Exec.CoreAccountingIn F`, `Exec.coreAccountingIn` with
`hsgF : ∀ {f}, F f → (Fork.ruleSet f).stateGas = none`, and the `rfl` control
`Exec.CoreAccounting.eq_coveredFork`). `messageRoot_facts` is fork-free and
reused unchanged; discharge `hsgF` on `HistFork` with `HistFork.stateGas_none`.

The message/transaction rungs over `F` live in
[`Blanc/ExecutionAccountingAdmissionIn.lean`](../Blanc/ExecutionAccountingAdmissionIn.lean):
`AccountingLadderAdmittedIn F` (with `AccountingLadderAdmitted.toIn` and
`AccountingLadderAdmittedIn.mono`), `processMessageIn`, `processCreateMessageIn`,
`messageCallIn`, `transactionMessageIn` (all routing `F` through entry
preparation, the settlement equations through their `_noStateGas` twins),
`transactionIn` (selected chronology, `InstalledCert` NoDel, the deletion fold
plus the touched sweep via `sweepTouchedAccounts_get_of_code_nonempty`), and
`transactionListIn`.

The staged-body, block and history rungs over `F` continue in
[`Blanc/ExecutionAccountingHistoryIn.lean`](../Blanc/ExecutionAccountingHistoryIn.lean):
`systemMessageIn`, `requestsIn`, the optional stage rungs `beaconStageIn`,
`historyStageIn`, `requestStageIn` (skipped arm is the identity), the
carrier-level `processWithdrawals_observed` and `payRewards_observed`
(generalised over carrier, observation, append and tag), `stagedBody` (with
the `beaconHistoryReplayIn` and `transactionsWithdrawalsRequestsReplayIn`
junctions, at most two nested appends each), `configuredBlockIn`, and
`configuredHistoryIn`.

A deployed contract whose certified bytes spawn only
by `STATICCALL` shares one descendant argument,
[`Blanc/Lift/StaticOnlyFrames.lean`](../Blanc/Lift/StaticOnlyFrames.lean):
`Exec.staticOnly_descendantFrames_flatMap_eq_nil` removes every observed
descendant of a target frame from a restriction to `STATICCALL` at every
same-frame location and the ladder's lower-depth hypothesis.
The static callee may be the contract itself; it is then a static
lower-depth target frame closed by the same hypothesis.

A target frame whose children may be non-static and may re-enter the contract
uses the entry carrier of
[`Blanc/ExecutionEntryAccounting.lean`](../Blanc/ExecutionEntryAccounting.lean):
`entryCarrier`/`entryObservation` observe every non-static committed frame at
`ca` with `EntryGood` (pc 0, covered fork, contract code, admission, the storage
invariant `I` at entry); `Exec.CoreAccounting.entryTarget` is the target handler
(target-parent spawn accounting) from three per-contract obligations —
`FramePreserves` (the frame theorem), `SpawnKinds` (only `CALL`/`STATICCALL`
along the frame's own chain) and `SpawnEntry` (`I` at each spawning node of a
successful target frame, a prefix fact); `entryLadder` gives the ladder. Its generic
supports: `Evm.step_spawn_child_world` (a child opens on its parent's storage at
code-bearing accounts, balance total not growing), `Xinst.step_spawn_world`,
`Exec.Deriv.ParentStep.balSum_le`, `Exec.Deriv.ParentPrefix.balSum_le_getCode`.
For a selected fork domain, `EntryGoodIn F`, `EntryReplayIn F` and
`EntryReplayIn.append`, `entryCarrierIn F` and `entryObservationIn F` in the
same owner provide the carrier and its exact frame observations. The older
interfaces are their `CoveredFork` instances. This generalizes the carrier;
it does not port the reentrant `entryTarget`/`SpawnEntry` handler. A contract
whose actual target subtrees have no observed descendants can use the
existing historical accounting core with its own observation filter,
retaining `obs = id` and the same actual settled frame list. These
arbitrary-invariant carrier interfaces are registry-only because there is
no narrow fixed goal head for recipe dispatch.
The same-target direct-code facts are `Xinst.step_call_sameTarget_code` and
`Xinst.step_staticcall_sameTarget_code` in
[`Blanc/ExecutionDirectCode.lean`](../Blanc/ExecutionDirectCode.lean), which
specialize the target-free `Xinst.step_call_spawn_code` and
`Xinst.step_staticcall_spawn_code` there.

When the same target frame must be *replayed by a pure model* — its own model step
taken before the steps of the children it settles — use
[`Blanc/ExecutionModelAccounting.lean`](../Blanc/ExecutionModelAccounting.lean).
The carrier's boundary reads the target's storage only through its words
(`ofStateGet`); the contract supplies `Exec.CoreAccounting.SpawnReplay` (its own
steps `own`, and where they sit against the frame's chain nodes that decode an
external instruction: taken at each such node, only silent steps and no further
external instruction after it), plus `SpawnKinds`.
`Exec.CoreAccounting.spawnReplayTarget` composes `own` with the settled
children's replays using the ladder's lower-depth hypothesis and
`Exec.spawn_seam_noStateGas` (the storage across a spawning step, from
`Xinst.storageReplay_some_of_body`); `Exec.CoreAccounting.modelFrame`
is the `CoveredFork` projection of `modelFrameNoStateGas`,
which assumes only `stateGas = none`; `ExecutionAccountingReplay.modelLadder`
turns it into an `AccountingLadderAdmitted`. `Exec.Deriv.FirstExec` and
`Exec.Deriv.exists_firstExec_or_none` split a chain at its first external instruction.

To read a contract's ledger at the **entry** of an arbitrary committed or settled frame (a static
read of a token by a foreign contract, a foreign frame between two target steps), use the positional
ladder in [`Blanc/ExecutionAccountingPositional.lean`](../Blanc/ExecutionAccountingPositional.lean):
`PositionalLadder` is an `AccountingLadderAdmitted` with an `Opaque` frame predicate and the
frame-level root law `rootAt` (a replay from the root's entry boundary to the entry of any committed
frame `f` whose prefix holds no opaque frame enclosing `f`, `Exec.Frame.Encloses`). The descent
invariant `Exec.PositionalAccountingIn F` is proved for every admitted derivation over a fork domain
`F` without state gas by `Exec.positionalAccountingIn` (`Exec.PositionalAccounting` and
`Exec.positionalAccounting` are the `CoveredFork` instances). Generic helpers live there:
`Blanc.List.split_append_cons` and `Exec.descendantFrames_getStor_of_static_noStateGas`.
[`Blanc/ExecutionAccountingPositionalHistory.lean`](../Blanc/ExecutionAccountingPositionalHistory.lean)
lifts the root law through **the frame carrier** `framesCarrier` (a step is a settled frame; a replay
carries the full replay beside the positional claim `PositionalAt`), so the ordinary history rungs do
the assembly on any fork domain: `framesCarrier_read` over `AccountingLadderAdmittedIn.midHistoryIn`:
every split `before ++ f :: after` of the settled frames gives a replay from the start to `f`'s entry
that observes exactly `before`.


When the owner's frames run a *family* of codes (a proxy's `DELEGATECALL` children run the
implementation at the proxy's storage), use [`Blanc/ExecutionOwnerFamily.lean`](../Blanc/ExecutionOwnerFamily.lean):
`CodeFamily ca root` lists the delegates (`FamilyMember`, tagged by code address) under the root
code's `CodeSem`, with `CodeFamily.Runs`, `MemberAt` and `DelegatesInstalled`;
`CodeFamily.descend` is the strong induction on depth that handles delegate frames from the root
ladder's lower-depth hypothesis; the target handler `CodeFamily.frameAccounting` observes nothing
in a static frame, replays an unguarded frame by `CodeFamily.Unguarded`, and replays a guarded frame
as a whole or as a model frame (`CodeFamily.SpawnReplay`) whose children `CodeFamily.SpawnKinds`
classifies (`CodeFamily.childReplays`: a `CALL`/`STATICCALL` child is located by the root, a
`DELEGATECALL` child is a member frame); `CodeFamily.ladder` is the resulting
`AccountingLadderAdmitted`. `Xinst.step_delegatecall_spawn_owner` (a `DELEGATECALL` child keeps the
storage owner), `Exec.descendantFrames_getStor_of_quiet` and `Exec.descendant_getStor_spawnNode`
(every committed descendant enters with the owner's storage at one of the frame's own spawning
nodes) are the storage facts positions inside a quiet frame need. Its positional law is
[`Blanc/ExecutionOwnerFamilyPositional.lean`](../Blanc/ExecutionOwnerFamilyPositional.lean): `CodeFamily.Opaque` (an earlier non-static whole
frame at the owner), the handler `CodeFamily.framePositional` (`CodeFamily.childCases` locates a
model frame's single settled child by the root's `CodeSem.At` or as a member frame),
`CodeFamily.positionalLadder`, and the history laws `CodeFamily.configuredHistory_at` and
`configuredHistory_atPos`. In
[`Blanc/Lift/Token/FamilyReplay.lean`](../Blanc/Lift/Token/FamilyReplay.lean), `ObserverChain` pairs each non-static entry with its observer.
`Exec.derivEntry P sevm pre` in
[`Blanc/ExecutionWholeFrameAccounting.lean`](../Blanc/ExecutionWholeFrameAccounting.lean) states `P` of
every pc-`0` derivation from a frame start, which is the frame's one actual derivation.

For a list induction over settled positions, use
[`Blanc/ExecutionTraceSettledForest.lean`](../Blanc/ExecutionTraceSettledForest.lean): the settled
frames are a pre-order forest, with no uniqueness of frames assumed.
`ConfiguredHistoryTrace.settledFrames_contig` (from
`rootFrames_forest`) says that at every split `before ++ F :: after` the list `after` begins with
`F`'s descendants; `ConfiguredHistoryTrace.settledFrames_parent` says a settled frame is a message
root or an earlier frame `G` spawned it as a direct child (`Exec.SpawnedBy`) at a position inside
`G`'s block of descendants; `Exec.Frame.committedFrames_self` places a committed frame in its own
expansion.


**A token's storage over a mid history.**

- [`Blanc/Lift/FrameChain.lean`](../Blanc/Lift/FrameChain.lean): `FrameChain`, `coinFrames`: an account's storage moves through its settled non-static frames over a mid history.
- [`Blanc/Lift/ViewChain.lean`](../Blanc/Lift/ViewChain.lean): `ViewChain`: the same through a view of the words, for a proxy whose upgrade writes its own slots between token frames.
- [`Blanc/Lift/RootChain.lean`](../Blanc/Lift/RootChain.lean): `RootChain`: storage moves root by root with no certificate of the code.
- [`Blanc/Lift/RootStanding.lean`](../Blanc/Lift/RootStanding.lean): `Stands`, `StateLive`: listed accounts that hold their code, and a cell whose witness list stands.
- [`Blanc/Lift/BalanceLocality.lean`](../Blanc/Lift/BalanceLocality.lean): `EntryLocal`, `CoinKey`: locality of one holder's balance entry for a certified code.
- [`Blanc/ExecutionMidHistoryInOwnCode.lean`](../Blanc/ExecutionMidHistoryInOwnCode.lean): `MidHistoryTraceIn.rawFrames_closed`: its raw frames contain every frame they enter.
- [`Blanc/ExecutionReceiptLogLink.lean`](../Blanc/ExecutionReceiptLogLink.lean): `SystemConfined`: the facts that confine a block's system stages to the system addresses.

### T3. The wrapper is a transaction and the fact is about an installed contract

Use
[`Blanc/ExecutionTransactionEffects.lean`](../Blanc/ExecutionTransactionEffects.lean):

- `ExecutionTrace.TransactionTrace.sender_ne` rules out a checked sender equal
  to the contract, and `ExecutionTrace.TransactionTrace.msgInv` carries an
  arbitrary `ContractSpec` invariant onto the prepared message.
- `ExecutionTrace.TransactionTrace.debitState_bal_eq` and
  `ExecutionTrace.TransactionTrace.debitState_getStor_eq` project the nonce
  bump and up-front gas debit. Storage equality remains unconditional:
  `ExecutionTrace.validateTransaction_nonce_ne_max` and
  `ExecutionTrace.checkTransaction_sender_nonce` extract the admission facts
  ensuring the increment protects the sender before the debit.
  `ExecutionTrace.TransactionTrace.msg_shouldTransferValue` records that a
  transaction message always transfers its value.
  `ExecutionTrace.TransactionTrace.msg_caller_nonce_ne_zero` (in
  [`Blanc/ExecutionAccountingAdmission.lean`](../Blanc/ExecutionAccountingAdmission.lean),
  beside `TransactionTrace.msg_caller`) packages those two admission facts:
  the prepared message's caller has a nonzero nonce, so it is `State.Protected`.
- `ExecutionTrace.TransactionTrace.accountsToDelete_ne` and
  `ExecutionTrace.foldl_destroyAccount_get_eq` cover the final deletion fold.
- `ExecutionTrace.TransactionTrace.settlement_sum_bounds` funds the sender
  refund and the coinbase priority fee out of the transaction's own up-front
  debit, so neither credit needs a wrap-around side condition.
  `ExecutionTrace.TransactionTrace.selected_settlement_sum_bounds` is the
  selected-settlement analogue under only `stateGas = none`; the modern bound
  is a thin specialization of the same shared credit arithmetic.
- `ExecutionTrace.TransactionTrace.benvInv` moves a whole `ContractSpec.BenvInv`
  across one retained transaction.  Its balance-sum premise is explicit: a
  general `ContractSpec.Side` need not be `SumNof`.

`ContractSpec.StateInv.ne_of_messageCreateCollision_false` in
[`Blanc/ExecutionMessageEffects.lean`](../Blanc/ExecutionMessageEffects.lean)
is the message-level companion: a CREATE wrapper that does not collide is
running at an address other than the installed contract.

For the transaction's exact debit/message/refund/coinbase/deletion chronology,
use `ExecutionTrace.TransactionStateChronology`,
`ExecutionTrace.TransactionTrace.exists_stateChronology`, and
`ExecutionTrace.TransactionStateChronology.stateReplay` in
[`Blanc/ExecutionTransactionStateTrace.lean`](../Blanc/ExecutionTransactionStateTrace.lean).

For the actual trace's gas counters, use
[`Blanc/ExecutionTransactionGas.lean`](../Blanc/ExecutionTransactionGas.lean).
On a covered fork, `ExecutionTrace.TransactionTrace.exists_gasSettlement`
identifies the counter increments with the retained message outcome and its
refund. `TransactionTrace.grossGas_refund_bound` gives
`4 * grossGas ≤ 5 * blockGasIncrement`, and `TransactionTrace.chargedGas_le`
bounds the charge by the validated transaction reservation. These statements
account for the refund cap and calldata floor. The block gas limit bounds the
settled counter increments; it does not bound the sum of transaction gas reservations.

For legacy creation before initcode metering,
`ExecutionTrace.calculateIntrinsicCost_legacy_create_le` bounds intrinsic gas
by the base/creation charges plus the input length times the larger per-byte
rate. `TransactionTrace.intrinsicGas_legacy_create_le` transports that bound
to the original transaction's retained validation result. This avoids evaluating
all byte values when a length bound already leaves enough execution gas.
Select the actual trace, legacy type and fork switches explicitly; this
inequality has no automatic recipe trigger and does not identify a transaction.

For the converse (a transaction *succeeds*, and I have its stages) use
[`Blanc/TransactionForward.lean`](../Blanc/TransactionForward.lean):
`checkTransactionGasLimits_ok_of_room` and `checkTransaction_ok_of_parts` assemble the
admission check from its parts, and `processMessageCall_call_of_message` settles a call message
(no authorizations, no delegation) over a successful `processMessage`, including the
touched-account output field. The
sender-account part is the rule-selected `checkTransactionSenderAccountFor`, and
`calculateIntrinsicCost_two_call` takes the nonzero-byte price and calldata floor
(`CoveredFork.rules_dataNonZero`, `CoveredFork.rules_calldataFloor`).

`dataCost_le_sixteen_length` bounds the actual byte-fold cost without evaluating a concrete payload.
`calculateIntrinsicCost_legacy_create` and `calculateIntrinsicCost_legacy_create_le`
are its symbolic legacy CREATE equation and structural bound, requiring no state gas,
16-gas nonzero bytes, no calldata floor or init-code word charge, and base/create charges
21000/32000. `allocateEvmGas_bounds_of_intrinsic_le` transports a proved intrinsic cap to
execution-allocation lower/upper bounds and a zero state reservoir under `stateGas = none`.
These supply no transaction validation, sender recovery or successful execution.


For the receipt of an existing admitted `TransactionTrace` under historical
settlement, use `TransactionTrace.receipt_of_selected_settlement` in
[`Blanc/ExecutionSettledReceiptLogs.lean`](../Blanc/ExecutionSettledReceiptLogs.lean).
`TransactionTrace.receipt_and_blockLogs_of_selected_settlement` also exposes
the exact message-log append to the actual block output from the same inversion.
It identifies the actual receipt at `BLT.toBytes (.bytes index.toBytes)` with
the same message status, message logs and final cumulative gas. Only
`rules.stateGas = none` is required: the selected refund quotient, calldata
floor, touched sweep and BAL policy remain intact. It does not establish chain
inclusion by itself.
`MessageCallTrace.logs_eq_settledRoots` equates the actual filtered message logs
to each complete-settlement root post once; each post already includes its
retained descendants. `TransactionTrace.receipt_of_settledRoots` inserts that
same sequence in the actual receipt, preserving status and cumulative gas.
`MessageCallTrace.logs_and_settledRoots_eq_nil_of_error` additionally proves
that a failed actual message has no receipt logs and no settled roots, including
CREATE code-deposit failure. The call/create core `settledRoots_eq_nil_of_error`
lemmas test their final error marker; they do not assert that internal raw logs
were erased.
For later transactions, `TransactionTrace.receipt_preserved_of_key_ne` reuses
the all-fork exact insertion theorem; `ApplyTransactionsTrace.receipt_preserved_of_keys_ne`
transports the lookup through the actual suffix replay. Both require explicit
encoded-key separation, not merely an unproved inference from unequal indices.
`TransactionTrace.receipt_of_settledRoots_after_suffix` combines that transport
with the original receipt, retaining the original transaction's cumulative gas.
`RequestsTrace.receiptsTrie_eq` and `RequestStageTrace.receiptsTrie_eq`
derive actual trie preservation for enabled and disabled request processing.
`RequestsTrace.receiptsTrie_and_blockLogs_eq` supplies both trie and block-log
preservation from the same original request result.
`StagedBodyTrace.receiptsTrie_eq_transactionBout` transports through the actual
withdrawal and final access-list fields to the body's final output.
For the ordered receipts and selected logs of original indexed transaction roots, use
[`Blanc/ExecutionKeptReceiptLogs.lean`](../Blanc/ExecutionKeptReceiptLogs.lean):
`TransactionsRoots.receipt_keptAt_logs` gives the exact ordered key append,
positional `Forall₂` final-trie lookups and equality of address-filtered receipt
logs with the original kept-frame added-log sequence. It requires `stateGas = none`,
`bal = none` and the indexed list's strict order; `putIndex_pairwise` supplies that
order for the actual `putIndex` list. `MessageRoots.keptAt_logs` gives the original
message-to-kept log equality under `stateGas = none` and the address-filter implication.
Receipt completeness and log attribution are derived from the supplied original
carrier, with no installed-code, calldata-bound or entry-freshness premise.


For a successful creation receipt, use
`StagedBodyTrace.decodedTxs_getElem_of_slot` and `txSplit_tx_eq_of_slot` in
[`ExecutionBodyTransactionCut`](../Blanc/ExecutionBodyTransactionCut.lean)
to identify the original decoded transaction from one indexed body slot and
its actual-fork decoder result. The other slots retain their original inputs
and successful decoding; full frozen-body equality is unnecessary for this
selected identity. `mapM_getElem_of_eq_ok` is the underlying position-preserving
successful `Except` traversal fact. These explicit slot/cut equality adapters
have no reliable narrow recipe head and do not authenticate observations.
If no cut has yet been supplied, `StagedBodyTrace.txSplitOfSlot` constructs it
from those same slot/decode facts: successful decoding proves the index is in
range, and `splitAt` retains the original prefix, head and suffix.
This witness-producing
API requires no separate bound or transaction-cut assumption.
For rules outside the covered forks (any schedule with `rules.stateGas = none` and
`rules.bal = none`, including the touched-sweep forks and refund quotient 2), use
[`Blanc/TransactionForwardH.lean`](../Blanc/TransactionForwardH.lean):
`processTransaction_of_stagesH` returns the settled state with the rules' own touched sweep and
refund quotient (`txGasUsedQ`), and
`settled_getCode_getStor_of_code_nonempty` carries an account with nonempty code through the
credits, the deletion fold and the sweep; `processTransaction_installed_of_stagesH` combines the
two for an account the message installs and does not schedule for deletion.


The raw `debit_get_self` account equation requires the sender nonce to differ
from `UInt64.max`; transaction admission supplies this nonwrap fact.
`debit_get_self_of_protected` is the same equation for a sender that is
`State.Protected` after its nonce increment (`incrNonce_protected_self` restates
that premise on the original account), so an extracted frame helper without
admission can take the weaker structural premise.
`addBal_get_self` is unconditional and returns the credited account followed
by `clearIfEmpty`. A balance write can clear an unprotected storage-only
account, so its full-account equation must retain that normalization.

For the admission stages, the transaction's logs and its historical refund rules:

- [`Blanc/TransactionAdmissionProjection.lean`](../Blanc/TransactionAdmissionProjection.lean)
  exposes the actual successful checker stages through `checkTransaction_admission_parts`;
  `checkTransactionSenderAccountFor_code_empty`, `_funds`, and
  `checkTransactionGasLimits_room` project disabled-delegation code emptiness,
  the admitted fee/value balance bound, and no-state-gas block capacity. These are
  facts about the pinned executable checker.
- [`Blanc/ExecutionTransactionLogProjection.lean`](../Blanc/ExecutionTransactionLogProjection.lean)
  provides `TransactionTrace.logs_receipt`: selected settlement appends the exact
  retained message logs and inserts its exact typed receipt at the actual index.
  `ApplyTransactionsTrace.messageLogs` and
  `.blockLogs_eq_messageLogs` preserve the exact ordered concatenation through the list wrapper.
- [`Blanc/ExecutionRetainedLogMembership.lean`](../Blanc/ExecutionRetainedLogMembership.lean)
  provides `MessageCallTrace.retained_log_mem`, `TransactionTrace.retained_log_mem`
  and `ApplyTransactionsTrace.retained_log_mem`: a canonical log of a retained
  frame belongs to that same message or transaction fold's output.
- For historical refund and sweep rules, use
  [`Blanc/TransactionHistoricalForward.lean`](../Blanc/TransactionHistoricalForward.lean).
  `processTransaction_of_stages_selected_receipts` consumes the same actual validation,
  admission, debit, preparation and message-call stages under `stateGas = none` and
  `bal = none`; `selectedTxGasUsed` retains the selected refund quotient.
- [`Blanc/TransactionForwardSupport.lean`](../Blanc/TransactionForwardSupport.lean)
  collects the machine, codec and transaction-forward lemmas these consumers share:
  storage-access projections of `afterSstore`, concrete RLP receipt-key separation
  (`RlpConcrete.receipt_key_ne_of_small`), `processMessage_ok_of_exec`,
  `directCreateMessageOutputOf`, `validateTransaction_ok_of_noInitcodeLimit` and
  `processMessageCall_create_of_message`.

### T4. The wrapper is a message call and I must see through delegation




For a whole-state balance preorder under `stateGas = none`,
`processMessageCall.call_balance_noninc` in `Blanc/CommonProofs/Balance.lean` follows
`legacyAuthorization` and `Msg.resolveCodeDelegation`, preserving the actual
activation facade and the authorization prefix's balance sum.
`ForkRules.accessDelegation_of_not_delegation` and
`ForkRules.delegationCost_of_not_delegation` give the facade's no-designator
identity without assuming delegation is enabled.

Use
[`Blanc/ExecutionMessageEffects.lean`](../Blanc/ExecutionMessageEffects.lean):

- Recursive nonce preservation uses `Xlot.NonceNonzero` to express the child
  obligation. `Msg.benvAfterTransfer_get_nonce` gives exact nonce equality
  across value transfer; `ProcessMessage.nonce_ne_zero_of_body` and
  `ProcessCreateMessage.nonce_ne_zero_of_body` transport that obligation through
  settlement. `ProcessCreateMessage.ok_nonce_eq_inner_of_clean` isolates nonce
  equality across successful code deposit. `State.incrNonce_nonce_ne_zero`
  uses an explicit nonwrap premise, discharged by the actual CREATE precheck
  in `GenericCreate.nonce_ne_zero_of_body`. The CALL and executable adapters
  are `GenericCall.nonce_ne_zero_of_body` and `Xinst.nonce_ne_zero_of_body`.
  These preserve nonce-protected accounts without assuming installed code.
  `ProcessCreateMessage.ok_setCode_state_of_clean` is the common concrete
  settlement representation behind the nonce projection: the clean output
  state is the inner message state with target code installed.
  `ProcessCreateMessage.ok_charge_of_clean` exposes the same-slot inner
  message, its successful code-deposit charge and the exact installed Devm;
  the older state projection reuses that one clean-settlement traversal.
  For actual execution, [`Blanc/LockExclusion.lean`](../Blanc/LockExclusion.lean)
  provides `Exec.nonce_ne_zero_committedPost_noStateGas`, requiring only
  `rules.stateGas = none`, and its original covered-fork projection
  `Exec.nonce_ne_zero_committedPost`. The corresponding instruction donors are
  `Rinst.get_nonce_eq_of_ok_noStateGas`, `Ninst.nonce_ne_zero_of_none_noStateGas`,
  `Evm.step_cont_nonce_ne_zero_noStateGas` and `Linst.get_nonce_eq_of_ok_noStateGas`.
  Each original name without `_noStateGas` retains its covered-fork API.
  `Evm.step_spawn_rollback_getStor` separately preserves all parent storage
  when complete child settlement discards the result, including unprotected
  owners; it requires no nonempty-code premise.
  `Evm.step_spawn_rollback_code_stor_noStateGas` also preserves the entire code
  map under the same complete-discard premise and `rules.stateGas = none`.
- `ExecutionTrace.messageCallDelegation_fields` and its named projections
  (`_caller_eq`, `_target_eq`, `_currentTarget_eq`,
  `_shouldTransferValue_eq`) carry a routing or value field across the
  EIP-7702 authorization prefix. `_getStor_eq` preserves an owner's storage
  when its code is nonempty and is not a delegation designator; `_bal_eq`
  preserves the whole balance map, and `_benv_stat` the static environment.
  `_nonce_ne_zero` keeps every nonzero nonce nonzero (unconditionally: the
  only nonce write is a guarded authority increment), with the same law at
  `setDelegationStep`, `setDelegationLoop`, and `setDelegation`. The matching
  gas preservations — `setDelegationStep_gas`, `setDelegationLoop_gas`,
  `setDelegation_gas`, `messageCallDelegation_gas` (the delegation prefix
  hands the call its original grant) — live beside those `*_fields` lemmas in
  [`Blanc/MessageDelegationGas.lean`](../Blanc/MessageDelegationGas.lean) as the one public copy
  shared by message-call and history gas bounds.
- `ExecutionTrace.messageCallExecutionMessage_caller_eq` and its siblings
  (`_target_eq`, `_currentTarget_eq`, `_shouldTransferValue_eq`,
  `_getStor_eq`, `_bal_eq`, `_benv_stat`) do the same across delegated-code
  resolution; `_state` equates the whole world state.
- `ExecutionTrace.TransactionTrace.exists_callRun_of_target` eliminates the
  CREATE and collision constructors of an actual transaction message whose
  target is a CALL, exposing that trace's exact delegation, resolved message,
  core trace, and settlement equation for a consumer that must classify it.
- `ExecutionTrace.benvAfterTransfer_getStor_eq` and
  `ProcessMessage.none_ok_getStor_eq` preserve storage at a Protected owner.
  `ProcessCreateMessage.none_ok_getStor_eq_of_protected_ne` also requires that
  owner differ from the CREATE target. The true production
  `GenericCreate.none_getStor_eq` API is unchanged.
- `ExecutionTrace.setDelegation_getStor_eq` and
  `messageCallDelegation_getStor_eq` require nonempty, non-designator owner
  code. Protection by code alone is insufficient: clearing a delegation marker
  can normalize an account and erase storage. `setDelegation_bal_eq` remains
  unconditional.
- `ExecutionTrace.messageCreateCollision_false_target_unprotected` reports
  zero nonce and empty code, permitting storage-only CREATE targets. The three
  `processMessageCall_*_state_eq` theorems expose wrapper endpoints exactly.
- `ContractSpec.MessageRunReady` and the `ContractSpec.MsgInv` transport
  family (`runReady_of_call`, `runReady_of_foreign`,
  `processCreateMessage_msg`, `of_messageCallDelegation`, and
  `messageCallExecutionMessage`) package the conditions needed to run an
  arbitrary installed contract invariant through the wrapper.

### T5. The wrapper is a block body and the fact is about an installed contract

For proof-of-work reward credits, use
[`Blanc/ExecutionRewardCredits.lean`](../Blanc/ExecutionRewardCredits.lean).
`fold_addBal_nat_preserves` threads a direct-credit law and proves the exact
natural total through a list of credits under its pre-credit sum bound.
`payRewards_preserves_and_sum` specializes it to Jaune's actual miner and
ommer credits; `sum_payRewards_eq` gives the exact `ChainConfig.rewardTotal`
mint. `RewardCreditsFunded.of_rewardTotal` (with `OmmerCreditsFunded.of_sum`)
turns that natural budget into the historical per-credit premise
`RewardCreditsFunded` of `Blanc/ExecutionHistoricalAdmission.lean`;
`ContractSpecSem.StateInv.payRewards_of_rewardTotal` transports an existing
semantic invariant through the fold under the budget, through that owner's
`StateInv.payRewards`. `ExecutionTrace.StagedBodyTrace.rewardCreditsFunded_of_budget` and
`ConfiguredBlockTraceIn.rewardCreditsFunded` (under `stateGas = none`)
discharge the `rewards` premise of the historical `stateInv_admitted_semIn`
theorems from the retained reward-inclusive bound.
`payRewards_getStor_of_protected` preserves a protected account's storage
with no balance bound; `payRewards_balance_mono` additionally needs the exact
reward budget. `ExecutionTrace.StagedBodyTrace.reward_preserves_and_sum`
connects those laws to the retained body's actual reward endpoint and exact
selected mint; `stateInv_of_requestState` and `reward_getStor_of_protected`
provide its semantic-invariant and storage projections. Beneficiary collisions
are permitted.

For the balance budget before that reward stage, the retained system-message,
beacon, history, transaction-fold and request carriers expose
`sum_le_of_stateGas_none`, using the actual selected rule's `stateGas = none`
without modern fork coverage. `ExecutionTrace.sum_processWithdrawalsState_eq`
gives the exact enabled-withdrawal mint under its opening bound.
`ExecutionTrace.StagedBodyTrace.request_sum_le` combines those actual stages;
`request_budget` transports a body-entry withdrawal-plus-future-mint bound to
the request endpoint. `ExecutionTrace.ConfiguredBlockTraceIn.request_reward_budget`
derives the selected PoW budget from the retained configured pre-block bound;
`reward_preserves_and_sum` reaches its actual post-state and `sum_post_le`
includes the configured reward mint. Earlier historical contract-invariant
preservation, authentication and deployment roots remain separate obligations.

For a gas-derived bound on actual retained frame occurrences, use
[`Blanc/ExecutionBodyGas.lean`](../Blanc/ExecutionBodyGas.lean).
`ExecutionTrace.ApplyTransactionsTrace.settledFrames_gas_budget` telescopes
the actual settled transaction increments, with the refund factor retained.
`AppliedBodyTrace.settledFrames_gas_bound` adds all four protocol system-call
grants, including their descendants without any code-identity premise.
`ConfiguredBlockTrace.settledFrames_length_lt` combines that budget with the
same block's validated header limit to obtain a count below `2 ^ 64`.
The counted list is the ordinary settlement-retained full-body trace.
`ConfiguredHistoryTrace.blockCount` counts a history's appended blocks, and
`ConfiguredHistoryTrace.settledFrames_length_le` lifts the per-block bound to
`settledFrames.length ≤ blockCount * 2 ^ 64` for a whole configured history.

For ordered cuts around consecutive protocol withdrawal calls, use
[`Blanc/ExecutionRequestSegments.lean`](../Blanc/ExecutionRequestSegments.lean).
`ConfiguredBlockTrace.beforeWithdrawalFrames` retains beacon, history and
transaction frames; `afterWithdrawalFrames` retains consolidation frames.
`consecutive_withdrawal_segments` partitions the two actual consecutive block
lists around their complete withdrawal-message subtrees, preserving the
previous suffix followed by the next prefix. These are whole-subtree cuts;
the theorem does not identify an internal storage reset or prove its counter.

Use [`Blanc/ExecutionBodyEffects.lean`](../Blanc/ExecutionBodyEffects.lean),
the body-level sibling of T3:

- System messages: `ExecutionTrace.systemTransactionMessage_msgInv` carries an
  arbitrary `ContractSpec` invariant onto a Jaune system message, and does so
  without needing the system target to differ from the installed contract.
  `ExecutionTrace.systemTransactionMessage_target`,
  `..._target_isNone`, `..._currentTarget`, `..._caller`, `..._benv_state`
  and `..._benv_createdAccounts` project the message's fixed fields — the
  caller is always `systemAddress`.
  `ExecutionTrace.SystemMessageTrace.stateInv_and_sum_le` and
  `ExecutionTrace.SystemMessageTrace.benvInv` move the invariant and the
  balance-sum bound across a retained system message.
- Transaction lists: `ExecutionTrace.ApplyTransactionsTrace.run` recovers the
  `applyTransactions` call a retained list trace witnesses, so every ladder
  rung stated over that function applies to a trace unchanged.
  `ExecutionTrace.ApplyTransactionsTrace.sum_le`,
  `ExecutionTrace.ApplyTransactionsTrace.createdAccounts_eq` and
  `ExecutionTrace.ApplyTransactionsTrace.benvInv` are the three facts a
  body-level lift needs from a transaction list.
- Direct withdrawals: `ExecutionTrace.withdrawalCredit_toNat` and
  `ExecutionTrace.withdrawalCredit_bounds` are the exactness and the induction
  step of the `wdsum` block bound;
  `ExecutionTrace.benvInv_processWithdrawalsState` moves an arbitrary
  invariant across the whole credit fold.
- Requests: `ExecutionTrace.RequestsTrace.stateInv_and_sum_le`.
- Empty-withdrawal body balance: use
  `ExecutionTrace.AppliedBodyTrace.sum_le_of_empty_withdrawals` to bound the
  final total balance by the input total, without a contract invariant. It
  composes both retained system prefixes, all transactions, and both request
  calls. The withdrawal list must be `[]`; it does not bound a body with
  consensus credits. This remains COMMON_API-only: a bare natural-number
  inequality goal does not identify the retained body or its withdrawal list,
  so the current goal matchers cannot select this route reliably.

For the same system-message, transaction-list, withdrawal, request, and body
layers in exact state order, use the chronology APIs named in E8.

For the converse (a system call *succeeds*, and I have its raw frame) use
[`Blanc/SystemCallForward.lean`](../Blanc/SystemCallForward.lean):
`processSystemTransaction_of_exec`, `processUncheckedSystemTransaction_of_exec` and
`processCheckedSystemTransaction_of_exec` return the call's exact `(post.state,
systemCallOutput post)` for any member of `systemContracts` on a covered fork, from
`exec (initEvm (systemCallMsg benv target code data)) = .ok post` with no frame error and a
non-negative refund counter (and, for the block-level forms, the canonical code installed).
`systemContracts_not_precompile`, `systemContracts_nondelegated` and
`systemContracts_nonempty` are the envelope facts; `afterSstore_state`,
`afterSstore_getAcct_ne`, `State.get_setStorVal_ne`, `State.get_setStorVal_self` and
`State.getStor_setStorVal_self` (both `setPresent` and `set` arms) read a store's world-state effect and account/storage preservation. Worked uses: the EIP-4788 and
EIP-2935 walks `Blanc/Lift/SystemExecution/BeaconRoots/SystemWalk.lean` and
`Blanc/Lift/SystemExecution/HistoryStorage/SystemWalk.lean` (`processUncheckedSystemTransaction_beaconRoots`,
`processUncheckedSystemTransaction_historyStorage`), and the EIP-7251 empty-queue walk
`Blanc/Lift/SystemExecution/ConsolidationRequest/SystemWalk.lean`
(`processCheckedSystemTransaction_consolidationRequest_empty`, via the checked form).
For an unchecked call with empty installed code away from precompiles on a covered fork, use
[`Blanc/SystemCallEmpty.lean`](../Blanc/SystemCallEmpty.lean):
`processUncheckedSystemTransaction_empty` supplies a successful call and identity of the complete state.

**Under Amsterdam** the wrapper takes `processTopLevelAmsterdam`, and the frame starts from
`systemCallBase` (two read records on `initDevm`), not `initEvm`. Use
[`Blanc/Lift/SystemCallAmsterdam.lean`](../Blanc/Lift/SystemCallAmsterdam.lean):
`processSystemTransaction_amsterdam_of_exec` and `processCheckedSystemTransaction_amsterdam_of_exec` return the exact `(post.state,
systemCallOutputA msg post)` for any target, from `benv.stat.fork = .amsterdam`, installed code that is
no delegation and not at a precompile, and `exec ⟨0, initSevm msg, systemCallBase msg⟩ = .ok post` with no
frame error and a non-negative refund counter. `systemCallBase_St` starts a walk there;
A direct user message takes the same path: `processMessageCall_ok`, `processMessageCall_revert`,
`processMessageCall_halt` and the inverse `processMessageCall_inv` over `userSevm` / `userEntry`, with `failedOutput`
for the settled failure. A direct type-2 transaction with an empty reservoir composes in
[`Blanc/Lift/TransactionAmsterdam.lean`](../Blanc/Lift/TransactionAmsterdam.lean): `DirectTx` names what it takes from its
block and sender, `DirectTx.stages` gives the stages, and `processTransaction_amsterdam_of_stages` the settled result.
An EIP-7928 access record is [`Blanc/Lift/AmsterdamAccess.lean`](../Blanc/Lift/AmsterdamAccess.lean)'s `Access`, and
[`Blanc/Lift/BalEffect.lean`](../Blanc/Lift/BalEffect.lean)'s `incorporate_storage` / `incorporate_keysets` read what
`BalBuilder.incorporate` does to one account's slots. A frame that fails at a known instruction comes from an exact walk on
a cut tree: `cutOk` and `exec_of_cut` in [`Blanc/Lift/ExecCut.lean`](../Blanc/Lift/ExecCut.lean), which reuse exact walks
up to a `REVERT` with no change to `Outcome`. A request contract's system call has its access-list entries in
[`Blanc/Lift/RequestSystem/Access.lean`](../Blanc/Lift/RequestSystem/Access.lean) (`SysCall.bal`).
`systemCallBase_stateGas`, `systemCallBase_error`, `systemCallBase_refundCounter`
and `systemCallBase_orig` read the base. The module holds this repository's only
`open private` on Jaune's top-level path. Rule facts under Amsterdam, with `CoveredFork` left as it is,
are `amsterdam_rules`, `amsterdam_stateGas`, `amsterdam_access`, `amsterdam_push0` and
`amsterdam_shifts` in [`Blanc/HistoricalFork.lean`](../Blanc/HistoricalFork.lean).
A request contract's dispatch and inhibitor pushes: `adr_eqCheck` and `inhibitor_push` in
[`Blanc/Lift/SystemCaller.lean`](../Blanc/Lift/SystemCaller.lean).

The canonical system-operation support is owned by `Blanc/Lift/SystemExecution/`.
For each walk above, the exact runtime certificate, checked lift, jump table, and
program bridge are its supporting modules:

- `Blanc/Lift/SystemExecution/BeaconRoots/Cert.lean`, `Blanc/Lift/SystemExecution/BeaconRoots/Check.lean`, `Blanc/Lift/SystemExecution/BeaconRoots/Jumps.lean`, `Blanc/Lift/SystemExecution/BeaconRoots/Prog.lean`.

- `Blanc/Lift/SystemExecution/HistoryStorage/Cert.lean`, `Blanc/Lift/SystemExecution/HistoryStorage/Check.lean`, `Blanc/Lift/SystemExecution/HistoryStorage/Jumps.lean`, `Blanc/Lift/SystemExecution/HistoryStorage/Prog.lean`.

- `Blanc/Lift/SystemExecution/ConsolidationRequest/Cert.lean`, `Blanc/Lift/SystemExecution/ConsolidationRequest/Check.lean`, `Blanc/Lift/SystemExecution/ConsolidationRequest/Jumps.lean`, `Blanc/Lift/SystemExecution/ConsolidationRequest/Prog.lean`.

These concrete implementations support the featured configured histories; this
owner does not introduce standalone protocol exhibits or a generic replacement
for their checked runtime behavior.


### T6. The wrapper is a configured block or a whole chain history

Use
[`Blanc/ExecutionHistoryEffects.lean`](../Blanc/ExecutionHistoryEffects.lean),
the history-level sibling of T5.  The carriers themselves
(`ExecutionTrace.ConfiguredBlockTrace`, `ExecutionTrace.ConfiguredHistoryTrace`
and their existence theorems) live in
[`Blanc/ExecutionHistory.lean`](../Blanc/ExecutionHistory.lean); both layers are
schedule-parametric over `CoveredFork`, so a history crossing covered fork
activations is one derivation. The carrier retains the actual block number and
timestamp in both `forkAt` and `rulesAt`, and its explicit ommers in the body.
`ExecutionTrace.exists_configuredBody_of_transition` extracts the selected
fork, rule lookup, exact body run and post-state from the actual scheduled
transition, without a coverage premise; `ExecutionTrace.stateTransitionUsing_scheduled_ok`
exposes only the selected fork and the successful scheduled transition, for
inverting header validation or the appended block through Jaune's
`stateTransitionCoreE_*` facts. The modern carrier adds its own
`CoveredFork` evidence and unconditional modern body trace.

For the accepted historical domain, `BodyStageCapabilities.historical`
derives both extraction capabilities from `HistFork` membership.
`exists_mainnetConfiguredBlockTrace_of_transition` retains an actual mainnet
transition with its explicit reward-inclusive bound;
`exists_mainnetConfiguredHistoryTrace_of_reachUsing` retains a mainnet history
with the existing explicit `ConfiguredRewardBudget`. Neither wrapper infers
that budget from reachability or asserts historical contract preservation.

For a selected historical domain `F`, use `ConfiguredBlockTraceIn F` and
`ConfiguredHistoryTraceIn F` in the same owner. They retain the selected fork,
rule lookup, explicit ommers, staged body and exact post-state, with the bound
`sum pre.state.bal + wdsum block.wds + cfg.rewardAt block < 2^256`.
`BodyStageCapabilities F` names the state-gas absence and conditional request
coverage needed by `exists_configuredBlockTraceIn_of_transition`; domain
lemmas must establish these capabilities. `ConfiguredBlockTraceIn.withdrawalsBound`
forgets the nonnegative reward
term without changing `ReachUsing`. The converse
`exists_configuredHistoryTraceIn_of_reachUsing` additionally requires
`ConfiguredRewardBudget cfg checkpoint`: the reward-inclusive bound for every
successful extension of a reachable prefix satisfying the old bound. It does
not infer that stronger budget from reachability alone. These carriers retain
execution; historical balance and contract-invariant transport are separate
proof obligations.

`BodyStageCapabilities.covered` supplies the extraction capabilities for the
unchanged modern domain. `ConfiguredBlockTrace.toIn` and
`ConfiguredHistoryTrace.toIn` embed supplied modern traces in that domain;
`ConfiguredBlockTrace.rewardAt_eq_zero` discharges the added reward term from
the actual selected fork. `ConfiguredBlockTraceIn.toModern` takes explicit
coverage of its selected fork, while `ConfiguredHistoryTraceIn.toModern`
consumes a history in the covered domain. Both block conversions' `bodyTrace`
projection laws identify the supplied body's adapter exactly.

For the exact admitted transaction sender population, use
[`Blanc/ExecutionSenderOccurrences.lean`](../Blanc/ExecutionSenderOccurrences.lean).
`SenderOccurrence.recovered` reads recovery from the actual admission check.
`ApplyTransactionsTrace.senderOccurrences_indexed` and
`senderOccurrences_getElem?` retain every input transaction and its position,
including duplicates and transactions whose later VM execution fails.
`ConfiguredHistoryTraceIn.senderQueries` projects those occurrences through
the actual ordered block bodies; `noSenderAt_of_senderQueries` turns exclusion
on precisely those queries into the selected history's `NoSenderAt` fold.
The modern counterpart uses `toIn_noSenderAt_iff` to preserve the existing
fold. These projections need no additional fork-domain assumption and do not
supply delegation or old-contract ECRECOVER exclusions.
The `admitted-sender-query-exclusion` recipe recognizes the three direct
transaction, modern-history and selected-history `NoSenderAt` goal heads.

[`Blanc/ExecutionSenderRootCallers.lean`](../Blanc/ExecutionSenderRootCallers.lean)
projects the same admitted senders to actual settled message roots.
`ConfiguredHistoryTraceIn.settledRoots_caller_ne_of_noSenderAt` combines
`NoSenderAt a` with `a ≠ systemAddress`; its `of_senderQueries` counterpart
consumes the exact recovery-query exclusion directly. Transaction roots retain
the original checked sender, while optional system stages retain systemAddress.
These results need no modern fork, code invariant or eligible-authority premise
for caller identity. `ExecutionMidHistoryInForest` supplies the corresponding
mid-history roots and exact sender-query suffix transport.

The following effects APIs consume the modern covered carrier:

- Entering a block's body: `ExecutionTrace.ConfiguredBlockTrace.openingState`
  says block preparation copies the parent chain's world state verbatim, so the
  preparation boundary moves no value;
  `..._.not_mem_openingCreatedAccounts` discharges any not-yet-created side
  condition from the empty created-account set each block opens with, which is
  why that side condition never has to cross a block boundary;
  `ExecutionTrace.ConfiguredBlockTrace.openingBenvInv` packages both into the
  `ContractSpec.BenvInv` an `applyBody`-level rung asks for, and
  `ExecutionTrace.ConfiguredBlockTrace.openingBound` reads the carrier's own
  `wdsum` bound at that same environment.
- Leaving a block: `ExecutionTrace.ConfiguredBlockTrace.postState` identifies
  the imported chain's state with the world the body left.
- Whole histories: `ExecutionTrace.ConfiguredHistoryTrace.stateInv` carries an
  arbitrary preserved `ContractSpec` invariant from a checkpoint to every
  configured continuation, over `ConfiguredHistoryTrace.toReachUsing`.
- For the gas measure of every frame a configured history enters, use
  [`Blanc/Lift/HistoryGas.lean`](../Blanc/Lift/HistoryGas.lean):
  `MessageCallTrace.rawFrames_gasMeasure_le` (every entered frame starts at
  or below the message's grant), with the transaction, body, and history
  companions (`TransactionTrace`, `ApplyTransactionsTrace`,
  `SystemMessageTrace`, `RequestsTrace`, and `AppliedBodyTrace` forms).

For schedule-parametric block/history state boundaries and replay, use
`ExecutionTrace.ConfiguredBlockStateChronology` and
`ExecutionTrace.ConfiguredHistoryStateChronology` from E8.

#### Contract-local fixed-fork to configured-schedule migration

When a contract-local carrier still fixes one fork, keep the common carrier as
the schedule-neutral spine and make the local extension follow its fields:

1. Replace the local `chainId`/fixed-fork parameter with `cfg : ChainConfig`.
   Each block retains its selected `rules`, the equation
   `cfg.rulesAt block.header.number block.header.timestamp = .ok rules`, the
   `stateTransitionUsing cfg` result, and the body trace produced from
   `initBenv fork` for the retained selected fork. Project literally to `ConfiguredBlockTrace cfg`; recurse
   over those projections for `ConfiguredHistoryTrace cfg` and derive the
   inverse local history by recomputing only contract-owned ledgers.
2. Parameterize a deployment root and every constructor/result carrier by
   `cfg` and the selected `rules`. State rule-sensitive facts — precompile
   membership, transaction gas caps, code limits, or opcode availability — as
   explicit premises or selected-record fields. A root intended to support
   arbitrary future blocks also needs the corresponding schedule-wide fact,
   such as target nonprecompile membership for every successful `rulesAt`.
3. Keep the generic theorem over `ReachUsing cfg`. Publish the named-network
   surface as a thin specialization, with local lemmas that classify every
   successful `rulesAt` and select the current rule record after its activation.
   Retain the former fixed-fork API as a thin audited compatibility corollary.

This pattern does not make the contract-local carrier common infrastructure.
A literal block/history adapter or repeated schedule-selection lemma is a
hoisting candidate only after another consumer needs the same shape.

A current-fork execution witness alone cannot supply a cross-activation history. Consumers deployed
before the current fork need a historical deployment root at the rule record
selected at their actual deployment timestamp, followed by one configured
history that crosses later activations; a fresh current-fork creation block is
evidence for a different claim. If a future fork changes execution semantics
rather than rule data already represented by Jaune, update Jaune and re-prove
the consumer instead of adding a premise that assumes the new semantics away.

**Selected-domain history facts.**

- [`Blanc/ExecutionHistoryInFrameEnv.lean`](../Blanc/ExecutionHistoryInFrameEnv.lean): `precompileReadyH`: frame-environment facts over selected-domain histories.

For the logs of an original selected-domain block and the history lemmas its consumers share:

- [`Blanc/ExecutionBlockLogs.lean`](../Blanc/ExecutionBlockLogs.lean): `RequestStageTrace.blockLogs_eq`
  keeps the block logs through request processing, and
  `StagedBodyTrace.blockLogs_eq_transactionBout` transports the transaction fold's logs through
  actual withdrawals, requests and finalization.
- [`Blanc/ExecutionHistorySupport.lean`](../Blanc/ExecutionHistorySupport.lean):
  `ConfiguredHistoryTraceIn.rewardCreditsFunded`, `settledFrames_append`, the system-opening
  transports (`SystemCodeAtOpenings_append`, `ForksSatisfy_append`,
  `systemCodeAtOpenings_of_preCancun`, `pragueNoAuthorityAt_of_prePrague`), the receipt read
  `TransactionTrace.receipt_of_settledRoots_after_later_indices`, and the frame-environment facts
  `not_mem_systemTargets_of_size`, `ConfiguredHistoryTrace.rawFrames_system_or_tx` and
  `ConfiguredHistoryTrace.txRawFrames_warm` (with their transaction, list and body forms).

### T7. I must construct a configured block forward from its parts

For the fixed synthetic BPO2-from-genesis fixture, use
[`Blanc/SyntheticBpo2Envelope.lean`](../Blanc/SyntheticBpo2Envelope.lean):
`SyntheticBpo2Envelope.config` selects chain 1 and BPO2 at every height;
`checkpointHeader`, `checkpointBlock`, `checkpoint` retain the supplied state;
`executionHeader` and `input` set up its successor with gas limit 1,000,000.
`committedHeader` fills body commitments independently of any transaction.
This is a synthetic fixed-fork envelope, with no mainnet or arbitrary-fork claim.
For its four system addresses, use
[`Blanc/SyntheticSystemWorld.lean`](../Blanc/SyntheticSystemWorld.lean):
`SyntheticSystemWorld.systemCode` is exactly `#[0x5b, 0]` (JUMPDEST; STOP),
`systemWorld` installs it at the beacon-roots, history-storage, withdrawal-request
and consolidation-request addresses, and `systemCode_size` and
`systemWorld_stor` give its nonempty and storage
facts. `systemAddresses` and `SystemCodes` state that a supplied world carries
this fixture at those addresses. These are fixture bytes, not mainnet system
contract code; funding, signing and contract deployment belong to each instance.

Use [`Blanc/BlockForward.lean`](../Blanc/BlockForward.lean), the forward
direction of T5/T6: it turns proof-produced evidence about the parts of a block
body into Jaune's own `applyBody`, `stateTransitionUsing` and
`ConfiguredBlockTrace` results, so a reachable history (a liveness witness or
a counterexample) is built without evaluating any root, bloom or hash.
Nothing in it names a contract; the only fork premise is `CoveredFork`.

- `BlockForward.applyBody_forward`: from the two unchecked system calls (each
  `processUncheckedSystemTransaction … = .ok _`), the retained last block hash,
  the decoded transaction list (`txs.mapM decodeTx = .ok txList`), the fold
  `applyTransactions txList.putIndex … BlockOutput.init = .ok _`, an empty
  deposit parse and the two checked request calls, conclude
  `applyBody benv txs [] = .ok (stC, requestsOutput boutTxs wData cData)`;
  `requestsOutput` is the transaction output with the two optional request
  entries appended and an empty block access list. Withdrawals must be `[]`.
- `BlockForward.parseDepositRequests_of_no_logs` /
  `parseDepositRequests_of_no_receipts` discharge the deposit parse for
  receipts without logs, and `parseDepositRequests_of_no_deposit_logs` for
  receipts whose logs all sit away from the deposit contract (via the
  body-generic `forIn_logs_yield_of_skip`);
  `BlockForward.runRequestContracts_prague` and
  `processGeneralPurposeRequests_forward` are the request-pass pieces.
- `BlockForward.validateHeader_ok_of_facts`: header validity from the parent
  tip and field equalities (parent hash, computed base fee, excess blob gas,
  `gasUsed ≤ gasLimit`, strictly later timestamp, `number + 1`, extra data,
  zero difficulty/nonce, empty ommers, rule-dependent field presence);
  `checkGasLimit_self` and `calculateBaseFeePerGas_unit` settle an unchanged
  admissible gas limit and a unit base fee when the parent used at most its
  target, so the base fee is a bound, never an evaluation.
- `BlockForward.commitHeader` and `BlockForward.commitHeader_ok` fill the parent,
  body commitments, successor number/timestamp, and excess-blob-gas fields before
  applying the shared header validator.
- `BlockForward.stateTransitionChecks_ok_of_eq` and
  `stateTransitionUsing_forward`: the configured transition
  `stateTransitionUsing cfg pre block = .ok ⟨appendBlock pre.blocks block, st, pre.chainId⟩`
  once the header commits, by construction, to the body's `blockGasUsed`,
  transaction/receipt/withdrawal roots, bloom, blob gas and
  `some (computeRequestsHash bout.requests)`.
- `BlockForward.configuredBlockTrace_forward` packages that transition into the
  `ConfiguredBlockTrace` carrier of T6 from `sum pre.state.bal < 2 ^ 256`, and
  `BlockForward.ConfiguredBlockTrace.sum_post_le` carries that bound to the
  next block when the withdrawal list is empty.
- `BlockForward.blockHashes_getLast_of_ne` supplies the last retained block hash
  (`getLast? = some lastHash`) for any chain with nonempty blocks.

This remains COMMON_API-only: the goal shape is a fixed Jaune equation and the
current recipe matchers have no forward-transition shape to bind.

## C — compilation and deployment

### C1. I need source-to-compiled execution

- Compiler relations and program bridges:
  [`Blanc/Compiled.lean`](../Blanc/Compiled.lean).
- Forward compiled construction:
  [`Blanc/Forward.lean`](../Blanc/Forward.lean).
- Arbitrary terminal outcomes:
  [`Blanc/Reverts.lean`](../Blanc/Reverts.lean).
- Call crossings:
  [`Blanc/ForwardCall.lean`](../Blanc/ForwardCall.lean).
- EIP-8024 immediates in compiled code: `Func.compile` rejects forbidden
  `DUPN`/`SWAPN`/`EXCHANGE` immediates through `Ninst.immAccepted`
  ([`Blanc/CommonCore.lean`](../Blanc/CommonCore.lean)); the `Ninst.step`
  equations for the three stack-access instructions are `Ninst.step_dupn`,
  `Ninst.step_swapn`, and `Ninst.step_exchange`
  (Jaune's `Jaune/ExecFrame.lean`); accepted-immediate
  byte classification for the `noPushBefore` boundary walk is
  `toInstType_ne_p_of_decodeSingle` and `toInstType_ne_p_of_decodePair`
  ([`Blanc/Compiled.lean`](../Blanc/Compiled.lean)). There is no recipe:
  the guard fires inside the compiler equation and the classification
  closes by `decide` over a private `DecidableEq`, neither exposing a
  reusable goal trigger.

### C2. I need deployment/message correspondence

- Successful no-code-address message and CREATE settlement with the actual
  rules-selected touch retained:
  [`Blanc/DeploymentTouch.lean`](../Blanc/DeploymentTouch.lean).
  `processMessage_ok_touch_of_exec` consumes successful transfer, no separate
  code address, actual raw execution and a clean raw result.
  `processCreateMessage_ok_touch_of_exec_and_charge` additionally consumes
  successful code charging on that touched result and installs its charged
  output with the actual `setCode` normalization.
  The forward settlement bridges do not assume touch recording is disabled;
  they require actual execution and charge witnesses. These APIs do not supply
  final transaction sweeping or a historical starting state. The
  `touch-preserving-message-settlement` recipe recognizes only the direct
  successful outer forms; it does not establish the theorem's entry,
  execution, address, output or charge obligations.
- Generic deployment-message facts:
  [`Blanc/DeploymentMessage.lean`](../Blanc/DeploymentMessage.lean).
  An inner creation error crosses through
  `processCreateMessage_ok_of_processMessage_error`; a raw creation-code
  REVERT with no separate code address crosses through
  `MessageExecution.processMessage_revert_of_exec_afterTransfer_of_noCodeAddress`
  without changing the message's precompile switch.
  `benvAfterTransfer_stat` preserves the complete static block environment
  across a successful message-entry transfer.
  The same module owns the shared receipt key, intrinsic/calldata gas
  projections and type-2 effective gas price;
  `deploymentTxPreludeBout` delegates to the lower
  `ExecutionTrace.transactionPreludeBout`.  Redemption and deployment owners
  should retain compatibility names only as thin aliases to these primitives.
- To state a scenario of root messages, each from the previous settled world, as one fold:
  [`Blanc/Lift/RootMessages.lean`](../Blanc/Lift/RootMessages.lean). `RootMsg` is a creation
  (`processCreateMessage`) or a call (`processMessage`) with its input built from the fork and
  the previous world; `runMessages fork W ms` returns the final world, or `none` at the first
  message that does not return `.ok` with no error. Message level only: no transaction admission.
- For a `CREATE2` address from an init-code digest, admitted `CREATE2` spawns,
  or an EIP-1167 clone of a lifted implementation, use
  [`Blanc/Lift/Create2Deploy.lean`](../Blanc/Lift/Create2Deploy.lean) and
  [`Blanc/Lift/Clone1167.lean`](../Blanc/Lift/Clone1167.lean), described under
  [C9.11](#c911-i-need-deployment-create-create2-or-a-clone).

### C5. I need to preserve a compile-shape equality under a known prefix

Import [`Blanc/CommonProofs/Base.lean`](../Blanc/CommonProofs/Base.lean) and apply
`Func.compileShape_prepend_congr l` to an existing equality
`p.compileShape = q.compileShape`. It returns
`(l +++ p).compileShape = (l +++ q).compileShape` without re-proving the
instruction-line recursion.

The `compile-shape-prepend-congruence` recipe matches only a direct equality
whose two sides apply `compileShape` to `prepend` with the same syntactic
prefix and distinct syntactic tails. It does not reduce either tail, search the
local context for the needed tail equality, compare different prefixes, or fire on
a no-prepend or reflexive-tail goal. The caller supplies the tail-shape
equality explicitly.

### C7. I need a storage-determined contract specification

`ContractSpec` carries an invariant over storage, in-flight callvalue, and
ETH balance, and a contract whose invariant reads only storage still owes the
record's eight balance obligations.  `ContractSpec.ofStorageOnly` in
[`Blanc/StorageOnlySpec.lean`](../Blanc/StorageOnlySpec.lean) packages that
argument once: `getStor_subBal_addBal` preserves the observed owner's storage
when `State.Protected` holds at entry; the corresponding credit donor uses
the same protected-owner domain. The specification's balance obligations
already supply this protection, so the adapters need no extra hypothesis.
`ofStorageOnly_preInv_iff`/`ofStorageOnly_postInv_iff`
reduce the frame invariants to the storage predicate, and
`ofStorageOnly_funcSound` reduces each per-target obligation to the bare
storage walk, declining the `nof`-class side condition a storage-determined
invariant never needs.  The module's no-write and `STATICCALL` sections
discharge targets that never write storage, and `ofStorageOnly_of_call`
carries the invariant across a child `call` under the deeper-frame hypothesis
and an explicit `CoveredFork` premise.  `ofStorageOnly_of_call_sameBenv` is
its general form: the deeper-frame hypothesis need only cover frames at the
caller's `benvStat`, which is what a trace-admitted consumer whose entry
condition reads the block environment can discharge.

For deployed bytecode with a certified `CodeSem`, use `ContractSpecSem.ofStorageOnly`
in the same module. Its `ofStorageOnly_preInv_iff` and `ofStorageOnly_postInv_iff`
reduce semantic frame invariants to the supplied storage predicate. These adapters
supply only balance/transfer transport; the caller still proves concrete frame
preservation from the incoming invariant and independently established admission.

### C8. A `decide +kernel` over a committed artifact reports kernel deep recursion


For a lifted certificate over deployed bytes, read the code through
`code.data.toList` (`ByteArray.toList` is quadratic in the kernel) and decide a
large entry on the trie-reading copies of
[`Blanc/Lift/CheckFast.lean`](../Blanc/Lift/CheckFast.lean); the measured rule is
in the certificate entry of
[C9.1](#c91-i-need-the-lifted-language-and-a-checked-certificate).

### C9. I need to verify deployed bytecode Blanc did not compile

The route is lift, then reason about the lifted program. A certificate is
checked against the bytes by the kernel, a generic theorem turns every real
execution into a run of the lifted program, and the contract's properties are
proved over that run. The
modules below supply the shared lifted-program vocabulary.

Route map. Find the need below; each module is cited in the sub-branch whose
need it serves, and [`docs/MODULE_INVENTORY.md`](MODULE_INVENTORY.md) lists
every shared module with its own summary and the branches that cite it.

- [C9.1](#c91-i-need-the-lifted-language-and-a-checked-certificate): the lifted language and a checked certificate.
- [C9.2](#c92-i-need-to-connect-a-real-execution-with-a-lifted-run): to connect a real execution with a lifted run.
- [C9.3](#c93-i-need-the-free-pointer-or-write-site-checkers-soundness): the free-pointer or write-site checker's soundness.
- [C9.4](#c94-i-need-what-one-lifted-step-does): what one lifted step does.
- [C9.5](#c95-i-need-hashed-storage-slots-write-locality-or-demanded-zero-cells): hashed storage slots, write locality or demanded zero cells.
- [C9.6](#c96-i-need-the-calls-child-frames-and-logs-of-a-lifted-frame): the calls, child frames and logs of a lifted frame.
- [C9.7](#c97-i-need-every-execution-prefix-to-a-node-whatever-the-outcome): every execution prefix to a node, whatever the outcome.
- [C9.8](#c98-i-need-facts-at-a-checked-cursor-of-an-actual-successful-execution): facts at a checked cursor of an actual successful execution.
- [C9.9](#c99-i-need-to-walk-a-successful-lifted-run): to walk a successful lifted run.
- [C9.10](#c910-i-need-a-vyper-02-runtimes-idioms): a Vyper 0.2 runtime's idioms.
- [C9.11](#c911-i-need-deployment-create-create2-or-a-clone): deployment, CREATE, CREATE2 or a clone.
- [C9.12](#c912-i-need-free-pointer-memory-images-or-solc-04-writer-walks): free-pointer memory images or solc-0.4 writer walks.
- [C9.13](#c913-i-need-a-whole-contract-property-without-per-path-walks): a whole-contract property without per-path walks.

#### C9.1. I need the lifted language and a checked certificate

- The lifted language: `SFunc` (a tree whose jumps are resolved to entry
  indices), `SFunc.Run`/`SProg.Run` and the derivation-carrying
  `SFunc.RunP`/`SProg.RunP` in [`Blanc/Lift/Basic.lean`](../Blanc/Lift/Basic.lean).
  It is a sibling of `Func`, not a replacement: nothing in the compiler's
  language changes.
- The certificate and its checker: `Cert`, `Entry`, `checkNode` and
  `Cert.check` in [`Blanc/Lift/Check.lean`](../Blanc/Lift/Check.lean), with
  the per-instruction abstract transfer (`ninstTransfer`, `ninstTransfer_run`)
  in [`Blanc/Lift/Transfer.lean`](../Blanc/Lift/Transfer.lean) (it accepts `XOR`,
  Vyper's `!=`, the `SLT`, `EXTCODESIZE`, `TLOAD`, and `TSTORE` steps needed
  by lifted bytecode, `EXTCODEHASH` (whose exact pushed word
  `run_extcodehash_val` gives: zero for an empty account, else the code's keccak-256), `CREATE2` through `create2Transfer`, which pops
  endowment, offset, size and salt and pushes the new address or zero, and
  `DELEGATECALL` through `delegatecallTransfer`, which pops gas, target, input
  offset and size, output offset and size and pushes the flag; these
  success-only lifted transfers do not extend native `regularTransfer_safe`).
  The checker reads each node's bytes from the code, so a certificate cannot
  claim `CALL` where the code holds `DELEGATECALL`
  (`checkNode_call_at_delegatecall`, [`Blanc/Lift/DelegatecallControl.lean`](../Blanc/Lift/DelegatecallControl.lean)). Decide
  `Cert.check` per entry with `decide +kernel`; one decision over the whole
  certificate does not fit in memory for a real contract, and read bytes with
  `code.data.toList` (`ByteArray.toList` is quadratic in the kernel). For a
  contract of more than a few kilobytes, decide each entry on the trie-reading
  copy `checkNodeT` (`CodeTries.ofCode`) in
  [`Blanc/Lift/CheckFast.lean`](../Blanc/Lift/CheckFast.lean): plain byte reads
  are linear per instruction and a 1,474-node entry of the 6,358-byte beacon
  deposit contract passed 16 GiB, while the trie decides it in 6 s / 3.4 GiB.
  `kernel_rfl_and`
  ([`Blanc/Lift/KernelBatch.lean`](../Blanc/Lift/KernelBatch.lean)) closes a
  conjunction of closed equalities in one kernel check.
  `LTrie`, `CodeTries` (`CodeTries.ofCode`) and, for an individual destination,
  `jumpdestOkT` with its equality `jumpdestOkT_eq` to `jumpdestOk`, live in the
  Lift-free [`Blanc/CodeTrie.lean`](../Blanc/CodeTrie.lean), with `windowT` and
  `getInst_windowT` (the instruction at a position, decoded from its 33-byte trie window).
- Bytecode whose control flow runs through `PC`, constant arithmetic, constant
  `JUMPI` conditions or memory (Vyper 0.2 internal calls keep the return tag in
  memory): `SFunc.pcAt` (a `PC` carrying its own pc) in `Blanc/Lift/Basic.lean`;
  constant arithmetic (including top-first `DIV`, with zero denominator),
  comparison and bitwise `AND`/`OR` folds (`foldConst`) and
  decided `JUMPI`s (`AVal.jumps?`) are part of `checkNode`; the memory-tracking
  checker `checkNodeM`/`Cert.checkM` over declared
  maps (`absMem`, `memTop`, `memCompat`; `checkNode_eq_checkNodeM` with tracking
  off) in [`Blanc/Lift/CheckMem.lean`](../Blanc/Lift/CheckMem.lean); the invariant
  `MemMatches`, the return address in frame or map (`RetIn`) and the
  per-instruction facts `absMem_sound`, `memTop_sound`,
  `staticcall_run_memory` (a `STATICCALL` changes memory only inside its
  output window), `Mem.write_agree` (needs no `Mem.Wf`), `Mem.extends_agree` and
  `Mem.AgreeOutside.trans`/`.mono` in
  [`Blanc/Lift/MemMap.lean`](../Blanc/Lift/MemMap.lean); `lift_soundM` in Sound,
  trie mirrors `checkNodeMT`/`jumpsOkNodeMT`
  in CheckFast. Produce with `scripts/lift/lift.py --memret callnext --const-mem`
  (`--frame-loops` for Vyper 0.2.x frame save/restore loops, `--mem-calls` to keep the
  map across `GAS` and constant-window `STATICCALL`).
  The state-gas-capability forms are `staticcall_run_memory_noStateGas`,
  `absMem_sound_noStateGas` and `step_mem_sound_noStateGas`. They preserve
  the same bounded output-window and memory-map invariants using actual
  selected access/delegation rules. Existing covered theorem statements
  forward to these cores. Select these routes from the actual instruction
  and memory-map premises; a general equality or memory-preservation goal
  alone does not distinguish them from writes, extension or pure steps.
- Decide a certificate in ranges of entries rather than one theorem per entry: `Cert.rangeOk`
  (the node check and, with its `j` flag, the jump check of every entry of a tail, memory maps
  included; a non-memory certificate runs it with no maps and tracking off), its trie-reading copy
  `Cert.rangeOkT` with `Cert.rangeOkT_eq`, the chain link `Cert.rangeOk_drop_take` over
  `(c.drop k).take n`, the end `Cert.rangeOk_drop_of_le`, the assemblies `Cert.checkM_of_rangeOk`,
  `Cert.check_of_rangeOk` and `Cert.jumpsOk_of_rangeOk`, in
  [`Blanc/Lift/CheckRange.lean`](../Blanc/Lift/CheckRange.lean). The registered producer emits it
  with `check.ranges B` (one `decide +kernel` per range of at most `B` summed tree nodes; `check.entries`
  re-exports named entries; `check.fuse_jumps` runs the jump checks in the ranges for a
  hand-written `Jumps` module, which then proves `jumps_ok` by `Cert.jumpsOk_of_rangeOk`), replacing the per-entry theorems, their `cert[i]'(by decide +kernel)`
  index proofs and the per-entry `rest_`/`jrest_` chain.
- Jump destinations: Jaune's own `jumpable_eq_jumpdestOk` (`Jaune/Machine.lean`)
  replaces its exponential `jumpable` by the linear `jumpdestOk` scan, for every
  byte string; Blanc keeps no copy.

#### C9.2. I need to connect a real execution with a lifted run

- On a fork with a state-gas record, for a certificate with no call-family node (`ProgNoExec`,
  `treeNoExec`, now in `Blanc/Lift/Sound.lean`): `lift_sound_noExec`, on the general `lift_sound_lane`.
- Execution to lifted run (safety), in [`Blanc/Lift/Sound.lean`](../Blanc/Lift/Sound.lean).
  For an actual successful execution with selected `rules.stateGas = none`,
  use `lift_sound_inM_noStateGas` / `lift_sound_in_noStateGas` to retain
  `StepIn`, or `lift_soundM_noStateGas` / `lift_sound_noStateGas` for the
  ordinary lifted run. `NodeClaim0NoStateGas`, `NodeClaimNoStateGas`, and
  `node_soundM_noStateGas` own the capability-level recursion; the original
  modern `NodeClaim0`/`NodeClaim` definitions and theorem statements retain
  their meaning. The `lift-node-no-state-gas` recipe matches only the two
  direct capability carriers; a general `SProg.Run` or `RunP` goal does not
  select this route from other constructive program proofs. These successful
  execution theorems assert neither opcode availability nor no-deletion.
- Lifted run to execution (liveness, exact gas): `SFunc.RunExact`,
  `Cert.jumpsOk` and `lift_exact` in [`Blanc/Lift/Exact.lean`](../Blanc/Lift/Exact.lean);
  on a fork with state gas, for a certificate with no call-family node, `lift_exact_noExec` (no fork
  premise; `ProgNoExec` from `progNoExec_of_all (by decide +kernel)`, a fact about the certificate's
  nodes, so push data that decodes as a call does not matter), and `lift_exact_lane`,
  `lift_exactM_core_lane` and `node_exactM_lane` carry the proof for both premises;
  `RETURN` with its expansion charged is `rx_return_charged` (`chargedRetExt`, `chargedRetPost`);
  the per-instruction walk steps (`rx_push`, `rx_sload_cold`, `rx_callRet`, …)
  over the gas-carrying state `St`, a frame's entry state as an `St` (`pre_eq_St`), the
  `St` projections (`St.stack`, `St.memory`, `St.gasLeft`, `St.returnData`, `St_error`,
  `St_state`, `St_getCode`, `St_getStor`: `St` replaces only the machine), the
  word read-back facts `sliceD_word_same` and `read_covered`, and one solc dispatcher
  comparison (`cmp_miss`, `cmp_hit`) are in
  [`Blanc/Lift/ExactWalk.lean`](../Blanc/Lift/ExactWalk.lean). The fixed-cost
  `rx_sload_cold` and `rx_sload_warm` constructors require both
  `sevm.benvStat.rules.stateGas = none` and selected access pricing
  `sevm.benvStat.rules.access = .eip2929`; flat historical schedules do not
  have their exact 2100/100 charges. More steps
  (`rx_shl`, `rx_byte`, `rx_mstore8`, `rx_calldatacopy`, `rx_log1`, …) are in
  [`Blanc/Lift/ExactWalkOps.lean`](../Blanc/Lift/ExactWalkOps.lean). `rx_shl`/`rx_shr`
  require the selected `rules.op.shifts = true` capability; arbitrary
  continuation evidence does not supply it. The generic success-inversion statements remain unchanged.
  The cut-run `rxc_shl` requires the same capability. To obtain it from a fixed
  run witness rather than a premise, use
  [`Blanc/Lift/ExactMustRun.lean`](../Blanc/Lift/ExactMustRun.lean):
  `SFunc.mustRun p K f` (a Boolean walk: every successful `SFunc.RunExact` from
  `f` executes an instruction selected by `p`, with jump/call targets in the
  entries `K`, checked by `SFunc.mustRunEntries p fs K`; `REVERT` leaves have no
  successful run; loops are covered), `SFunc.RunExact.of_mustRun` for any fact a
  selected step implies, and its shift instance `SFunc.RunExact.shifts_of_mustRun`
  (`Ninst.isShift`, `Ninst.RunCompiled.shifts_of_isShift`); discharge both checks
  with `decide +kernel` on the concrete tree. `CoveredFork.rules_shifts`
  (`Blanc/Semantics.lean`) supplies the capability from fork coverage.
  The cut-run forms (`rxc_*`, `SFunc.RunExact.toCut`) in
  [`Blanc/Lift/ExactWalkCut.lean`](../Blanc/Lift/ExactWalkCut.lean) and
  [`Blanc/Lift/ExactWalkCutOps.lean`](../Blanc/Lift/ExactWalkCutOps.lean), which
  also holds the pointer arithmetic the steps take as premises
  (`toB256_div_two`, `one_add_toB256`; word addition and subtraction of naturals are Jaune's
  `Nat.toB256_add_toB256` and `Nat.toB256_sub_toB256`), the
  SHA-256 precompile step's premises and world facts (`ShaReady`, `ShaCallPost`,
  `staticcall_sha_step`), and `BaseRel`, the world a step that writes no storage and emits
  no log keeps.
- Concrete runs checked by kernel evaluation of Jaune's own `Evm.step`:
  `ConcreteRun.stepN` (at most `n` continuing steps) and `stepN_add`, in
  [`Blanc/ConcreteRun.lean`](../Blanc/ConcreteRun.lean).
- A concrete frame run over a lifted certificate, as a gas-exact `SProg.RunExact`
  (an executable witness: liveness from one start state, by kernel evaluation): the
  interpreter `Witness.wrun` over the certificate's decoded tree, its single step
  `wstep`, the configuration `Cfg` with the accessed-set and storage/account shadows
  (`StorShadow`, `AcctShadow`, `storOf`, `AcctAgree`), Jaune's `State.set`
  directly (kernel-reducible at the pinned Jaune), the kernel-cheap memory write
  `memWriteB` (with `mem_write_eq_B`), and the `CALL`
  preparation `callPrep`/`callPrep_spec`
  in [`Blanc/Lift/WitnessArms.lean`](../Blanc/Lift/WitnessArms.lean). Transfer
  shadows use `storSetBal` and `storTransfer`: account deletion filters every
  cell at that owner, debit precedes credit, and zero value leaves the shadows
  unchanged. `lookupS_filter_owner`, `storSetBal_agree`, and
  `benvAfterTransferS_stor` prove these exact storage projections;
  `acctView_clearIfEmpty` preserves the account-view fields. The raw
  `storOf_setBal` now returns a conditional zero for deletion.
  `frameEnterB_done_acc` preserves accessed sets; use the separate
  `frameEnterB_done_ok_state` for a successful child's actual transfer world.
  The soundness theorem `Witness.wrun_exact` (from `wrun_done` over `RunK`/`Agree`), the
  shadow seeds `stateFoldAcct`/`stateFoldStor`, and code children supplied as data
  (`ChildAgree`) in
  [`Blanc/Lift/Witness.lean`](../Blanc/Lift/Witness.lean). A code child discharged by its
  own witness run: `childStart` and the DELEGATECALL
  preparation `dcallPrep`, in
  [`Blanc/Lift/WitnessChild.lean`](../Blanc/Lift/WitnessChild.lean).
  `Witness.wrun_exact` remains generic. Historical settlement still needs a
  producer that retains `recordTouch` and the touched-account metadata. Child starts
  (`childStart` and `NodeWalk.childCfg`) use
  `storTransfer` alongside `acsTransfer`; reusing the pre-transfer storage
  shadow requires a separate no-change proof. The frame-level spawn
  fact `SpawnedBy sevm devm x child` (`Xinst.step` spawns a frame entering as `child`) in
  [`Blanc/Lift/WitnessSpawn.lean`](../Blanc/Lift/WitnessSpawn.lean); the literal-free
  scaffolding for deciding a long `wrun` as kernel chunks between literal boundaries
  (`Bnd1`/`cfgOf1` with the refund counter and the accounts to delete optional (the created set always
  empty)) in
  [`Blanc/Lift/WitnessBoundary.lean`](../Blanc/Lift/WitnessBoundary.lean). Code tries given as
  generated literals (checked once by kernel `rfl`): `CodeTries.ofData` in
  [`Blanc/Lift/CodeTriesData.lean`](../Blanc/Lift/CodeTriesData.lean); the data checked in one
  linear pass that also yields the length bound (`LTrie.build`, `LTrie.build_eq`,
  `LTrie.eq_ofList_of_build`, `LTrie.length_le_of_build`; producer option `check.trie_build`) in
  [`Blanc/Lift/CodeTriesBuild.lean`](../Blanc/Lift/CodeTriesBuild.lean). The machine a code
  child of `CALL` starts with carries the caller's block environment (`childStart_stat`, in
  [`Blanc/Lift/WitnessFork.lean`](../Blanc/Lift/WitnessFork.lean)).
- Assemble the free-pointer check of a long certificate from range decisions: `fpRange`
  (entries `k .. k + n - 1` under their annotations, one kernel decision), `fpFrom` over the tails
  `(c.zip ann).drop k`, the link `fpFrom_range`, the end `fpFrom_of_le` and the assembly
  `fpCert_of_fpFrom` in [`Blanc/Lift/FreePtrChain.lean`](../Blanc/Lift/FreePtrChain.lean), emitted by
  the registered `scripts/lift/fp_annot.py` (registry key `fp`; ranges of at most
  `CHECK_RANGE_BUDGET` summed cost proxy). For any other annotated check, instantiate the generic kit there:
  `chainRange`/`chainFrom` over a check function, with `chainFrom_range` and `chainFrom_of_le`.
- Assemble the write-site check of a long certificate the same way: `wsRange`, `wsFrom`,
  `wsFrom_range`, `wsFrom_of_le` and `wsCert_of_wsFrom` in
  [`Blanc/Lift/WriteSiteChain.lean`](../Blanc/Lift/WriteSiteChain.lean), emitted by the registered
  `scripts/lift/ws_annot.py` (registry key `ws`).

#### C9.3. I need the free-pointer or write-site checker's soundness

- For the free-pointer checker's memory effect, use
  [`Blanc/Lift/FreePtrMem.lean`](../Blanc/Lift/FreePtrMem.lean): `FpWord`
  (the pointer word's meaning), `memEff_fpWord`, `memEff_touched`,
  `memEff_obs` and `memEff_mload_top`. `memEff_fpWord_noStateGas` uses the
  executing rules' state-gas absence with the same checker and memory-effect
  proof; `memEff_fpWord` retains its original covered-fork interface.
- For the free-pointer checker's facts and their soundness, use
  [`Blanc/Lift/FreePtr.lean`](../Blanc/Lift/FreePtr.lean),
  [`Blanc/Lift/SymTransfer.lean`](../Blanc/Lift/SymTransfer.lean), and
  [`Blanc/Lift/FreePtrFacts.lean`](../Blanc/Lift/FreePtrFacts.lean):
  `Fact.Holds`/`AllHold` (the meaning of facts under a symbol valuation),
  `bnd2_sound`/`entails_sound` (the interval reading and entailment),
  `opFacts_sound` (the facts about an instruction's fresh result),
  and `learn1_sound` (what a `JUMPI` arm learns). The interval folds both bound
  checkers share (`bndOf` over `bnd` facts, `bnd2` refined once through
  `lt`/`le` facts) live in
  [`Blanc/Lift/BndInterval.lean`](../Blanc/Lift/BndInterval.lean):
  `bndOfG`/`bnd2G` over a small projection interface, with the shared fold
  inductions `bndOfG_sound`/`bnd2G_sound`; each checker's `bndOf_sound`/
  `bnd2_sound` keeps its statement, discharging one per-fact bridge over its
  own `Fact` type.
  For selected state-gas absence, `SymTransfer.transfer_val_noStateGas` in
  the same shared owner carries symbols through the actual successful
  instruction using the generic stack-transfer theorem. It retains the
  frame-size, one-fresh-result and index-map hypotheses. Its existential result requires
  these joint transfer/run premises, so discovery remains in this registry.
- For the free-pointer checker's soundness, use
  [`Blanc/Lift/FreePtrSound.lean`](../Blanc/Lift/FreePtrSound.lean) and
  [`Blanc/Lift/FreePtrSoundStep.lean`](../Blanc/Lift/FreePtrSoundStep.lean):
  `fpRun_sound` (every run of an accepted certificate reads a good free
  pointer, `FpStep`), `fp_run` (the big-step recursion), `fstep_sound`
  (one accepted step keeps the invariant `FpInv`), and the frame-length facts
  `mapM_length` (an `Option` `mapM` keeps length), `foldTop_length` and
  `transfer_length_mono`. The `rdsKeep_sound_noStateGas`,
  `fstep_sound_noStateGas`, `fp_run_noStateGas` and `fpRun_sound_noStateGas`
  variants use the executing rules'
  `stateGas = none`. They share the original induction and checker, retaining
  the actual `Exec` and `StepIn` witnesses; modern interfaces remain projections.
- For the write-site checker's step and join soundness, use
  [`Blanc/Lift/WriteSiteStep.lean`](../Blanc/Lift/WriteSiteStep.lean) and
  [`Blanc/Lift/WriteSiteJoin.lean`](../Blanc/Lift/WriteSiteJoin.lean): `WSt.Holds`/`WSt.Sat`
  (an abstract state's meaning), `wstep_sound` and `wstep_nonpush` (one step),
  `refine_sound`, `popped_sound`, `compat_sound`, `param_sat`, `init_sat`, `retOk_sound`,
  `resume_sound` and `callNext_obs` (joins, calls and returns); `map_of_zip_prefix` (an
  annotation's entry words name a prefix of the incoming ones).
  For a selected rule set with `stateGas = none`,
  `WriteSite.memEff_sound_noStateGas`,
  `WriteSite.getStor_of_writesStor_noStateGas` and
  `WriteSite.wstep_sound_noStateGas` keep the same actual instruction/run,
  frame, valuation, stack bound and accepted-step premises. The single proof
  tree uses common call-write effects, raw storage keeping and symbolic
  transfer; the modern statements remain wrappers. These routes require the
  checker/run premises; a bare memory or storage equality does not select them.
  Write-site refinement keeps comparison chains through three live-symbol closures and
  applies one learning round after `FreePtr.refineFacts`; `refine_sound` reuses
  `learn1_sound`, `zeros_sound` and `ones_sound` for that additional round without changing
  the free-pointer checker.
- For the write-site checker's run-level soundness, use
  [`Blanc/Lift/WriteSiteSound.lean`](../Blanc/Lift/WriteSiteSound.lean): `wsRun_sound`
  (every run of an accepted certificate's entry `0` is a `WsStep` run), `ws_run` (the big-step recursion: `WsStep`
  steps, `RetObs` at a return), `goto_run` (an accepted goto: `compat` or a tail call, under a
  summary below the jumper's, via `retLe_steps`, `argFree_steps`, `RetObs.of_retLe`,
  `RetObs.of_callee` and `tail_entry`), `Term.eval_argFree` (an entry-word-free term reads the
  same in every environment of a frame), and `SFunc.RunP.mono_at` (a run under a step relation
  implied at the run's own frame).
  The capability forms `WriteSite.wstep_keeps_noStateGas`,
  `WriteSite.ws_run_noStateGas` and `WriteSite.wsRun_sound_noStateGas`
  require selected `stateGas = none`
  instead of modern coverage. They retain the original accepted certificate,
  frame/run and summary premises, with the same `WsStep`/`RetObs` meanings. Historical membership supplies the
  capability through `HistFork.stateGas_none`. Old modern statements remain
  wrappers; no additional outcome or storage-survival premise is introduced.
- For the write-site observation at one `SSTORE` of a synthetic prefix (any outcome, any
  stopping point), use [`Blanc/Lift/WriteSiteReach.lean`](../Blanc/Lift/WriteSiteReach.lean):
  `WriteSite.ws_reach_noStateGas` (a `Reach` from entry `0` of an accepted write-site
  certificate to a configuration whose tree is `next (.reg .sstore) g` meets a root site,
  `WsObs (wsRoot ann) (Env.root sevm)`, on `stateGas = none`) and
  `WriteSite.ws_reach_start_noStateGas` (the same from `(Cursor.start c).conf pre`, the
  cursor reach's start). The invariant is `WriteSite.WsConf` (per level `WsLevel`, pending
  continuations `WsCont`), preserved by `WriteSite.wsConf_step` with `ws_run`'s step lemmas;
  `WriteSite.wstep_sstore_obs` is the pre-state-only observation of an accepted `SSTORE`.
  For a successful raw store, `WriteSite.successfulSstore_site`
  ([`Blanc/Lift/WriteSiteReachHistory.lean`](../Blanc/Lift/WriteSiteReachHistory.lean)) takes the checked
  code and write-site annotation, pc-zero entry, `stateGas = none`, and the actual
  `ParentPrefix` and `successfulSstore?` equation. It returns a root site with its
  slot denotation, guards and nonincrease implication at the same node's current
  storage cell. `ConfiguredHistoryTraceIn.rawFrame_successfulSstore_site` obtains
  the entry facts from raw-frame membership and the history's capabilities.
  This also covers stores in frames that later revert; it does not assert
  retention, hash separation, or coverage of unexecuted descriptors. These existential site results have no reliable registered
  goal-head trigger; use this branch rather than a broad `Exists` recipe.

#### C9.4. I need what one lifted step does

- For one lifted step's effect on memory, use
  [`Blanc/Lift/StepMemory.lean`](../Blanc/Lift/StepMemory.lean): the stack-pop
  forms `Devm.pop_cons`/`popToNat_cons`/`popToAdr_cons`, `genericCall_memory`,
  `genericCreate_memory`, `resume_create_memory`, the `run_*_memory` lemmas for
  `CALL`, `DELEGATECALL`, `STATICCALL`, `CREATE2`, `BALANCE`, `EXTCODESIZE`,
  `EXTCODEHASH`, `EXP`, `MSTORE8`, `CODECOPY`, `RETURNDATACOPY` and `MLOAD`, and
  `Mem.write_size_ge` (a write never shrinks memory). The
  `run_call_memory_noStateGas`, `run_delegatecall_memory_noStateGas`,
  `run_staticcall_memory_noStateGas` and `run_create2_memory_noStateGas`
  variants consume the executing rules' `stateGas = none`; their covered-fork
  counterparts are projections of the same proofs. `run_selfbalance_memory`
  preserves memory from the actual successful instruction, without a fork premise.
- For which bytes one lifted step wrote, use
  [`Blanc/Lift/MemWrites.lean`](../Blanc/Lift/MemWrites.lean): `Mem.WritesAt`/`AgreeBelow`
  (the capability forms `call_run_writesAt_noStateGas`,
  `delegatecall_run_writesAt_noStateGas` and `staticcall_run_writesAt_noStateGas`
  use the common actual-rule CallEffects owner; modern statements remain wrappers)
  and the `*_run_writesAt` lemmas for `MSTORE8`, the five copies and the output windows of
  `CALL`/`DELEGATECALL`/`STATICCALL` (every outcome, including a failed call).
- For the stack top after one lifted step of an environment or hashing instruction, use
  [`Blanc/Lift/StepTops.lean`](../Blanc/Lift/StepTops.lean): `run_{caller,address,not,shl,exp,
  calldataload,keccak256,sload}_top`, `Ninst.Run.getStor_of_storKeep` and `getStor_push`.
  `Ninst.Run.getStor_of_storKeep_noStateGas` takes only selected state-gas
  absence plus the same regular-non-SSTORE-or-actual-STATICCALL premise.
  Its STATICCALL arm uses the shared capability-level raw-storage theorem;
  the original modern statement remains a wrapper. A storage equality alone
  does not select this route without the actual instruction/run premises.
- For the return-data buffer across one lifted step, use
  [`Blanc/Lift/ReturnDataKeep.lean`](../Blanc/Lift/ReturnDataKeep.lean): `regular_returnData` and
  `Ninst.Run.reg_returnData` (every regular instruction keeps `returnData`).

#### C9.5. I need hashed storage slots, write locality or demanded zero cells

- Hashed storage slots: `mapSlot key base = keccak256(pad32 key ‖ pad32 base)`, solc's mapping
  slot and, with the arguments swapped (slot first), Vyper's, in
  [`Blanc/Lift/MapSlot.lean`](../Blanc/Lift/MapSlot.lean).
- For write-site provenance terms, use
  [`Blanc/Lift/WriteSite.lean`](../Blanc/Lift/WriteSite.lean),
  [`Blanc/Lift/WriteSiteTerm.lean`](../Blanc/Lift/WriteSiteTerm.lean),
  [`Blanc/Lift/WriteSiteObs.lean`](../Blanc/Lift/WriteSiteObs.lean), and
  [`Blanc/Lift/WriteSiteLocality.lean`](../Blanc/Lift/WriteSiteLocality.lean):
  `Term.den_subst` (instantiating a callee's term at a call site is sound).
- To preserve demanded zero cells using that locality, use
  [`Blanc/Lift/WriteSiteZero.lean`](../Blanc/Lift/WriteSiteZero.lean):
  `ZeroSlots` states the seed; `GuardObs.sstore_zero` combines
  `GuardObs K False` with the actual SSTORE storage update, for the written
  cell and every distinct cell, without a fork or hash premise.
  `GuardObs.step_zero` covers the other instructions on a `CoveredFork`,
  while its external arm requires the actual filled recursive slot and
  `Xinst.Run` preservation law. `runP_zero` and `progRunP_zero` fold through
  the actual lifted derivation, including callee returns and continuations,
  with explicit external-step and terminal semantic obligations.
  `runP_zero_of_step` is that fold from any one-step zero law, with no fork.
  For a run whose same-run observation excludes every external instruction,
  `GuardObs.step_zero_noExec`, `runP_zero_noExec` and `progRunP_zero_noExec`
  need no fork premise and discharge terminals by actual semantics; only the
  initial seed remains explicit.
  `terminal_zero` keeps the non-SELFDESTRUCT compatibility form;
  `terminal_zero_all` handles every actual successful terminal, including
  SELFDESTRUCT. Its storage law in
  [`Blanc/TerminalStorage.lean`](../Blanc/TerminalStorage.lean),
  `Linst.run_getStor_eq_or_empty` (and the SELFDESTRUCT-specific
  `selfdestruct_getStor_eq_or_empty`), permits empty-account clearing rather
  than asserting false storage equality. `runP_zero_of_children` and
  `progRunP_zero_of_children` discharge the terminal premise using that actual
  law; the initial seed and real external-step obligation remain explicit.
  These tools do not infer child effects, transaction settlement, a historical
  zero seed or hash separation from locality alone.
  `exec_zero_of_committed_child` uses the actual filled `RunWith Q` child and
  existing spawn/entry/settlement storage laws: STATICCALL, childless execution
  and complete-settlement rollback close automatically. Only a committing
  nonstatic child needs recursion, with its actual `Exec`, `Q` provenance,
  smaller depth, inherited fork and the transported seed at the same observed
  owner. `runP_zero_of_committed_children` and its `progRunP_` form compose
  that producer. Nonstatic steps require nonempty world code at the observed
  owner for protected childless storage and child-entry alignment; the child
  need not execute at that owner. Initial zero and committing-child recursion
  remain explicit, including every actual entered occurrence.
  On historical forks use the `_noStateGas` forms
  (`exec_zero_of_committed_child_noStateGas`,
  `runP_zero_of_committed_children_noStateGas`,
  `progRunP_zero_of_committed_children_noStateGas`): their premise is
  `stateGas = none` and the recursive obligation receives
  `child.sta.benvStat = sevm.benvStat` in place of a covered child fork; the
  covered-fork forms are corollaries. `GuardObs.step_zero_of_exec` is the
  fork-free one-step law with the external arm supplied by the caller.
- For solc's storage-string clearing tail, use
  [`Blanc/Lift/SolcStorageClear.lean`](../Blanc/Lift/SolcStorageClear.lean).
  `body_store_cut` derives the literal-zero value from the actual
  push/duplicate/store sequence and retains its continuation. Given the
  actual function-table entry and erasure of the step relation to `Ninst.Run`,
  `runP_zeroStores` strengthens the same source run with zero-store
  observations; `runP_zeroStores_noExec` also derives that the same source
  run contains no external instruction. `runP_nonInc` exposes the existing
  `GuardObs K False` interface. The source-shaped `head`, `body`, `tail` and `exitTree` retain
  the concrete destination bytes and back edge. These observations need no slot separation,
  but neither establish an initial zero seed nor preserve an arbitrary
  nonzero administrative word when a cleared cell aliases it.
  For the legacy layout with extra push/swap staging and an indirect return,
  `legacyBody_store_cut` derives the actual zero store and its continuation;
  `legacyRunP_zeroStores_noExec` follows both the head and return table entries.
  It shares the comparison and back-edge fold with the compact layout. For a string allocation that stores a length header then copies bytes,
  use [`Blanc/Lift/SolcStringAllocation.lean`](../Blanc/Lift/SolcStringAllocation.lean).
  It derives the actual copy-window bound, preserved header and unwrapped
  rounded next pointer from the actual header/copy memory equations and
  poststate memory potential. The empty-copy case uses the header store's
  size bound. Earlier recorded words below the header survive without a
  memory-well-formedness premise. The consumer must still derive the actual
  wrapper stacks, intermediate memory equality and initial potential; this
  facility does not assert a complete ABI decoder or historical execution.
  For solc ABI decoding of dynamic strings from calldata, use
  [`Blanc/Lift/SolcAbiStringStaging.lean`](../Blanc/Lift/SolcAbiStringStaging.lean).
  `allocMem` is one allocation's memory in code order (free-pointer read
  expansion, free-pointer update at 64, header, payload copy); `stage1` and
  `stage3` derive the header readbacks, pointer chain, final free pointer,
  ordered non-overlap and prior-word survival from `96 <= p1`, the payload
  lengths and the final post-`Pot` size bound. The exact code fragments
  `strFrag`, `rotFrag` and `staticFrag` come with `PotStep` run inversions
  (`strFrag_runP`, `rotFrag_runP`, `staticFrag_runP`) over an abstract stack
  tail, memory and continuation, so a wrapper with several decodes composes
  them instead of unfolding one long walk; prove the wrapper's code equals
  their composition by `rfl`. Their `_lift` forms (`strFrag_lift`,
  `rotFrag_lift`, `staticFrag_lift`) also return `Lifts`, the rebuild of the
  state-silent prefix under any stronger step relation (`lstep`,
  `Lifts.trans`). For the source-shaped memory-to-storage payload loop, use
  [`Blanc/Lift/SolcStoragePayload.lean`](../Blanc/Lift/SolcStoragePayload.lean).
  `runP_enriched` retains the actual step relation, entry state and outcome,
  classifying stores as zero or an indexed modular payload key. Its count is
  `(end.toNat - initialCursor + 31) / 32`, using the actual endpoint word.
  Inputs include the actual head table equation, a proved exit certificate
  and a `ReadWindow` law for executed memory loads. `readWindow_potStep`
  supplies that law from existing poststate memory potential; `body_case`
  derives the actual store and back-edge stack without a fork-specific
  storage-update law. Keys remain modular. Initial potential, concrete
  wrapper staging, whole-root coverage and protected-key separation must
  still be established by the consumer; none follows from this local loop.
  When a caller continues after such a storage-string helper, use
  [`Blanc/Lift/SolcStorageReturn.lean`](../Blanc/Lift/SolcStorageReturn.lean)
  for what the helper returns: `legacyRunP_returned` gives the returned stack
  and unchanged memory of a legacy clearing run, `payload_exit` reaches the
  payload loop's exit tail with the same stack tail under `Keeps` memory, and
  `runCutP_done` turns a finished cut run into an ordinary run. It also holds
  fork-free `SLOAD`/`SSTORE` walk inversions with exact memory
  (`ri_sload_any`, `ri_sstore_any`) and the branch rebuilder
  `qbranch` for strengthening a run in place.
  At a raw frame of a `ConfiguredHistoryTraceIn`, the root form of both
  classifiers comes from the history:
  [`Blanc/ExecutionStagedRootFacts.lean`](../Blanc/ExecutionStagedRootFacts.lean)
  `ConfiguredHistoryTraceIn.rawFrame_entryFacts` gives pc zero, the selected
  fork, `stateGas = none`, fresh stack and memory and `gasMeasure < 2 ^ 256`
  from `BodyStageCapabilities` alone. [`Blanc/ExecutionStagedSstoreAttribution.lean`](../Blanc/ExecutionStagedSstoreAttribution.lean)
  `StagedBodyTrace.rawFrames_closed` (with the stage forms) closes the raw
  frames under descent.

#### C9.6. I need the calls, child frames and logs of a lifted frame

- For a callee that cannot return, use
  [`Blanc/Lift/NodeRet.lean`](../Blanc/Lift/NodeRet.lean): `RetClosed` (a node
  predicate with `checkNode`'s return discipline), `SFunc.RunP.ret_mem` (a
  returning run starts from a frame holding `.ret`) and
  `SFunc.RunP.not_returned_of_noRet` (a callee whose frame has no `.ret` never
  returns), bytes-free and for any step relation.
- An `EXTCODESIZE` step with the actual warm/cold account access is in
  [`Blanc/Lift/CodeSizeWalk.lean`](../Blanc/Lift/CodeSizeWalk.lean).
  `temporalAccountAccessBase` and `temporalAccountAccessCost` name the selected
  successor world and charge; `temporal_extcodesize_runCompiled` supplies the
  compiled step from the code-size word, stack-room and covered-fork facts.
  `ri_extcodesize` inverts the actual instruction into that world, exact word,
  unchanged memory and residual gas. `rx_extcodesize` consumes an exact
  continuation at the selected warm/cold charge.
  `temporalAccountAccessBase_state`, `temporalAccountAccessBase_output` and
  `temporalAccountAccessBase_logs` project the unchanged state, output and logs
  through account warming. For the separate flat-pricing route, use
  `Ninst.runCompiled_extcodesize_flat` in
  [`Blanc/ForwardFlatAccess.lean`](../Blanc/ForwardFlatAccess.lean), with explicit
  flat prices and disabled BAL recording. Its successor retains the original
  base and actual code-size word; use `Ninst.exec_of_stepRun` for continuation.
  Neither route proves nonzero code size, callee liveness or the concrete
  constructor execution.
- A `STATICCALL` to an arbitrary callee, whose code is unknown: its abstract outcome
  (`StaticCallPost`: flag, returned bytes as output window and return data, every storage
  map and the log list kept) and, for a set flag, the successful static child message
  (`StaticAnswered`), inverted (`ri_staticcall`) and forward over a caller-supplied step
  (`rx_staticcall`), in [`Blanc/Lift/StaticCall.lean`](../Blanc/Lift/StaticCall.lean).
  `StaticCallPost.output` retains the parent's enclosing output when the flag
  is set; child bytes populate memory and `returnData`. It reuses
  `Resume.call_output` in `Blanc/LadderBase.lean`.
  `ri_staticcall_bounded` additionally derives `out.length < 2^256` from the
  actual static-call producer, for the same outcome and full return data. This
  bound is independent of the caller's output window and needs no callee premise.
- A mutable `CALL` to an arbitrary callee: `MutableCallPost` (flag on top of the
  rest; for a set flag, the output window written with a prefix of the full
  return data and the caller's own output kept) and its inverse `ri_call_post`, in
  [`Blanc/Lift/MutableCallPost.lean`](../Blanc/Lift/MutableCallPost.lean). Callee
  storage effects are deliberately unstated; consume them through a turn fold over
  the child derivation.
  For literal call-success and return-width guards around that primitive, use
  [`Blanc/Lift/StaticCallGuard.lean`](../Blanc/Lift/StaticCallGuard.lean):
  `staticCallGuard_invP` keeps the original instruction predicate and witness,
  full reply, bounded producer and original continuation; `returnWidthGuard_invP`
  derives the ABI minimum width from the actual guard. Their `_exact` forms
  consume the genuine compiled call, actual returned stack/gas and continuation.
  Request/output windows and `PtrMem` are parameterized; replies need not have
  exactly32 bytes, and the returned world is not replaced by its pre-call world.
  For an actual `Line.Run` through the comparison, use
  `returnWidthCompareLine_inv` with `returnWidthCompareLine` and `PtrMem`.
  It retains the actual post-state and comparison stack, including the full
  returndata length converted to a word. Combine the bounded producer result
  with the actual taken branch to derive the minimum width; the line alone
  does not establish it. `returnWidthGuard_invP` reuses this single inversion
  while retaining the residual cut's original instruction predicate.
  The required literal tree and failure facts are not selected reliably by a
  general `RunCutP` or `RunExact` goal head, so these entries remain registry-only.
  `CALLER` (`rx_caller`, `ri_caller`), `KECCAK256` inverted (`ri_keccak`), `LOG3`
  (`rx_log3`, `ri_log3`), `SSTORE` forward at its selected cost (`rx_sstore`), `RETURN`
  inverted (`ri_return`), and the memory facts `Mem.reads_data`/`Mem.read_write_word_of_wf` are in
  [`Blanc/Lift/WalkSteps.lean`](../Blanc/Lift/WalkSteps.lean), which also holds
  exact forward `TIMESTAMP` (`rx_timestamp`, actual block-header time and two gas),
  `SLT`, `LOG2`, `TLOAD` and `TSTORE` inverted (`ri_slt`,
  `ri_log2`, `ri_tload`, `ri_tstore`; `getStor_setTransVal`, `getCode_setTransVal`) and
  `StorStep sevm b b' s`, a chain of loads and stores that changed only the executing
  contract's storage (to `s`) and no log, built with `StorStep.refl`/`.sload`/`.sstore`/
  `.trans`/`.congr`/`.of_getStor` and read with `StorStep.getStorVal`
  (`getStorVal_eq_getStor` unfolds a word read).
  `ri_log2_post` retains the precise added log (current target, both topics,
  actual read bytes) and the read-expanded memory, leaving only residual gas
  existential. `ri_log2` is its compatibility projection. Prove memory fit
  before simplifying that returned memory to the input memory. This inverse
  needs an existing instruction run and does not manufacture gas affordability;
  its existential endpoint alone is not a reliable recipe trigger.
- The byte walk `callKindsCheck code` (it refuses every external instruction but
  `CALL`/`STATICCALL`) reads `code.data.toList`, so the kernel decision is
  linear, in [`Blanc/Lift/SpawnKindsM.lean`](../Blanc/Lift/SpawnKindsM.lean).
- The byte walk `guardCheck code` (each `CALL`/`STATICCALL` at an instruction
  start is followed by `PUSH2; JUMPI` falling through to `PUSH1 0; DUP1; REVERT`, or is an
  identity copy `PUSH1 4; GAS; CALL`) is in [`Blanc/Lift/GuardedCalls.lean`](../Blanc/Lift/GuardedCalls.lean).
- Restrict external instruction families along a checked certificate cursor:
  [`Blanc/Lift/CallRestriction.lean`](../Blanc/Lift/CallRestriction.lean) defines
  `SFunc.execsSatisfy` and `Cursor.ExecsSatisfy` (active function and pending
  returns). `SStep.execsSatisfy` preserves the restriction;
  `Cursor.execsSatisfy_of_reachable` starts it from the checked certificate;
  `CursorOK.execsSatisfy` turns actual instruction decoding into `allowed x = true`.
  This constrains same-frame instruction families, not child commitment or
  effects, and requires the check on every certificate function.
  The same owner separately defines `SFunc.lastsSatisfy` and
  `Cursor.LastsSatisfy` for terminal families, with `SStep.lastsSatisfy` and
  `Cursor.lastsSatisfy_of_reachable` propagating a certificate-wide check.
  `SFunc.noSelfdestruct` / `Cert.noSelfdestruct` specialize this walk to
  reject terminal `SELFDESTRUCT`; `Cursor.noSelfdestruct_of_reach` retains
  that checked restriction at active and suspended trees. This terminal
  check is separate from `Cert.callOnly`, which still permits every halt.
  `CursorOK.lastsSatisfy` applies that restriction to actual `Linst.At`
  decoding through the shared `CursorOK.tree_of_last` donor;
  `CursorOK.not_selfdestruct` gives the terminal exclusion. For a whole
  same-frame chain use `not_selfdestruct_of_parentPrefix_noStateGas` with
  `Cert.check`, the actual certificate's `noSelfdestruct` check, pc-zero
  entry, installed-code equality, selected state-gas absence and the actual
  `ParentPrefix`. It covers every eventual frame outcome. This is local
  decoded-terminal exclusion, not account-deletion or contract preservation;
  child routing and inherited deletion safety require their own proofs.
  `call_or_staticcall_of_parentPrefix_noStateGas` is the matching fork-free
  spawn restriction: a same-frame prefix of a `Cert.callOnly` certificate
  decodes only `CALL`/`STATICCALL`, every outcome.
- A reentrancy lock checker over a certificate:
  the checker `LockCheck.Spec` (one Boolean walk with
  producer annotations from `scripts/lift/lift.py --lock-spec`) in
  [`Blanc/Lift/LockCheck.lean`](../Blanc/Lift/LockCheck.lean); the fact
  semantics in [`Blanc/Lift/LockCheckSound.lean`](../Blanc/Lift/LockCheckSound.lean);
  the invariant `LConts` in
  [`Blanc/Lift/LockCheckFlow.lean`](../Blanc/Lift/LockCheckFlow.lean).

#### C9.7. I need every execution prefix to a node, whatever the outcome

- Every execution prefix to a certificate node (all outcomes, no success
  premise): the certificate cursor `Cursor`/`Cont`, its invariant `CursorOK`
  (checked node, pc, stack segments matched per pending function), the
  synthetic step `SStep`, `cursor_start` and `cursor_step` (one `ParentStep`,
  including a `CALL` over a child of any outcome, is one `SStep`),
  with `CursorOK.exec_spawn` (a reached node spawns
  only by `CALL`, `STATICCALL`, `CREATE2` or `DELEGATECALL`) and, for a certificate with
  `Cert.callOnly` (no `CREATE2` or `DELEGATECALL` node), `Cursor.callOnly_of_reach` and
  `CursorOK.exec_call_or_staticcall` (only `CALL`/`STATICCALL`), in
  [`Blanc/Lift/Cursor.lean`](../Blanc/Lift/Cursor.lean).
  With only selected state-gas absence, use
  `Cursor.absNinst_run_stack_noStateGas`, `cursor_stepS_noStateGas`,
  `cursor_step_noStateGas`, `cursor_of_parentPrefix_noStateGas` and
  `reach_of_parentPrefix_noStateGas` in the same module. They retain the
  exact actual same-frame edge/prefix, cursor invariant and child provenance,
  cover every frame outcome, and add no success premise. Original modern
  statements forward to these cores; no cursor/checker carrier changed.
  Their existential step/reach conclusions require the joint certificate and
  actual-edge/prefix premises, so select the route here rather than matching
  an arbitrary existential or reachability goal.
  `CursorOK.tree_of_last` places an actual decoded terminal instruction
  at the cursor's checked `.last` node. It uses only `CursorOK` and
  `Linst.At`, with no fork or successful-outcome premise. This is terminal
  decoding, not a claim that the certificate excludes `SELFDESTRUCT`;
  `Cert.callOnly` continues to permit every terminal instruction.
- Every same-frame node with its machine state (all outcomes):
  `CursorOK.tree_of_exec` puts an external instruction at its
  `next` node, in `Blanc/Lift/Cursor.lean`. The configurations, steps and walk
  inversions (`Conf`, `ConfStep`, `Reach`, `AtExec`, `Reach.next`/`exec`/`dest`/
  `branch`/`branchTo`/`pcAt`) are in
  [`Blanc/Lift/Reach.lean`](../Blanc/Lift/Reach.lean). Use them for a prefix
  fact of a certified frame, e.g. a storage invariant at a spawning node.
  The walk kit over the state `St b S M G` (`rr_next`, `rr_dest`, `rr_branch`),
  the exec-free region refutation
  `Reach.false_of_execFree` with its decidable `ExecFreeSet`/`SFunc.execFreeIn`,
  and `Reach.lastExec` (register steps up
  to the last external instruction) are in
  [`Blanc/Lift/ReachWalk.lean`](../Blanc/Lift/ReachWalk.lean). Use it for safety facts
  about reverting or out-of-gas frames.
- The same walk to an `SSTORE` target (`AtSstore`): `Reach.nextS`/
  `branchToS`/`jumpS`, `Reach.sstoreS` (stop at the
  `SSTORE` or step past it), and the state kit `rs_next`,
  `rs_dest`, `rs_branch`, `rs_branchTo`, `rs_jump` in
  [`Blanc/Lift/ReachWalkSstore.lean`](../Blanc/Lift/ReachWalkSstore.lean); with
  `reach_of_parentPrefix_noStateGas` and `CursorOK.tree_of_sstore` it names the key and
  value of every `SSTORE` a certified frame reaches, whatever its outcome.
- Storage loops and straight-line steps on such a reach, in
  [`Blanc/Lift/ReachSstoreLoops.lean`](../Blanc/Lift/ReachSstoreLoops.lean): the step
  function `stepR`/`ri_stepR` with the tactics `rsx` (one straight-line step), `rsd`
  (a `JUMPDEST`), `rsw` and `rsld` (over `run`, `hT`, `erase`); the loop principles
  `reach_loop_measure` and `reach_loop_index`; the solc storage-string copy loop over `MLOAD` or `CALLDATALOAD`
  (`ReachPayload.bodyR`/`headB`/`headJ`, `payloadB_reach`/`payloadJ_reach`: a store of the
  loop writes `base + j` for `j < count fin p`, with
  `cdload_rdStep`/`cdload_win` for its read), and both clearing layouts
  (`ReachClear.clear_reach`, `legacyClear_reach`: a store of the loop writes zero).
  `ReachClear.legacyClear_reach_range` additionally preserves the actual initial
  key and end word: a reached zero-store key lies at or above the initial key
  and strictly below the end, or the original pending continuation is reached.
  `legacyClear_reach` projects this single traversal to its original interface;
  no old-header shape or additional gas assumption is required.
  `ReachPayload.payloadB_reach_exact` retains equality of the exit index to
  `count fin p`; the original `payloadB_reach` projects the same traversal.
  Also there: `rs_callIn` (enter a callee with its continuation pending), `rsk` (one step taken
  without inverting it), `rsa` (`rsd`, `rsx` or `rsld`, for `repeat rsa`) and `mapSlot_scratch`
  (a mapping slot from solc's scratch words at any closed offsets). The
  solc 0.6 `string storage = string calldata` helper, as a shape over its jump tags
  (`StrStoreCd.helper`), with
  `StrStoreCd.reach` (a store writes the slot, zero, or `keccak(slot) + j` for
  `j < (len + 31) / 32`), is in
  [`Blanc/Lift/ReachSolcStringStore.lean`](../Blanc/Lift/ReachSolcStringStore.lean). The same module
  has the memory form (`StrStore.reach` over `MLOAD`, memory kept outside scratch).
- Further prefix-reach facts for a certified frame: the goto inversion `rr_branchTo`
  and the instruction inversions `ri_address`/`ri_dup_any` in
  [`Blanc/Lift/RunPWalk.lean`](../Blanc/Lift/RunPWalk.lean); the route
  of a selector word through a solc binary-search dispatcher (`SFunc.selWalk σ f`, computed by the
  kernel for a concrete selector; `Reach.selWalk_inl`/`_inr`) in
  [`Blanc/Lift/SelectorRoute.lean`](../Blanc/Lift/SelectorRoute.lean); `ShReachR`, what a checked
  result promises for a reach to an external instruction, in
  [`Blanc/Lift/ReachSkip.lean`](../Blanc/Lift/ReachSkip.lean).
- Preserve an actual external-instruction target while routing a literal
  comparison dispatcher: [`Blanc/Lift/ReachDispatch.lean`](../Blanc/Lift/ReachDispatch.lean)
  provides `rr_cmp_gt` and `rr_cmp_eq` for `DUP`/`PUSH4`/comparison/`PUSH2`
  branches. They preserve arbitrary instruction relation `P`, its soundness
  projection, the original `AtExec` target and continuation stack; the equality
  variant consumes the actual function lookup; the proof recipe for
  `Exec.NoRetainedWriteTo` registers them. They have no in-tree consumer
  at this registry entry. These
  projections alone do not identify a retained occurrence or child outcome.
- From a cursor-placed node to *later* nodes of the same frame:
  [`Blanc/Lift/ReachChain.lean`](../Blanc/Lift/ReachChain.lean).
  `reach_between` is the prefix lift started at any cursor-placed node;
  `getStor_post_of_silent` says the
  frame's post storage at an observed owner is the node's storage when the
  owner is `State.Protected` at that node and the remaining tree is state-silent
  (`Reach.silentTo`, `SFunc.silentTree`). The accepted terminal tree includes
  `SELFDESTRUCT`, so a certificate alone does not protect every world owner.
  `Evm.step_halt_getStor_eq` likewise takes protection at the pre world.
  `StepIn.exec_getStor_eq_of_noDescendants` preserves a protected observed
  owner in a frame with no raw descendants (a child would be the frame itself,
  yet strictly shallower). When the remaining source suffix is `SFunc.silent`
  (which excludes `SELFDESTRUCT` terminals), use `SFunc.RunP.state_of_silent`
  for whole-state preservation without an owner-protection premise.
- To retain an observation of each full synthetic configuration edge, use
  [`Blanc/Lift/ObservedReach.lean`](../Blanc/Lift/ObservedReach.lean).
  `ObservedReach` pairs the existing `ConfStep` with a before/after `Conf`
  predicate; `.forget` erases observations and `.of_reach` instantiates them
  with `True`. This relation adds no interpreter or actual-node premise;
  the observation producer must supply provenance. No automatic recipe is
  registered for this relation-construction interface.
  `observed_reach_of_parentPrefix_noStateGas` in
  [`Cursor.lean`](../Blanc/Lift/Cursor.lean) builds that observation from the
  original prefix induction: `Cursor.RawEdgeAt` retains the actual parent
  edge, root-prefix and stop-suffix cuts, both cursor checks and their `SStep`
  at the same full configurations. The old prefix theorem projects it.
  Observed variants of the SSTORE-target inversions live in
  [`ReachWalkSstore.lean`](../Blanc/Lift/ReachWalkSstore.lean); selectors and
  `orsx`/`orsd`/`orsld` in [`ReachSstoreLoops.lean`](../Blanc/Lift/ReachSstoreLoops.lean)
  preserve the observations through the same shared walk implementations.
  `ObservedReach.rs_retBase` and `rs_retBase` return through the actual
  pending continuation with the same walk base and memory, so storage
  bounds survive internal returns. The older `rs_retM` interfaces remain
  projections with unchanged signatures. Their joint return-prefix and
  SSTORE-target premises do not provide a reliable generic goal-only trigger.
  `ObservedReach.rs_retM` returns through the actual pending continuation,
  retaining memory and the remaining edge observations; `rs_retM` projects
  the existing observation-free interface. Its joint return-prefix and
  SSTORE-target premises do not give a reliable generic goal-only trigger.
  `ObservedKeccak` keeps the original runtime witness, full edge observation,
  exact read input and source shape. `KeccakBefore` in
  [`Blanc/Lift/CursorKeccak.lean`](../Blanc/Lift/CursorKeccak.lean) packages an actual successful occurrence,
  its pc, exact input, 0/64 stack and ordered raw-prefix edge before the stop.
  These facts do not produce a hash census or freshness.
  For two hashes whose relative order matters, use
  [`Blanc/Lift/CursorKeccakOrder.lean`](../Blanc/Lift/CursorKeccakOrder.lean).
  `ObservedKeccak.of_next_linked` retains the first hash's after-configuration;
  `ObservedReach.withPrefix` carries the remaining segment into the second
  observation. `ObservedKeccakPair.actual` converts that joined pair to
  `KeccakPairBefore`: successful original occurrences with the first successor
  preceding the second occurrence and the second successor preceding the stop.
  The proof
  uses `Cursor.RawEdgeAt.gasMeasure_lt`, `ObservedReach.raw_gasMeasure_le`,
  `parentPrefix_of_gasMeasure_le` and `keccakOccurrence_of_parentPrefix` to
  relate the observed segment to actual derivation positions. No hash
  injectivity, final-frame success or numeric pc order is assumed.
  `KeccakPairBefore.forget` projects both individual earlier-occurrence witnesses.
  The `ordered-observed-keccak-pair` recipe matches the ordered package goal.

#### C9.8. I need facts at a checked cursor of an actual successful execution

- To advance a checked certificate cursor through an actual successful raw
  suffix, use [`Blanc/Lift/CursorCuts.lean`](../Blanc/Lift/CursorCuts.lean).
  `cursor_next_forward` derives the actual `ParentStep`, instruction witness
  with `Cursor.DescOf`, `SStep`, `ConfStep` and successor `CursorOK`.
  `cursor_jinst_forward` reuses the decoded jump edge; `cursor_branch_forwardH`
  (from `rules.stateGas = none`; at `CoveredFork.rules_stateGas_none` it gives the modern form)
  derives the faithful branch disjunction from the checked tree and literal
  abstract target, without choosing the branch as a premise.
  `cursor_nexts_line_cont_free_forward` composes a literal instruction list into
  a real `ParentPrefix`, pc sum, preserved static environment/outcome, checked
  tail cursor and `Line.Run` to the same actual endpoint. It preserves the full
  continuation stack and derives `ExecFreeUntil` when the list is non-exec.
  `CursorOK.ninstAt_of_next`
  exposes the actual decoded instruction from the checked next node and is
  shared by the single-step and exec-free cuts.
  The cursor-only projection `cursor_nexts_forwardH` lives in
  [`HistCursorCuts.lean`](../Blanc/Lift/HistCursorCuts.lean) and takes
  `rules.stateGas = none`; its `_covered` form accepts `CoveredFork`. These are
  certificate/SFunc cuts, not the compiled Func prefix API. They require raw
  success; they do not establish child context, settlement or ordered history. The joint node/tree premises are discovered here because the
  existential result alone is not a reliable recipe trigger.
- To pin a complete state while retaining the internal return continuation,
  use [`Blanc/Lift/CursorExactLine.lean`](../Blanc/Lift/CursorExactLine.lean).
  `cursor_line_exact_cont` and `cursor_dest_line_exact_cont` cross literal
  non-external lines with an exact synthetic walk and preserve `cursor.K`.
  `cursor_callNext_exact_cont` retains the actual prepended `Cont`, and
  `cursor_ret_exact_cont` returns through that same continuation with an exact
  popped state. These strengthen the exact cut interfaces when a consumer
  must carry an internal return stack; their conclusions do not assert
  settlement or successful external replies.
- To classify actual successful states without imposing a gas schedule, use
  [`Blanc/Lift/CursorStateCuts.lean`](../Blanc/Lift/CursorStateCuts.lean).
  `CursorStateAt` carries a checked actual cursor, a call-free span, a complete
  `St` state with existential residual gas, and the mapped return continuation.
  Its `jump` method applies
  source inverses to the actual `ConfStep`, deriving the
  successor state and tree. Its `call` method
  retains the actual mapped internal continuation,
  preserving the complete non-gas state without requiring a gas schedule.
  `memory_eq` projects the symbolic memory without unfolding a concrete state.
- To cross a checked referenced goto while preserving the complete actual
  state and return continuation, use
  [`Blanc/Lift/CursorJump.lean`](../Blanc/Lift/CursorJump.lean).
  `CursorOK.jumpAt_of_jump` derives the actual JUMP byte from the checked node;
  `CursorStateAt.gotoH` consumes its actual
  `ConfStep` and checked lookup,
  retaining the full non-gas state and original K. The joint node/tree/lookup
  premises are discovered here; the existential result is not a reliable
  recipe trigger.
- To exclude later external instructions from an actual returned parent, use
  [`Blanc/Lift/HistCursorReturn.lean`](../Blanc/Lift/HistCursorReturn.lean).
  `cursor_reach_of_parentPrefixH` transports its checked cursor along the supplied
  relative same-frame prefix. `CursorOK.noExecSuffixH` uses a checked closed
  region and the actual pending continuations to exclude later external nodes.
  `CursorOK.revertLineNoOkH` rules out a literal reverting suffix under actual
  success. These APIs preserve the supplied execution and do not select a
  different root or call occurrence.
  [`Blanc/Lift/CursorNoExecSuffix.lean`](../Blanc/Lift/CursorNoExecSuffix.lean) remains
  an import compatibility module; the historical module owns these proofs.
- To obtain successful source suffix facts at a supplied actual checked node,
  use `CursorOK.sourceRun` in
  [`Blanc/Lift/CursorSourceRun.lean`](../Blanc/Lift/CursorSourceRun.lean).
  It applies `node_soundM` to that same node, its matched frame and pending
  return tag. Its outcome may return internally; it does not fabricate a
  top-level halt. The resulting `StepIn` source run can establish guards and
  widths, while actual cursor cuts still own external occurrence and slot
  identities.
- To preserve an internal return's actual continuation execution and checked
  frame, use
  [`Blanc/Lift/CursorSourceRunReturn.lean`](../Blanc/Lift/CursorSourceRunReturn.lean).
  It keeps the supplied actual successful node and either its halted source
  outcome or the actual internal continuation `Exec`, complete returned state,
  checked caller cursor and structural subderivation relation. That relation
  alone does not assert a call-free predecessor gap; use `quietReturnH` for a
  body whose checked region excludes external instructions.
- Literal `returnWordGuardLine` and `callFlagGuardLine` definitions remain in
  [`Blanc/Lift/CursorBalanceReply.lean`](../Blanc/Lift/CursorBalanceReply.lean).
- To return through a supplied checked call-free internal body, use
  [`Blanc/Lift/HistCursorReturn.lean`](../Blanc/Lift/HistCursorReturn.lean).
  `CursorOK.quietReturnH` walks the actual parent derivation and stops at the
  first return through its supplied mapped continuation. It returns a relative
  `ExecFreeUntil`, the checked actual caller cursor and remaining continuation,
  and a source run whose complete returned state is that actual parent node.
  Only the body and locally pushed continuations must lie in the checked
  exec-free, nonhalting region; the caller may make further external calls.
  The direct actual trace needs no source-selected endpoint or gas schedule.
  [`Blanc/Lift/CursorQuietReturn.lean`](../Blanc/Lift/CursorQuietReturn.lean) remains an
  import compatibility module; the historical module owns the return proof.
- To connect a checked original-bytecode external next node to its actual
  occurrence and returned parent, use
  [`Blanc/Lift/CursorOccurrence.lean`](../Blanc/Lift/CursorOccurrence.lean).
  `cursor_next_call_occurrence_forwardH` there derives a
  `CallOccurrenceStep root x`
  from the supplied same-frame prefix, checked cursor and successful suffix.
  The carrier keeps the exact `NinstOccurrence`, decoded external instruction,
  same-frame `ParentStep` and complete returned `Devm`; its
  `occurrence_stepRun_unique` comparison preserves both recursive slot and
  step result. `CallOccurrenceStep.reRoot` transports that same call along a
  supplied earlier same-frame `ParentPrefix`; `reRoot_identity` exposes exact
  preservation of the node, instruction, recursive slot, step result and
  returned derivation. It changes only root-indexed reachability evidence.
  Raw occurrence identity alone does not establish settlement,
  call-free predecessor gaps or a child's queue/path origin. The
  On `stateGas = none` (historical forks) use `cursor_next_forwardH` and
  `cursor_next_call_occurrence_forwardH`. A cursor-placed node decoding any instruction other than `PC`
  sits at that instruction's checked `next` node (`CursorOK.tree_of_ninst`,
  `CursorOK.tree_of_sstore`; `CursorOK.tree_of_exec` is the external case) in
  [`Blanc/Lift/CursorTreeNinst.lean`](../Blanc/Lift/CursorTreeNinst.lean).
- To pin the *complete* actual state (gas and world metadata included) at a
  later cursor of a successful raw suffix, use
  [`Blanc/Lift/CursorExact.lean`](../Blanc/Lift/CursorExact.lean). Build
  `SFunc.CutAt fs tgt f f'` along the actual path (`next` for frame-free
  instructions, `dest`, `zero`/`succ`, `toZero`, and `toSucc` inlining
  `fs[k]`), then prove the gas-exact synthetic run of the cut tree with the
  usual `rx_*` kit ending in `rx_stop`; `cursor_cut_exact` returns the actual
  node at `tgt`, its `ExecFreeUntil` span, cursor, unchanged static
  environment/outcome and `N.devm` equal to the synthetic halting state.
  `cursor_callNext_exact` crosses one internal call edge with its exact pop.
  `Exec.Deriv.ExecFreeUntil.eq_of_execAt` identifies two frame-entry-free
  spans from one node ending at decoded frame-entering instructions (use it to
  identify a cut with a canonical occurrence), and `ninstRun_eq_of_runCompiled`
  pins an actual primitive step against a compiled one from the same state.
  `popBurnBy_eq_of_length`, `burnBy_eq` and `ConfStep.of_dest`/`of_branch`/
  `of_branchTo`/`of_callNext` are the supporting inversions.
- To expose the six actual STATICCALL operands, use
  `cursor_staticcall_operands` in
  [`Blanc/Lift/CursorCuts.lean`](../Blanc/Lift/CursorCuts.lean). `CursorOK` and
  the exact next-staticcall tree force a six-word concrete stack prefix.
  No successful outcome, child context or settlement premise is needed.
  The existing forward-cut consumers can retain these operands at the same
  actual occurrence; the projection alone supplies no occurrence order.

#### C9.9. I need to walk a successful lifted run

- Symbolic environment-push inversion in
  [`Blanc/Lift/EnvironmentInv.lean`](../Blanc/Lift/EnvironmentInv.lean): `ri_number` and `ri_timestamp`
  identify the successor as `St` with the block-number word or timestamp pushed onto the original stack,
  the same base and memory, and an existential remaining gas value. They state no numeric gas charge.
- Successful lifted run to facts (safety, the inversion walk): per-node `ric_*`
  (control, over `SFunc.RunCut`; `SFunc.Run.cut`/`SFunc.RunCut.uncut` for uncut
  runs) and per-instruction `ri_*` (successor as an `St`, `ri_xor` among them; numeral-offset forms
  `ri_mstore_nat`/`ri_calldatacopy_nat`, `ri_val` to name a successor's top word, and
  `ri_sstore_nonstatic`: a completed `SSTORE` proves the frame non-static) in
  [`Blanc/Lift/InvWalk.lean`](../Blanc/Lift/InvWalk.lean) and
  [`Blanc/Lift/InvWalkOps.lean`](../Blanc/Lift/InvWalkOps.lean), which also holds the
  solc word-copy loop inverted (`ric_copy_step`, `ric_copy_exit`, the converses of
  `copy_step`/`copy_exit`) and the facts a failed comparison guard leaves
  (`toNat_le_of_gtCheck_eq_zero`, `toNat_ge_of_ltCheck_eq_zero`,
  `eq_zero_of_iszero_ne_zero`); failing arms
  (`SFunc.noOk`, `SFunc.RunCutP.false_of_noOk`), trees that cannot halt (`SFunc.noHalt`,
  `NoHaltSet`, `SFunc.RunP.not_halted`), conditional gotos
  (`ric_branchTo`), internal calls (`ric_call`) and `ri_sload`
  in [`Blanc/Lift/InvWalkWorld.lean`](../Blanc/Lift/InvWalkWorld.lean);
  on a historical fork, where the access schedule may be flat (Istanbul, Muir Glacier)
  rather than EIP-2929, invert `SLOAD` with `ri_sloadH` from `rules.bal = none` alone; its
  successor `afterSloadH` is `afterSload` under EIP-2929 (`afterSloadH_of_eip2929`) and the
  unchanged base under flat access, with `afterSloadH_getStor`/`afterSloadH_logs` and the storage-walk
  steps `StorStep.sloadH`/`StorStep.sstoreH`; invert
  `SSTORE` with `ri_sstoreH` (`rules.stateGas = none`, `rules.bal = none`) over
  `afterSstoreH`, whose refund is `sstoreRefundH` (legacy, flat net-metered, or EIP-2929) and
  which is `afterSstore` under EIP-2929 net metering (`afterSstoreH_of_eip2929`); invert or run `EXTCODESIZE` with
  `ri_extcodesizeH`/`rx_extcodesizeH` over `accountAccessH` and `extcodesizeCostH`; each
  `_covered` form recovers the modern statement, all in
  [`Blanc/Lift/HistAccessWalk.lean`](../Blanc/Lift/HistAccessWalk.lean); invert a
  `STATICCALL` to an arbitrary callee from `rules.stateGas = none` alone with
  `ri_staticcall_boundedH`/`ri_staticcallH`/`rx_staticcallH` (answer `StaticAnsweredH`, code
  resolution `CallCodeH` under the actual delegation flag; on a covered fork
  `CallCodeH_iff_of_covered`, `StaticAnsweredH_iff_of_covered` and
  `CoveredFork.rules_delegationEnabled`), the step/run inversions
  `of_step_staticcall_val_with_depth_frame_causeH`/`of_run_staticcall_val_with_depth_causeH`,
  quiet steps with `Ninst.world_of_quietH`, static log preservation with
  `Exec.logs_eq_of_static_okH` (any fact about every successful outcome transfers to the
  committed post by `Execution.committedPost_of_okFact`), and the return-data bound
  `ReturnDataBound.staticcall_returnData_length_ltH`; the
  `_covered`/`of_covered` forms recover the modern statements; the value-carrying `CALL`
  inversion `of_step_call_val_with_depth_frameH`, all in
  [`Blanc/Lift/HistStaticCall.lean`](../Blanc/Lift/HistStaticCall.lean); the forward cursor cuts from `rules.stateGas = none` alone (`cursor_next_forwardH`,
  `cursor_jinst_forwardH`, `cursor_nexts_line_cont_free_forwardH` in `CursorCuts.lean`,
  `CursorStateAt.jumpH`/`callH` in `CursorStateCuts.lean` and
  `cursor_next_call_occurrence_forwardH` in `CursorOccurrence.lean`, beside the modern forms they
  derive; `cursor_nexts_forwardH`, `cursor_branch_forwardH` and the state cut
  `CursorStateAt.gotoH` in
  [`Blanc/Lift/HistCursorCuts.lean`](../Blanc/Lift/HistCursorCuts.lean)). For checked steps
  forced by a later same-frame SSTORE, use
  `cursor_step_toward_sstore_noStateGas` in
  [`Blanc/Lift/CursorCutsToward.lean`](../Blanc/Lift/CursorCutsToward.lean).
  For state-shaped producers, `CursorStateToward` in
  [`Blanc/Lift/CursorStateToward.lean`](../Blanc/Lift/CursorStateToward.lean)
  extends the existing `CursorStateAt` with the actual remaining prefix to the
  observed SSTORE. Its line, branch, destination, internal call and return cuts
  retain both spans. Guards exclude actual halting SSTORE-free branches; the
  single-primitive cut requires a distinct target node, allowing an earlier
  write only after the producer proves its separation from the tracked write.
  Source runs and
  returns (`CursorOK.sourceRunH`/`sourceRunReturnH`, in `CursorSourceRun.lean` and
  `CursorSourceRunReturn.lean`), exec-free suffixes (`reach_betweenH`
  in `ReachChain.lean`; `cursor_reach_of_parentPrefixH`, `CursorOK.noExecSuffixH`,
  `CursorOK.revertLineNoOkH`), call-free internal returns
  (`CursorOK.quietReturnH`, over the fork-free `SFunc.ReturnRegion`/`ConfStep.returnRegion`) in
  [`Blanc/Lift/HistCursorReturn.lean`](../Blanc/Lift/HistCursorReturn.lean) on every fork,
  `ecrecover_activeH` activates address 1 and
  `ecrecover_output_of_processMessage_cleanH` (from `rules.stateGas = none`; its `_covered`
  form is the modern statement) reads a clean address-1 child's output, while
  `CallCodeH.direct_of_nodeleg`/`CallCodeH.of_nodeleg` resolve a non-delegated callee's code
  under either delegation flag. `CallCodeH.direct_of_effective`/`CallCodeH.of_effective`
  use the selected rules' effective lookup-none result, including arbitrary
  code bytes when delegation is disabled. These helpers live in
  [`Blanc/Lift/HistEcrecover.lean`](../Blanc/Lift/HistEcrecover.lean);
  the forward creation kit under
  historical rule facts (the `SLOAD`/`SSTORE` charges `sloadCostH`/`sstoreCostH` with the
  `sloadCostH_of_eip2929` equation and the exact step
  `rx_sstoreH` in
  [`Blanc/Lift/HistAccessWalk.lean`](../Blanc/Lift/HistAccessWalk.lean); their `_le` bounds, the
  settlement `processMessage_ok_of_execH`/`liftCreate_postH`/`liftCreate_okH` from
  `rules.stateGas = none` with the target's EIP-161 touch recorded, and `CREATE2` as
  `create2ChargeH`/`Xinst.step_create2_spawnH`/`create2_runCompiledH`) in
  [`Blanc/Lift/HistCreate.lean`](../Blanc/Lift/HistCreate.lean); the bookkeeping fields a
  settled frame reads across those steps (`afterSloadH_accountsToDelete`,
  `afterSloadH_refundCounter`, `afterSstoreH_accountsToDelete`, and
  `afterSstoreH_refundCounter_legacy` under the legacy `SSTORE` refund schedule for a nonzero
  write) in [`Blanc/Lift/HistAccessMeta.lean`](../Blanc/Lift/HistAccessMeta.lean);
  the symbolic settlement projection cuts `liftCreatePost_meta` (deletion set, refund,
  created accounts) and `recordTouch_meta` (the same fields and gas) in
  [`Blanc/Lift/HistCreate.lean`](../Blanc/Lift/HistCreate.lean) keep concrete constructor
  images out of definitional unfolding;
  the remaining historical successor projections (`afterSloadH_getCode`/
  `_error`/`_createdAccounts`/`_accessedStorageKeys`, `afterSstoreH_accessedStorageKeys`,
  the `ite` form `getStor_afterSstoreH`) in
  [`Blanc/Lift/HistAccessWalkFacts.lean`](../Blanc/Lift/HistAccessWalkFacts.lean);
  the SHA-256 precompile call (`ri_staticcall_sha`) and the solc packed-SHA
  site (`ric_copy_sha`, the converse of `copy_sha_gen`) in
  [`Blanc/Lift/InvWalkSha.lean`](../Blanc/Lift/InvWalkSha.lean).
  When the GAS word must equal the complete successor state's residual gas,
  use `ri_gas_remaining` in
  [`Blanc/Lift/InvWalkGas.lean`](../Blanc/Lift/InvWalkGas.lean). Its existential
  gas comes from the actual charged state, rather than a supplied gas schedule.
  Actual dispatcher comparison segments (`DUP1/PUSH4/GT/PUSH2/branch` and
  `DUP1/PUSH4/EQ/PUSH2/branchTo`) are inverted by `ric_cmp_gt` and
  `ric_cmp_eq` in
  [`Blanc/Lift/InvWalkDispatch.lean`](../Blanc/Lift/InvWalkDispatch.lean).
  They retain an arbitrary stack suffix and cut set, select the actual comparison
  continuation, and require the real target lookup and non-cut proof for EQ.
  For a cut run over an arbitrary instruction relation, `ric_nextP`, `ric_destP`
  and `ric_branchP` in
  [`Blanc/Lift/InvWalkProvenance.lean`](../Blanc/Lift/InvWalkProvenance.lean)
  retain that relation in the exposed instruction and the continuation. Use these
  projections when a walk must preserve execution-derivation provenance.
  For a complete linear prefix, `SFunc.RunCutP.split_nexts` exposes its actual
  intermediate state and `Line.Run`, using an explicit projection to `Ninst.Run`.
  The residual cut keeps the original instruction relation, program, cut set and
  final segment. Use it when an existing instruction inverse consumes a line
  while the remaining cut must retain provenance. Split a line itself with the
  existing `Blanc.of_run_append`; no second cut relation is needed.
- Big-step node inversions under an arbitrary step relation, for a run
  `SFunc.RunP P fs sevm d f o` over the walk state `St b S M G` (`rpw_next`, `rpw_dest`,
  `rpw_branch`, `rpw_ret`; `SFunc.haltsOnly` with
  `SFunc.RunP.not_returned_of_haltsOnly`; `St.self'`) in [`Blanc/Lift/RunPWalk.lean`](../Blanc/Lift/RunPWalk.lean).
- One-lemma straight-line steps and the inversion helpers of solc walks:
  [`Blanc/Lift/InvWalkStep.lean`](../Blanc/Lift/InvWalkStep.lean). `stepX` computes the successor walk state of the
  straight-line instructions a walk crosses and `ri_stepX` inverts any of them at once; the
  `ri_stepX_nonstorage` projection needs no fork premise when the actual instruction
  is neither `SLOAD` nor `SSTORE`. It shares the original inversion body and leaves
  the `stepX` definition unchanged; storage walks still need their actual fork semantics.
  The
  `istep h` tactic runs one such step (or a `JUMPDEST`) of a cut run, so a straight segment is
  `repeat istep h`; `ibranch h c` crosses a conditional jump whose other arm only reverts;
  `keccak_scratch` is solc's fresh mapping hash;
  the word fact `word_ff20` reads solc's address mask. The cut-run kit of [`Blanc/Lift/WalkCutKit.lean`](../Blanc/Lift/WalkCutKit.lean) adds
  the storage projections of the walk
  bases. The shared accumulated walk is owned by
  [`Blanc/Lift/AccumulatedWalk.lean`](../Blanc/Lift/AccumulatedWalk.lean).
- Straight-line inversion steps of a cut run without writing them out: `winv n` / `winv` read
  the node off the tree of `h : SFunc.RunCut …` (or `SFunc.RunCutP P …` with `using project`) and
  run the hand-written step `replace h := ric_next h; obtain ⟨_, hd, h⟩ := h;
  obtain ⟨_, rfl⟩ := ri_<op> hd; clear hd` (`ri_push`, `ri_dup rfl`, `ri_swap rfl`, `ri_pop`,
  `ri_add`, `ri_mload`, …; `ric_dest` for a `.dest`; a `ri_dup`/`ri_swap` implicit such as
  `(w := x)` is spelled out only where a `set` abbreviation or rewritten shape needs it), stopping at a branch, jump, storage or call node; `at h` names the run (default: the
  most recent cut run); `wskip n` steps over any `n` nodes forgetting the state
  (`obtain ⟨_, _, h⟩ := ric_next h`), in [`Blanc/Lift/WalkInvKit.lean`](../Blanc/Lift/WalkInvKit.lean).
- Straight-line forward steps without writing them out: `wstep` / `wrun n` / `wrun` read the
  instruction off the goal's tree (`SFunc.RunExact` or `SFunc.RunEx`) and apply the hand-written
  term (`rx_push rfl (by wroom)`, `rx_dup rfl …`, `rx_swap1`, `rx_pop`, `rx_dest`, `rx_<op> rfl …`),
  stopping at a branch, jump, memory, storage or call instruction; `using tac` swaps the
  stack-room tactic `wroom`; `wrun! n` states pushed words as numerals (`rx_push (w := 64) rfl …`)
  and `SWAP2`–`SWAP4` by `rx_swap2`–`rx_swap4`. One
  line replaces a run of `xr (rx_… ·)` or `refine rx_… ?_` lines, in
  [`Blanc/Lift/WalkKit.lean`](../Blanc/Lift/WalkKit.lean). The backward twin for a frame walk
  `h : XAt …` reads the instruction off the code's byte trie (`xa n`, one family's macros, so it
  lives with them).
- Forward runs to *some* outcome, for walks through a call answered only by an `∃ d` premise
  (the outcome is learned midway, so it cannot be fixed up front): `SFunc.RunEx` /
  `SFunc.RunExCut` (`∃ r, RunExact … r ∧ Q r`), the lift `SFunc.RunEx.of` with the tactics
  `xr (rx_push rfl h ·)` / `xrc …` for any fixed-outcome step,
  and the fresh-state twins `rxce_call_identity`, `rxce_vyRawCallJoin`, `rxce_vyRawCallTail` in
  [`Blanc/Lift/RunEx.lean`](../Blanc/Lift/RunEx.lean).
- Crossing code without walking it, the route-C skip theorems. A checked synthetic run never
  touches the stack below its frame, [`Blanc/Lift/FrameSkip.lean`](../Blanc/Lift/FrameSkip.lean): `FrameAt`,
  `SFunc.RunP.stack_below`, `SFunc.RunCutP.stack_below` (every stop satisfies `CutStop`),
  and `SFunc.RunP.entry_stack_below`. The `FrameAt.next_noStateGas`,
  `SFunc.RunP.stack_below_noStateGas` and `SFunc.RunP.entry_stack_below_noStateGas`
  variants share the original induction with actual state-gas absence.
  `ric_call_silent` crosses any state-silent internal
  call (hashing, ABI encoding, view-like helpers) with the continuation's stack
  `Y ++ S.drop e.frame.length`, `Y.length = e.rets`. A silent
  stack-shuffling segment crossed by one kernel decision, [`Blanc/Lift/ShuffleSkip.lean`](../Blanc/Lift/ShuffleSkip.lean):
  the abstract words `SVal` (`arg i`, `lit w`, `unk`), `Carried`, the checker `shuffle` (every
  instruction state-silent, its stack effect the lift's own `ninstTransfer` on index labels,
  literal `JUMPI`s followed, reverting arms pruned, gotos into an entry list `Fw` disjoint from the
  cut list). The `shNinst_run_noStateGas` and
  `shuffle_sound_noStateGas` variants share those
  proofs with actual state-gas absence and the same checker/fuel.
- Loops: a back-edge to entry `k` is reasoned about one iteration at a time on
  runs cut at `k` (`SFunc.RunCutP`, `SFunc.RunExactCut`). Safety:
  `SFunc.RunCutP.loop` (invariant; `SFunc.RunP.loop`), which
  nests because the outer cut list is a parameter; liveness:
  `SFunc.RunExactCut.iterate` builds a whole loop run from per-iteration cut
  runs; both in [`Blanc/Lift/Loop.lean`](../Blanc/Lift/Loop.lean).
- Fuel-bounded loops (a `range(cap)` loop that stops early on a test and
  otherwise returns its last iterate, e.g. Newton loops): the model
  `fuelLoop body close fuel D` and its gas `fuelCost`;
  peeled head copies whose back edge targets the next copy via
  `RunExactCut_fuelLoop_peel`; all in
  [`Blanc/Lift/FuelLoopWalk.lean`](../Blanc/Lift/FuelLoopWalk.lean).
- Indexed loads from three consecutive carried words: `pickWord3` selects the word. Owner:
  [`Blanc/Lift/ThreeWordFrame.lean`](../Blanc/Lift/ThreeWordFrame.lean).
- Walking a successful frame along its own derivation (`XAt sevm post pc d L`: the actual state
  at `pc` and the direct children `L` still to come): `XAt.of_exec` and the `CALL`/`STATICCALL` steps
  that peel one child, in [`Blanc/Lift/FrameWalk.lean`](../Blanc/Lift/FrameWalk.lean).
  `StaticWordChild` records an exact target/calldata, staticness, at least one return
  word and no child logs. It is an observation carrier; use the actual `XAt`/`ChildOf`
  derivation separately to establish parent-child provenance.
- Crossing a certified tree (callee) from a walked state: `xa_node` (any checked node; the walk
  resumes at the return address in the actual returned state) and `xa_node_span` (an exec-free
  tree, `ExecFreeSet`/`SFunc.execFreeIn`: the remaining children `L` are kept, a halt leaves
  `L = []`), with gas monotonicity `Exec.Deriv.Prec.gasMeasure_lt`/`lt.gasMeasure_lt`/
  `ParentPrefix.gasMeasure_le`, in
  [`Blanc/Lift/FrameWalkNode.lean`](../Blanc/Lift/FrameWalkNode.lean); the span-strengthened
  lifting recursion `node_spanM` (returned node reached by an `Exec.Deriv.ExecFreeUntil` span;
  halting chain `ChainFree`), `node_span_childFrames`, `prec_parentStep_of_free`,
  `SpanOut.back` and `SilentSet.execFreeSet` in
  [`Blanc/Lift/SoundSpan.lean`](../Blanc/Lift/SoundSpan.lean).
- Matching a gas-exact forward run's states and call steps with the actual derivation (so a
  reply a forward run consumed is the reply `Exec.childFrames` records): `SFunc.CutCall` (a cut of a tree) and the cut-by-steps helpers `CutStep` (`.cl`
  crosses a call, `.pc` a return-address `PC` push), in
  [`Blanc/Lift/FrameWalkCut.lean`](../Blanc/Lift/FrameWalkCut.lean).
- Memory across a crossed callee: `Mem.KeepsOff M M' W` (no shrink; every byte off the windows
  `W` kept) with `refl`/`trans`/`mono`/`of_agreeOutside`, the image transport
  `MemMatches.keepsOff` and `memWord_keepsOff`, in
  [`Blanc/Lift/MemGlue.lean`](../Blanc/Lift/MemGlue.lean).
- Frame walks keeping memory word-aligned (`M.size % 32 = 0`, which callee contracts need): `Mem.size_write_mod32`, `Mem.size_extends_mod32` and the
  spawning steps `xa_staticcall_imgA`/`xa_call_imgA`/`xa_identity_imgA` in
  [`Blanc/Lift/FrameWalkAligned.lean`](../Blanc/Lift/FrameWalkAligned.lean).
- solc idioms, gas-exact: the word-copy loop (`copy_loop`) in
  [`Blanc/Lift/CopyLoop.lean`](../Blanc/Lift/CopyLoop.lean); the
  `sha256(abi.encodePacked(a, b))` site through the SHA-256 precompile
  (`copy_sha_gen` over memory of any word-aligned size, with its result image
  `shaImg`; its corollaries `copy_sha`, `packed_sha_pair`, and `pair_mem_sha` for a
  pair whose second word is the previous digest at the free pointer) in
  [`Blanc/Lift/PackedSha.lean`](../Blanc/Lift/PackedSha.lean), and the corollary
  over memory that already covers the destination (`copy_sha_covered`) in
  [`Blanc/Lift/PackedShaCovered.lean`](../Blanc/Lift/PackedShaCovered.lean).

For the fee path of a system request contract (the shape EIP-7002, EIP-7251 and the EIP-8282
builder runtimes share), instantiate
[`Blanc/Lift/RequestFee/Window.lean`](../Blanc/Lift/RequestFee/Window.lean) rather than walking it:
`loopTree`, `initTree` and `postloopTree` take the pushed targets, calldata length and continuations
as parameters, so a generated tree is an instance by `rfl`. `init_inv`/`init_exact` set up from
`[excess, 17]`, `loop_inv`/`loop_exact` follow a `WordFakeExponential.Run`, and
`postloop_inv`/`postloop_exact` select the continuation by calldata length. For the getter,
[`Blanc/Lift/RequestFee/Getter.lean`](../Blanc/Lift/RequestFee/Getter.lean) gives
`guard_inv`/`guard_exact` over `guardTree` and `return_inv`/`return_exact` over `returnTree`, with
the post state `feeGetterPost`. Exact walks take `PUSH0`'s activation as a hypothesis. The excess
read, the inhibitor guard and the submission body are not here, since they differ by contract.
For the plain user path the EIP-7002 and EIP-7251 runtimes share (dispatch, `PUSH1 17`, the slot-zero inhibitor
guard, the window on slot 0 as stored, then the value guard of a submission), instantiate `PlainUserPath` in
[`Blanc/Lift/RequestFee/Plain.lean`](../Blanc/Lift/RequestFee/Plain.lean): `plainPath_inv`/`plainPath_exact`
over `plainPathTree`, `paid_inv`/`paid_exact` over `paidTree`, `dispatch_user_inv` and `exec_of_dispatch_user`
for any dispatch root, and per runtime `exec_user_cases`, `exec_fee_read`, `exec_fee_read_exact` and
`exec_inhibited_no_ok`, all under covered forks. `word_fee_eq_of_le` and `word_fee_ne_at_2893` restate the
2892/2893 boundary on a stored excess word. EIP-7002 keeps its own glue, which its pins reach. A request queue's storage layout, generic over record width
(`QueueState`, `Represents`, `queueSlot`), is
[`Blanc/Lift/BuilderRequest/QueueLayout.lean`](../Blanc/Lift/BuilderRequest/QueueLayout.lean) (shared; the
namespace is the builder family's). For what a request system call leaves on a represented queue, for any excess
arm, use [`Blanc/Lift/RequestQueue/Drain.lean`](../Blanc/Lift/RequestQueue/Drain.lean): `represents_drain` (post
storage of `sysState` represents `drainedBy`), `drained_represented` and `output_represented` (the return window is
the oldest `min(length, cap)` records). For the queue model over a list of frames, instantiate
[`Blanc/Lift/RequestQueue/Model.lean`](../Blanc/Lift/RequestQueue/Model.lean) (`Effect`: push, keep, or drain with a
stored-excess function; `run`, `deliveries`, the FIFO `fifo`; `represents_push` for a submission's storage) and
[`Blanc/Lift/RequestQueue/Chain.lean`](../Blanc/Lift/RequestQueue/Chain.lean) (`Queue`, a `Step` packaging a
frame with its queue law, `Chain`, `Chain.delivered`, `Chain.drain_delivers`).
For queue-model delivery under consecutive drains, without storage or kept-history premises, use
[`Blanc/Lift/RequestQueue/DrainLatency.lean`](../Blanc/Lift/RequestQueue/DrainLatency.lean):
`deliveries_drain_slot` follows record `cap*k+i`, with `i<cap`, to effect `j+k`;
`deliveries_drain_position` gives destination `j+q/cap` and slot `q%cap` for `cap>0`.
Every effect through the destination must be a drain.
To produce that list from a kept history at covered forks, give a canonical request contract a `Linked` (its
address, type byte, `record?` and a `Step` for each kept user frame and for its request-phase call) and use
[`Blanc/Lift/RequestQueue/Link.lean`](../Blanc/Lift/RequestQueue/Link.lean): `history_chain` (the kept frames are a
`Chain`, pushing what `record?` reads, outputting the blocks' requests of the type, whole records per block, with the
SYSTEM_ADDRESS exclusion discharged from no code, sender, authority or creation there), `covered_request_root` (a
covered-fork request step at a system contract is one kept root with the system caller) and `chunks_flatMap`.
To lift a `DrainLinked` canonical request contract from `Link.history_chain` to per-submission FIFO ordering, exact
draining block index, fate trichotomy (already emitted with a latency bound or still at an exact stored queue slot)
and block-latency bound over any `KeptHistory`, use
[`Blanc/Lift/RequestQueue/Occurrence.lean`](../Blanc/Lift/RequestQueue/Occurrence.lean) (`storedQueue`, `submissions`,
`emissions`, `remainingQueue`, `BlockSteps`, `Premises`, `history_fifo`, `history_block`, `history_fate`,
`history_latency`).
The builder family's user frames are walked once over a fork's `StorageSteps` (`FeePath.lean`), with
`coveredSteps` and `amsterdamSteps` (`UserFrameAmsterdam.lean`) as its instances: only `SLOAD` and `SSTORE`
differ between them, and those certificates have no call-family node, so `lift_sound_noExec` lifts on any fork.

Under Amsterdam, all four request contracts' system paths are one instance family. `SysShape` and `SysPath`
in `Blanc/Lift/RequestSystem/Path.lean` are a runtime's pushed words, excess arm and record body, with the
whole frame from any storage (`frame_run`); its caller dispatch is `Blanc/Lift/RequestSystem/Dispatch.lean`.
The path is fork-parametric: its reads and record bodies are fork-free, and its stores are a fork's
`SysStores` (`Blanc/Lift/RequestSystem/Stores.lean`: `amsterdamStores`, whose readiness is the system
reservoir, and `coveredStores`), so `frame_runOn`, `frameCost_leOn` (against `frameBoundOn`) and
`framePostOn_state` serve both, and the Amsterdam statements are their instances. On the covered forks,
`CoveredSysCall.spec` in `Blanc/Lift/RequestSystem/CoveredCall.lean` takes the same `SysPath` through the
checked system call of a canonical system contract, with `SysOutput.coveredPost_output` for its return.
`plainNext_toNat` reads the
plain excess arm in naturals without wrap.
`SysCall.spec` in `Blanc/Lift/RequestSystem/Call.lean` takes it through the checked system call, with
`sysState` as the exact post state and a regular-gas bound (`RegularGasWithin`: regular gas, state gas
excluded); `sysState_getCode` says no
account's code moves. The pure whole-storage transformer is in
[`Blanc/Lift/RequestSystem/Storage.lean`](../Blanc/Lift/RequestSystem/Storage.lean):
`drainStor` and `sysState_getStor` retain their legacy namespace. For the WORD drain count `c`,
the transformer resets head and tail exactly when `head + c = tail`, otherwise advances head;
it then writes `shape.next` of the original excess/count to slot 0 and zero to slot 1.
All arithmetic is WORD arithmetic; every other slot, including stale record storage, is unchanged.
`SysOutput` and `runRequestContracts_step` in `Blanc/Lift/RequestSystem/Output.lean`
read the return window and one request-phase step. A record body's segments (`seg_start`, `seg_source`,
`seg_word`, `seg_last`, `seg_byte`) are `Blanc/Lift/RequestSystem/BodySegs.lean`. The EIP-7002 and EIP-7251
excess arm (no latch; the inhibitor counts as zero) is `plainShape` in
`Blanc/Lift/RequestSystem/PlainExcess.lean`; the EIP-8282 arm is `latchShape` in
`Blanc/Lift/BuilderRequest/SystemPath.lean`, family-local, and its nonempty-calldata side, on
`SysPath.frame_prefix` and `SysPath.prefix_le`, is `Blanc/Lift/BuilderRequest/Latch.lean`. The builder family's
statements over a given list of frames (`Contract`, `Frame`, `Chain`, the queue model `step`/`replay`/`chunks`) are
`Blanc/Lift/BuilderRequest/Delivery.lean`, family-local; word and natural request fee at fraction 17, through excess
2892 and not at 2893, are `Blanc/RequestFeeWordDomain.lean` (with total fee helpers `specFee`, `wordFee`, `quotedFee`,
`quoted_run` and `quotedFee_eq_spec_iff` in `Blanc/RequestFeeWord.lean`). The fee loop's run, length (at most 462, tight at 2892) and value on that domain, its linear bound above (`quotedFee_eq_spec_of_le`, `quotedFee_lt_spec_2893`), are `Blanc/RequestFeeWordBound.lean`.
The converse, every *successful* system-arm run from any storage, memory, calldata and gas on a covered
fork, is [`Blanc/Lift/RequestSystem/PathInv.lean`](../Blanc/Lift/RequestSystem/PathInv.lean): the trees inverted
node by node (`dispatch_system_inv`, `setup_inv`, `header_inv`, `book_inv`, `final_inv`, and `over_inv`/`excess_inv`
for the plain arm), the loop by induction on the count (`SysPath.loop_inv`, over a runtime's `SysPath.BodyInv`), and
the frame: `SysPath.frame_inv`/`SysPath.exec_frame_inv` (non-static, post state `sysState`, unchanged `.logs`, the return window over
`SysPath.memFold`) with `SysOutput.frame_inv_output` (on well-formed memory that window is `drained`, whatever the
memory held). A runtime supplies `BodyInv` for its record body and `ExcessInv` (from `excess_inv` for the plain
arm).
For original successful prefixes over either storage-gas backend, use
[`Blanc/Lift/RequestSystem/PrivilegedInv.lean`](../Blanc/Lift/RequestSystem/PrivilegedInv.lean).
`StoreInv` records the effects of an actual successful SSTORE; `setup_access_inv`,
`book_store_inv`, `final_store_inv` and `SysPath.prefix_inv` consume the selected access
rules and that callback. The prefix ends at the runtime's own excess tree and reuses
the existing record-loop inversion. It assumes no ready reservoir, chosen gas,
fresh storage or empty memory; a consumer must discharge the actual store and body
callbacks and its own excess arm.
`Blanc/Lift/RequestSystem/Effects.lean` holds what a call touches and returns: `sysState_getElem_ne` and
`sysState_getElem_congr` (every other account is unchanged; its own result depends only on its own account),
`sysFold` with `run_sysFold` and `sysFold_getElem` (a fold of calls, by account), `SysPath.frame_exec` (the walk as
an `Exec` at any system-caller `Sevm`, not only the phase's message), and `SysOutput.drained_length` and
`callPost_output_length` (return length from any storage). Worked consumers:
`Blanc/Lift/WithdrawalRequest/AmsterdamSystem.lean`,
`Blanc/Lift/SystemExecution/ConsolidationRequest/AmsterdamSystem.lean`, and the phase at
`Blanc/Composition/RequestPhaseAmsterdam.lean`.

#### C9.10. I need a Vyper 0.2 runtime's idioms

- Vyper 0.2.x runtimes: the frame prologue memory `vyMem`/`vyImg` and `sstoreCost_le`, in
  [`Blanc/Lift/Vyper.lean`](../Blanc/Lift/Vyper.lean).
- Unrolled Vyper frame save/restore chains (a counter word walks a frame `[lo, lo + 32 n)`,
  pushing or popping one word per copy): constants `FrameLoopTpl`;
  memory `saveMem` and `restoreMem`, and the word-slot carrier `Words M L` (`Words.write`, `.agree`, `.read`) over
  `memWord`/`Mem.AgreeOutside`; all in
  [`Blanc/Lift/VyperFrameLoop.lean`](../Blanc/Lift/VyperFrameLoop.lean).
- Vyper 0.2.x word-slot frames:
  the frame carrier `WordFrame M0 M lo ws` (`ws` at `lo + 32 j`, `M0`'s size, agreement off the
  window, `Mem.Wf` kept); the `int128` range check `ri_sltV`; the untracked load `ric_mloadU`
  (`imloadU`), `isltV`, and `xname` (name the tracked memory of a forward walk); all in
  [`Blanc/Lift/VyperCheckedArith.lean`](../Blanc/Lift/VyperCheckedArith.lean).
- Vyper 0.2.x internal-callee walks (a callee's value contract without concrete memory
  terms, windows as `Mem.KeepsOff` of `Blanc/Lift/MemGlue.lean`): the tracked walk memory
  `MemTrack M₀ M W L` (kept off the windows `W`, carrying the words `L`, well formed) with the
  steps `ric_mloadT`/`ric_mstoreT`/`ric_mstoreO` (overwrite, `wordsOff`)/`ric_keccakT` (tactics
  `imload`/`imstore`/`imstoreO`/`ikeccak`, `wmem`, `iassert`) and the
  node-directed inversion step `istep`; load-only bases `SloadsOnly sevm b B` (`.state`,
  `.getStor`, `.logs`, `.output`, `.getCode` in `VyperCallee.lean`; `.idReady` in
  `IdentityCallGas.lean`); the
  `ISZERO (LT …)`/`ISZERO (GT …)` branch readings; forward twins over a covered memory with the
  final memory named at the return (`∃ M', RunExactCut … ∧ facts`): `xlift`, `rxc_mloadT`,
  `rxc_mstoreT`, `rxc_keccakT`, `rxc_retT`,
  and the node-directed forward tactic `xstep` (`xmload`, `xmstore`, `xkeccak`, `xassert`,
  `xzero`, `xjump`, `xgoto`, `xret`); all in
  [`Blanc/Lift/VyperCallee.lean`](../Blanc/Lift/VyperCallee.lean).
- Vyper 0.2.x walk kit (inversion `ric_*`/`ri_*` over cut runs, forward `rxc_*` over exact
  cut runs):
  fixed-array storage slots `mstore(0xc0, s); sha3(0xc0, 0x20) + i` (`vyArrayBase`,
  `vyArraySlot`; pushed word `Bytes.keccak s.toBytes + i`) in
  [`Blanc/Lift/VyperArraySlot.lean`](../Blanc/Lift/VyperArraySlot.lean);
  a value-0 `CALL` of the identity precompile (`IdReady`, `processMessage_identity_clean`,
  `ri_call_identity`, world relation `ShaCallPost`) in
  [`Blanc/Lift/IdentityCall.lean`](../Blanc/Lift/IdentityCall.lean); an unchecked identity
  copy that forwarded `gas()` and failed at a nonzero depth leaves no gas
  (`ri_call_identity_gas_fail`), and `IdReady` survives `SLOAD`
  bases (`IdReady.afterSload`; `SloadsOnly.idReady` across a load-only base), in
  [`Blanc/Lift/IdentityCallGas.lean`](../Blanc/Lift/IdentityCallGas.lean);
  a one-word `STATICCALL` reply with its `RETURNDATASIZE > 31` check (`vyReplyWord`,
  `ric_vyStaticReply` / `rxc_vyStaticReply`) and a checked subtraction from a saved word
  (`vyChkSubMem`, `ric_vyChkSubMem` / `rxc_vyChkSubMem`, `chkSub_of_le`) — the fee-on-transfer
  balance difference — in
  [`Blanc/Lift/BalanceDiffCall.lean`](../Blanc/Lift/BalanceDiffCall.lean);
  the `raw_call(…, max_outsize=32)` tail (`VyRawSite`, `vyRawCallTail`/`vyRawCallJoin`/
  `vyRawCallCheck`, `RawCallOk`, `ric_vyRawCall`, `ric_vyRawCallTail`, forward
  `rxc_vyRawCallTail` at `rawTailCost (min len 32)` with memory `vyRawMem`), with the
  byte-number bridge `Bytes.toNat_toB256_of_length` / `B256.toNat_eq_toBytes` and the
  no-`Mem.Wf` byte readers `Mem.write_getD_inside`, `Mem.read_fst_of_getD`, in
  [`Blanc/Lift/VyperRawCall.lean`](../Blanc/Lift/VyperRawCall.lean).

#### C9.11. I need deployment, CREATE, CREATE2 or a clone

- Deploying lifted creation code: `liftCreatePost_facts` identifies the target account as the raw
  target with its code replaced, followed by `Acct.clearIfEmpty`; nonempty
  installed code recovers the original raw storage equality. Arbitrary creation
  messages do not supply the nonce-zero collision premise of an actual CREATE.
  The constructor walk steps
  the shared kits lack (`rx_codecopy`, `rxc_sstore`, `rxc_callvalue`, `rx_return_any` and
  `rxc_return_any`, with the halting state `returnPost` named over a variable state;
  `returnPost_state` projects the persistent world before substituting
  concrete memory images) in
  [`Blanc/Lift/Deploy.lean`](../Blanc/Lift/Deploy.lean); and the further steps solc 0.8
  constructors need (`rx_push0`, `rx_codesize`, `rx_log2`) in
  [`Blanc/Lift/CreationOps.lean`](../Blanc/Lift/CreationOps.lean).
  For exact creation walks under the selected historical schedule, use
  [`Blanc/Lift/HistAccessWalk.lean`](../Blanc/Lift/HistAccessWalk.lean):
  `Ninst.runCompiled_sload_selectedH`/`runCompiled_sstore_selectedH`,
  `rx_sstoreH` and `rxc_sload_selH`/`rxc_sstoreH` charge
  `sloadCostH`/`sstoreCostH` and retain `afterSloadH`/`afterSstoreH`; then
  [`Blanc/Lift/HistCreate.lean`](../Blanc/Lift/HistCreate.lean):
  `sstoreCostH_congr` transports only the actual price inputs. `sloadCostH_muir_eq`
  and `sstoreCostH_muir_le` give the actual 800-gas read and at-most-20000 write
  under Muir rules. `liftCreate_postH`
  and `liftCreate_okH` lift a checked exact constructor run from `stateGas = none`,
  retaining the historical target touch. Code admissibility, deposit gas, size,
  value transfer and the run remain explicit obligations.

  For a contract deployed through the deterministic CREATE2 factory
  (`0x4e59b448...956c`, 69 bytes), use
  [`Blanc/Lift/Create2Factory/Walk.lean`](../Blanc/Lift/Create2Factory/Walk.lean):
  `factory_install` takes a `FactoryMessage` (factory code at its address, zero value,
  non-static, calldata a salt then the init code) on a covered fork and a consumer's checked
  child creation, and returns the child's code, storage and nonce one at the address computed by
  `create2NewAddress`, under the actual collision check's premises; `factory_message` is the
  same with the child's outcome left abstract. The factory's certificate, checked lift, lifted
  code and jump table are
  [`Blanc/Lift/Create2Factory/Cert.lean`](../Blanc/Lift/Create2Factory/Cert.lean),
  [`Blanc/Lift/Create2Factory/Check.lean`](../Blanc/Lift/Create2Factory/Check.lean),
  [`Blanc/Lift/Create2Factory/Code.lean`](../Blanc/Lift/Create2Factory/Code.lean) and
  [`Blanc/Lift/Create2Factory/Jumps.lean`](../Blanc/Lift/Create2Factory/Jumps.lean). For a `geas`-style constructor that
  ends `PUSH0; CODECOPY; PUSH0; RETURN` over a creation input that is a prefix and a
  registered runtime, use
  [`Blanc/Lift/RuntimeInstall.lean`](../Blanc/Lift/RuntimeInstall.lean):
  `creation_runtime_window` reads the runtime window, `push0RuntimeReturn_runExact` is the
  terminal walk from empty memory (the PUSH0 twin of `solcRuntimeReturn_runExact`), and
  `install_of_run` turns a checked constructor run into the settled account with the
  runtime installed, no code or storage outcome assumed.

  For Solidity's terminal code-window sequence, use `solcRuntimeReturn` and
  `solcRuntimeReturn_runExact` from `Lift/Deploy.lean`. The common forward
  theorem accepts nonempty PUSH encodings for the length and offset, a nonzero
  length, aligned symbolic memory and four-word stack room. Its exact charge
  is memory expansion plus `gasCopy * ceilDiv length 32 + 19`; RETURN causes
  no additional expansion. `solcRuntimeReturn_effects` inverts a successful
  source run to the actual returned code window and unchanged storage, without
  a fork or memory-alignment premise. Neither theorem identifies a runtime
  literal or proves CREATE settlement or historical installation.
  The `solc-runtime-return` recipe matches only a named terminal-body exact
  run ending in a halted outcome; it never unfolds arbitrary certificate
  entries or concrete machine images to discover this pattern.
  Installation by
  `processCreateMessage` is not part of them.
  For exact creation walks under the selected historical schedule, use
  [`Blanc/Lift/HistAccessWalk.lean`](../Blanc/Lift/HistAccessWalk.lean):
  `Ninst.runCompiled_sload_selectedH`/`runCompiled_sstore_selectedH`,
  `rx_sstoreH` and `rxc_sload_selH`/`rxc_sstoreH` charge
  `sloadCostH`/`sstoreCostH` and retain `afterSloadH`/`afterSstoreH`; then
  [`Blanc/Lift/HistCreate.lean`](../Blanc/Lift/HistCreate.lean):
  `sstoreCostH_congr` transports only the actual price inputs. `sloadCostH_muir_eq`
  and `sstoreCostH_muir_le` give the actual 800-gas read and at-most-20000 write
  under Muir rules. `liftCreate_postH`
  and `liftCreate_okH` lift a checked exact constructor run from `stateGas = none`,
  retaining the historical target touch. Code admissibility, deposit gas, size,
  value transfer and the run remain explicit obligations.
- To retain constructor metadata through symbolic historical walks, use
  [`Blanc/Lift/CreateSettlementMeta.lean`](../Blanc/Lift/CreateSettlementMeta.lean).
  `CreateRunMeta` records a zero refund, empty logs, the inherited deletion set and
  created-target membership. Its `st`, `returnPost`, `of_meta_eq` and `afterSstoreH`
  operations preserve these facts; the store operation needs a currently zero slot
  and uses created membership to justify its original zero value.
  `sstoreRefundH_zero_zero` covers all selected refund schedules without evaluating
  a hash. `ShaCallPostDelete` extends the SHA successor facts with deletion-set
  equality; the Muir packed-SHA constructors retain this stronger record.
  `shaResume_accountsToDelete`, `recordTouch_accountsToDelete` and
  `afterSstoreH_accountsToDelete` are symbolic projections, and `St_meta` projects
  metadata before any concrete memory image is substituted.
- The settled world of a zero-value CREATE as a closed term of its input world (so a later
  message that takes it as `origState` can evaluate it): the entry world `entryState` in
  [`Blanc/Lift/CreateEntry.lean`](../Blanc/Lift/CreateEntry.lean).
- Creating an EIP-1167 clone of any implementation `I` by the 9-byte copier `602d3d8160093d39f3`:
  `creationCode I` (copier ++ `forwarderCode I`), in
  [`Blanc/Lift/Clone1167.lean`](../Blanc/Lift/Clone1167.lean). A modeled harness: a consumer labels
  its registered input synthetic.
- Shared `CREATE2` address and state helpers live in
  [`Blanc/Lift/Create2Deploy.lean`](../Blanc/Lift/Create2Deploy.lean); opcode composition
  from explicit rule facts lives in [`HistCreate.lean`](../Blanc/Lift/HistCreate.lean).
  `create2AddressOfHash` computes the CREATE2 address from an init-code digest
  (with `create2NewAddress_eq_ofHash` its identity against Jaune's
  `create2NewAddress`). An admitted `CREATE2` (non-static, affordable endowment,
  creator nonce below the maximum, positive depth) needs only
  `Create2TargetNoCollision`: target nonce zero and code size zero, with arbitrary
  target storage. `Xinst.step_create2_spawnH_of_nonce_code` constructs the
  `.spawn` over `create2Prepared`. When the creation message succeeds without
  error (`processCreateMessage … = .ok child`, `child.error = none`),
  `create2_runCompiledH_of_nonce_code` closes the spawn into a compiled step
  (`Ninst.RunCompiled`) to `create2Post` with the new address on the stack and
  the child's world installed. Create-message entry resets target storage.
  The original `Create2TargetEmpty`, `Xinst.step_create2_spawnH` and
  `create2_runCompiledH` retain their original nonce/code/storage contracts as
  compatibility APIs. The registered `runcompiled-construction` goal-head
  triggers select function walks, not these instruction-level CREATE2 spawns;
  discover these helpers through this branch.

#### C9.12. I need free-pointer memory images or solc-0.4 writer walks

- Accumulated-cost exact walks and a Reads-based fixed-size free-pointer image:
  [`Blanc/Lift/AccumulatedWalk.lean`](../Blanc/Lift/AccumulatedWalk.lean)
  owns `Blanc.Lift.AccumulatedWalk.FpM`, its image operations, `rk`,
  internal-call adapters and the `xrun`/`xcallM` step tactics. The pointer is
  arbitrary; the carrier retains its existing Reads witness and fixed-size
  write interface, rather than changing to the separate extending `PtrMem` shape.
- Initial frame-gas field independence:
  [`Blanc/Lift/GasField.lean`](../Blanc/Lift/GasField.lean) gives
  `sloadCost_gasField`, `sstoreCost_gasField`, `afterSload_gasField`,
  `afterSstore_gasField` and `dataWord_gasField` in `Blanc.Lift.GasField`.
  `Blanc.Lift.callChildPost_withGasLeft` is owned beside the generic child-post
  definition in [`Blanc/Lift/ExactWalkCallChild.lean`](../Blanc/Lift/ExactWalkCallChild.lean);
  parent gas and stack projections reuse the existing `Blanc.callSpawnParent_gasLeft`
  and `Blanc.callSpawnParent_stack` in the shared forward-call owner.
  These are identities of generic frame operations, not cost or behavior
  assumptions about a token.

- Free-pointer memory with a pointer independent of allocation: `PtrMem p n M`
  in [`Blanc/Lift/ExactWalkMemory.lean`](../Blanc/Lift/ExactWalkMemory.lean)
  combines aligned size, `Mem.Wf` and the existing `MemMatches` word at offset64.
  It permits pointer128 with allocated size96. `PtrMem.init`, `word`, `write`,
  `set` and `read_self` expose initialization, disjoint word writes, pointer
  replacement and reads within the allocation. Use this carrier when the fixed pointer 96 of `FpMem` does not describe the bytecode.
- Free-pointer word without an allocation size: `PtrWord p M` in
  [`Blanc/Lift/PtrWordMemory.lean`](../Blanc/Lift/PtrWordMemory.lean) keeps only
  `Mem.Wf M` and the pointer word at offset64. Use it instead of `PtrMem` when a
  walk's allocation grows by an unbounded reply (for example a moved free pointer
  after a full-returndata copy), so no size bound is owed. `PtrWord.of_ptrMem`
  enters it; `write` (any byte list at offset96 or above), `extend`, `extends`
  and `set` (pointer replacement) preserve it.
- Gas-exact writer walks for solc-0.4-style runtimes: the scratch-memory invariant `FpMem n M` (word-aligned,
  free pointer `0x60`, kept for an arbitrary `M`; `FpMem.init`, `FpMem.write`, `FpMem.write_out`,
  `FpMem.readback`, `scratchW`), its steps (`rx_mstoreF`, `rx_mstoreOut`, `rx_mloadFp`, `rx_keccakF`,
  `rx_log2W`, `rx_log3W`, `rx_returnW`, `rx_stop`, `rx_mask20`, `rx_mask20_adr`, `rx_swap4`), `SLOAD`/`SSTORE` with
  named charges (`rx_sload_selC`, `rx_sstoreC`), the account facts after a selected `SSTORE`
  (`afterSstore_getAcct`, `afterSstore_getBal`, `afterSstore_empty`, `afterSload_getAcct`), `require(x >= y)`
  (`ltCheck_zero_of_le`) and the tactic macros that apply one step to the head instruction (`rdest`, `rpush`,
  `rdup`, `rswap`, `rpop`, `radd`, `rsub`, `riszero`, `rmask`, `rmst`, `rmld`, `rkec`, `rhash`, `rsloadC`,
  `rsstoreC`, `rsent`, `rlog2`, `rlog3`, `rreq`) in [`Blanc/Lift/ExactWalkSolc.lean`](../Blanc/Lift/ExactWalkSolc.lean).

#### C9.13. I need a whole-contract property without per-path walks

- Properties of the lifted program without per-path walks: a state-silent
  entry set (`SilentSet`, `SFunc.Run.state_of_silent`) in
  [`Blanc/Lift/Silent.lean`](../Blanc/Lift/Silent.lean), its balance analogue
  (`BalSilentSet`, `SFunc.RunP.getBal_of_balSilent`) in
  [`Blanc/Lift/BalSilent.lean`](../Blanc/Lift/BalSilent.lean). Its stronger
  `SFunc.RunP.balance_deletion_frame_of_balSilent` also preserves both
  deletion-tracking sets through the same induction, with the old balance
  theorem as a projection; no fork or installed-code premise is added.
  `Blanc.Lift.frame_keeps_balances` lifts `BalSilentSet` to a successful frame over any `CodeSem`, and
  [`Blanc/ExecutionKeptBalSilent.lean`](../Blanc/ExecutionKeptBalSilent.lean) lifts it to `KeptValueAt` and
  `KeptHistory.systemContract_bal_covers` (including precompile exclusion for canonical system contracts and
  `sum_map_filter_le` for withdrawal slices).
  [`Blanc/Lift/Quiet.lean`](../Blanc/Lift/Quiet.lean) proves that a static
  frame on a covered fork keeps its log list on every successful outcome, committing or
  not (`Exec.logs_eq_of_static_ok`; committed form `Exec.logs_committedPost_eq_of_static`).
  For a lifted tree that can write storage and make static calls while preserving logs,
  [`Blanc/Lift/LogSilent.lean`](../Blanc/Lift/LogSilent.lean) supplies
  `Ninst.logSilent`, `SFunc.logSilent`, the reference-closed `LogSilentSet`,
  `Ninst.logs_of_logSilent` and `SFunc.Run.logs_of_logSilent`.
  The same original run preserves its entry log list under `CoveredFork` and the checked
  instruction/reference predicates; the scanner permits SSTORE and STATICCALL,
  rejects LOG instructions and excludes SELFDESTRUCT terminals.
- The preservation ladder over a code image instead of `Prog.compile`:
  `CodeSem` (image, run relation, `correct`) in
  [`Blanc/CommonCore.lean`](../Blanc/CommonCore.lean); `ContractSpecSem`, its
  `Sound`/`Preserves` rungs, `preserves_lift_sem` and `post_of_call_self` in
  [`Blanc/LadderSem.lean`](../Blanc/LadderSem.lean); the admitted forms
  `SoundAdmitted`/`PreservesAdmitted`/`preserves_inv_admitted` in
  [`Blanc/ContractAdmissionSem.lean`](../Blanc/ContractAdmissionSem.lean) and
  `lift_inv_admitted_sem` in
  [`Blanc/ExecutionAdmissionSem.lean`](../Blanc/ExecutionAdmissionSem.lean),
  which carry a frame-local premise up the message, transaction, body and history rungs. The
  `Prog.compile` ladder in [`Blanc/Ladder.lean`](../Blanc/Ladder.lean) is the
  instance of this one at `Prog.compile`, with byte-identical statements;
  [`Blanc/LadderBase.lean`](../Blanc/LadderBase.lean) holds the
  code-independent vocabulary both share.

There is no recipe: the entry points are whole-contract theorems, not goal
shapes a trigger could match.

#### C9.16. I need a fixed synthetic token for a concrete witness

- Fixed synthetic coin fixture: the hand-assembled **299-byte Token20** is
  shared support for concrete witnesses, not a mainnet token or an arbitrary
  ERC-20 implementation. Its historical inputs and registry IDs remain fixed.
  Success runs are proved; documented rejection behavior of the bytes is not
  upgraded into a universal proved property. Balances use address-word slots;
  transferFrom always decrements allowance, including self-spends.
  `Blanc/Lift/Token20/Cert.lean` supplies the runtime literal/certificate.
  `Blanc/Lift/Token20/Check.lean` supplies the runtime kernel acceptance and layout.
  `Blanc/Lift/Token20/Creation/Cert.lean` supplies the creation lift certificate.
  `Blanc/Lift/Token20/Creation/Check.lean` supplies the creation kernel acceptance.
  `Blanc/Lift/Token20/Creation/Input.lean` supplies the 315-byte constructor/runtime input.
  `Blanc/Lift/Token20/Run.lean` supplies the scratch/approve exact-run helpers.
  `Blanc/Lift/Token20/RunBalance.lean` supplies the balanceOf success run.
  The 16-byte constructor mints 10^6 to its creator and installs exactly the
  fixture runtime. Instance worlds and concrete V± histories stay local.

**Walk kits for coin runtimes.**

- [`Blanc/Lift/InvWalkLegacy.lean`](../Blanc/Lift/InvWalkLegacy.lean): step, branch and normalization tactics for inversion walks of pre-0.5 solc runtimes (`EXP` packed reads, `div`-and-mask selectors).
- [`Blanc/Lift/HistIdentityCall.lean`](../Blanc/Lift/HistIdentityCall.lean): `IdReadyH` across `afterSloadH` and `afterSstoreH`.
- [`Blanc/Lift/WalkCost.lean`](../Blanc/Lift/WalkCost.lean): `xcost` support: closing a forward walk's charge as a bound.
- [`Blanc/Lift/WalkCostExact.lean`](../Blanc/Lift/WalkCostExact.lean): `xsum` and the storage-charge facts: closing it as an equality.
- [`Blanc/Lift/LinearRuntimeSafety.lean`](../Blanc/Lift/LinearRuntimeSafety.lean): `selfdestructFreeCheck`: no instruction start of a code holds `SELFDESTRUCT`.
- [`Blanc/Lift/WriteSiteMapping.lean`](../Blanc/Lift/WriteSiteMapping.lean): `BalancePath`: how a balance-table row reads its site.
- [`Blanc/Lift/CodeImage.lean`](../Blanc/Lift/CodeImage.lean): `CodeSem.ofBytes`: the code semantics that records only which bytes a frame runs.

For historical (pre-Shanghai) walks, the size-optimized packed-SHA site and static-only In-frames:

- The historical SHA-256 `STATICCALL` kit (`ShaReadyRules`, `ShaReady.toRules`,
  `ri_staticcall_shaH_of_delegation`; the solc packed-SHA site `ric_shaCallH_of_delegation`,
  `ric_copy_shaH_of_delegation`, `ric_pack_shaH_of_delegation`) is in
  [`Blanc/Lift/HistShaWalk.lean`](../Blanc/Lift/HistShaWalk.lean).
- The packed-SHA site as solc emits it under its size-favouring constant optimiser
  (`mcpyTreeN`, `mergeTreeN`, `copy_shaN_gen`, `copy_shaN`, `packed_sha_pairN`) is in
  [`Blanc/Lift/PackedShaSize.lean`](../Blanc/Lift/PackedShaSize.lean), and its form under actual
  Muir Glacier rules (`staticcall_sha_stepMuir`, `copy_shaNMuir_gen`, `copy_shaNMuir`,
  `packed_sha_pairNMuir`) in
  [`Blanc/Lift/HistPackedShaSize.lean`](../Blanc/Lift/HistPackedShaSize.lean).
- The selected-domain static-only frame facts are in
  [`Blanc/Lift/StaticOnlyFramesIn.lean`](../Blanc/Lift/StaticOnlyFramesIn.lean):
  `parentPrefix_exec_staticcall_of_cert_noStateGas` uses a frame's neutral gas schedule, and
  `Exec.staticOnly_descendantFrames_flatMap_eq_nilIn` carries the selected fork predicate through
  actual child environments.
- [`Blanc/Lift/WalkKitSupport.lean`](../Blanc/Lift/WalkKitSupport.lean) collects the walk-kit
  lemmas these consumers share: `BaseRel.trans`, `rxc_callRet`, `rx_exp'`, `ric_jumpCut`,
  `ric_undefined`, `ri_byte`, `ri_log1`, `SFunc.RunP.not_halted_entry`, the quiet-function facts
  (`SFunc.quiet`, `QuietSet`, `Burn.world`, `SFunc.Run.world_of_quietH`), the historical
  access facts `afterSloadH_accessedAddresses` and `afterSstoreH_getCode`, `lift_sound`,
  `cursor_of_parentPrefix`, `Xinst.isStaticcall`, `parentPrefix_exec_staticcall_of_cert` and
  `liftCreate_ok`.

## Common-library-first workflow

A needed definition, lemma, tactic, or instance has a **generic shape** when
its statement nowhere mentions the contract immediately being worked on — when
that contract's own names could be abstracted away without changing what it
says. Every generic-shaped need triggers this workflow. It is the standing
default for all Blanc work, not per-goal advice, and it exists because the
point of each new contract is to leave the common library stronger than it
found it, not merely to add the contract.

1. **Search before writing.** Follow the branches above, search the
   declarations themselves, and run `blanc_suggest` at the goal. A `blanc_suggest`
   no-match is not evidence that no shared declaration exists; the registry
   branches and declaration search are the authority on existence.
2. **Found in a shared module: use it.** When a close variant exists but is
   too narrow, generalize the shared declaration in place, provided every
   existing proof still elaborates — verify with the build and the repository
   gates. A generalization that would force consumer rewrites is a design
   change to surface, not a silent rewrite.
3. **Found only in another contract's module: hoist it first, then use it.**
   Move it to a shared module below every consumer, rename away any
   contract-claiming name (the `wbsum` → `balSum` example in `README.md`,
   *Module hierarchy: contracts are siblings*), remove the contract-local
   copy, and use it through the shared owner. Never import a sibling contract
   to reach it; `scripts/check-layering.sh` fails that import in either
   direction.
4. **Found nowhere: build it in the common library, then use it.** The
   generic shape that motivated the search is the placement decision — a new
   generic declaration is born in a shared module, not in the contract that
   first needed it. Place it in the **narrowest shared owner**: the lowest
   shared module below every consumer, or a new small module imported only by
   its consumers. A hub — a module more than 500 production modules import,
   such as `Blanc/CommonCore.lean`, a `Blanc/CommonProofs/*.lean` piece or the
   ladder — is not a default destination: every line it gains is re-elaborated
   by all of its dependents, and `scripts/check-proof-module-size.sh` blocks a
   hub's growth past its ceiling. The same rule applies when hoisting (step 3).
5. **Close with discoverability.** Every common-library addition or change —
   built, generalized, or hoisted — updates this registry in the same change:
   add the declaration to the narrowest branch above (or add a sub-branch),
   and when a reliable goal shape exists, register a goal-sensitive recipe in
   `scripts/proof-recipes.toml` and regenerate the surfaces
   (`python3 scripts/generate-proof-recipes.py --write`). Verify with
   `scripts/check-proof-recipes.sh --base main`. Discoverability closure is
   part of the change that touched the library, not a follow-up task.

Do not add a contract module as a registry destination: that is evidence the
declaration has not yet reached its common owner.

The workflow is enforced as well as documented, and this section is the map
of that machinery: [`scripts/check-layering.sh`](../scripts/check-layering.sh)
owns placement (no cross-contract import, no shared module importing a
contract); [`scripts/check-proof-recipes.sh`](../scripts/check-proof-recipes.sh)
keeps the recipe registry and its generated surfaces synchronized, and reports
byte-identical declaration copies and unregistered local selector tables among
changed declarations; and
[`scripts/check-proof-duplication.sh`](../scripts/check-proof-duplication.sh)
holds the shrink-only textual-duplication baseline. A red row from any of them
usually means a step above was skipped. Bytecode-segment sharing between call
sites is a separate, opt-in mechanism with its own guide outside this
repository; nothing in this workflow requires it.
