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

## Root: what are you trying to do?

- Construct or analyze execution: go to [E — execution](#e--execution).
- Prove that an observation survives execution: go to
  [I — invariance and noninterference](#i--invariance-and-noninterference).
- Simplify or relate machine states: go to
  [S — state and machine updates](#s--state-and-machine-updates).
- Reason about bytes or EVM memory: go to
  [M — bytes and memory](#m--bytes-and-memory).
- Reason about the integer exponential loop and its iteration count: go to
  [S9](#s9-i-need-the-integer-exponential-recurrence-or-a-finite-loop-witness).
- Relate raw execution to message/frame settlement: go to
  [T — settlement](#t--settlement).
- Relate source programs, compiled code, and deployed artifacts: go to
  [C — compilation and deployment](#c--compilation-and-deployment).
- Verify bytecode Blanc did not compile (a deployed contract's runtime
  bytes): go straight to
  [C9](#c9-i-need-to-verify-deployed-bytecode-blanc-did-not-compile).
- Link an auxiliary call table by name instead of by index: go straight to
  [C6](#c6-i-need-to-link-an-auxiliary-call-table-by-name-instead-of-by-index),
  the last branch of that section rather than its head.
- None matches: search public declarations in `Blanc/CommonCore.lean`,
  `Blanc/CommonProofs.lean`, and the ladder (`Blanc/LadderBase.lean`,
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
  point; a new EVM-generic execution fact belongs in Jaune, and
  `scripts/check-extraction-ownership.sh` fails if Blanc redeclares a
  relocated declaration. Blanc's own list
  prefix/split algebra (`Split`, `Pref`, `Frel`) lives in
  [`Blanc/Basic.lean`](../Blanc/Basic.lean), which also holds
  `Blanc.getElem?_append_mid` (an element of a middle block at `A.length + j`). Both are the substrate the
  branches below are stated over, so read the declaration and its module
  documentation there rather than expecting a need-first branch for it.
- Exact byte-pattern offsets: [`Blanc/BytePattern.lean`](../Blanc/BytePattern.lean)'s
  `BytePattern.occurrences` scans successive suffixes in increasing order.
  `mem_occurrences_iff` characterizes matches of a nonempty pattern without a
  caller-supplied offset bound; `bounds_of_match` supplies the fit bound.
  `match_iff_eq_of_singleton` and `eq_of_singleton` turn a singleton scan into
  unique-position facts. Empty patterns yield no offsets. Every byte offset is
  considered, including instruction immediates; these facts alone say nothing
  about parsing or execution.
- Fork coverage: `CoveredFork f` (`f ∈ coveredForks`) in `Blanc/Semantics.lean`.
  Consume it only through `CoveredFork.stateGas_none`, `bal_none`,
  `rules_stateGas_none`, `rules_bal_none`, `rules_access`, `rules_push0`,
  `rules_shifts`, `rules_touchedSweep`, `rules_refundQuotient`, `rules_dataNonZero`,
  `rules_calldataFloor`, `rules_sstore`, `requests_eq`,
  `beaconRoots_not_precompile`, `historyStorage_not_precompile`, `of_eq` and,
  where a per-fork case split is unavoidable, `CoveredFork.cases`. Discharge a
  schedule premise with a concrete config lemma such as
  `Drip.concreteConfig_covered`. `mainnetChainConfig_covered` takes both the
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
  A concrete source-fragment consumer is `ProxyCreation.isContract_runExact`
  in [`Blanc/Lift/Usdc/ProxyCreation/CodeSize.lean`](../Blanc/Lift/Usdc/ProxyCreation/CodeSize.lean):
  the registered constructor entry returns the actual B256 code-size predicate
  at the flat charge plus 47 gas. This is an exact compiled source walk;
  actual bytecode entry/return and whole-constructor execution remain separate.
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
- For that prefix across a whole public entry — the `fsig` dispatcher head,
  the tree dispatcher, and the standard guards — use
  [`Blanc/FuncMainPrefix.lean`](../Blanc/FuncMainPrefix.lean).
  `run_prefix_prepend` and `run_prefix_branch` are the path-agnostic forms of
  `Func.RunPrefix.of_run_prepend` and `of_run_branch`: the start path is
  arbitrary and the cut's path is hidden, so callers compose with
  `Func.RunPrefix.trans` and never do path arithmetic.
  `dispatch_entry_of_run_mainWith_prefix` walks a nonempty
  `Func.mainWith k dt` run to its dispatch tree with the selector alone on the
  stack and state, memory, logs and output unchanged;
  `dispatchWith_run_prefix_of_sorted` and `dispatchWith_run_prefix_of_sorted_list`
  continue through a sorted indexed-fallback `dispatchWith` tree to a member
  selector's body, removing the selector and preserving state and memory.
  For the guards, `run_prefix_nonpayable_logs` peels `nonpayable` (zero
  call value; state, memory, logs and output unchanged),
  `of_run_exactCalldata_prefix` peels the exact-calldata-length guard
  `exactCalldata`, and `of_run_nonpayable_exactCalldata_prefix` composes both.
  Nothing in their statements concerns DRIP. Each lemma returns a prefix plus
  the body run from the cut, never a compiled walk; to place the cut on an
  actual execution use
  `Exec.Deriv.SourceCursor.ofRunPrefix` (E5). Worked uses: the WETH `withdraw`
  locator in `Blanc/Composition/ProrataWethVaultWithdrawLocator.lean` and
  DRIP's exit locator. The same trigger check as `Func.RunPrefix` applies, so
  there is no recipe.
- For a successful source branch whose selected arm calls a known
  nonreturning auxiliary, use `of_run_branch_call_of_not_run` in
  [`Blanc/CommonProofs.lean`](../Blanc/CommonProofs.lean).  Its shared
  specializations `of_run_branch_call_revert`,
  `of_run_branch_call_revertWith`, and
  `of_run_branch_call_revertReturnData` cover the standard empty,
  constant-payload, and returndata-bubbling reverters.
- Known stack steps without a tactic arm: `prefix_of_mul`, `prefix_of_div`,
  `prefix_of_timestamp`, `prefix_of_xor`, `prefix_of_extcodesize_val`, and
  `prefix_of_argCheckNonAddress` in
  [`Blanc/CommonProofs.lean`](../Blanc/CommonProofs.lean).
  The `EXTCODESIZE` helper pins the exact code-size word from the instruction's
  input state and carries unchanged memory across address warming.
  For an exact stack rather than a prefix, use
  `Ninst.extcodesize_stack` in
  [`Blanc/CodeReadInversion.lean`](../Blanc/CodeReadInversion.lean).
  It derives the output word followed by the unchanged tail from the actual
  input-stack equation and successful instruction run.
  `Ninst.extcodesize_stack_length` supplies the arity fact behind it. Both
  cover flat and warm/cold access without a fork or BAL restriction.
  Their stack-equality conclusions have no reliable dedicated recipe trigger.
- The common `fsig +++ dispatch` entry preserves logs and output by
  `fsig_logs` and `fsig_output` in `Blanc/CommonProofs.lean`.
- Recover a known selected body from a sorted tree dispatcher with
  `reach_of_dispatch` for the inline-revert form or `reach_of_dispatchWith`
  for the indexed-fallback form in
  [`Blanc/CommonProofs.lean`](../Blanc/CommonProofs.lean). Both consume the
  exact selector/list membership and return the selected body with the
  selector removed while preserving world state and memory; neither asserts
  that an execution exists.  `reach_of_dispatchWith_logs` is the same
  factorization with the dispatcher's log and output silence carried to the
  selected body.  `reach_of_dispatch_logs` in
  [`Blanc/ReachDispatchPrefix.lean`](../Blanc/ReachDispatchPrefix.lean) is the
  inline-revert form with log/output silence plus the loose gas-free walk
  prefix reaching the selected body's entry state.
- Rule a selector *out* at source level with `not_run_dispatch_of_miss` in
  [`Blanc/CommonProofs.lean`](../Blanc/CommonProofs.lean): a selector with no
  leaf in the tree has no successful inline-revert dispatcher run at all, so a
  contract's selector census becomes "every successful call is one of these
  entries".  It is the `Func.Run` counterpart of the compiled
  `DispatchTree.dispatchMiss_runCompiledTo_with_path`.
- Peel the shared `nonpayable` entry wrapper on a source run with
  `run_body_of_run_nonpayable_frame`, or with `run_body_of_run_nonpayable_logs`
  when the endpoint's events or returndata must also be related to the public
  frame's entry.  Both derive zero call value.
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
- A selected `LOG` step that exposes unchanged storage, balances, code,
  access sets, output, and error while threading an arbitrary continuation:
  `Func.runCompiledTo_log_step_ext` and its exhibited-state form
  `Func.runCompiledTo_log_step_exists` in
  [`Blanc/ForwardLog.lean`](../Blanc/ForwardLog.lean). The exhibited form
  also exposes the unchanged created-account set, which carries Jaune's
  machine original read across the log.
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
  [`Blanc/CommonProofs.lean`](../Blanc/CommonProofs.lean).
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
  in `Blanc/CommonProofs.lean` across a log), `getOrigStorVal_congr_created`
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
- To show a frame ends with a nonnegative refund counter when its own `SSTORE`s are arbitrary
  (a world invariant closed under every step), track the refund potential
  `refundPotential sevm b a K` (counter less the clear refund per currently cleared slot of `a`
  over a key set `K` covering the nonzero originals): `refundPotential_afterSstore` (never lowered
  by an `SSTORE` at `a`), `refundPotential_add` / `refundPotential_congr`, `clearedCount_eq_zero`
  and `refundCounter_nonneg_of_potential` in
  [`Blanc/StorageRefundPotential.lean`](../Blanc/StorageRefundPotential.lean). `ShaCallPost`
  (precompile calls) keeps the refund counter (`ShaCallPost.refund`).
- For TWG trigger packets, local-call rebasing commutes with constant-store
  prefixes by `Trigger.rebaseLocalCalls_prependStoresRev` in
  [`Blanc/LidoTriggerableWithdrawalsGatewayTrigger.lean`](../Blanc/LidoTriggerableWithdrawalsGatewayTrigger.lean).
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
- A compiled walk that designates the step that caused a revert
  (`Func.RunCompiledToVisiting`, `Prog.RunCompiledToVisiting`):
  [`Blanc/RevertCause.lean`](../Blanc/RevertCause.lean).  The same module
  inverts a reverting frame into its gas-exact walk
  (`Prog.runCompiledTo_of_exec_revert`), proves a visiting walk by
  contradiction through `Func.RunCompiledToAvoiding` (with its step, branch,
  call, line, nonpayable and sorted-dispatch inversions), rules out a reverting
  walk of a `Func.revertFreeIn` body, and checks a program's terminals with
  `Func.TerminalsReturnOrRevert`.
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
- Peel a successful source-level `nonpayable` wrapper while retaining state,
  memory, logs, and output with `run_body_of_run_nonpayable_frame_logs` in
  [`Blanc/NonpayableInversion.lean`](../Blanc/NonpayableInversion.lean).
  This is the stronger event/returndata-sensitive companion of
  `run_body_of_run_nonpayable_frame`; product modules should consume it rather
  than restating the wrapper walk.
- Recover a selected body from a linear selector dispatcher:
  [`Blanc/LinearDispatch.lean`](../Blanc/LinearDispatch.lean) defines the
  shared `Blanc.linearDispatchWith` and `Blanc.selectorUnique`; the companion
  [`Blanc/LinearDispatchCorrectness.lean`](../Blanc/LinearDispatchCorrectness.lean)
  owns `dispatchBodyWitness_of_runCompiledTo` for hits and
  `dispatchFallbackWitness_of_runCompiledTo` for misses.  For a hit, supply
  selector uniqueness and selected-entry membership; for a miss, supply a
  nonempty entry list and exclusion from every entry.  Both take the initial
  `selector :: tail` stack and exact `RunCompiledTo` walk, remove the selector,
  recover the exact selected body or fallback call, and return a
  `DispatchFramePreserved` witness before any contract-specific ABI, role, or
  storage reasoning.  Compose adjacent witnesses with
  `Devm.DispatchFramePreserved.trans`.  To build a dispatcher fallback forward
  from a residual arbitrary-outcome body witness, use
  `Func.execWitness_linearDispatchWith_fallback`; its
  `linearDispatchFallbackCost` budget pays every `DUP`, `PUSH`, `EQ`, branch,
  and internal-call charge and removes the selector without requiring an
  already-built dispatcher walk. Supply selected `rules.op.push0 = true` for
  each entry whose emitted `toBytes.sig` is empty; nonempty immediates need no
  PUSH0 capability. This per-entry premise preserves historical dispatcher
  tables with no empty immediate. When a family builds its own dispatcher
  walk it can also consume the frame steps directly:
  `dispatchFrame_of_burnBy`, `dispatchFrame_of_pushBurn`,
  `dispatchFrame_of_popBurnBy`, and `dispatchFrame_of_diffBurn` carry a
  `DispatchFramePreserved` across one burn, push, burning pop, and stack
  difference respectively.  When the route also needs the exact operand stack,
  use `stack_of_pushBurn`, `stack_of_popBurnBy`,
  `stack_of_diffBurn_one`, and `stack_of_diffBurn_two` against the known input
  stack equation.
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
  contract-neutral fact behind any per-contract `canonicalAddress`), and
  `addressSlotReadWord_eq_self_of_lt` is its corollary for a value already
  known to read back clean, without a second word or
  `addressSlotReadWord_write_of_clean`.  The
  value-carrying inversions
  `of_loadAddressWordAt_val` and `of_storeAddressWordAt_val` live in
  [`Blanc/AddressSlotProofs.lean`](../Blanc/AddressSlotProofs.lean), with the
  `PUSH20 0xff..ff` literal as the mask (`ff20_eq`, `ff20_and_adr`, `ff20_and_word`,
  `and_mask_word`, `ff20_and_and`) and `addressMask_and_write_of_clean` (a packed
  write of a clean word keeps the raw upper ninety-six bits).
  Use it when delegated code can make a nominal address slot raw-dirty; a plain
  full-word `SSTORE` is observably different in that state.
- **Four-bit tagged logical storage keys.** `Blanc.TaggedStorage.encode` in
  [`Blanc/TaggedStorage.lean`](../Blanc/TaggedStorage.lean) combines a region
  with a payload after masking the payload to 252 bits.  Use
  `encode_eq_of_payload_lt` when bridging an existing unmasked `OR` encoder,
  `encode_region_payload_of_bounds` to decode its region and bounded payload,
  `encode_injective_of_payload_lt` for a fixed region, and
  `encode_ne_of_region_ne` for distinct regions.  The injectivity facts require
  payloads below `2^252`, and region separation also requires both regions
  below 16.  This key algebra does not model Solidity `address` slot reads or
  assignments: use `AddressSlot` for their low-160-bit read and
  upper-96-bit-preserving write semantics.
- **WETH calldata addresses.** `Weth10.normalizedAddressArg_eq_toAdr_toB256` in
  [`Blanc/Weth10StateFunctional.lean`](../Blanc/Weth10StateFunctional.lean)
  exposes the shared round trip from `normalizedAddressArg` to the low 160-bit
  address word.  Reuse it in WETH execution, accounting, and write proofs.
- Calls, delegate calls, or child-frame resumption: go to E2.
- A predicate must hold for every entered child root: go to E3.
- Only the terminal RETURN/REVERT remains: go to E4.

### E2. The walk crosses a child frame

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
- For an all-gas, zero-value call site with a one-word output window, use
  `Blanc.Lift.AllGasCall` in
  [`Blanc/Lift/CallProfileTransport.lean`](../Blanc/Lift/CallProfileTransport.lean):
  `ext`, `access`, `forwarded`, `warmed`, `parent`, `message`, and `resume`
  name the priced site and its child message; `forwarded_le` and `cross`
  construct the existing clean call crossing from the callee's actual execution.
  `message_sevm_reframe` and `message_devm_reframe` expose complete child
  initialization at normalized parent gas, with the actual forwarded gas restored;
  the latter preserves the state-gas grant and every world/metadata field.
  `resume_debit` cancels funded forwarding against returned child gas, leaving
  exactly access + expansion + child consumption as the parent debit.
  The forwarding fraction is returned through `resume`; it is not an extra
  consumed charge. Supply the fork, nondelegation, depth, non-precompile,
  funding, input-gas bound and result-stack-room hypotheses explicitly.
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
  For a loop that calls once per iteration (`GAS; CALL` forwarding everything),
  `calculateMsgCallGas_all` closes `calculateMsgCallGas` to all but one 64th of
  the gas left after the fixed charge (plus the stipend), and the cut-run steps
  `rxc_push0` / `rxc_calldataload` complete the `rxc_*` kit for
  `SFunc.RunExactCut.iterate` bodies; the EIP-7002 flood looper
  (`Blanc/Lift/WithdrawalRequest/FloodRun.lean`) is the worked example.
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
  outcome or the resumed parent; take those from the retained slot.  Worked
  use: `Blanc/DripExitPreCallbackLocator.lean` lifts DRIP's payout CALL to a
  body-frame occurrence by case-splitting `Ninst.step` on the accepted node and
  feeding the `.spawn` arm here.  Import `Blanc.CallSpawnExact` (it imports
  only `Blanc.Ladder`).
- `Xinst.step_delegatecall_spawn_exact` in [`Blanc/Lift/SpawnExact.lean`](../Blanc/Lift/SpawnExact.lean): the
  `DELEGATECALL` counterpart. A spawning `DELEGATECALL` step on a covered fork whose code-address
  operand `w` names an undelegated account enters a child at the parent's storage owner with code
  address `w`, the parent's caller, value and static flag, `w`'s code, and the calldata the input
  window of the parent's extended memory holds. `Xinst.step_delegatecall_spawn_meta` is the
  operand-free projection (nonzero depth, one level deeper, resumes as a call),
  `Xinst.step_delegatecall_done_flag` the failure flag `0` of a call that completes without a
  child, and `Resume.call_run_inv` the resumed parent (flag `1`, the child's output and world on a
  clean success; flag `0` otherwise). Worked uses: `Blanc/Lift/QuietDelegateSkip.lean`,
  `Blanc/Lift/Usdc/ProxyForward.lean`, `Blanc/Lift/Usdc/ImplSpawns.lean`.
- For historical caller/context inheritance from a known operand stack, use
  `Xinst.step_delegatecall_spawn_St_noStateGas` in
  [`Blanc/Lift/HistSpawnExact.lean`](../Blanc/Lift/HistSpawnExact.lean). It needs only
  `stateGas = none` and the actual spawning step: the child retains target,
  caller, value and staticness and reads the exact physical input window. It
  does not fix the code address or assume commitment, BAL, access or delegation
  settings. The raw USDC proxy consumer
  [`Blanc/Lift/Usdc/ProxyRawCallers.lean`](../Blanc/Lift/Usdc/ProxyRawCallers.lean)
  proves `Proxy.proxy_rawChild_inheritsH` and `proxy_rawChild_caller_selectorH`:
  a child called by an address apart from the proxy target must inherit the
  proxy caller through DELEGATECALL. Exact calldata/selector equality also
  uses the calldata word bound, supplied for historical raw frames by
  `ConfiguredHistoryTraceIn.calldata_bound_hist`.
- `AcceptedCallerPayout` in `Blanc/Lift/SpawnExact.lean`: the entered, clean, success-consumed value
  `CALL` to `sevm.caller` (gas word, 7-operand stack, `PopBurn [1]` guard, exact
  `ProcessMessage (callMsg …)` child, `Resume.call` and post projections) — the shape
  `of_run_call_val_with_depth_frame`'s entered arm yields for a payout.  Contracts keep a
  local `AcceptedPayout` wrapper only to retain pinned statement constants and dot-notation
  namespaces (`Prorata.AcceptedPayout.exists_trace`).
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
- For the actual six popped words and original-memory payload, use
  [`Blanc/StaticcallOperands.lean`](../Blanc/StaticcallOperands.lean).
  `Xinst.step_staticcall_spawn_operands` derives `StaticcallSpawnOperands`
  from the supplied spawn; `Ninst.step_staticcall_spawn_operands` also
  derives the successor PC. The descriptor preserves the selected fork's
  delegation lookup, exact capped gas, input and output windows, and both
  ordinary and Amsterdam resumes, including the actual state-gas grant.
  `Ninst.staticcall_observation_with_operands` and its
  `Exec.NinstOccurrence` wrapper enrich the same observation, message and
  original slot without filtering child failures. These theorems require
  no fork-coverage, success or supplied-operand premise. A direct
  `StaticcallSpawnOperands` goal uses the `call-boundary-outcomes` recipe;
  the enriched disjunction is reached through the named theorem. Target
  address alone does not establish enabled native execution or historical
  relevance.
- Consumption pattern: Blanc's compiled callers branch on the pushed flag, so a
  caller holding the success guard dismisses the failed arm with the trailing
  `iszero`+guard; the entered arm's `StepRun` aligns to the occurrence slot by
  `Ninst.StepRun.unique_exec_of_filled`, and `RawCommits` comes from
  `ProcessMessage.settlementCommits_of_some_ok_clean`.

For the entered child's code and code address at the `Xinst`-step level — from a
spawn equation without operand knowledge — use the spawn-source family in
[`Blanc/CommonProofs.lean`](../Blanc/CommonProofs.lean):

- `Xinst.step_spawn_source`: the trichotomy over any
  `Xinst.step sevm devm x = .spawn f rsm` — empty target code, same target as
  the parent, or code identity under `¬ isValidDelegation`. Its second disjunct
  (`f.inner.currentTarget = sevm.currentTarget`) remains open for an arbitrary
  instruction. For an actual STATICCALL spawn,
  `Xinst.step_staticcall_sameTarget_code` in
  [`Blanc/ExecutionDirectCode.lean`](../Blanc/ExecutionDirectCode.lean) gives
  direct-code identity from same-target and nondelegation evidence. It is the
  shared owner of the former Lido private proof. Message-level resolution with
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
word), one-step lemmas `xa_next`, `xa_jumpdest`/`xa_jump`/`xa_jumpi` (and `_St` forms),
`xa_halt`, `xa_revert`, and the spawning steps `xa_call`/`xa_staticcall`, which peel the next
child as `ChildOf` (target, calldata, value, static flag, output, logs, storage and code at
entry and exit, warm growth) unless the target is an undelegated precompile.
[`Blanc/Lift/FrameWalkKit.lean`](../Blanc/Lift/FrameWalkKit.lean) carries memory as a byte
image (`ri_*_img`, `xa_call_img`, `xa_staticcall_img`, `xa_identity_img`), normalizes the next
pc (`xa_nextAt`, `xa_jumpiAt`, …), and states image facts as `WordAt`/`Region` with the
`Mem.Reads.forget` cut and the `wchain` tactic (a memory word read off its image is
`WordAt.of_memWord`); it also holds the branch-condition lemmas,
Vyper's checked product `mul_check_toNat`, and `ChildOf.congr_left`. The 3pool's
`remove_liquidity` walk (`Blanc/Lift/Curve3Pool/Walk/RemoveLiquidity*.lean`) is the worked
example.

If the property concerns which child roots were entered rather than only the
terminal result, continue to E3.

### E3. I must carry a predicate over all entered child roots

Use [`Blanc/RootedExecution.lean`](../Blanc/RootedExecution.lean):

- `rootedRunCompiledTo` mirrors a compiled walk while carrying the predicate.
- `ninstAllChildRoots_of_not_exec` handles a known childless instruction.
- `NonExecInstruction` supplies reusable structural childlessness instances.
- `ninstAllChildRoots_of_exec_spawn` handles a spawning instruction from a
  predicate over the entered child's `Exec.rawFrameRoots`.
- `funcExecFree` and `rootedRunCompiledTo_of_execFree` discharge a whole
  execution-free tail.
- `Prog.exec_of_rootedRunCompiledTo` produces the final `Exec` and predicate
  over all `Exec.rawFrameDescendants`.

For retained or settlement-filtered children, do not encode the filter into
this raw-root bridge; continue to T2.

For raw `SSTORE` exclusion on one exact selected compiled path, use
[`Blanc/ForwardNoRawSstore.lean`](../Blanc/ForwardNoRawSstore.lean):

- `Func.RunCompiledTo.NoRawSstorePath` mirrors the chosen branches and
  internal calls and requires explicit childlessness at external instructions.
- `NoRawSstorePath.of_execFree` discharges an execution-free, locally
  SSTORE-free body; `NoRawSstorePath.of_revertWith` is the symbolic
  constant-error specialization.
- `NoRawSstorePath.of_emptyRevertGuard` certifies a selected nonzero guard
  whose internal auxiliary is the common empty `Func.revert` body.
- `NoRawSstorePath.of_prepend_nonexec` prepends an instruction-only line when
  every instruction is non-external and distinct from raw `SSTORE`; its tail
  certificate may depend on the intermediate compiled state.
- `NoRawSstorePath.of_entrySstoreFree_reachableExecFree` converts an exact
  compiled walk directly when the shared executable entry/component checkers
  certify both same-frame SSTORE freedom and absence of child-entering
  instructions; recursive internal-call components are supported.
- `Func.replaceStopWith` replaces successful `STOP` leaves and
  `Func.replaceStopWith_prepend` pushes that replacement through an
  instruction-only prefix, while
  `NoRawSstorePath.replaceStopWith_of_error` transports an exact error-ending
  path and its certificate across that replacement.  Use this when a checker
  can certify a prefix only with a harmless success continuation: the error
  proof establishes that the replaced continuation was not entered.
- For a warm fixed-width SHA-256 precompile crossing, use
  `Ninst.childlessRunCompiled_staticcall_sha256_64_warm_ext` in
  [`Blanc/ForwardSha256.lean`](../Blanc/ForwardSha256.lean); the ordinary
  `runCompiled_*` projection intentionally forgets the empty child slot. Use
  `Ninst.childlessRunCompiled_staticcall_sha256_64_warm_ext_full` when later
  transaction settlement also needs the crossing's exact refund preservation,
  account-deletion-set emptiness preservation, or the unchanged
  created-account set (which an exact later `SSTORE` price depends on).
- `Prog.exists_exec_noRawSstore` produces the exact `Exec` witness and
  `Exec.NoRawSstore`; its consequences exclude every successful raw SSTORE and
  force `retainedStorageWrites = []` for that same witness;
  `retainedStorageEffectTriples_eq_nil` gives the proof-erased chronology.
- `Exec.noRawSstore_of_exactMain_entrySstoreFree_reachableExecFree` is the
  occurrence-direction counterpart for an existing exact `Exec`: reachable
  exec freedom collapses child frames, then the same-frame entry certificate
  excludes every raw SSTORE node.

This is construction-direction evidence. A late revert may already have
executed an SSTORE, so neither rollback nor an empty retained-write list can
replace the selected-path certificate.

To identify the caller and target of settlement-committed frames, use
[`Blanc/Lift/CallerProvenance.lean`](../Blanc/Lift/CallerProvenance.lean).
`Exec.childFrames run` lists a frame's direct settlement-committed children;
`Evm.step_spawn_child_caller` says each child either receives the parent's
current target as caller or keeps the parent's target. `CallerTarget p ca Q`
states the desired property of frames at `ca` called by `p`. `settledRoots`
is defined at every trace layer, with `settledFrames_eq : settledFrames =
rootFrames settledRoots`. For the parent-to-child fold consuming this
vocabulary, use `ConfiguredHistoryTrace.settledFrames_callerTarget_of_children`
in `Blanc/Lift/CallChildren.lean`, described below. Worked use:
`Blanc/Composition/PairTokenCallers.lean`.

To show that every direct child of a frame is called by the frame's own current
target, use
[`Blanc/Lift/CallChildren.lean`](../Blanc/Lift/CallChildren.lean):
`Exec.childFrames_caller_of_callKinds` concludes it from the frame's
CALL/STATICCALL-only restriction along its chain (a checked certificate's
`SpawnKinds`, e.g. `weth9_spawnKinds`), via `Xinst.step_call_spawn_caller` and
`Xinst.step_staticcall_spawn_caller`. `Exec.childFrames_isStatic` says a static
frame has only static children. For the caller fold of
`Blanc/Lift/CallerProvenance.lean` with the weaker obligation that every direct
child of a frame at `p` or `ca` satisfies the target property (`CallerChildren`),
use `ConfiguredHistoryTrace.settledFrames_callerTarget_of_children`. Worked use:
`Blanc/Composition/PairTokenCallers.lean`.
The fold's root case needs that `ca` enters no settled message root itself.
[`Blanc/ExecutionTraceRootCallers.lean`](../Blanc/ExecutionTraceRootCallers.lean)
gives it: `ConfiguredHistoryTrace.settledRoots_caller_ne` says every settled
root of a configured history has a caller other than `ca`, for an address whose
contract invariant holds at the checkpoint and is preserved by its admitted
frames (EIP-3607 makes it no sender, `TransactionTrace.sender_ne_sem`) and that
is not `systemAddress`. The per-wrapper forms (`ProcessMessageTrace`,
`MessageCallTrace`, `SystemMessageTrace`, `RequestsTrace`, `TransactionTrace`,
`ApplyTransactionsTrace`, `AppliedBodyTrace` `.settledRoots_caller[_ne]`) are
the same fact at each layer.
For an address whose checkpoint code `C` is nonempty and not an EIP-7702
designator, with no contract invariant to carry, use
[`Blanc/ExecutionSettledOwnCode.lean`](../Blanc/ExecutionSettledOwnCode.lean):
`ConfiguredHistoryTrace.settled_ownCode` says every settled frame finds `C`
installed at `ca` when it starts and every settled frame at `ca` runs `C` from
pc `0` (`OwnCodeAt`), provided frames running `C` at `ca` spawn only by `CALL`,
`STATICCALL` or `CREATE2` (`OwnSpawns`; for a certified runtime whose cursor carries no
`DELEGATECALL`, `CursorOK.exec_spawn_undelegated` with `Xinst.notDelegatecall` in
`Blanc/Lift/CallRestriction.lean`, since `CursorOK.exec_spawn` itself admits `DELEGATECALL` as a
fourth arm); `Exec.descendantFrames_ownCode` is the per-derivation
form and `Xinst.step_create2_spawn_unprotected` says a `CREATE2` child targets
an address with no code. `ConfiguredHistoryTrace.settledRoots_caller_ne_of_code`
is the root-caller fact above for such an address. A code image equal to
`some C.toList` pins the bytes by `ExecutionTrace.bytes_eq_of_image`
([`Blanc/ExecutionImmutableCode.lean`](../Blanc/ExecutionImmutableCode.lean)).
Worked uses: `Blanc/Lift/UniswapV2Factory/CallShape.lean`,
`Blanc/Composition/UniswapV2FactoryQuiet.lean`.
When the address's frames may run other code (a proxy's `DELEGATECALL` children) and only the
installed image matters, use [`Blanc/ExecutionSettledCodeImage.lean`](../Blanc/ExecutionSettledCodeImage.lean):
`ConfiguredHistoryTrace.settled_codeImage` says every settled frame of a configured history finds
the certified image `sem` installed at `a` when it starts, with no spawn restriction
(`Exec.descendantFrames_codeImage` is the per-derivation form; nonempty code is never replaced).
For every *raw* frame, rolled back or not, [`Blanc/ExecutionRawFramesCodeImage.lean`](../Blanc/ExecutionRawFramesCodeImage.lean):
`ConfiguredHistoryTrace.rawFrames_codeImage` (and `_of_installed`) carries a `ContractSpecSem`'s
image through the admitted rungs (`*.rawFrames_codeImage` per wrapper, from the `*.stateInv_admitted_sem`
message invariant) and `Exec.rawFrameRoots_codePreserve` inside each message. Worked uses: USDC
(`Blanc/Lift/Usdc/HistorySlots.lean`, `HistoryFamily.lean`).
For the In-carrier (`StagedBodyTrace` / `ConfiguredBlockTraceIn` /
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
`…codeImage_of_safe` per wrapper (message, transaction, system / request
stages, staged body, In-block) threads each entry world's `getCode wa = C`
with the `…_of_safe` chain of `ExecutionNoDelSafeHistory` (same
`SafeRawFrames wa` premise, plus `C.toList ≠ []` and `¬ isValidDelegation C`)
and keeps it at every raw root by `Exec.rawFrameRoots_codePreserve`,
ending in `ConfiguredHistoryTraceIn.rawFrames_codeImage_of_safe`
(`R.devm.getCode wa = C` for every raw frame, rolled back or not) and
`…settled_codeImage_of_safe` (`f.pre.getCode wa = C` for every settled frame)
through the settled-to-raw bridge. No recipe is registered: use this branch
and the named theorem.
To produce that `SafeRawFrames wa` premise from the codes run in `wa`'s storage
context, use [`Blanc/ExecutionSafeRawFramesCodes.lean`](../Blanc/ExecutionSafeRawFramesCodes.lean):
`SafeRawFrames.of_entryCodes` (any descent-closed raw-root list) and
`ConfiguredHistoryTraceIn.safeRawFrames_of_codes` take a code family whose
members each have a checked certificate with `noSelfdestruct = true` and the
fact that every raw frame in context `wa` runs a family code;
`…rawFrames_codeImage_of_codes` and `…settled_codeImage_of_codes` compose it
with the code image above. Which codes run in `wa`'s context stays a premise.
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
membership, fork coverage or final frame success. The USDC compatibility name
is a direct alias. No recipe is registered: use the recognizer equation.
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
For cell preservation from complete-settlement roots, use
[`Blanc/ExecutionRetainedCellZero.lean`](../Blanc/ExecutionRetainedCellZero.lean)
when the actual retained writes are non-increasing at their own prefixes:
`Exec.cell_zero_of_retained_nonInc_noStateGas` preserves an initial zero cell
of any initially code-bearing observed account through a committing execution.
The surrounding frames need no lifted code image or equality of their current
target with that account. Only complete-settlement-retained child writes are
examined; failed child settlement uses rollback. The selected rules must have
no state gas. This is conditional zero preservation, not unconditional cell
equality, and does not discharge transaction deletion or a historical seed.
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
are not identified with the transaction input. The beacon/history
`state_eq_of_disabled` adapters expose each skipped opening stage's actual
state identity. Use this explicit trace/cell
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
`MidHistoryTraceIn.cell_zero_before_txSplit` transports an actual initial zero
from the settled-after origin to the target's exact before endpoint, using only
conditional root-zero laws on the intervening mid history plus final prefix.
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
induction over `rawNodes` that bounds the codes run in a storage context;
`List.forall_mem_of_positional` is that induction along list positions.
No recipe is registered: use this branch and the named theorem.
For positional origin within one committing settlement-retained execution,
[`Blanc/ExecutionRetainedNodeOrigin.lean`](../Blanc/ExecutionRetainedNodeOrigin.lean):
`Exec.retainedNodes_split_origin` takes the exact retained split and gives the
actual input root, an earlier retained node with the same static environment,
or an earlier retained node satisfying the existing `SpawnedAt` relation.
Complete child settlement excludes discarded child witnesses. It requires no
code, fork, no-write or own-code premise; actual message-root own-code facts
remain the caller's separate obligation. Use the named theorem with retained
prefix provenance when inducting over retained contexts.
For the own-code fact at an actual settled outer root, use
[`Blanc/ExecutionInRootOwnCode.lean`](../Blanc/ExecutionInRootOwnCode.lean):
`ConfiguredHistoryTraceIn.settledRoots_rootOwnCode` derives `RootOwnCode`
for that root's `rootDeriv` directly from message entry, authorization and
CREATE collision handling. It needs no installed-world invariant or extra
stage capability. `mem_rawFrames_of_mem_settledRoots` supplies the same root's
raw-frame membership. This applies to outer message roots; delegated
descendants still need the positional origin classification above.
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
For the origin of raw nodes after such a boundary (every later node is reached
from nodes after the boundary, so a frame running after it was entered after
it), [`Blanc/ExecutionInRawNodeOriginFrom.lean`](../Blanc/ExecutionInRawNodeOriginFrom.lean):
`ConfiguredHistoryTraceIn.BoundaryAt.origin` (the rest of the chronology is an
`OriginList`), its per-level forms, `ConfiguredHistoryTraceIn.BoundaryAt.rawOrigin`
at a split `pre ++ mid ++ n :: after`, and `List.forall_split_of_positional`, the
strong induction along positions for a property of a node and its prefix. No
recipe is registered: use this branch and the named theorem.
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
For the contract postcondition across a CALL on a historical fork (where
`CoveredFork` cannot hold),
[`Blanc/LadderSemHist.lean`](../Blanc/LadderSemHist.lean):
`ContractSpecSem.post_of_call_self_withIn F` is the historical form of
`ContractSpecSem.post_of_call_self_with` (`Blanc/LadderSem.lean`): the
deeper-frame hypothesis is quantified over the selected fork-domain fact `F`
instead of `CoveredFork`, with `stateGas = none` as the only rule premise.
The access schedule (`.flat` / `.eip2929`) and the delegation flag are cased
on, never assumed, so every premise discharges on `HistFork` with
`HistFork.stateGas_none`. Worked consumer: the WETH9 `withdraw` self-CALL via
`Weth9.withdraw_post_gen` (`Blanc/Lift/Weth9/Withdraw.lean`). No recipe is
registered: use this branch and the named theorem.

For a committed-replay history that takes one step per *outermost* settled,
non-static frame at an address (a re-entered frame consumed inside its
ancestor), use [`Blanc/Lift/OutermostFrames.lean`](../Blanc/Lift/OutermostFrames.lean):
`Exec.Frame.obsAt` / `Exec.Frame.subtreeAt` (the Pair's `pairFrameObs` /
`pairSubtreeFrames` shape), `ConfiguredHistoryTrace.committedFramesAt` (all
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
`Exec.childFrames_spawnedAt` places every direct child at a spawning step of a
node of the frame's own chain, where `reach_of_parentPrefix` gives a cursor.
`SFunc.nodesSatisfy ok` checks `ok n f` at every `.next n f` node of a tree;
check it over the certificate with one kernel `decide` per entry, in a module of
its own. `Reach.nodesSatisfy` keeps it along the stateful reach, and
`CursorOK.nodesSatisfy_exec` turns it into a fact about the cursor's tree at a
node that decodes an external instruction. Name a site inside a generated
tree's straight prefix with `SFunc.lineDrop n t` (`SFunc.lineSuffix_lineDrop`).
`Xinst.step_call_spawn_selector` equates a CALL child's selector with
`CallInputSelector`'s reading of the parent's input window;
`ChainMemoryBelow R bound` is the memory bound such content facts take.
`Xinst.step_call_spawn_stack` is used by
`Blanc/Composition/Weth9TokenFramesNode.lean`.

For a contract address that must originate no settled message root, use
[`Blanc/ExecutionTraceRootCallers.lean`](../Blanc/ExecutionTraceRootCallers.lean).
`ConfiguredHistoryTrace.settledRoots_caller_ne` derives the caller exclusion from
an admitted preserved contract invariant at the checkpoint and `ca ≠ systemAddress`.
The transaction case uses EIP-3607; the system-root cases retain the system caller.
To prove a property of every committed descendant of a run from the spawns of the run's own chain,
use [`Blanc/ExecutionSpawnFrames.lean`](../Blanc/ExecutionSpawnFrames.lean): `Exec.descendantFrames_of_spawns` reduces it to each
spawning node of the chain whose child settles, for that child and its committed descendants, with
the spawning step (`Ninst.StepRun.spawnParts`), the child's entry (`Evm.step_spawn_entry`) and its
membership among the root's direct children supplied, so entry facts come off the spawn
(`Evm.step_spawn_child`, `Evm.step_spawn_enter_getStor`) or off a child-classification theorem over
`Exec.childFrames`; `Exec.FrameAdmitted.of_mem_descendantFrames` reads admission off membership.
Worked use: `Blanc/Lift/Usdc/HistorySlotsCore.lean`.

### E4. I need a common terminal walk

Use [`Blanc/ExecutionTerminal.lean`](../Blanc/ExecutionTerminal.lean):

- `Func.runCompiledTo_return_word_at_zero` for a known 32-byte return at offset 0.
- `Func.runCompiledTo_revert_empty_at_zero` for an empty revert at offset 0.
- `Func.runCompiledTo_push1Zero_return_empty` for two PUSH1-zero instructions
  followed by an empty RETURN from an empty stack and empty memory, paying exactly six gas.

For different offsets, sizes, stack tails, or payloads, use the general
`Func.runCompiledTo_return_word` in `ForwardCall` or
`Func.runCompiledTo_revert` / `Func.runCompiledTo_revert_of` in `Reverts`.
For a primitive gas charge, `chargeGas_eq_ok` in
[`Blanc/Compiled.lean`](../Blanc/Compiled.lean) exposes the exact successful
decrement, while `chargeGas_eq_outOfGas` in
[`Blanc/ChargeGas.lean`](../Blanc/ChargeGas.lean) exposes the unchanged-state
out-of-gas result without pulling compiled-execution infrastructure into a
small consumer.
For CALL-family steps that reach that failing charge, use
`Xinst.step_call_zero_value_outOfGas` and
`Xinst.step_staticcall_outOfGas` from
[`Blanc/CallOutOfGas.lean`](../Blanc/CallOutOfGas.lean); their premises expose
the decoded operands, memory-extension and delegation results, call-gas split,
and exact insufficient-gas inequality.

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
  a DRIP row can carry. `regularTransfer_safe` proves every accepted transfer
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
- For a finite table of actual decoded stack patterns, use
  [`Blanc/AbstractStackCertificate.lean`](../Blanc/AbstractStackCertificate.lean).
  `AbstractStackSafety.Table` stores full patterns in a finite search tree.
  `checkTable_certificate` constructs `CompiledStackSafety.Certificate` from
  the kernel-checked `checkTable` result. The checker reads the actual public
  `ByteArray.getInst`, rejects out-of-code rows and truncated PUSH widths,
  preserves exact PUSH literals, and checks both JUMPI successors and actual
  `jumpable` destinations. `checkSuccessor` independently checks output and
  destination bounds and full-pattern inclusion through `covers`;
  `Matches.covered` proves that inclusion sound. The accepted transfer family
  supports maximum bounds at most eight and rejects unsupported opcodes,
  including SELFDESTRUCT. `stepSafe_mono` retains every child settlement and
  fatal-error provenance while adapting the accepted opcode theorems.
  `Table.checkOrder_sound`, `lookup_iff_row`, and `row_unique` connect checked
  strict subtree ordering to exact structural-row lookup and unique patterns.
  `Table.count_le_one` excludes even identical duplicate rows. Independently,
  `Table.checkLayout_sound` proves exact decoded-byte interval coverage from
  the layout check; each node consumes its actual decoded instruction width.
  `Table.all_node` composes named row checks while retaining their identical
  predicate (and thus the complete table for successor lookup).
  `Table.checkLayout_node` composes checked left/right intervals through an
  actual-decoder-checked singleton; no gap or assumed instruction width is
  introduced by a named-subtree boundary.
  `checkTable` itself does not include that separate layout check or establish
  entry, feasible-path reachability, or arbitrary child-frame stack safety.
  This table-construction interface is registered here; the existing
  same-frame recipe supplies the subsequent actual `ParentPrefix` transport.
- Raw nodes (`Exec.rawNodes`, Jaune's `Jaune/ExecChronology.lean`), raw frame
  roots, and instruction occurrence:
  [`Blanc/ExecutionOccurrence.lean`](../Blanc/ExecutionOccurrence.lean).
- `Prog.SourceSite.pcs` projects a source inventory to compiled counters;
  `Prog.SourceSite.coordinates` keeps each counter coupled to its owning
  function-table index for role-preserving finite inventory checks.
- `Func.sourceSiteCount` in
  [`Blanc/SourceSiteCount.lean`](../Blanc/SourceSiteCount.lean) counts source instruction
  nodes selected by a Boolean `Ninst` predicate.  Keep contract-named totals
  as thin predicate specializations.
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
  `Exec.Deriv.step_cont`, `step_halt` and `step_spawn` pin any node's same-frame
  successor, outcome and spawned child (`LockExclusion.Spawns`) from one driver step.
  `pwalkH` is a kernel-evaluable pc-level walk over a `CodeTries` of the code with the
  witness engine's shadows (`PAgree`) and a hash policy `HashPol` (`.refuse`: stop at
  `KECCAK256`; `.avoid slot`: run it through `keccakStep` and refuse a digest equal to
  `slot`); `pwalk` is the `.refuse` walk. `pstepH_cont`/`pstepH_halt` make each walk step
  the real `Evm.step`. The `SELFBALANCE` shadow step requires the selected
  `op.selfBalance` capability as well as absence of a balance access list; it refuses
  the step when the opcode is unavailable. `pwalkH_cont` and `pwalkH_halt` then hold for *any* derivation node
  at the start configuration: a `ParentPrefix` successor at the end configuration, every
  node in between passing a pc check and satisfying the policy (`NodeOKH`; at `.refuse` it
  is `NodeOK`: no `KECCAK256`), unchanged `Exec.rawFrameDescendants`, and for a halting
  walk the frame's outcome (`pwalk_cont`/`pwalk_halt` are the `.refuse` cases).
  `hashAvoid_of_hashOK` (trace-local `HashAvoid` from `.avoid slot` nodes) and
  `hashAvoid_of_noKeccak` close chain arguments with `parentPrefix_total`.
  `scallPrep`/`staticcall_node`, `callPrepP`/`call_node` and `dcallPrep`/`delegatecall_node`
  (over `spawn_node`) cross a call-family spawn; `PrepFacts` supplies the settle
  (`PrepFacts.settle_ok`, requiring the frame's selected `settle.touchedSweep = false`;
  `settle_error`) and resume (`resume_agree_ok_of`/
  `resume_agree_error_of`; `resume_agree_ok`/`_error` for `STATICCALL`) facts.
  `scallPrep_value_zero` extracts the zero message value from successful
  `scallPrep`, without a world or shadow agreement premise; use it with exact
  zero-value entry to preserve the unchanged storage shadow of a static call.
  [`Blanc/Lift/NodeWalkFrames.lean`](../Blanc/Lift/NodeWalkFrames.lean) builds on it:
  `spawn_resume_ok` (requiring the frame's selected `settle.touchedSweep = false`) and
  `spawn_resume_err` cross a spawn on any derivation (the child's node, the
  resumed same-frame successor with its agreement, the descendants list), `leaf_frame`/
  `leaf_frame_ok` a frame that walks and halts, `halt1_childAgree` a successful halt's shadows,
  and `chain_trans`, `chain_step`, `interval_trans`, `interval_step` assemble a same-frame chain
  from its walk segments. `RETURNDATACOPY` runs by Jaune's own step (`returndatacopy_accKeep`).
  To decide many closed walk equalities in one kernel check (each boundary evaluated once, not
  once per equality), close a conjunction of them with `kernel_rfl_and`
  ([`Blanc/Lift/KernelBatch.lean`](../Blanc/Lift/KernelBatch.lean)).
  Worked examples: `Blanc/Lift/VyperNonreentrantDeployed/Fixed/Witness/Top.lean` (a read-only
  spawn) and `.../Fixed/Witness2/{Run,Frames,Top}.lean` (an ETH-paying body, a nested reentry
  through an EIP-1167 forwarder, a committing run).
- To consume a call-family child whose code is a lifted certificate *without* walking it by the
  kernel — the child's inputs symbolic, its run built forward as `SProg.RunExact` with
  `Blanc/Lift/ExactWalk.lean` — use [`Blanc/Lift/ExactLeaf.lean`](../Blanc/Lift/ExactLeaf.lean).
  `exact_leaf` turns the run (and `SpawnFreeReach` of the code) into the outcome and the empty raw
  descendants of every derivation node at the child's start configuration, the premise
  `spawn_resume_ok` asks for. `ChildAgree.afterSload`/`afterSstore`/`ret` move the witness
  engine's shadows across the selected-access bases `afterSload`/`afterSstore` and a `RETURN`
  over an `St`, so an explicit post state has explicit shadows; `ChildAgree.getStorVal`,
  `sloadCost_shadow`/`sstoreCost_shadow` (`sloadCostS`/`sstoreCostS`) and
  `afterSload_shadow`/`afterSstore_shadow` (`afterSloadS`/`afterSstoreS`) restate values, charges
  and bases on the shadows without inspecting the accessed-key hash set.
  `sstoreCostS` takes the actual `Devm` after `Sevm`; it and `afterSstoreS` retain
  the machine's created-account-aware original storage read. A transaction
  snapshot alone does not determine that value. Worked example: the synthetic token's `approve_child` in
  `Blanc/Lift/VyperNonreentrantDeployed/Token20/Frame.lean`.
- To state a closed walk witness under every covered fork rather than the one its machine
  fixes, transport its kernel facts with
  [`Blanc/Lift/NodeWalkFork.lean`](../Blanc/Lift/NodeWalkFork.lean): `pwalk_withFork`
  (`pwalkH_withFork`) leaves a walk unchanged from `s.withFork g` for covered forks when
  `s.benvStat.excessBlobGas = 0` (walks never run `CLZ`: it is not an `ninstAccKeeps`
  instruction), `scallPrep_withFork`/`callPrepP_withFork`/`dcallPrep_withFork` spawn the same
  frame with its fork changed, `frameEnterS_withFork` commutes with the change for a
  `Frame.PrecompNeutral` frame (`Frame.precompNeutral_of_codeAddress` from a kernel fact on the
  frame's `codeAddress`), and `scallPrep_stat`/`callPrepP_stat`/`dcallPrep_stat`/
  `frameEnterS_stat` carry the block environment into children.
  At the resumed parent, `resumeCallB_withFork` preserves the parent and output
  window, and `CallPrep.withFork_adrs` preserves the accessed-address shadow.
  Use these abstract equalities to avoid converting record updates on a concrete
  call preparation. These field laws have no unique registered goal matcher.
  `nodeAt_withFork_entry` and `pagree_withFork_entry` normalize the node and
  agreement views of a child entered through a transported call preparation,
  without unfolding the concrete child machine or preparation.
  For transaction-environment inheritance, use `callPrep_tenvStat` or
  `dcallPrep_tenvStat` on the successful preparation equation (both outer and
  inner frames), then `frameEnterS_tenvStat` on the entry equation for the
  child's `Sevm.tenvStat`. These equalities use the named inheritance lemmas;
  the ordinary projection recipes do not select a call-preparation or frame-entry
  hypothesis, so no specialized goal matcher is registered for this chain.
  The bundles
  `scallSpawn_withFork`/`callSpawn_withFork`/`dcallSpawn_withFork` give a whole spawn (the
  preparation and the entry) under any covered fork from the Prague facts, and
  `settle_withFork_of_stat` a child's settle. Generalize the run lemma over
  `S = e0.sta.withFork g` and derive the fixed-fork statement at Prague; worked examples
  `vplus_run_at`/`vplus_witness_covered` in
  `Blanc/Lift/VyperNonreentrantDeployed/Fixed/Witness/Top.lean` (one nesting level) and
  `vplus_run2_at`/`vplus_witness2_covered` in `.../Fixed/Witness2/{Frames,Top}.lean` (the
  frame lemmas take the fork, six spawns of all three call kinds). The message-level layer
  underneath is [`Blanc/ForkUniform.lean`](../Blanc/ForkUniform.lean) (see the root's
  *Fork coverage* entry).
- A `STATICCALL` into a precompile is no raw frame (its entry answers at once, `Exec.doneOk`),
  so a node walk crosses it with
  [`Blanc/Lift/NodeWalkPrecomp.lean`](../Blanc/Lift/NodeWalkPrecomp.lean):
  `Exec.Deriv.step_done` (a synchronous spawn pins the node's same-frame successor, outcome and
  raw descendants unchanged), `staticcall_done_node` (at an agreeing configuration, a prepared
  call whose shadow entry answers successfully resumes at the configuration the shadows
  describe, with its agreement), and `scallDone_withFork` (the preparation and the synchronous
  entry under any covered fork, for a frame avoiding `MODEXP`/`P256VERIFY`). Worked example: the
  identity-precompile copy of `initialize` in
  `Blanc/Lift/VyperNonreentrantDeployed/Fixed/Init/{Run,Top}.lean`.
- To read a walk's final shadows back as finite maps: `canonS` drops shadowed and zero writes
  from a storage log and `lookupS_canonS` says it reads the same everywhere (a kernel equation
  `canonS l = l'` then gives a canonical storage table, `lookupS_eq_of_canonS`), and
  `lookupA_eq_of_keys` makes two account logs agree everywhere once they agree at the addresses
  either names, in [`Blanc/Lift/ShadowCanon.lean`](../Blanc/Lift/ShadowCanon.lean) (worked use:
  `init_run`/`oracle_run` in `.../Fixed/Init/{Top,OracleTop}.lean`). `lookupA_eq_of_map` takes
  that agreement from one closed list equation a kernel check decides (`Acct` has no decidable
  equality); worked use: `approve_run`/`add_run` in `.../Fixed/Fund/{Approve,Add}.lean`.
- When a closed walk's message runs over a world whose evaluation is expensive (a settled world
  of earlier messages: every `SSTORE` charge reads the transaction-original storage), evaluate
  the kernel facts under a cheap original state and transport them with
  [`Blanc/Lift/NodeWalkOrig.lean`](../Blanc/Lift/NodeWalkOrig.lean): `origOf l` is the closed
  world holding exactly the storage the shadow `l` reads (`storOf_origOf`), `origAgree_origOf`
  turns a world's storage agreement with `l` into `OrigAgree`, and `walk_re`,
  `scallSpawn_re`/`callSpawn_re`/`dcallSpawn_re`, `settle_re` and `frame_enter_re` move walks,
  spawns, settles and the root entry to `(s.withFork g).withOrig W` (any covered fork, the real
  original state) under `ReOK W s`; the `*_withOrig` lemmas are the original-state layer alone.
  `Jaune.Sevm.withOrig_code` and `Blanc.ForkUniform.Sevm.withFork_code` transport the code projection
  by named equalities, keeping a concrete source machine out of kernel conversion.
  `Blanc.Devm.getOrigStorVal_withOrig_of_eq` transports an actual original-storage
  read from snapshot agreement at one owner/key; created accounts read zero on
  both sides. Both the full `OrigAgree` and finite `OrigAgreeOn` transport proofs
  use it without a not-created premise.
  The interpreter's `SSTORE` arm reads the original value through
  `Blanc.Lift.Witness.origReadK` (WitnessArms), not `Devm.getOrigStorVal` directly:
  `Std.HashSet` membership in `createdAccounts` does not reduce in the kernel (the
  bucket index goes through the opaque `System.Platform.numBits`), while the set's
  `size` field does, so an empty created set is decided by size. A proof that
  unfolds `sstoreStep` rewrites with `origReadK_eq` to recover the machine read.
  A concrete witness whose created set is nonempty still cannot be kernel-evaluated
  through an `SSTORE` that needs the original value.
  Hand a transported spawn's agreement and child nodes to lemmas stated over the kernel
  configuration through `pagree_re`/`nodeAt_re`: left to definitional
  unfolding, the kernel compares a concrete machine with its transported form by evaluating both
  (measured: a frame module went from a 16.4 GiB retraction to a 5.1 GiB build). Use
  `resumeCallB_re` to preserve the parent and output window of a transformed call preparation,
  and `CallPrep.re_adrs` for its accessed-address shadow at the resumed configuration.
  The `changed-frame-projection` recipe recognizes direct equality goals exposing
  `Sevm.code` over `Sevm.withOrig`, `CallPrep.adrs` over `CallPrep.re`, or
  `resumeCallB` with all three parent/window projections from the same `CallPrep.re`.
  Its fully qualified helpers are `Jaune.Sevm.withOrig_code`,
  `Blanc.Lift.Witness.CallPrep.re_adrs`, and `Blanc.Lift.NodeWalk.resumeCallB_re`.
  If an alias hides the update or projection, unfold only that local binding and
  run `blanc_suggest` again; the advice never normalizes a concrete machine.
  Worked use: `forwarder_root_re`/`leaf_root_re` and the frames of
  `Blanc/Lift/VyperNonreentrantDeployed/Fixed/Fund/{Root,Add}.lean` and `.../Fixed/Exit/`.
- To run a walk (`pwalkH`) or a certificate run (`wrun`, `childRun`, `callResume`) whose
  `SSTORE` charges read a transaction-original state that is not a closed term (a root
  message's own input world): evaluate the kernel facts with the original state replaced by a
  closed world holding the same storage (`Sevm.withOrig`, `OrigAgree`), and transport them back
  with `pwalkH_withOrig`, `wrun_withOrig`, `childRun_withOrig`, `callResume_withOrig` (spawns and
  entries: `dcallPrep_withOrig`, `callPrep_withOrig`, `frameEnterS_withOrig`,
  `frame_enter_withOrig`), in [`Blanc/Lift/NodeWalkOrig.lean`](../Blanc/Lift/NodeWalkOrig.lean)
  (worked use: `frameB_at` in `.../Vulnerable/Reach/AddTop.lean`). `kernel_forall_rfl_and`
  ([`Blanc/Lift/KernelBatchForall.lean`](../Blanc/Lift/KernelBatchForall.lean)) decides a
  universally quantified conjunction of equalities in one kernel check. Its shared builder
  imports `Lean.Elab.Tactic.ElabTerm` for the tactic elaboration support. Over a free world,
  compare computed values by `decide` (or against literal boundaries, `Boundary.obsD1`), never
  as terms.
- To make a kernel-checked witness quantify over **every world that agrees on finitely many
  entries** (a checkpoint predicate as a genuine finite read-set agreement, not a world pinned
  everywhere): [`Blanc/Lift/ShadowTail.lean`](../Blanc/Lift/ShadowTail.lean). `storOf_prefix_tail`
  and `acctAgree_prefix_tail` turn an agreement with a finite storage prefix (resp. account
  prefix) into a full engine shadow `prefix ++ storTailOf W` (resp. `prefix ++ acctTailOf W`)
  describing `W` everywhere, where `storTailOf`/`acctTailOf` list the rest of `W` and the walk,
  reading only prefix keys, never consults the free tail; `Boundary.cfgOfT`/`obsDT`/
  `cfg_of_obsDT`/`obsDT_cont` are the boundary kit with such a tail (prefixes decided, tails
  compared as terms). Read the unextended prefixes with `Boundary.cfgOf1_stor`/
  `cfgOf1_acs`, and read the complete prefix-plus-tail shadows with
  `Boundary.cfgOfT_stor`/`cfgOfT_acs`; use these projection lemmas over symbolic
  boundaries before substituting a concrete machine image.
- To transport such a run's `SSTORE` charges to an original state that agrees with the kernel's
  closed one **only on the keys the run touches** (a finite checkpoint agreement, where
  `OrigAgree`'s everywhere-agreement is unavailable): `wrun_withOrig_keys` and
  `childRun_withOrig_keys` in [`Blanc/Lift/OrigKeys.lean`](../Blanc/Lift/OrigKeys.lean) need
  only `OrigAgreeOn O O' (resKeys …)`, the agreement on the keys the run's final configuration
  records (`wrun_keys`: keys are only added; `sstoreStep_key_mem`: every `SSTORE` records its
  key) (worked use: `origAgreeOn_O0` in `.../Vulnerable/Reach/ViolBoundary.lean`).
- To state a closed *frame-level* witness (the certificate interpreter `wrun`, code children by
  `childStart`/`callResume`/`callPairFrom`, proxy frames by `stepN`) under every covered fork,
  rewrite its kernel facts with `wrun_withFork`
  ([`Blanc/Lift/NodeWalkFork.lean`](../Blanc/Lift/NodeWalkFork.lean)) and the child-machinery
  lemmas `childStart_withFork`, `childRun_withFork`, `callResume_withFork`,
  `callPairFrom_withFork` and `stepN_withFork` (a
  Prague machine's `stepN` run, in which `CLZ` is invalid) in
  [`Blanc/Lift/WitnessFork.lean`](../Blanc/Lift/WitnessFork.lean): the interpreter's
  synchronous precompile children and code children run only frames that avoid `MODEXP` and
  `P256VERIFY` (`frameEntryForkFree`), so a run is unchanged by the fork with no side
  condition beyond zero excess blob gas. Restate each frame lemma for the machines
  `X.withFork g`, taking the Prague kernel fact and the spawn facts (`callPrep_withFork`,
  `frameEnterS_withFork_of_stat`, a kernel fact on the spawned frame's `codeAddress`); worked
  example `vminus_witness_covered` in
  `Blanc/Lift/VyperNonreentrantDeployed/Vulnerable/{ForkKernel,ForkFrames,ForkTop}.lean`.
- To state a transaction-level witness under every covered fork, give the transaction an access
  list that already names every precompile of every covered fork (`osakaPrecompiles`), the
  target and (via the coinbase) the sender: `prepareMessage` pre-warms the fork's own precompiles
  (Osaka adds `P256VERIFY`) and re-inserting an address already in a `Std.HashSet` returns the same
  set (`hashSet_insert_of_mem`, `hashSet_insertMany_of_subset`), so the prepared message is the
  Prague one with its fork changed (`prepareMessage_withFork` in
  [`Blanc/TransactionFork.lean`](../Blanc/TransactionFork.lean)); `Std.HashSet` insertion does not
  evaluate in the kernel, so a kernel `rfl` cannot show it. The per-transaction gas cap of EIP-7825
  (2^24, Osaka and later) needs a transaction with less gas. The admission checks and the
  `processTransaction` envelope are then per-fork kernel evaluations (`hg.cases`) feeding
  `processTransaction_of_stages`. Worked example
  `Blanc/Lift/VyperNonreentrantDeployed/Vulnerable/{TxTopC,TxC/*}.lean`
  (`vminus_txC_message`, `vminus_txC_process`: a 16,043,200-gas transaction, one kernel run of the
  Prague chain, every frame lemma restated for `withFork g`).
  Its signature premise is discharged for the concrete transaction by `TxC.txC_recoveredSender`
  (`TxCRecover.lean`): the access-list encoding by `toBLT_noKeys`/`join_entries`, the signing hash and
  secp256k1 recovery by `decide +kernel` (the kernel cannot unfold `BLT.toBytes`, so rewrite the encoding first).
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
- [`Blanc/ExecutionTraceCreateResult.lean`](../Blanc/ExecutionTraceCreateResult.lean)
  supplies `ExecutionTrace.MessageCallTrace.exists_clean_create`: for an actual
  retained creation-message trace under `stateGas = none`, its output's
  `error = none` excludes collision and exposes the same retained CREATE core,
  core result equation, clean marker and world-state equality.
  `exists_clean_create_with_deletions` additionally identifies the actual
  output deletion set with that same CREATE result. Outer
  `Except.ok` alone is insufficient. This supplies neither receipt inclusion
  nor transaction settlement or historical occurrence. Its existential result
  has no selective direct goal-head recipe.
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
prefix or empties consolidation output. Payload validity, withdrawal FIFO
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

To recover the receipt root, logs bloom and transaction root checked by an
original selected-domain block, use
[`Blanc/ExecutionBlockCommitments.lean`](../Blanc/ExecutionBlockCommitments.lean):
`ExecutionTrace.ConfiguredBlockTraceIn.headerCommitments` returns their
conjunction, and `.receiptRoot`, `.bloom` and `.txsRoot` give the individual
header-to-output equalities. These consume only the original trace; its
successful transition, selected fork and deterministic body run identify the
checked output. They do not authenticate separately fetched receipts or prove
trie injectivity. The projected equality goals have no carrier-specific head,
so discovery stays in this branch rather than in a proof recipe.

To exclude an address using a missing log-bloom bit, use
[`Blanc/LogBloom.lean`](../Blanc/LogBloom.lean).
`LogBloom.ContainsAddress` requires all three address bits from Jaune's actual
Keccak digest; `HasIndex`, `byteIndex` and `bitMask` expose an individual bit.
`LogBloom.containsAddress_of_mem` proves that a member of `logs` has all three
bits in `logsBloom logs`; `address_ne_of_missing` is its exclusion form. OR
updates preserve existing bits, including through later logs and topics.
No hash injectivity or cryptographic exclusion premise is needed.
[`Blanc/ExecutionBlockLogExclusion.lean`](../Blanc/ExecutionBlockLogExclusion.lean)
connects this to the original configured execution:
`ExecutionTrace.ConfiguredBlockTraceIn.containsAddress_of_log_mem` gives the
checked header's bits from membership in that block's actual output logs, and
`.address_ne_of_bloom_missing` excludes an address when those bits are missing.
Identifying an observed historical header remains a separate obligation.
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
the second history's `.step` spine. Its lemmas `rawFrames_append` and
`settledFrames_append` concatenate the frame lists in order, and
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
[`Blanc/ExecutionBodyTransactionCut.lean`](../Blanc/ExecutionBodyTransactionCut.lean)
provides `decodeTxs_inr`, `StagedBodyTrace.decodedTxs_eq_of_inr`, and
`StagedBodyTrace.txSplit_tx_eq_of_inr`. An explicit full ordered body equality
and selected-list position identify the supplied original cut's transaction;
they supply no historical observation, sender, receipt, or state fact.
The common owner also derives structural `DecidableEq` instances for
`Jaune.Auth`, `Jaune.TxType`, and `Jaune.Tx` for finite kernel certificates.
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
`ConfiguredBlockTraceIn.rawFrames_txSplit` / `settledFrames_txSplit` split a
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
credits under `BodyStageCapabilities F`), `rawFrames_entered` (any `EnteredCondition`),
`rootEntryIn` and `calldata_bound`, each through `rawFrames_mem_block`.

For the original retained forest and admitted queries after a transaction cut,
use [`Blanc/ExecutionMidHistoryInForest.lean`](../Blanc/ExecutionMidHistoryInForest.lean).
It imports the canonical `MidHistoryTraceIn.settledRoots` and `settledFrames_eq`
from [`Blanc/ExecutionHistoryCommittedCuts.lean`](../Blanc/ExecutionHistoryCommittedCuts.lean);
`settledFrames_parentIn` adds the actual suffix roots' parent relation.
`ApplyTransactionsTrace.TxSplit.senderQueries_after` proves the exact query drop
for any genuine cut; `senderOccurrences_tail_indexed` preserves original indices
and full transaction inputs. `senderQueries_cut_prefix`, `rawFrames_cut_prefix`
and `settledFrames_cut_prefix` embed the mid history as the original full history's
ordered suffix, with membership corollaries. The query list preserves duplicates
and includes admitted transactions whose VM execution reverts.
`settledRoots_caller_ne_of_senderQueries` transfers actual sender-query exclusion
and a distinct system address to mid root callers. The start remains the cut's
actual `afterBenv`; these APIs neither create a block-chain checkpoint there nor
rebase deployment-world facts from the full history.

For an interval ending before another actual transaction cut, use
[`Blanc/ExecutionSenderQueryCuts.lean`](../Blanc/ExecutionSenderQueryCuts.lean).
`ConfiguredHistoryTraceIn.senderQueries_between_txSplits` identifies exactly the
first suffix, intermediate blocks and final prefix, retaining query order and
duplicates. `noSenderAt_between_txSplits_of_senderQueries` supplies precisely
those three sender folds; `txRawFrames_caller_excluded_between_txSplits` consumes
them with independent entry-code emptiness and creation-avoidance producers.
`settledRoots_caller_excluded_between_txSplits` transfers that result to every
committed frame under the original interval's complete roots, using the actual
disabled system stages. Its origin bridges are
`ApplyTransactionsTrace.mem_rawFrames_of_mem_root_committed` and
`ConfiguredHistoryTraceIn.mem_txRawFrames_of_mem_settledFrames_of_disabled`.
The existing forest owner also supplies `TxSplit.senderQueries_before` for the
strict prefix and `TxSplit.senderQueries_from` for the selected admission plus
suffix. No unrelated transaction before the first cut is required. The selected
last transaction remains outside the interval. These quantified interval
conclusions have no reliable single goal-head recipe; the existing admitted
sender-query recipe remains the route for each direct `NoSenderAt` subgoal.

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
transactions on Cancun and later eras goes through the neutral non-deletion
chain in
[`Blanc/ExecutionHistoryInNoDel.lean`](../Blanc/ExecutionHistoryInNoDel.lean):
neutral (`stateGas = none` plus EIP-6780 flag) twins of the interpreter core
(`Evm.step_effect_noStateGas`, `Exec.effect_neutralSchedule`,
`Exec.inv_noDel_noStateGas`), the message/create/call preservation twins
(`processMessageCall_accountsToDelete_ne_noStateGas`), the settlement-form
twin (`TransactionTrace.exists_finalStateForm_noStateGas` with explicit
refund-quotient/touched-sweep hypotheses), and the transaction(-list) keep
twins (`TransactionTrace.codeAt_keep_noStateGas`,
`ApplyTransactionsTrace.codeAt_keep_noStateGas`). Era schedule facts
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

To identify the literal block in a retained configured transition, use
`ExecutionTrace.ConfiguredBlockTrace.block_eq_of_transition` in
[`Blanc/ExecutionHistoryExact.lean`](../Blanc/ExecutionHistoryExact.lean).
For an append-shaped post-chain equality, `BlockForward.ConfiguredBlockTrace.block_eq`
directly identifies the retained block.
Supply a successful transition with the same configuration and endpoints;
the post-world last-block field identifies the retained block without
reconstructing its body trace. This remains COMMON_API-only: the projected
block equality alone does not identify an available successful-transition
witness. Existing facilities were checked, but current matchers do not inspect
that required local premise; a broad `Eq` trigger would not be selective.

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

For forward location from a supplied root-frame occurrence, use
[`Blanc/ExecutionPathLocator.lean`](../Blanc/ExecutionPathLocator.lean):
`Exec.NinstOccurrence.exists_root_call_child` takes the root commit proof,
the exact root-indexed occurrence and root-same-frame `ParentPrefix`, an actual
some child slot, and its matching CALL-shaped spawn, clean `ProcessMessage`
and successful resume. It returns committed child membership and an
`EnteringOccurrence` whose parent is exactly the root and whose occurrence is
the supplied one, with the exact slot and singleton child-index path. Its
call-shaped premise is `Frame.ofCall`, not an instruction-label classification;
the consumer must still identify the concrete source CALL. A clean
child alone does not retain an uncommitted parent, and an immediate/no-code
slot does not establish an entered child. The later source-route producer
must supply that same-frame provenance; endpoint states cannot replace it.
`Exec.Deriv.ExecFreeUntil.descendantFramePaths_eq` preserves the exact ordered
path list across a proved frame-entry-free span at any supplied parent path and
child counter. Both ends use the same counter; childless completed messages
outside that span still count. Obtain the span from actual execution evidence.
This equality supplies no root commitment or chosen child occurrence by itself.
`Exec.Deriv.ParentStep.descendantFramePaths_spawn_suffix` crosses one actual
spawning parent edge: its exact settlement-filtered child prefix is followed by
that same parent continuation at counter `index + 1`. A childless completed
message contributes an empty prefix and still advances the counter. Combine
this with proved entry-free spans to retain the original ordered suffix; a
membership witness or selected index is not a substitute. This theorem does
not supply root commitment, an entering witness or an exhaustive source replay.
Its joint edge/spawn premises retain the same registry-only discovery boundary.
Existing discovery and suggestion facilities were checked. The existential
membership goal alone does not identify the available occurrence, root-prefix,
spawn and process witnesses; current matchers do not inspect this joint local
context, so a broad existential trigger would not reliably select this route.

To take apart an arbitrary run whose first step is a spawn,
`Exec.exists_next_of_run_spawn` in the same module takes the step equation
`Evm.step … = .spawn frame resume nextPc`, the entry
`frame.enter = .run childEvm`, the entered child's `Exec` and a successful
resume, and returns the continuation `next` together with the equation
`run = .runOk spawn entered child resumed next`. Rewriting by that equation lets
raw-frame membership facts about `next` and the child transfer to `run`.

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
target and code address. Worked use: `Blanc/Lift/UniswapV2Pair/PairPositionalCalls.lean`.

The same owner supplies the raw counterparts, including rolled-back children:
`Exec.Deriv.ExecFreeUntil.rawFrameDescendants_eq` preserves raw descendants across
an actual entry-free span, and `Exec.Deriv.ParentStep.rawFrameDescendants_cases`
separates the continuation from an actual entered child's raw roots. These facts
do not assert settlement commitment. Worked use:
`Blanc/Composition/UniswapV2PairWeth9CapstoneSwapRaw.lean`, through the preserved
CapstoneRaw wrappers. This is a registry-only route: the equality or membership
goal alone does not identify the required free-span or parent-edge witness;
the current suggestion matchers do not select from that joint local evidence.

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
`Frame.settle_logs_of_ok` preserves logs through successful frame settlement,
and `Frame.enter_done_clean_logs_noStateGas` proves an immediate clean entry
has no logs. These reuse the same settlement and native-entry proofs.

To identify the observation of an actual successful LOG without unfolding a
physical memory image, use
[`Blanc/ExecutionLogImage.lean`](../Blanc/ExecutionLogImage.lean).
`Exec.Deriv.successfulLog?_eq` combines the same node's actual successful
outcome, decoded LOG count, explicit operand prefix and symbolic memory-read
payload. It derives that node's exact `successfulLog?` entry, with topics taken
from the operand tail. It proves neither enclosing retention nor receipt
identity; use the parent-log attribution bridge for those. Keep the memory as
a variable projection and pass a separately proved payload equation. The
joint decoded-node/stack/payload requirements have no reliable narrow recipe
trigger; discover the helper here before normalizing a concrete machine image.

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
`Exec.targetLogEventsFrom_frames` proves its frame projection equals
`Exec.retainedTargetFramesFromAt`, with matching `_target`, `_halt`, `_cont`,
`_doneOk` and `_runOk` equations. The same module transports one foreign step for
arbitrary callee code: `Evm.step_cont_getStor_foreign_noStateGas` preserves a foreign owner's
storage without protection; `Evm.step_done_getStor` requires a protected owner
for completed childless message settlement; `Xinst.spawn_run_getStor` and
`Evm.step_run_getStor_noStateGas` transport code-bearing storage from the settled child's
committed endpoint or rollback, pointwise. The `_noStateGas` forms take
`rules.stateGas = none`; under a covered fork apply them to
`CoveredFork.rules_stateGas_none`. The actual-step helpers
`GenericCreate.step_done_getStor`, `GenericCall.step_done_getStor` and
`Xinst.step_done_getStor`, in
[`Blanc/ExecutionMessageEffects.lean`](../Blanc/ExecutionMessageEffects.lean),
preserve every owner when the step itself returns `.done (.ok post)`; the
executable helper requires `CoveredFork`. Successful CALL message transfer is a
spawn and does not satisfy that actual-step premise. The module also transports
logs (`Exec.cont_logs_eq`,
`Exec.doneOk_logs_eq`, `Exec.runOk_logs_eq`, path-independent `Exec.committed_logs_at`,
and `Xinst.call_run_logs`: a CALL/STATICCALL appends exactly its committed child's
logs), the installed image (`CodeSem.At.parentStep`, `CodeSem.At.spawnChild_noStateGas`,
`CodeSem.At.callChild`, self-calls included), child entry (`Xinst.spawn_child_world`,
`Xinst.spawn_child_logs`, `Xinst.call_spawn_ofCall`, `Frame.ofCall_settle_clean`),
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

Use [`Blanc/AbstractStackCertificate.lean`](../Blanc/AbstractStackCertificate.lean)
and reach the whole chain with one import, `import Blanc.AbstractStackCertificate`.
It is contract-neutral: nothing in it names a contract, and it rests only on
[`Blanc/ExecutionOccurrence.lean`](../Blanc/ExecutionOccurrence.lean) and
[`Blanc/ForwardCall.lean`](../Blanc/ForwardCall.lean).

The need is to show that fixed compiled bytes never underflow or overflow the
operand stack, over the *actual* decoded execution — including failing terminal
outcomes and resumption after a child call — without an adequate-gas or
successful-run premise. Do not hand-roll a per-contract stack-height counter for
this; that is the argument the checker replaces.

The four layers, bottom-up:

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
- [`Blanc/AbstractStackCertificate.lean`](../Blanc/AbstractStackCertificate.lean)
  is the entry point. `Table` is a finite search tree of rows; `checkTable` runs
  the complete finite validation and `checkTable_certificate` turns a successful
  check into a `Certificate`.

The whole minimal use is four declarations, kept live at the end of the owner
module as `exampleCode`, `exampleTable`, `exampleTable_checked` and
`exampleTable_certificate`:

```lean
def exampleCode : ByteArray := ByteArray.mk #[0x60, 0x01, 0x50, 0x00]

def exampleTable : Table :=
  .node 2 [none] (.node 0 [] .empty .empty) (.node 3 [] .empty .empty)

theorem exampleTable_checked : checkTable exampleCode exampleTable 1 = true := by
  decide

theorem exampleTable_certificate {sevm : Sevm} (code : sevm.code = exampleCode) :
    Certificate sevm exampleTable.Invariant 1 :=
  checkTable_certificate (code ▸ exampleTable_checked)
```

**Semantic boundary.** The certificate is *local and same-frame*. It concludes
that every reached same-frame node satisfies the checked invariant and that no
step generates an operand-stack fault; it says nothing about gas, liveness,
termination, whether any program counter is reached at all, or what the code of
a spawned child frame does. A CALL's own child is arbitrary — only the parent's
resumption is covered, and a stack fault arriving through the settlement is
attributed to the child by `InheritedStackFault`, not excluded.

The accepted family is deliberately narrow and every rejection fails closed to
`false`, never to a silent pass. `regularTransfer` covers `ADD`, `MUL`, `SUB`,
`DIV`, `LT`, `GT`, `EQ`, `ISZERO`, `AND`, `SHR`, `CALLER`, `CALLVALUE`,
`CALLDATALOAD`, `CALLDATASIZE`, `TIMESTAMP`, `POP`, `MLOAD`, `MSTORE`, `SLOAD`,
`SSTORE`, `GAS`, and `DUP`/`SWAP`; every other regular opcode is rejected. Among
the external instructions only `CALL` is accepted. `SELFDESTRUCT` is rejected.
`checkRow` requires the row to sit inside actual code and refuses to rely on
padded PUSH bytes; a jump destination must be an exact literal *and* satisfy the
public `jumpable` predicate, neither condition alone being enough (see the
destination boundary below); `Table.checkOrder` checks search order rather than
assuming it. The table shape supplies no trusted premise: a wrong tree fails the
check instead of weakening the theorem.

**Destination boundary.** The checker cannot certify a program whose `JUMP` or
`JUMPI` destination is not a literal the table can name. `jumpable` is a
necessary condition applied *after* the destination has already been pinned to a
concrete `B256`, not an alternative to pinning it:
`Blanc.AbstractStackSafety.jumpTransfer` matches only `some destination :: words`,
so a destination the pattern has forgotten — the `none` entry that `Pattern` uses
for an abstract word — falls through to the wildcard, returns `none`, and
`checkInstruction` returns `false`. `jumpiTransfer` behaves the same way for the
`JUMPI` destination, though its branch *condition* may stay abstract because the
theorem covers both arms. So a computed or otherwise unpinned jump target is
rejected; it is never certified on the strength of being jumpable. This is a
boundary of the checker, not a defect: the rejection is the same fail-closed
`false` as any other unaccepted shape, and no theorem is weakened by it. Lifting
it needs a `jumpTransfer` soundness theorem that admits an abstract destination —
one concluding safety for every value the forgotten word could take, and so
obliged to relate an unknown target to the table's rows — not a change to the
table format or a wider `jumpable` check.

**Cost boundary.** `checkTable` hard-caps the stack ceiling at `maximum ≤ 8` —
that is the limit of the accepted transfer family, not a tuning knob, and
raising it needs new transfer theorems, not a larger literal. Validation is one
kernel `decide` over the tree, so its cost grows with row count and pattern
width and it is not the place for a table with thousands of rows; split the
program and check pieces with `Table.all_node`. `Table.count_le_one` and
`Table.checkLayout` are available when a row-uniqueness or contiguous-layout
argument is wanted.

**Untrusted producer.** `scripts/stack_certificate.py` accepts bytes and an
explicit maximum, runs the conservative whole-stack worklist transfer, and
emits deterministic sorted, balanced packs of at most 15 leaf rows. Its CLI is
the generic entry point; import the module when a contract-specific extractor
needs to name its source. The producer neither extends the accepted opcode
family nor supplies a theorem. Its output becomes evidence only when the
unchanged Lean `checkTable` accepts it against the actual code.

The first working extraction route is
`python3 scripts/gen-proxy-pair-stack-certificate.py`. It evaluates
`Blanc.ProxyPair.Upgrade.v1Bytes`, which is the actual `Prog.compile` result,
then byte-compares the generated owner. Add `--write` to regenerate that owner.
This is also the registered stale/missing-output check. The fixed 15-row leaf
size is inherited from the DRIP donor and is only a representation boundary;
no packing optimum is claimed.

**First real consumer.**
[`Blanc/ProxyPairUpgradeStackSafety.lean`](../Blanc/ProxyPairUpgradeStackSafety.lean)
certifies `v1Code` — the 74-byte upgrade-witness runtime deployed at
`v1Implementation` and executed by `ProxyPairUpgradeRefinement` — with 47 rows
for its 47 reachable program counters, a ceiling of three words, one
`decide +kernel`, and `Certificate.at_parentPrefix` for the transported
conclusion. Its former right-leaning handwritten table is now generated as four
15-row-or-smaller leaves and three composing nodes. The 47 PCs, heights, and
known words are unchanged; selector literals render as their numeric `B256`
values, which the check validates against `v1Code`. The PC30 fallback jump and
its PC0 destination lie in different packs: the source pack passes when it
looks up successors in the full table, fails against itself, and removing only
row zero makes the full check reject. The original four negative controls also
remain beside the certificate.

**What is in reach.** For Blanc-compiled code the binding constraint is the
accepted opcode family, not the destination boundary. `Func.compile` emits a
jump only as `PUSH2 <literal>` before `JUMP`/`JUMPI`, and `Func.call` the same,
so no program this compiler produces can carry a destination the table cannot
name; the destination boundary above is real but unreachable from Blanc source.
Every production runtime in the tree is instead rejected for an instruction
outside the family: WETH and FMINT for `ADDRESS`/`BALANCE`/`SHL` (`Blanc/Weth.lean:115`,
`Blanc/Fmint.lean:300`), PRORATA for `NOT`/`SELFBALANCE` (`Blanc/Prorata.lean:81`),
BeaconDeposit for `CALLDATACOPY`/`MSTORE8`/`MOD`/`STATICCALL`
(`Blanc/BeaconDeposit.lean:49`), Lido CircuitBreaker for
`EXTCODESIZE`/`STATICCALL`/`TLOAD`/`TSTORE`
(`Blanc/LidoCircuitBreaker.lean:330`), Lido TriggerableWithdrawalsGateway for
`OR`/`XOR` (`Blanc/LidoTriggerableWithdrawalsGateway.lean:74`), WETH10 for
`CHAINID`/`RETURNDATACOPY` and the WETH set (`Blanc/Weth10.lean:173`), and both
proxies for `DELEGATECALL`/`RETURNDATASIZE`/`CALLDATACOPY`
(`Blanc/ProxyPairProgram.lean:49`). Widening the transfer family is what admits
them. `Blanc/ProxyPairImplementation.lean`'s 25-byte `implGuardedCode` is the
one other runtime already inside the family, at a 19-row table and a ceiling of
two.

### E10. I have a successful source run of a body that must store

Use [`Blanc/StaticStores.lean`](../Blanc/StaticStores.lean). Prove
`StoresOrHalts fs f`, then apply `StoresOrHalts.isStatic_eq_false` to the exact
premise `Func.Run fs e s f r`; the conclusion is `e.isStatic = false`.
`stores_structure` walks instruction and branch structure to an `SSTORE` or an
unrunnable `Func.revert` arm. For a long `Line` before the first store, use
`stores_line line` with the exact prefix supplied explicitly; the driver never
searches for an arbitrary line split. Contract-specific calls remain explicit
through `StoresOrHalts.call` or the `with` arm of `stores_structure`.

The relation requires every successful path either to reach `SSTORE` or to be
impossible under the universal premise carried by `StoresOrHalts.never`. A body
with an executable `Func.stop` arm does not meet it. The result neither proves
that the body runs nor describes the storage effect. The production example is
`LidoTriggerableWithdrawalsGateway.setLimitWrite_storesOrHalts` in
[`Blanc/LidoTriggerableWithdrawalsGatewayStaticStores.lean`](../Blanc/LidoTriggerableWithdrawalsGatewayStaticStores.lean):
it names the exact `mloadWord 0 ++ [pushB256 maxExitRequestsLimitSlot]` prefix
and closes at the following `SSTORE` without changing or duplicating the body.

## I — invariance and noninterference

### I1. One instruction/line/function preserves an observation

- Coarse outcome-aware instruction frames in
  [`Blanc/CommonProofs.lean`](../Blanc/CommonProofs.lean):
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
- `Xinst.step_shapeNoStateGas` in
  [`Blanc/CommonProofs.lean`](../Blanc/CommonProofs.lean) gives the
  `Xinst.ShapeCovered` done/create/call decomposition from the actual
  `rules.stateGas = none` capability, including disabled CREATE2's error arm.
  Its existing `Xinst.step_shapeCovered` wrapper keeps the modern interface.
  The `xinst-step-shape` recipe applies only to this ordinary-lane shape goal;
  it proves no opcode availability, successful run, gas equality or child commitment.
  For capability transport into an actual entered child, use
  `Xinst.Run.some_child_benvStat` or `Evm.step_spawn_child_benvStat` in the same
  owner: each gives exact parent/child block-environment equality without a
  fork-domain premise. Existing modern child-fork facts wrap these equalities.
  Their equality conclusions have no additional reliable single-head trigger.
- For successful checked stack transfer, use `ninstTransfer_run_noStateGas`
  in [`Blanc/Lift/Transfer.lean`](../Blanc/Lift/Transfer.lean). It requires only
  `rules.stateGas = none`, handles both access schedules and delegation
  settings, and derives opcode availability from actual success where needed.
  `run_balance_stack` in the same module gives BALANCE's exact account-read
  stack result under either access schedule. The original `ninstTransfer_run`
  retains its modern statement. These stack observations have no reliable
  registered single goal-head trigger.
- `Ninst.Inv`, `Rinst.Inv`, and `Line.Inv`: use `line_inv` plus the registered
  `Ninst.Hinv` / `Rinst.Hinv` instances in `Blanc/Tactics.lean`.
- `Func.Inv`: use `func_inv`; it intentionally refuses arbitrary `Func.call`.
- For direct stack-prefix transport through shared line instructions, use the
  `prefix_of_*` family in [`Blanc/CommonProofs.lean`](../Blanc/CommonProofs.lean),
  including `prefix_of_mul`, `prefix_of_div`, `prefix_of_timestamp`,
  `prefix_of_xor`, and `prefix_of_argCheckNonAddress`. These declarations are
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
  `ninstRunCompiled_withStaticGas` retains the same child-execution slot for
  every instruction, including external calls; `linstRun_withStaticGas`
  covers terminal instructions. `SFunc.RunExact.withStaticGas` transports the
  full exact derivation, including program references and PC nodes.
  `ExactCallProfile.withStaticGas` preserves the literal debit and successor
  functions; `StaticWordCallProfile.withStaticGas` and
  `MutableCallProfile.withStaticGas` also transport their indexed identity
  readiness postconditions via `IdReady.withStaticGas`. `sloadCost_withStaticGas`,
  `sstoreCost_withStaticGas`, `afterSload_withStaticGas`, `afterSstore_withStaticGas` and
  `dataWord_withStaticGas` (all `rfl`) are the storage-charge, post-world and calldata-word
  facts an exact schedule's cost transport unfolds to. These theorems update
  `Sevm.gas`, leaving dynamic `Devm.gasLeft` unchanged.
- To state a frame theorem (given at an arbitrary static machine and entry
  `St pre [] Mem.empty G`) for a message entered with an execution grant, use
  [`Blanc/Lift/StaticGasMessage.lean`](../Blanc/Lift/StaticGasMessage.lean): `Msg.withGas`,
  `initSevm_withGas` (`{initSevm msg with gas := G}`), `initDevm_withGas`
  (`St (initDevm msg) [] Mem.empty G`), `initDevm_gasMeasure` and `exec_withGas_of_frame` (a frame
  `Exec` at the grant is `exec (initEvm (msg.withGas G)) = .ok post`). Fix the cost at the base
  message, instantiate the frame theorem at a fresh gas variable `F` with the premises transported
  by `*.withStaticGas F`, rewrite the cost back with the schedule's `*_withStaticGas`, and only
  then relate `F` to `R + c` (rewriting `← hF` rather than substituting, so no definitional check
  unfolds the closed cost). The Curve 3pool instances are
  `Blanc/Lift/Curve3Pool/ExactMessage.lean` (`*_msg_exact`), with the exchange/add_liquidity
  stage transports in `Blanc/Lift/Curve3Pool/ExactStaticGas.lean`. Comparing runs from
  different dynamic gas values still needs the following gas-erasure branch.
  Existing recipe triggers cannot distinguish this static-coordinate update
  from ordinary run construction, so discovery remains in this registry.
- For the canonical successor of a value-0 identity-precompile copy (a gas-normalized
  data form of the resumed caller, at the copy's explicit stack tail, memory and windows),
  use `identityCallNext` in
  [`Blanc/Lift/IdentityCall.lean`](../Blanc/Lift/IdentityCall.lean), with its literal
  `_memory`/`_stack`/`_returnData`/`_gasLeft` facts, `identityCallNext_congr` (the base modulo
  gas, `S`/`M` literal) and `identityCallNext_withStaticGas`.
  `call_identity_step_canonical` / `rxc_call_identity_canonical` and the `RunExCut` twin
  `rxce_call_identity_canonical` in [`Blanc/Lift/RunEx.lean`](../Blanc/Lift/RunEx.lean) add
  `Devm.EqModGas b' (identityCallNext …)` to the old step's post; the old statements are
  their projections. For Vyper's `raw_call` join and tail, `rawJoinBaseNext` (explicit clamped
  length `n`) and `rawTailBaseNext` (the original base's clamped return-data length) in
  [`Blanc/Lift/VyperRawCall.lean`](../Blanc/Lift/VyperRawCall.lean) name the copy's canonical
  base, with congruence and static-gas lemmas; `rxc_vyRawCallJoin_canonical` /
  `rxc_vyRawCallTail_canonical` and their `RunExCut` twins `rxce_vyRawCallJoin_canonical` /
  `rxce_vyRawCallTail_canonical` hand it to the continuation, keeping the literal `vyRawMem`
  memory and the exact charge. These carry no new charge, world premise or gas quantifier.
  No registered trigger distinguishes these from the bounded steps, so discovery remains in
  this registry.
- For the literal memory the 3pool's crossed callees leave (exact walks of `add_liquidity`,
  `remove_liquidity_imbalance`, `remove_liquidity_one_coin`): `_A()`'s is `aMemNext` (`a_exactL`
  in [`Blanc/Lift/Curve3Pool/Callee/A.lean`](../Blanc/Lift/Curve3Pool/Callee/A.lean), the
  `0x1e0` variant `a_exact_1e0L` in
  [`Blanc/Lift/Curve3Pool/Callee/AGrow.lean`](../Blanc/Lift/Curve3Pool/Callee/AGrow.lean));
  `get_D_mem`'s is `getDMemNext` up to bytes (`Mem.EqExcept … fun _ => False`: one logical
  size, every byte equal; `getDMem_exactL` in
  [`Blanc/Lift/Curve3Pool/Callee/GetDMemExact.lean`](../Blanc/Lift/Curve3Pool/Callee/GetDMemExact.lean),
  `getDMem_exact_400L` in
  [`Blanc/Lift/Curve3Pool/Callee/GetDMemGrow.lean`](../Blanc/Lift/Curve3Pool/Callee/GetDMemGrow.lean)),
  since the callee's scratch writes are not materialised alike; the caller's next growing
  store makes it literal (`eqB_write_word_grow` in
  [`Blanc/Lift/MemGlue.lean`](../Blanc/Lift/MemGlue.lean), below). The pool's literal-memory
  forward steps are one kit: `rxe_mstoreL`, `rxe_calldatacopyL`, `rxe_identityL` (with the
  identity call's canonical successor) and `rxe_sstoreX` (exact `SSTORE` charge) in
  [`Blanc/Lift/Curve3Pool/Walk/LiveKit.lean`](../Blanc/Lift/Curve3Pool/Walk/LiveKit.lean), whose
  bounded twins `rxe_mstore`, `rxe_calldatacopy`, `rxe_identity`, `rxe_sstore_le` are
  projections; `rxe_mloadXL`, `rxe_sloadVX`, `rxe_staticWordE` (and the projections
  `rxe_mloadX`, `rxe_sloadB`/`rxe_sloadV`, `rxe_sstoreB`/`rxe_sstoreV`/`rxe_sstoreVX`,
  `rxe_mstoreW`, `rxe_staticWord`) in
  [`Blanc/Lift/Curve3Pool/Walk/ExchangeLiveKit.lean`](../Blanc/Lift/Curve3Pool/Walk/ExchangeLiveKit.lean);
  `add_liquidity`'s `rxe_mloadXE`/`rxe_staticWordAlE` are their projections. A fee iteration's
  words are functions of its inputs (`RliDif.unique`, `RliFeeIter.unique` in
  [`Blanc/Lift/Curve3Pool/Walk/RliExactKit.lean`](../Blanc/Lift/Curve3Pool/Walk/RliExactKit.lean)). The frame save/restore loops around them are literal
  through `rx_svFromLM` / `rx_rsFromLM` (`saveMem`/`restoreMem`) in
  [`Blanc/Lift/Curve3Pool/Walk/LiveLoops.lean`](../Blanc/Lift/Curve3Pool/Walk/LiveLoops.lean).
  The bounded statements (`a_exact`, `getDMem_exact`, `rx_svFromL`, …) are their projections.
- For the 3pool's exact-gas entry frames and their stage cores (an exact walk to reuse or extend):
  `removeLiquidity_live_exact`, `exchange_live_exact`, `addLiquidity_live_exact`,
  `removeLiquidityImbalance_live_exact`, `removeLiquidityOneCoin_live_exact` in
  `Blanc/Lift/Curve3Pool/{RemoveLiquidityExactFrame,ExchangeExactLive,AddLiquidityExactFrame,RemoveLiquidityImbalanceExactFrame,OneCoinExactFrame}.lean`,
  each over a schedule with call data, premise bundle, closed cost and static-gas transport
  (`Walk/{RemoveLiquidity,AddLiquidity,Rli,OneCoin}ExactSchedule.lean`,
  `ExchangeExactSchedule.lean`, `ExactStaticGas.lean`) and relation-parametric stage cores (the
  `*E`/`*_core` walks in `Walk/RemoveLiquidityLive.lean`, `Walk/ExchangeLive*.lean`,
  `Walk/AlLive*.lean`, `Walk/RliLive*.lean`, `Callee/CalcWithdrawLive*.lean` (`rx_cw_*E`) and
  `Walk/OneCoinLive*.lean` (`rx_oc_*E`)), whose bounded statements are projections; the
  message-entry, history and composed twins are `ExactMessage.lean`, `HistoryLiveExact.lean`
  and `Blanc/Composition/Curve3Pool3CrvHeadlinesExact.lean`.
- For equality modulo `gasLeft` across two successful runs of a whole lifted
  tree (`SFunc.RunP`), use
  [`Blanc/Lift/GasErasureRun.lean`](../Blanc/Lift/GasErasureRun.lean).
  `SFunc.RunP.eqModGas` takes two runs of the same tree from `Devm.EqModGas`
  states (the first under any step relation `P` that implies `Ninst.Run`, e.g.
  an actual frame's `StepIn`; the second e.g. a `SFunc.RunExact.toRun`) and
  returns `Outcome.EqModGas`: both halt or both return, in states equal modulo
  gas. The tree is certified by `SFunc.gasFree` and the entry closure
  `GasFreeSet fs S` (decide them by `decide +kernel`); the whitelist is
  `Ninst.gasFreeRun` (`Ninst.gasFree` plus `KECCAK256` and `LOG n`, with
  `Ninst.run_eqModGasRun`) and `Linst.gasFree` (`STOP`, `RETURN`, vacuous
  `REVERT`; `Linst.run_eqModGas`). The consumer pattern removes a gas premise
  from an output fact: run the gas-exact forward walk from
  `pre.withGasLeft N` (`Devm.EqModGas.withGasLeft`) and transfer its output
  (`Devm.EqModGas.output_eq`). The same module adds `of_withOutput`,
  `of_addLog`, `of_popList`, `of_popBurnList`, and
  `Devm.EqModGas.getOrigStorVal_congr`, which transports transaction-original
  storage reads using equality of the created-account sets. It also supplies
  gas-independence of the forward cost helpers (`sloadCost_congr`, `sstoreCost_congr`, `afterSload`,
  `afterSstore`). A dispatcher that reaches a non-gas-free entry needs a
  two-run walk to the selected entry first.

`Linst.selfdestruct_preserves_getCode` and `Linst.selfdestruct_balance_effect`
cover the actual beneficiary credit and refund hooks across historical rules.
The `Linst.selfdestruct_preserves_noDel`, `Linst.run_noDel` and
`Linst.inv_noDel` helpers instead require
`rules.settle.selfdestructOnlyCreated = true`: before that activation, an
existing coded account can schedule itself for deletion. These helpers do not
assert a historical-uniform NoDel invariant.

For a weaker actual step condition,
`Linst.selfdestruct_preserves_noDel_of_onlyCreated_or_foreign` in
`Blanc/CommonProofs.lean` accepts the modern creation restriction **or**
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

- `Linst.EffectFork`, `Evm.step_effectForkTerminal` and
  `Exec.effectForkTerminal` in `Blanc/CommonProofs.lean` let terminal as well
  as nonterminal effects use the frame's `CoveredFork` premise. Child
  coverage follows the actual spawn; the existing unrestricted terminal
  traversal APIs remain available. `Linst.noDelCode_effectFork` and
  `Exec.inv_noDel` in `Blanc/LadderBase.lean` consume this interface without
  assuming historical-uniform no-deletion behavior.
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
  `Exec.inv_noDel_of_retained_terminal_safe` takes a committing actual `Exec`,
  `stateGas = none`, input `Devm.NoDel`, and decoded SELFDESTRUCT exclusion only
  at the selected run's `Exec.retainedNodes` in the protected storage context.
  A single driver induction invokes the selected child's obligation only when
  complete settlement commits. Discarded children require no terminal safety.
  `Evm.step_spawn_resume_atd_of_discarded_noStateGas` proves that an actual spawn,
  discarded COMPLETE `frame.settle raw`, and successful same-resume equation
  preserve the parent's deletion set. `Resume.create_atd_of_error` and
  `Resume.call_atd_of_error` expose its ordinary flagged-resume components.
  `Evm.step_spawn_resume_noDel_of_discarded_noStateGas` combines this with
  `Exec.accountPreserve true` for the actual entered child. The public
  `Exec.noDel_step_of_safe` in `Blanc/ExecutionDeletionSafety.lean` exposes the
  existing step backend with its actual `Xlot.InvNoDel` obligation unchanged.
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
  authorization and code resolution); `ExecutionTrace.TransactionTrace.noDel_of_installedCert`
  gives `wa ∉ messageOut.accountsToDelete` and `wa`'s code `C` after the
  message and in the final state under `stateGas = none` (the deletion fold
  and touched sweep keep it). Generic helpers: `Xlot.invGetCode_of_filled`
  (fork-free slot code preservation) and
  `sweepTouchedAccounts_getCode_of_nonempty` (the sweep never erases an
  account with nonempty code). It needs `wa ∉ benv.createdAccounts`.
- History closure of that producer:
  [`Blanc/ExecutionNoDelHistory.lean`](../Blanc/ExecutionNoDelHistory.lean).
  `InstalledCert C` bundles the actual runtime facts (certificate check,
  `callOnly`, `noSelfdestruct`, no designator, nonempty). Stage lemmas
  `SystemMessageTrace`/`RequestsTrace.noDel_of_installedCert` (system calls,
  including a system target equal to `wa`), `Beacon`/`History`/`RequestStageTrace.code_of_installedCert`,
  `ApplyTransactionsTrace.noDel_of_installedCert`, `StagedBodyTrace.noDel_of_installedCert`,
  `ConfiguredBlockTraceIn.noDel_of_installedCert` and
  `ConfiguredHistoryTraceIn.noDel_of_installedCert` carry `getCode wa = C` from
  the checkpoint to the history's endpoint state (by induction, every
  checkpoint of its spine) and prove the recursive `…NoDelScheduled wa` (no
  selected transaction schedules `wa` for deletion). No `CoveredFork`;
  per-block `stateGas = none` from `BodyStageCapabilities F`; no premise that
  `wa` is never targeted; block-level `createdAccounts` is empty at
  `initBenv`. Also `payRewards_getCode` and the shared
  `toList_ne_nil_of_size_ne_zero` behind each contract's `code_toList_ne_nil`.
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
  `cut.before` to `cut.benv`.
  `MidHistoryTraceIn.code_before_txSplit_of_installedCert` composes those exact
  source and destination boundaries. Only `InstalledCert`, the selected
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
  The old WETH10 namespace theorem interfaces are direct compatibility aliases.
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
  `ConfiguredBlockTraceIn.settledRoots_eq_txSplit` lifts that arbitrary-cut split
  to the original block including system stages.
  `ConfiguredHistoryTraceIn.mem_settledRoots_of_between_txSplits` embeds the exact
  after-first/before-last interval in the connected prefix/blocks/suffix history.
  Use it to derive root membership rather than supplying an independent population
  premise. These list membership/equality goals have no selective recipe head.
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
  For the cell at every actual settlement-retained node entry, use
  [`Blanc/ExecutionRetainedCellAt.lean`](../Blanc/ExecutionRetainedCellAt.lean):
  `Exec.retainedNodes_cellProv_noStateGas` takes a committing run, state-gas
  absence, nonempty owner entry code and the exact retained split
  `before ++ node :: after`. It proves `CellProv` at the node using only the
  strictly earlier retained `before`, with no no-write, context or safety
  premise. Child endpoint replay witnesses stay in that child's retained
  nodes; no raw or later writer is substituted.
  `Exec.retainedNode_cell_eq_of_noRetainedWriteTo_noStateGas` projects this
  producer under `NoRetainedWriteTo`, preserving its original signature.
  Completely rolled-back children contribute no nodes; their raw writes
  remain permitted. This is a per-run law, not transaction settlement or
  receipt/history continuity. Use this branch and the named theorem: an
  expanded cell equality alone does not identify the intended retained run.
- Reentrancy-lock exclusion over the all-outcome frame tree:
  [`Blanc/LockExclusion.lean`](../Blanc/LockExclusion.lean).
  `LockExclusion.LockSpec.lock_exclusion` says an active lock frame's spawned
  child (any outcome) enters no guarded body of the same owner and code;
  `LockSpec.locked_core` keeps the lock cell fixed, slot-addressed owner
  `SSTORE`s absent and `NoRetainedWriteTo` true below any locked node.  Both
  take nonempty entry world code at the observed owner, the per-code
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
  `Exec.ownerCode_of_world` says every raw frame root (any outcome) owning
  `P`'s storage runs `C` or an EIP-1167 forwarder `K` to `I`, when `P` holds
  `K` or `C`, `I` holds `C`, and no frame running `C` executes
  `DELEGATECALL`/`CALLCODE` (`Exec.NoDelegateFrom`);
  `Exec.ownerDiscipline_of_world` discharges `LockSpec.OwnerDiscipline` from
  it.  `ForwarderShape K I` is the decidable forwarder shape (`forwarderCode`
  template; `forwarderShape_847e`/`_6326` by `decide`), `noSstore_of_scan`
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
- Write-freedom across cycles:
  [`Blanc/CycleWriteFree.lean`](../Blanc/CycleWriteFree.lean).
  Its public `Func.callsIn_mem_iff` reflects the shared internal-call checker.
- Route-local source-`.exec` freedom across finite call-closed components:
  [`Blanc/ReachableExecFree.lean`](../Blanc/ReachableExecFree.lean).
  Use `Prog.reachableExecFree` / `Prog.reachableExecFree_iff` for the
  executable certificate, `SourceCursor.noExec_of_reachableExecFree` for an
  already-selected actual source cursor, and
  `Exec.noRetainedWriteTo_of_exactMain_reachableExecFree` for an exact main
  invocation.  A calldata-selected dispatcher consumer can first use
  `Toward.linearDispatchWith_selectedBody`, then the same cursor theorem.
  The certificate checks both branch arms and a finite, lookup-resolved,
  call-closed component; it deliberately says nothing about unselected
  entries, child outcomes, commitment, gas, or liveness.
- Persistent-storage silence of static execution:
  [`Blanc/StaticStorage.lean`](../Blanc/StaticStorage.lean).  `Devm.storageView`
  is the extensional `Stor.get` observation the contract invariants use.  The
  module supplies its `PopBurn.Inv`, `Burn.Inv`, and lifts the existing generic
  `Linst.Hinv` / `Ninst.Hinv` facts to that observation; it deliberately does
  not manufacture a universal `STATICCALL` `Hinv`.
  `Exec.rawNodes_isStatic_of_static` and
  `Exec.retainedStorageWrites_eq_nil_of_static` propagate the static flag and
  exclude successful `SSTORE`. Storage can also change through normalized
  balance transfer, so `Exec.storageView_committedPost_eq_of_static` and
  `Exec.getStor_committedPost_eq_of_static` require a protected entry current
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
  The shared raw-storage proof now lives in `Blanc.StaticStorage`;
  `Ninst.staticcall_getStor_eq` derives its entry condition from actual routing.
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
  theorem directly.  Worked use:
  `Blanc/Composition/ProrataWethVaultPairVaultSegment.lean` discharges the
  vault's live-quoting read-only paths through it.  Import
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

## S — state and machine updates

### S1. I need a projection through one update

Use Jaune's update-first laws named `Devm.<update>_<projection>` before
unfolding a concrete state tower. Examples include:

- `Devm.setMach_stack`, `Devm.setMach_memory`,
  `Devm.setMach_accessedStorageKeys`, and the other `setMach` projections.
- `Devm.withOutput_state`, `Devm.withOutput_logs`,
  `Devm.withOutput_transientStorage`, and sibling projections.
- `Devm.memWrite_gasLeft` in Jaune and `Devm.memWrite_memory` /
  `Devm.memWrite_stack` in `Blanc/CommonProofs.lean`.

- `Devm.creditBeneficiary_getCode` and `Devm.creditBeneficiary_delSets` in
  `Blanc/CommonProofs.lean` preserve code and the deletion sets under either
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
  existing-account `setPresent` branch, and Blanc's
  `setStorVal_getStor_self` / `Devm.getStorVal_setStorVal_self` projections.

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

`Devm.getStorVal_of_state` in
[`Blanc/MachineDataFacts.lean`](../Blanc/MachineDataFacts.lean) transports a
persistent-storage word across account-state equality, without requiring
equality of the whole machine or world. Import that primitive owner directly.
For the entire storage map at one address, the corresponding adapter is
`getStor_eq_of_state_eq` in `Blanc/LadderBase.lean`.

Use [`Blanc/CommonProofs.lean`](../Blanc/CommonProofs.lean):

- `Stor.get_set_ite` exposes a single storage-map update as the equality
  branch at an arbitrary observed key.
- `Devm.addAccessedStorageKey_setMach_setMach` cancels an obsolete machine
  component across an access-key update followed by the final `setMach`.
- `of_run_sload_state` and `of_run_sload_logs` expose the persistent-state
  and log silence of a successful `SLOAD`, including its cold access-list
  warming path.  Use these instead of widening the global `Ninst.Hinv`
  instance set: access metadata changes even though these projections do not.
- `Devm.getStorVal_setStorVal_self` is persistent storage read-after-write.
- Jaune's `Devm.setStorVal_getCode` carries account code across a persistent
  storage write, and Jaune's `Devm.setCode_getStor` storage across code
  installation. `Devm.withRefundCounter_getStor`,
  `Devm.withRefundCounter_getCode`, `Devm.withRefundCounter_getBal`, and
  `Devm.withRefundCounter_createdAccounts` cut through the refund-counter
  update of an SSTORE post; `Devm.setStorVal_createdAccounts` carries the
  created-account set across the storage write itself. Rewrite with these
  before unfolding a concrete write tower instead of a `change` or a local
  `rfl` restatement. `Devm.setCode_logs`,
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
  `State.subBal_zero_of_protected` (in `Blanc/CommonProofs.lean`) are exact
  world equalities: a zero credit, zero debit, or current-balance rewrite at a
  `State.Protected` owner returns the identical raw world. Their tree step is
  `treeMap_insert_same` (over `treeMapImpl_insert_same`), an exact structural
  identity for inserting a key at its current value, not map extensionality.
  Without protection the zero write can normalize an empty account to absent
  and erase its storage, so the premise is necessary.
- `State.Protected.of_compile` (an account carrying `Prog.compile p` is
  protected) sits beside `State.Protected.of_image` and `.of_code_ne_nil` in
  `Blanc/CommonProofs.lean`. `selfPayment_entry_clears_storage` is the
  mechanism that makes protection necessary across message entry: a
  full-balance self-payment empties a codeless, nonce-zero account, and the entry
  deletes it with its storage.
- `Acct.clearIfEmpty_of_not_empty`, `Acct.clearIfEmpty_withBal_of_code`,
  `Acct.clearIfEmpty_withBal_of_nonce` (with `Acct.withBal_nonce`/`_code`) in
  `Blanc/CommonProofs.lean` remove the normalization of a nonempty account or
  of a balance write at a coded or nonce-carrying account. Rewrite with the
  `withBal` forms rather than closing the branch by `exact`: at a concrete
  literal credit the unifier otherwise unfolds word arithmetic.
- `Acct.clearIfEmpty_of_code_toList_ne_nil` (in `Blanc/CommonProofs.lean`) is
  the account-level form: `setAccount` normalization is the identity on an
  account whose code is a nonempty byte list, so a code installation followed
  by `State.setAccount_get_self` returns the written account exactly. Jaune's
  `Acct.clearIfEmpty_bal`, `_nonce`, `_code`, and `_stor` project single fields
  without any premise.

### S3. I need state-relation or write-frame composition

Use `Devm.StateWriteFrame` and its reflexive/transitive/composition lemmas in
`Blanc/CommonProofs.lean`, then inspect higher-level relation combinators in
[`Blanc/LadderBase.lean`](../Blanc/LadderBase.lean).

If the fact is about which holder's balance moved rather than how states
compose, continue to S5.

### S4. I need to separate upgrade migration from behavioral refinement

Use [`Blanc/Upgrade.lean`](../Blanc/Upgrade.lean). `UpgradeArchitecture`
records all five identifying objects explicitly: the proxy program, v1, v2,
the state migration, and the pre/post relation. `MigrationSound` says that the
named migration reaches the v2 domain and establishes the relation;
`BehavioralRefinement` separately says that admitted shared inputs have equal
observations and preserve the relation. Neither predicate says that a proxy
transaction realizes the migration, and neither may be used as evidence for
the other.

Keep `proxyProg` an explicit value through product corollaries. Instantiate
the vocabulary in the contract family that owns the concrete programs,
storage projection, execution route, and relation. For the worked exact
OssifiableProxy instance, see
[`docs/PROXY_PAIR_UPGRADE.md`](PROXY_PAIR_UPGRADE.md).

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
  that separately (`Stor.rest_set_supplySlot`, `Stor.rest_set_prorataSupplySlot`)
  because the slot is the contract's own.
- When the credit itself is unchecked and may wrap, use
  [`Blanc/BalanceAlgebra.lean`](../Blanc/BalanceAlgebra.lean) rather than
  assuming `B256.Nof`: `B256.toNat_add_le` bounds a wrapped sum by the
  mathematical one, `sumBelow_increase_le` and `sum_increase_le` bound the
  growth of an address-prefix sum by the value credited including the wrapping
  case, and `transfer_does_not_increase_sum` is the paired-movement form.
  These are upper bounds; they do not establish that no wrap occurred.
- For a *pure* token model whose ledger is a function `Adr → B256` rather
  than storage, use [`Blanc/LedgerUpdate.lean`](../Blanc/LedgerUpdate.lean).
  `ledgerDebit`/`ledgerCredit` are the one-row `Function.update` movements,
  with `_self`/`_ne` read-back lemmas; `ledgerDebit_decrease`,
  `ledgerCredit_increase` and `ledgerDebit_credit_transfer` package them as
  `Decrease`/`Increase`/`Transfer`; `sum_ledgerDebit`, `sum_ledgerCredit` and
  `sum_ledgerDebit_credit` read off the exact `sum` movement under the
  checked-arithmetic guard; `ledgerDebit_credit_nof` shows the credit half of
  a covered transfer cannot wrap when `SumNof` holds (a checked-add revert is
  then dead), and `ledgerDebit_credit_ge_of_ne` says no row other than the
  debited one falls across such a transfer.
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
  To compare two footprint sums row by row, import
  [`Blanc/Lift/LedgerFootprintOrder.lean`](../Blanc/Lift/LedgerFootprintOrder.lean):
  `footprintSum_le_footprintSum` (pointwise growth on the footprint) and
  `footprintSum_lt_footprintSum` (plus one strictly grown footprint row) order
  the sums without a `Nodup` premise; `footprintSum_cons` peels one key.  A
  statement control uses the strict form to show one moved row breaks an
  equation with an unmoved supply.

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

For the natural-number arithmetic of a Babylonian square-root loop, use
[`Blanc/Lift/BabylonianSqrt.lean`](../Blanc/Lift/BabylonianSqrt.lean), namespace
`Blanc.BabylonianSqrt`. `iter_eq_sqrt` reuses the core iterator from any guess
at or above the root; `sourceResult_eq_sqrt` covers the half-plus-one initial
guess and both small-input branches. `body_bounds` supplies positive-divisor,
unchecked-sum and next-candidate bounds for an arbitrary input limit.
`iterCount` and `sourceCount` expose descending/terminal equations and include
the mandatory first body on the large source branch. These are natural-number
result, count and range facts; consumers must still prove their B256 operation,
certified-loop and opcode-charge correspondences.

For a two-reserve AMM's natural-number share bound, use
[`Blanc/Lift/AMMArithmetic.lean`](../Blanc/Lift/AMMArithmetic.lean).
`mintLiquidity` is the minimum of two proportional floors; `burnPayment` is
a proportional redemption floor. `mint_side_bound` and `burn_side_bound`
establish the per-reserve inequalities, and `product_share_bound` transports
two such inequalities to the reserve-product/share-supply bound.
`mint_product_bound` and `burn_product_bound` provide their composed forms;
burn requires initial backing, liquidity covered by supply, and a final answer
plus the floored payout covering the initial answer. `swap_product_bound`
cancels a positive scale from an accepted adjusted product bounded above by
the scaled observed balances. These are unbounded Nat facts; callers supply
word-overflow, source-local/observation and callee-acceptance connections.

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
proves `floorRoot` monotone in each balance (`floorRoot_mono`) and in `ann`
(`floorRoot_mono_ann`) and pins it by one point (`floorRoot_eq`).
[`Blanc/Lift/StableSwapNewton/D.lean`](../Blanc/Lift/StableSwapNewton/D.lean)
bridges the checked `get_D` to the plain one (`getDChk_some`) and proves
`getD_lower` / `floorRoot_le_getD`: for positive balances and `A ≥ 1`, `getD` is
never below `⌊D*⌋`, at every tolerance, stopped or capped; it also holds the cap,
non-monotonicity and ceil-mutation witnesses.
[`Blanc/Lift/StableSwapNewton/Fuel.lean`](../Blanc/Lift/StableSwapNewton/Fuel.lean)
identifies the checked loops with the neutral fuel loop
(`loopDChk_eq_fuelLoop`, `loopYChk_eq_fuelLoop`), so the `FuelLoopWalk`
bridges apply to their compiled heads.
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
wrapping products, and `B256.not_lt_of_ltCheck_eq_zero` turns a zero unsigned
comparison flag into the negated strict comparison. The latter does not
assert that arithmetic producing either operand was overflow-free. Import
this owner directly; CommonProofs and Ladder do not reexport it.
For the converse direction, a comparison flag discharged from values,
[`Blanc/B256CheckFacts.lean`](../Blanc/B256CheckFacts.lean) has
`B256.gtCheck_eq_zero_of_toNat_le` (`GT` is `0` when the left operand's
value is at most the right's), the step a walk needs at a solc range check.
For a logical shift right that never grows its shifted operand, use
`B256.shr_toNat_le` in
[`Blanc/Lift/FreePtrFacts.lean`](../Blanc/Lift/FreePtrFacts.lean).

Use the fixed-width arithmetic declarations in
[`Blanc/WordArithmetic.lean`](../Blanc/WordArithmetic.lean) and the basic word
identities in [`Blanc/CommonProofs.lean`](../Blanc/CommonProofs.lean) before
destructing a `B256` (`B256.or_comm` and `B256.or_zero` are in
[`Blanc/AddressSlotProofs.lean`](../Blanc/AddressSlotProofs.lean)). `wordModulusN`, `maxWordN`, `wordModulusN_pos`,
`maxWordN_lt_wordModulusN`, and `maxWord_toNat` name the standard `2^256`
bounds. `div_two_div_pow`, `div_pow_div_two`,
`one_and_toB256_eq_mod_two`, and `toB256_shiftRight_one` bridge recurring
natural-number calculations to exact word operations. `Nat.xor_or_shiftLeft`,
`B128.toNat_xor`, and `B256.toNat_xor` expose `xor`, while
`Nat.or_or_shiftLeft`, `B128.toNat_or`, and `B256.toNat_or` expose `or`
through the nested word representation. In `CommonProofs`,
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
require no timestamp ordering. The immediate consumers are the deployed
Pair's UQ112x112 arithmetic and uint32 elapsed-time bridge. Discovery remains
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

For the pause face specifically, `pauseInfiniteSentinel`, `pauseForProjection`,
and `compact_pause_word_eq_projection` in
[`Blanc/PinnedPauseTarget.lean`](../Blanc/PinnedPauseTarget.lean) name the
sentinel and identify the branch-free compiled pause word
`time * ((sentinel =? duration) =? 0) + duration` with its source projection.
Every faithful `PausableUntil` port compiles that arithmetic, so consume these
shared declarations rather than restating them per family.

At the settled account boundary, use `acceptedBoolWord_iff_of_output` to turn
a clean full-word output equation into `AcceptedBoolWord`,
`acceptedBoolExecution_ok_iff` to remove an `.ok` execution wrapper, and
`boolQueryExecutionFailure_ok_iff` for the corresponding rejected-answer
predicate.  These adapters live beside the protocol in
[`Blanc/PinnedPauseTarget.lean`](../Blanc/PinnedPauseTarget.lean); do not
repeat their byte-slice normalization in a contract family.

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
names a contract; `Blanc/Conserved.lean` proves the same algebra for fmint's
own supply slot and predates this module.

A ledger keyed by *hashed* slots (a Solidity or Vyper mapping) cannot claim "every key's slot holds
its value": two keys may share a slot, and a history touches a tiny fraction of the key space.  State
the ledger over a set `K` of **tracked keys** instead, with
[`Blanc/SlotFootprint.lean`](../Blanc/SlotFootprint.lean): `Support` (every nonzero word is at a fixed
slot or a tracked key's slot), `Inj`/`Apart` (tracked slots pairwise distinct and off the fixed slots),
`Fresh`/`FreshKeys`/`extendBy` (a frame's or trace's touched keys are tracked or on slots in no use, and
extend the footprint), `Support.get_eq_zero`/`Support.set`/`Inj.extend`/`Apart.extend`, and
`FreshKeys.of_universe`, which turns injectivity and apartness of one *trace-fixed universe* into the
freshness of every touched key. `extendBy_subset` in
[`Blanc/SlotFootprintSubset.lean`](../Blanc/SlotFootprintSubset.lean) preserves inclusion
in the same universe when both the old footprint and the added key list lie in it.
The key type, its slot function and the fixed slots are parameters.
When a later frame's keys are stated fresh against the universe itself (not held by it),
[`Blanc/SlotFootprintRestrict.lean`](../Blanc/SlotFootprintRestrict.lean)'s `FreshKeys.restrict`
carries that freshness to every tracked subset of the universe (worked use: the Uniswap V2 pair's
`pair_history_writer_live` in `Blanc/Lift/UniswapV2Pair/PairHistoryLive.lean`).
For an explicit query list and write list, `checkFaithfulOn slot observed written`
checks that a written key shares its raw slot only with itself among the requested
observations; `checkFaithfulOn_eq_true` gives its exact finite soundness statement.
`checkApartOn slot observed foreign` and `checkApartOn_eq_true` check raw foreign
slots against those same explicit observations. These require neither a
`Support` premise nor zero values for keys outside the observation list.
WETH9's `Blanc/Lift/Weth9/Footprint.lean` is the first consumer (with `tracked`/`trackedSum` over
`sum`); Curve's `Layout.lean` keeps its own copy of the same notions.
To read a footprint ledger off raw storage words, use [`Blanc/SlotFootprintWord.lean`](../Blanc/SlotFootprintWord.lean):
`trackedWord slot K s k` is the word at a tracked key's slot and `0` at an untracked key
(`trackedWord_of_mem`, `trackedWord_of_not`); a write at a tracked key's slot is that key's row
update under `Inj` (`trackedWord_set`), a write at a slot no tracked key uses leaves every row alone
(`trackedWord_set_off`), touching fresh keys leaves the rows alone (`trackedWord_extend`), and
`Support.set_fixed` is `Support.set` for a write at a fixed slot. Worked use: USDC's footprint
(`Blanc/Lift/Usdc/Footprint.lean`).

For old USDC blacklist writes, use `HistoricalMappingKey` in
[`Blanc/Lift/Usdc/HistoricalMappingKeys.lean`](../Blanc/Lift/Usdc/HistoricalMappingKeys.lean).
It embeds modern keys unchanged and adds the historical mapping at slot 3.
[`Blanc/Lift/Usdc/V1MappingTouches.lean`](../Blanc/Lift/Usdc/V1MappingTouches.lean)'s
`actualV1OldBlacklistKeys` collects actual successful writes from the same
history, retaining order and duplicates. Its soundness theorem derives their
slot identities from the checked V1 write sites. The off-implementation-slot
consumer requires initial apartness and freshness of this exact list; modern
balance-slot freshness does not establish historical blacklist freshness.
`ConfiguredHistoryTraceIn.actualV1OldBlacklistKeys_hash` additionally retains
the original frame, actual successful base-3 hash, its exact 64-byte
calldata-account/base input, and its successful edge before the same store.
`V1BlacklistReach.successfulSstore_hash` supplies this witness by following
both original selectors through the blacklister guard and packed Boolean
update; no final-call success or hash-injectivity premise is needed. The
existing key-only interfaces project this stronger source proof.

`ConfiguredHistoryTraceIn.v1Initializer_write_ne_implSlot` applies the concrete
initializer range proof directly to actual raw-history stores. Fresh stack and
memory, the entry gas bound and the no-state-gas capability come from the
history's own raw-frame admission; the bound includes old-tail clearing stores.
`V1WriteFamilies` checks every certified root site and reduces actual V1 stores
to fixed-slot apartness or an initializer/mapping selector. This selects a
source family without classifying mapping rows by digest equality.
`ConfiguredHistoryTraceIn.v1_write_ne_implSlot` in
[`V1WriteApart.lean`](../Blanc/Lift/Usdc/V1WriteApart.lean) closes every family,
including transferFrom. `V1MappingFreshKeys` bundles freshness of the seven
exact actual mapping collectors; initial apartness remains explicit.
The earlier `v1_write_ne_implSlot_or_transferFrom` interface is retained.
[`V1RetainedContext.lean`](../Blanc/Lift/Usdc/V1RetainedContext.lean)'s
`settledRoot_v1_write_ne_implSlot` derives the retained-root premise from
same-history raw membership. `settledRoot_proxyV1_context_of_freshKeys`
then supplies the coupled retained code/slot context, and
`settledRoot_proxyV1_preserves_of_freshKeys` preserves both deletion exclusion
and the exact implementation word at settlement. These consumers retain the
actual root-entry Proxy/V1 code, implementation address, absent retained upgrade
log and initial NoDel premises; they do not yet propagate those entry facts
between successive roots or authenticate a historical creation cut.
`settledRoot_proxyV1_implSlot_eq_of_freshKeys` exposes the cell conclusion
without an incoming NoDel premise. In
[`V1TransactionContinuity.lean`](../Blanc/Lift/Usdc/V1TransactionContinuity.lean),
`v1_transaction_preserves` and `v1_transactions_preserve` derive both installed
entry codes and the implementation word through the actual ordered transaction
sequence. V1's existing installed certificate preserves the implementation
account itself. Initial code/slot, block-created exclusions, exact-list freshness,
same-history root inclusion and absent retained upgrade logs remain explicit;
[`V1HistoryContinuity.lean`](../Blanc/Lift/Usdc/V1HistoryContinuity.lean)'s
`v1_block_preserves` and `v1_history_preserves` extend this to actual block
settlement and configured segments whose rule bits disable system stages.
Withdrawals, rewards and finalization use the existing shared cell transport.
Every retained root's entry control is derived from the segment's initial
control. For genuine transaction boundaries,
[`V1MidHistoryContinuity.lean`](../Blanc/Lift/Usdc/V1MidHistoryContinuity.lean)'s
`v1_tail_preserves` begins at the original `TxSplit.afterBenv`, including a
proxy created by that selected transaction. `v1_mid_preserves` appends actual
later blocks; `v1_before_txSplit_preserves` stops at the original before-trace.
`v1_between_txSplits_preserves` composes these into the exact after-C/before-D
interval, deriving deletion exclusions and every intervening root's entry
control from the initial state. Its conditions exclude the final selected
transaction and its suffix. In
[`V1MainnetContinuity.lean`](../Blanc/Lift/Usdc/V1MainnetContinuity.lean),
`v1_between_txSplits_preserves_mainnet` derives all stage bits from the final
block's actual pre-Cancun timestamp, mainnet selection and accepted-header
chronology. Historical-domain capabilities and absent state gas/BAL are supplied
by their existing theorems. Historical C/D identities, constructor state, the
endpoint timestamp and receipt evidence for absent upgrade logs still require
their own binding. [`V1ReceiptContinuity.lean`](../Blanc/Lift/Usdc/V1ReceiptContinuity.lean)'s
`v1_between_txSplits_preserves_from_receipts` consumes absence of proxy Upgraded
logs from the actual first-block suffix, every actual intermediate receipt, and
the last-block prefix. It derives the retained-root absence needed for the same
V1 continuity conclusion, with no separate per-root absence premise. The first
and last selected transactions stay outside the scan; historical identities,
constructor state and factual receipt-log absence are still caller obligations.
`V1RetainedAllowanceZero`'s `settledRoot_v1_allowanceWrite_nonInc` and
`settledRoot_v1_allowance_zero` reuse the retained Proxy/V1 context to classify
actual stores and preserve a tracked zero row. They require no code restriction
on discarded execution. V1's only caller exception is approve; initializer
stores consume the existing calldata-key separation proof. In
`V1ReceiptAllowanceZero`, `v1_allowance_zero_between_txSplits_from_receipts`
composes these laws with the exact-cut cell fold, deriving zero at the later
before-state from zero at the original after-state. Receipt absence supplies
all root code/slot and deletion facts. Caller exclusion, row separation and the
actual constructor seed remain producer obligations; the final selected
transaction and its settlement are outside this result. These contract-specific
consumers do not add a generic recipe for arbitrary equality goals.
`V1ConstructorReceiptZero`'s
`original_v1_seed_before_cut38_of_constructor_receipt` supplies that zero seed
from the actual successful constructor receipt at index22. It derives proxy
code and the initial implementation word from `OriginalConstructorSeed`, then
returns V1 control and tracked zero rows before the original index38 cut.
[`UniswapV2PairUsdcOriginSeed.lean`](../Blanc/Composition/UniswapV2PairUsdcOriginSeed.lean)'s
`original_pair_allowance_seed_of_constructor_receipt` carries those facts
through the same actual factory transaction using foreign-account preservation.
Its result is the settled after-D state, with no supplied zero-at-C or zero-at-D
hypothesis. It derives the pre-Cancun bound from D's anchored timestamp.
These are internal composition interfaces: actual historical authentication,
initial V1 implementation code, finite separation and genuine pre-D approve
safety remain producer obligations. Caller exclusion is not a new final
assumption and does not follow from R3 or Pair target emptiness.
`original_pair_allowance_seed_of_boundary_blooms` additionally consumes the
original C/D body and bloom identities. The checked literals in
[`Blanc/Lift/Usdc/HistoricalBloomExclusion.lean`](../Blanc/Lift/Usdc/HistoricalBloomExclusion.lean)
exclude USDC logs in both boundary blocks, so this adapter needs Upgraded
absence and the receipt-value Approval alternative only on the intervening
history. The caller-exclusion alternative still covers the whole original interval.
Original receipt success, C sender, initial V1 code and finite separation remain
explicit; these conditional literal identities are not historical adoption.

For V1 `approve`, use
[`Blanc/Lift/Usdc/V1ApproveMappingTouches.lean`](../Blanc/Lift/Usdc/V1ApproveMappingTouches.lean)'s
`actualV1ApproveKeys`. It collects the allowance key of each actual successful
store at the requested target with exact V1 code and the approve selector,
preserving history order and duplicates. The checked V1 site fixes the caller
and calldata spender; the recognizer does not test equality with the written
key. Its separation consumer requires initial apartness and freshness of this
same list. `ConfiguredHistoryTraceIn.actualV1ApproveKeys_hashes` additionally
retains the original frame prefix and both successful nested-mapping hashes,
with exact caller/base-10 and spender/inner-digest inputs before the store.
Its producer in [`Blanc/Lift/Usdc/V1ApproveReach.lean`](../Blanc/Lift/Usdc/V1ApproveReach.lean)
walks the checked dispatcher, guards and body; no final call success or hash
injectivity is assumed. The hash PCs are the actual witnessed PCs, not a
separate fixed-PC classification. Both collectors share `v1_store_site` and
`v1Mapping_site_iff`; selectors with multiple mapping sites still require
finer source attribution.

For V2 `approve`, use
[`Blanc/Lift/Usdc/V2ApproveMappingTouches.lean`](../Blanc/Lift/Usdc/V2ApproveMappingTouches.lean)'s
`actualV2ApproveKeys`. Soundness and completeness cover every successful
selected approve store in the original history's `rawNodes`, retaining order
and duplicates. The recognizer tests target, exact code, selector and store
success. [`Blanc/Lift/Usdc/V2ApproveReach.lean`](../Blanc/Lift/Usdc/V2ApproveReach.lean)'s
`successfulSstore_ordered_hashes` derives its caller/spender nested slot10 key
and the shared `KeccakPairBefore` witnesses from the same original frame
prefix, without final-frame success, descriptor separation or hash injectivity.
The off-implementation-slot consumer keeps initial apartness and freshness of
this exact collected list explicit.

For `approve`, `increaseAllowance` and `decreaseAllowance` in all three modern
runtimes, use
[`Blanc/Lift/Usdc/ModernCallerMappingTouches.lean`](../Blanc/Lift/Usdc/ModernCallerMappingTouches.lean).
`ModernVersion` selects the exact existing code, certificate, annotations and
selector table. `modernCaller_store_key` obtains the caller/calldata-spender
slot-10 key from the certified site of the original successful store.
`actualModernCallerKeys` filters the original `rawNodes` by target, exact code,
caller selector and successful store, preserving order and duplicates. Its
soundness/completeness theorems retain the actual root and store; recognition
does not compare the written key. Under `checkFaithfulOn` for the exact
observed Pair/spender list and this collected list, `modernCaller_write_source`
derives the Pair caller and exact spender, and `modernCaller_write_allowed`
supplies the existing `AllowedFrame` caller arm. Check truth remains an
explicit premise. For successful hash-occurrence provenance, use
[`ModernCallerReach`](../Blanc/Lift/Usdc/ModernCallerReach.lean) and its
[`ModernCallerHashBodies`](../Blanc/Lift/Usdc/ModernCallerHashBodies.lean)
inner-path lemmas. `successfulSstore_ordered_hashes` follows the original
dispatcher, ABI decoder and guards in every version/method combination. It
produces `KeccakPairBefore` for caller/base-10 followed by masked-spender/inner
digest before the same successful store. The history adapters
`modernCallerKey?_ordered_hashes` and `actualModernCallerKeys_ordered_hashes`
retain the original root, node, written key and both successful hashes for
the unchanged collector. The existing V2 approve witness is preserved.
Other modern selectors and the full classifier remain outside this family.

For exhaustive modern successful-store coverage, use
[`ModernWriteFamilies`](../Blanc/Lift/Usdc/ModernWriteFamilies.lean).
`modern_store_fixed_nonInc_or_family` applies the unchanged certified root
tables to the actual store: its key is a listed literal slot, its value is
non-increasing at that same node, or its original selector is in a listed
version-specific family. `actualModernCoveredKeys` concatenates the actual V2 transfer keys, increasing
older-transferFrom credits, exact configure/mint family, cancellation and caller
collectors and the applicable blacklist collector: old base-3 keys for V2/V2_1 and packed balance keys for V2_2;
soundness retains the original root, node, successful store, owner and key.
Under finite faithfulness for that exact list and apartness from
`modernFixedWriteSlots`, `modern_allowance_write_reduction` eliminates fixed,
cancellation, blacklist and established configure/mint aliases and attributes caller writes,
leaving existing allowed exceptions, actual
nonincrease, owner selectors or `modernOtherWriteSelectors`. This is a
reduction toward the full classifier; the owner and remaining mapping cases
and check truth stay open. Both V2_2 packed-blacklist selectors are discharged;
`initializeV2_1` is not promoted to an allowed exception.

For `cancelAuthorization` in all three modern versions, including both V2_2
overloads, use
[`ModernCancelMappingTouches`](../Blanc/Lift/Usdc/ModernCancelMappingTouches.lean).
`modernCancel_store_key` obtains the authorization-state key at base slot 16
from the original successful store: masked calldata owner at word 4 and the
full nonce at word 36. `actualModernCancelKeys` filters original `rawNodes`
by target, exact runtime, cancellation selector and successful store, without
testing the written key. Completeness and soundness retain the original root,
node and actual write. `modernCancel_write_ne_allowSlot` consumes finite
faithfulness for exactly this list; its key constructors distinguish an
authorization entry from an allowance entry. Cancellation selectors are now
discharged by the exhaustive family reduction. Finite-check truth remains
an explicit obligation.

[`ModernCancelReach`](../Blanc/Lift/Usdc/ModernCancelReach.lean) supplies the
original ordered successful hashes for all four cancellation routes.
`successfulSstore_ordered_hashes` follows the original entry, dispatcher,
ABI decoding and pause guard into the unused-authorization check. The first
hash consumes the masked calldata owner with base slot 16; the second consumes
the full calldata nonce with that first result. Both occur before the same
successful store, with no final-frame-success or signature-result premise.
The history adapters `modernCancelKey?_ordered_hashes` and
`actualModernCancelKeys_ordered_hashes` retain the original root, raw node,
write owner and exact key from the unchanged collector. This proves occurrence
and order within that prefix, without assuming hash injectivity or changing
the finite population.

[`ModernRemoveMinterReach`](../Blanc/Lift/Usdc/ModernRemoveMinterReach.lean)
proves `successfulSstore_nonInc` for every actual removeMinter store in
V2, V2_1 and V2_2. The original dispatcher, ABI bounds and master-minter
guard lead to a masked same-key reload or a literal-zero store. Each value
is bounded by that same node's current cell, including when earlier writes
alias it. `modernRemoveMinter_nonInc` supplies the raw-history adapter.
`modern_allowance_write_reduction` in `ModernWriteFamilies` consumes this result
directly, removing selector 0x3092afd5 from the unresolved families without
adding hash-separation premises or changing the actual-key population.

For the balance-writing suffixes of modern burn, use
[`ModernBurnStores`](../Blanc/Lift/Usdc/ModernBurnStores.lean).
`caller_key_hash` covers V2 and V2_1's final caller-balance writer;
`packed_setBalance_key_hash` covers V2_2's shared setBalance helper,
including its cap, blacklist query and original internal return.
Each retains the actual base-9 key and successful `ObservedKeccak` before
that store under the original edge observation, without final-frame success
or hash-separation premises. These are suffix producers; they do not alone
establish an original-entry or history theorem. The complete nonincrease route
below avoids needing a separate burn key collector.

For complete original-entry V2_2 burn nonincrease, use
[`V22BurnNonIncBodies`](../Blanc/Lift/Usdc/V22BurnNonIncBodies.lean) and
[`V22BurnNonIncReach`](../Blanc/Lift/Usdc/V22BurnNonIncReach.lean).
`successfulSstore_nonInc` follows the original dispatcher, ABI and role checks,
actual balance/supply reads and checked subtractions. Each actual write is
bounded by its own node's pre-state word. If the supply slot and balance hash
coincide, the masked balance bound and monotone subtraction still discharge
the second store after the first. No key-separation or final-frame-success
premise is needed. `ConfiguredHistoryTraceIn.v22Burn_nonInc` supplies the
raw-history adapter.

For V2 and V2_1, use
[`OldBurnNonIncCallees`](../Blanc/Lift/Usdc/OldBurnNonIncCallees.lean) and
[`OldBurnNonIncBodies`](../Blanc/Lift/Usdc/OldBurnNonIncBodies.lean).
The actual returning subtraction helpers preserve the storage base while
changing scratch memory, and their guards prove the nonwrapping bound.
The caller-balance read and exact first-store effect discharge both
same-node bounds, including when its hash equals the supply slot.
[`ModernBurnNonIncReach`](../Blanc/Lift/Usdc/ModernBurnNonIncReach.lean)
combines all three original dispatchers and body proofs in
`successfulSstore_nonInc`. `ConfiguredHistoryTraceIn.modernBurn_nonInc`
connects this to actual raw-history nodes. The full
`modern_allowance_write_reduction` consumes this theorem directly, removing
burn from every modern residual selector list without a new collector,
hash-separation premise or change to the finite actual-key populations.
No final-frame-success or additional covered-fork premise is introduced.

For V2_2 packed-blacklist updates, use
[`V22BlacklistReach`](../Blanc/Lift/Usdc/V22BlacklistReach.lean) and
[`V22BlacklistMappingTouches`](../Blanc/Lift/Usdc/V22BlacklistMappingTouches.lean).
`successfulSstore_key_hash` follows the original dispatcher, public ABI,
blacklister guard and both flag-update branches to the shared packed-word
store. It proves the actual written key is the masked calldata address's
base-9 balance slot and retains a successful `KeccakBefore` in that same
original prefix, with no final-frame-success or hash-separation premise.
`actualV22BlacklistKeys` collects one logical balance key per original
matching successful store, preserving order and duplicates without testing
the written digest. Its soundness carries the original root, node, owner,
exact key and hash; completeness covers both selectors. Finite faithfulness
for that exact population lets `v22Blacklist_write_ne_allowSlot` exclude
these writes from protected allowance rows. The full modern family
reduction consumes this collector alongside the unchanged older collectors.

For V2 and V2_1 old-blacklist writes, use
[`Blanc/Lift/Usdc/V2BlacklistMappingTouches.lean`](../Blanc/Lift/Usdc/V2BlacklistMappingTouches.lean)'s
`actualV2OldBlacklistKeys` with its explicit version. The certificate and
same original prefix derive the masked calldata address at slot 3. The
collector selects actual successful blacklist/unblacklist stores, preserving
raw-node order and duplicates, with soundness and completeness.
`v2OldBlacklist_write_ne_allowSlot` consumes the exact finite
observed-versus-collected-key check; its truth remains an explicit obligation.
For successful hash provenance, import
[`Blanc/Lift/Usdc/V2BlacklistReach.lean`](../Blanc/Lift/Usdc/V2BlacklistReach.lean).
Its `successfulSstore_hash` follows the original dispatcher, ABI wrapper, role
guard and memory writes in either version. The exact masked address/base-3
input is hashed successfully before the same store. The history adapters
`v2OldBlacklistKey?_hash` and `actualV2OldBlacklistKeys_hash` retain that
original root, prefix, actual store and key equality for the unchanged
collector. Final-frame success, hash injectivity and finite-check truth are
not required to obtain these witnesses. Initializer writes are outside this
two-selector collector.

[`V2TransferFromCallee`](../Blanc/Lift/Usdc/V2TransferFromCallee.lean)
reuses the existing V2 transfer-body proof with an arbitrary original caller
continuation. It derives the exact balance-store/hash alternative or a return
along that same observed path. Its `subtraction_return` reuses the existing
checked subtraction return theorem, deriving the actual bound and unchanged
storage base while retaining both observed cuts; it assumes no bound or
store-free caller. It does not yet discharge transferFrom's
original dispatcher or allowance continuation.

[`V2TransferFromEntry`](../Blanc/Lift/Usdc/V2TransferFromEntry.lean) derives
that original dispatcher, ABI and public-guard path while retaining the exact
caller stack below the balance helper. Its companion
[`V2TransferFromContinuation`](../Blanc/Lift/Usdc/V2TransferFromContinuation.lean)
uses the checked frame return to recover that stack, then proves the allowance
continuation non-increasing at the same original store. The allowance value is
reloaded after the balance helper, so this bound tolerates balance/allowance
hash aliasing. `successfulSstore_source_or_nonInc` derives either that bound or
the original owner/recipient balance store with its own successful hash from
an actual root prefix. It does not yet exclude the owner branch for the
strictly increasing recipient-key collector; no finite population is widened.

For modern `transferFrom`, use
[`ModernTransferFromSites`](../Blanc/Lift/Usdc/ModernTransferFromSites.lean)
to reuse the unchanged root certificates at the same original successful store.
`modernTransferFrom_store_nonInc_or_balance` derives nonincrease, the recipient
balance key, or (only in V2.2) the sender balance key. V2/V2.1 sender debits and
all three allowance writes already have certified nonincrease.
[`OldTransferFromMappingTouches`](../Blanc/Lift/Usdc/OldTransferFromMappingTouches.lean)
collects only actual increasing V2/V2.1 writes by testing the actual pre-word
and written value, without comparing a key to a proposed digest. Soundness
identifies the exact recipient key at that original store; completeness proves
all omitted selected writes non-increasing. `ModernWriteFamilies` adds this
exact list to its finite faithful check and discharges the two older transferFrom
cases. V2.2 transferFrom remains explicit. Original successful hash occurrences
for this new collector remain a separate producer obligation; certificate key
denotation alone does not provide them or prove finite-check truth.

The V2 transfer and V2.1 mint producers are also consumed by
`ModernWriteFamilies`: only these version/selector cases leave its residual
list. The existing finite faithful/apart checks use their exact actual-key
collections; original hash witnesses remain in the producer interfaces.

For the combined configure/mint family, use
[`ModernMinterFamilies`](../Blanc/Lift/Usdc/ModernMinterFamilies.lean).
`actualModernMinterKeys` selects the version's actual configureMinter keys and,
for V2/V2.1, its actual mint keys. `modernMinter_write_source` derives either
literal supply slot 11 or a collected logical key distinct from every allowance
key. It assumes no hash separation. `ModernWriteFamilies` includes this exact
list in `actualModernCoveredKeys`; its existing finite faithful/apart checks
then eliminate all three configureMinter selectors and V2/V2.1 mint from the residual
families. V2.2 mint remains explicit. No AllowedFrame exception,
spender population, or global hash-injectivity premise is added.

For V2 `configureMinter`, use
[`Blanc/Lift/Usdc/V2ConfigureMinterMappingTouches.lean`](../Blanc/Lift/Usdc/V2ConfigureMinterMappingTouches.lean)'s
`actualV2ConfigureMinterKeys`. The collector preserves the original history's
order and duplicates. Its completeness theorem derives the reached store site
for every selected successful store; recognition never compares the written key
with a proposed hash. `V2ConfigureMinterReach.successfulSstore_source` derives
the minter flag at base 12 or allowance at base 13, retaining that store's own
successful original hash strictly before it. No final-frame success or hash
injectivity is required. Initial apartness and freshness of this exact list
remain explicit in the implementation-slot separation consumer.

V2.1 uses
[`Blanc/Lift/Usdc/V2_1ConfigureMinterMappingTouches.lean`](../Blanc/Lift/Usdc/V2_1ConfigureMinterMappingTouches.lean)'s
`actualV2_1ConfigureMinterKeys` with the same exact-history guarantees.
`V2_1ConfigureMinterReach` proves its own dispatcher, ABI, guard and source-PC
coverage. It reuses `V2ConfigureMinterReach.body_reach_observed`, generalized
over the surrounding program, because the two concrete body trees are
definitionally equal. The existing V2 body walk and store-tail definitions
remain the single owners; each runtime has its own source-location proof.

V2.2 uses
[`Blanc/Lift/Usdc/V22ConfigureMinterMappingTouches.lean`](../Blanc/Lift/Usdc/V22ConfigureMinterMappingTouches.lean)'s
`actualV22ConfigureMinterKeys` for the same exact-history interface.
`V22ConfigureMinterReach` proves the route and source locations in `Impl.code`,
then reuses the identical V2 body without another generalization. Each collected
row retains its own original successful hash before that actual store.

For V2 `mint`, use
[`Blanc/Lift/Usdc/V2MintMappingTouches.lean`](../Blanc/Lift/Usdc/V2MintMappingTouches.lean)'s
`actualV2MintKeys`. The actual-store completeness theorem classifies the literal
total-supply write at slot 11 separately, deriving its exclusion from the
mapping collector. The recipient balance at base 9 and caller minter allowance
at base 13 retain their own successful original hashes before their stores.
`V2MintReach.successfulSstore_source` traverses the checked dispatcher, guards
and arithmetic returns; its subtraction bound comes from the actual earlier
mint guard. Recognition tests source PCs and actual store success, never a
proposed key digest. Order, duplicates and original history membership remain
explicit, as do initial apartness and freshness for slot separation.

For V2 `transfer`, use
[`Blanc/Lift/Usdc/V2TransferMappingTouches.lean`](../Blanc/Lift/Usdc/V2TransferMappingTouches.lean)'s
`actualV2TransferKeys`. Original entry coverage derives the caller and recipient
base9 balance stores, each with its own earlier successful hash. The actual
balance guard supplies the subtraction bound through the unchanged storage
read; the source theorem adds no bound premise. The collector preserves raw-node
order and duplicates and derives source sites without testing proposed hashes.

For V2.1 mint, use
[`Blanc/Lift/Usdc/V2_1MintMappingTouches.lean`](../Blanc/Lift/Usdc/V2_1MintMappingTouches.lean)'s
`actualV2_1MintKeys`. Original entry coverage derives supply at `0x1fd6`,
recipient balance at `0x202c`, and caller minter allowance at `0x204d`.
The mapping collector preserves raw-node order and duplicates, excludes the
literal supply store, and retains each mapping store's own successful earlier
hash in the same history. The arithmetic bound comes from the original mint
guard. `V2_1MintReach` follows its own ABI and arithmetic helper paths;
`V2MintReach.minter_store_reach_observed` shares only the identical final store
tail over an arbitrary surrounding program. `ObservedSourceFor` shares the
three-way classification with the version-specific balance tail as a parameter.
The existing V2 interface remains
available. Separation consumes freshness for exactly this collected list.

For V1 `burn`, use
[`Blanc/Lift/Usdc/V1BurnMappingTouches.lean`](../Blanc/Lift/Usdc/V1BurnMappingTouches.lean)'s
`actualV1BurnBalanceKeys`. The recognizer selects actual successful balance
stores at 0x1f27, preserving history order and duplicates without comparing
the digest. `V1BurnReach.successfulSstore_source` follows the checked selector,
guards and two subtraction returns, classifying the supply store at 0x1ed1
separately from the caller's base-9 balance write. The balance arm retains
the successful hash at 0x1f24 and its exact caller/base input before that store;
the earlier supply-store arm requires no later hash. The history soundness
and completeness theorems bind this exact collector, and implementation-slot
separation requires its explicit initial apartness and freshness. No final
call success or hash injectivity is assumed.

For V1 `mint`, use
[`Blanc/Lift/Usdc/V1MintMappingTouches.lean`](../Blanc/Lift/Usdc/V1MintMappingTouches.lean)'s
`actualV1MintKeys`. Its two recognized source PCs select the calldata recipient's
base-9 balance row and the caller's base-13 minter-allowance row. The actual
prefix producer `V1MintReach.successfulSstore_source` separates the supply
write at 0x1bcc, balance write at 0x1c61 and allowance write at 0x1cb7; the
mapping arms retain the successful hash at 0x1c5e or 0x1cb4, respectively.
Each earlier write requires no later hash or final call success. The collector
preserves actual history order and duplicates, never compares the written digest,
and has same-history soundness, completeness and explicit exact-list freshness
consumers for implementation-slot separation.

For V1 ordinary transfers, use
[`Blanc/Lift/Usdc/V1TransferMappingTouches.lean`](../Blanc/Lift/Usdc/V1TransferMappingTouches.lean)'s
`actualV1TransferKeys`. It selects both actual successful balance writes by
selector and source PC, preserving raw-history order and duplicates without
recognizing a digest. `V1TransferReach.successfulSstore_source` proves the
caller and calldata-recipient keys and each successful 64-byte hash on the
same original prefix, including early writes before a later failure.
`ConfiguredHistoryTraceIn.actualV1TransferKeys_sound` retains both occurrences,
their actual frame, and their prefix order; `mem_actualV1TransferKeys_of_site`
is complete for either site. `v1Transfer_write_ne_implSlot` uses freshness of
exactly that collected list and an explicitly separated initial footprint.

For V1 transferFrom, use
[`Blanc/Lift/Usdc/V1TransferFromMappingTouches.lean`](../Blanc/Lift/Usdc/V1TransferFromMappingTouches.lean)'s
`actualV1TransferFromKeys`. Its exact `filterMap` recognizes target, code,
selector, source pc and successful SSTORE, never the written digest. It covers
the calldata owner's balance, recipient's balance and owner/caller allowance.
`V1TransferFromReach.successfulSstore_source` supplies each computed key and
successful own-prefix hash, plus the allowance's linked inner→outer→store
chronology. Its early balance-store alternatives need no later hash or call
success. `ConfiguredHistoryTraceIn.actualV1TransferFromKeys_sound` retains the
original frame, store and hash in the same history;
`v1TransferFrom_allowance_ordered_hashes` exposes both original nested hash
witnesses and their order. `mem_actualV1TransferFromKeys_of_successfulSstore`
collects every selected successful row, while
`v1TransferFrom_successfulSstore_ne_implSlot` derives separation directly from
initial apartness and freshness of exactly this producer list. No key
injectivity, final-state invariant or never-signer premise is inferred.

For the actual V1 transferFrom allowance value, use
[`Blanc/Lift/Usdc/V1TransferFromNonInc.lean`](../Blanc/Lift/Usdc/V1TransferFromNonInc.lean)'s
`allowanceStore_nonInc`: at pc 0x14e2, a successful store writes no more than
that same node's current cell under the original raw `ParentPrefix`.
`successfulSstore_source` retains both balance-site alternatives and reuses the
existing mapping-key and ordered-hash witnesses, adding the bound only to the
allowance alternative. The proof follows the allowance reload after both
balance writes and the checked subtraction; it needs no row separation or
final-frame outcome. Its focused body walk is
[`Blanc/Lift/Usdc/V1TransferFromNonIncReach.lean`](../Blanc/Lift/Usdc/V1TransferFromNonIncReach.lean).

For V1 `removeMinter` and `configureMinter`, use
[`Blanc/Lift/Usdc/V1MinterMappingTouches.lean`](../Blanc/Lift/Usdc/V1MinterMappingTouches.lean)'s
`actualV1MinterKeys`. It recognizes each of the four successful store PCs
separately, preserving order and duplicates without testing the written digest.
`ConfiguredHistoryTraceIn.actualV1MinterKeys_sound` retains the original store
and its successful earlier hash, exact input, and membership in the same
history. The first store requires no later hash or final call success.
`mem_actualV1MinterKeys_of_site` collects every matching actual row;
`ConfiguredHistoryTraceIn.v1Minter_write_ne_implSlot` requires initial apartness
and freshness of exactly this list. It reuses the modern minter and minter
allowance keys without changing the modern collectors.

To establish such a footprint at a concrete checkpoint world, decide it with
[`Blanc/Lift/FiniteCheckpoint.lean`](../Blanc/Lift/FiniteCheckpoint.lean): for a finite row list
`rows : List (κ × B256)` (each key with its precomputed slot word; the tracked set is `rowKeys rows`),
`checkRows slot fixed rows s` checks that every word is its key's slot, the words ascend strictly
(`ascending`, so distinct), no word is a fixed slot, and every nonzero entry of the storage tree is a
fixed slot or a listed word (`covered`, a merge walk); `checkRows_sound` turns `true` into
`RowsSound` (`Support`, `Inj`, `Apart`). `checkSumNof w` decides `SumNof w.bal` by summing the
world's actual accounts (`sum_bal_eq_worldBalSum`, `checkSumNof_sound`). Worked uses:
`Blanc/Lift/Weth9/FiniteFootprint.lean` and `Blanc/Lift/UniswapV2Pair/FiniteCheckpoint.lean`.

For what a token's **address** answers along a configured history, with no storage layout, use the
token interface core in [`Blanc/Lift/Token/Core.lean`](../Blanc/Lift/Token/Core.lean): a pure `Book`
(ledger, step per entered frame, decoded `Op`, balances, allowances, well-formedness), the `BookLaws`
a composition consumes, and `Core T B`, which ties a book to the settled frames of a history
(`IsEntry`, `replayAt`, `replayEnd`, the `balanceOf`/`transfer` answers), with the facet
`TransferLive`. [`Blanc/Lift/Token/Holder.lean`](../Blanc/Lift/Token/Holder.lean) gives
`Book.run_append`, `entryAsks_append`, the holder argument `BookLaws.run_holder` and the positional
segment `Core.segment`; [`Blanc/Lift/Token/Along.lean`](../Blanc/Lift/Token/Along.lean) gives
`Core.good_along` (every ledger met along a settled prefix is good) and
`Core.run_holder_segment`. Further facets are separate structures in their own files:
`Erc20Abi` ([`Blanc/Lift/Token/Abi.lean`](../Blanc/Lift/Token/Abi.lean)) and `SelfCaller`
([`Blanc/Lift/Token/SelfCaller.lean`](../Blanc/Lift/Token/SelfCaller.lean)). Worked instance:
WETH9 (`Blanc/Composition/Weth9TokenCore.lean`, `weth9Core`).
For a token with a privileged minter, the minter/supply facet `SupplyFacet B`
([`Blanc/Lift/Token/Supply.lean`](../Blanc/Lift/Token/Supply.lean)) reads a book's supply and minter
and classifies mint and burn messages (zero amounts included); `SupplyFacet.run_supply` says that
along an accepted run whose minter-sent messages keep the minter (`KeepsMinter`), the minter persists
and the final supply plus `burned` equals the initial supply plus `minted`; `SupplyFacet.run_keep`
says that a run none of whose messages the minter sends keeps supply and minter. Worked instance: 3Crv
(`Blanc/Composition/Curve3CrvTokenCore.lean`, `c3crvSupply`, `c3crv_history_supply`), composed with
the Curve 3pool over one history in `Blanc/Composition/Curve3PoolSupply.lean` (`pool_3crv_history`).
The Uniswap V2 pair's composition with any token given by such a core is generic:
`pair_token_joint` and `pair_token_noShrinkSide` (`Blanc/Composition/PairTokenJoint.lean`) and the
share-value rows `pair_token_feeOff_product`/`pair_token_feeOn_product`
(`Blanc/Composition/PairTokenShareValue.lean`) take `Core T B` and `BookLaws B` as arguments;
`Blanc/Composition/UniswapV2PairWeth9Joint.lean` instantiates them at WETH9.

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
a plain book as a signature book with no signer (`weth9Book_lawsS`,
`Blanc/Composition/Weth9TokenSigned.lean`). [`Blanc/Lift/Token/SignedControl.lean`](../Blanc/Lift/Token/SignedControl.lean) is the
kernel counterexample showing that `NeverSigner` is needed (`control_signer_breaks_holder`). The
transfer-liveness facet conditioned on a gas budget rather than on the consumed cost plus the
stipend (a proxy forwards only 63/64 of its gas) is `TransferLiveBudget` in
[`Blanc/Lift/Token/TransferLiveBudget.lean`](../Blanc/Lift/Token/TransferLiveBudget.lean), with `TransferLive.toBudget` (worked use:
`Blanc/Composition/UsdcTokenLive.lean`).

The generic Pair headlines over these: `pair_token_joint_signed` and
`pair_token_noShrinkSide_signed` ([`Blanc/Composition/PairTokenSigned.lean`](../Blanc/Composition/PairTokenSigned.lean)) take `BookLawsS`
and `NeverSigner`; `pair_two_token_joint` ([`Blanc/Composition/PairTwoToken.lean`](../Blanc/Composition/PairTwoToken.lean)) runs the
walk once per core over the same Pair steps for a Pair whose `token0` and `token1` are `CoreW`
instances with holder laws for the Pair, so one Pair witness carries both joint relations and the
two sides combine through `sourceReplayNoShrink_iff_sides`; `pair_two_token_feeOn_product` and
`pair_two_token_feeOff_product` ([`Blanc/Composition/PairTwoTokenShareValue.lean`](../Blanc/Composition/PairTwoTokenShareValue.lean)) are the
share-value rows with no token antecedent (the fee-off row keeps only the factory's fee-off answer
`sourceReplayFeeOff`).

### S8. I need Nat-level PRORATA pricing, accounting effects, or coalition-attack bounds

Four modules carry the offset-priced proportional economics both PRORATA
families share.  [`Blanc/OffsetPricing.lean`](../Blanc/OffsetPricing.lean)
owns the virtual-offset arithmetic: `mintN`/`payN` price deposits and
withdrawals, `mintN_never_overmints`/`payN_never_overpays` floor both in the
ledger's favor, `depositResidueN`/`withdrawResidueN` name the exact floor
residues, and `deposit_price_nondecreasing`/`withdraw_price_nondecreasing`
say settlement never lowers the cross-multiplied share price.
[`Blanc/ProrataAccounting.lean`](../Blanc/ProrataAccounting.lean) classifies
one semantic step: `AccountingSnapshot` is the observed state,
`ProrataAccountingKind` the four SF-frozen classes, `ProrataAccountingEffect`
the exact state equation per class with `deposit_inv`/`withdraw_inv`/
`externalCredit_inv`/`silent_inv` inversion at a known class, and
`ProrataAccountingPath` chains steps with `snapshotAt`/`XAt`/`DAt`/`rhoAt`/
`kappaAt` projections and the `prorata_dust_trace_exact` dust telescope.
[`Blanc/ProrataAttackModel.lean`](../Blanc/ProrataAttackModel.lean) bounds one
coalition move: `PriceLe` with `refl`/`trans` orders snapshots by virtual
price, `ProrataAccountingEffect.priceLe` lifts every classified effect into
it, `claimN` values a share balance with `claimN_le_balance`,
`payN_mono_price`, and the per-move bounds `claimN_externalCredit_le`,
`claimN_deposit_le`, and `claimN_withdraw_le`, closing in
`victim_loss_le_ceil`/`victim_loss_le_div_add_one`.
[`Blanc/ProrataAttackPath.lean`](../Blanc/ProrataAttackPath.lean) runs the
whole attack: `ProrataAttackState.Invariant` conjoins `SharesPartition`,
`FlowExact`, `ClaimBound`, and `VictimConsistent`, `genesis_invariant` seeds
it, each `ProrataAttackEffect` preserves it (`preservesInvariant`), and a
closed `ProrataAttackPath` yields `attacker_no_profit_of_attackPath` and
`victim_loss_bound_of_attackPath`.  Nothing here names an asset, a contract,
or a program; the WETH-backed vault is the second consumer of arithmetic
first stated for PRORATA's ETH-denominated shares.

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

## M — bytes and memory

For concrete RLP encoding and parsing, use
[`Blanc/RlpConcrete.lean`](../Blanc/RlpConcrete.lean).
`RlpConcrete.nat_bytes_roundtrip` recovers the entire natural from Jaune's
variable-width encoding. `receipt_key_small` evaluates a positive index below
128 to its one-byte RLP atom; `receipt_key_ne_of_small` distinguishes that key
from every unequal natural index, without bounding the other index. These
specialized receipt-key facts do not assert unrestricted RLP injectivity.
For arbitrary byte payloads, [`Blanc/RlpBytesInjective.lean`](../Blanc/RlpBytesInjective.lean)
provides `encode_bytes_injective`. Its length argument uses
`nat_bytes_length_mono`, so it needs no payload bound or assumption that an
extremely long encoding has a valid unwrapped parser tag. `receipt_key_injective`
and `receipt_key_ne` then distinguish every natural index, including zero and
indices at or above 128. These are byte-payload encoder facts, not injectivity
of arbitrary nested BLT values or a parser/canonicality theorem.
`RlpConcrete.splitAt_append` retains an arbitrary payload and suffix;
`encode_bytes_many` selects the ordinary length-prefixed byte encoder;
`decode_bytes_long_two`, `decode_bytes_short`, `decode_bytes_32`, and `decode_list_long_two`
apply Jaune's actual parser equations while keeping payload bytes abstract.
The additive owner
[`Blanc/ExecutionBodyTransactionCut.lean`](../Blanc/ExecutionBodyTransactionCut.lean)
also provides `RlpConcrete.decode_bytes_long_one` and
`RlpConcrete.decode_list_long_one` for one-byte long-length headers.
They preserve the exact payload and suffix, and the list equation retains
the supplied actual recursive child parse.
`decode_byte`, `decode_empty_bytes`, `decode_empty_list`, and
`decode_bytes_three` cover the small field headers; `parse_cons` composes
the actual first-item and remaining-list equations.
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

- Read a fixed-size ABI `bytes4` head word with `argBytes4` in
  [`Blanc/CommonCore.lean`](../Blanc/CommonCore.lean).  It right-aligns the
  ABI's left-aligned four significant bytes before an integer comparison;
  use ordinary `arg` for integer/address head words.
- Full source from offset zero: `Bytes.sliceD_zero_length` in
  `Blanc/CommonProofs.lean`.
- Recover a selector from calldata described as
  `abiSelectorBytes selected ++ tail` with
  `selector_eq_of_data_eq_abiSelectorBytes_append`; discharge its explicit
  canonicality premise `Bytes.toB256 (abiSelectorBytes selected) = selected`
  for the concrete four-byte selector.
- Normalize arbitrary, including 0–3-byte, calldata with
  `Sevm.selector_eq_toB256_takeD_four`: it identifies the selector with the
  first four bytes padded on the right with zeros.  Its limb bridge is
  `shiftRight_224_eq_toB256_take_four`.
- Read back a `Bytes.writeAt`: `Bytes.sliceD_writeAt` and the neighboring
  pointwise/write-layout laws in `Blanc/CommonProofs.lean`.
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
- For the fixed four-byte word merge, use `mergeFour_bytes` in
  [`Blanc/Lift/ByteWindowMemory.lean`](../Blanc/Lift/ByteWindowMemory.lean).
  It identifies `(source & ~mask) | (destination & mask)` with the first four
  source bytes followed by the last twenty-eight destination bytes, for the
  low-224-bit mask. This covers the selector store and partial last-word copy
  without restricting either word. Discovery is manual: the existing
  `fixed-byte-offsets` matcher recognizes `Mem.Wf`, `Mem.Reads`, or
  `Bytes.writeAt` in a target, and does not recognize this byte-codec equality
  or a `Mem.read` equality alone. No broader trigger is registered.
- For an ordered two-word and four-byte copy, use `copy68Memory` and
  `copy68Memory_read` in
  [`Blanc/Lift/ByteWindowMemory.lean`](../Blanc/Lift/ByteWindowMemory.lean).
  The readback theorem requires `source + 68 ≤ target`; it covers an adjacent
  destination even though the final padded source load overlaps earlier stores.
  `PtrMem.extend` preserves the free-pointer carrier across an arbitrary
  memory read, with the actual rounded allocation size.
  `mergeFourMemory_read68` covers a four-byte prefix store that preserves the
  following 64 bytes, at an arbitrary offset in well-formed memory. These
  `Mem.read` equalities use the same manual discovery boundary as the codec
  equality above; the existing matcher has no reliable trigger for them.
- For an arbitrary byte-array allocation, use `bytesArrayMemory` and
  `bytesArrayMemory_image` in
  [`Blanc/Lift/ByteWindowMemory.lean`](../Blanc/Lift/ByteWindowMemory.lean).
  They stage the free-pointer word, the length header and the complete payload,
  retaining the modular pointer and actual rounded memory size. The image
  theorem needs a covered header and no wrap at the payload start; it supplies
  the header readback and the first-word readback of a sufficiently long payload.
  `PtrMem.write_bytes` preserves the pointer across a disjoint byte write that
  may grow memory; `PtrMem.write_bytes_of_le` specializes it to a covered write.
  Discovery of this carrier conjunction is manual, through this branch.
- Whole-word byte images and the low-byte mask live in
  [`Blanc/Lift/WordImage.lean`](../Blanc/Lift/WordImage.lean).
  `Bytes.sliceD_writeAt_word_after` keeps a window that starts past an earlier
  word write; `Bytes.sliceD_writeAt_word_last` appends a word written exactly at
  a window's end, so consecutive word stores (an ABI encoding, a recovery
  request) read back as their concatenation, peeled from the right.
  `Bytes.sliceD_writeAt_short` reads a short write (a call reply prefix of at
  most 32 bytes) at the head of a word window followed by the old image, and
  `B256.zero_toBytes_sliceD` reads zeros from any tail of the zero word.
  `B256.and_ff_eq_toUInt8` and `UInt8.toB256_and_ff` identify `AND 0xff` with
  the low byte as a `UInt8`, as a `uint8` ABI decoder masks it. Discovery is
  manual; no trigger is registered. First consumer: the Uniswap V2 Pair permit
  walk (`Blanc/Lift/UniswapV2Pair/PermitWalk.lean`).
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
  that signatures are unforgeable. Consumers: the Uniswap V2 Pair permit
  canonical corollary; `Blanc/Weth10Permit.lean`'s two address-1 clean-child
  theorems can become corollaries (proposed migration). Discovery is manual.
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
  `EcrecoverCall.consumes_toward_sstore` instead uses an actual later same-frame
  SSTORE to force the helper's return. It retains the original call slot,
  native execution, paid gas, canonical nonzero answer and caller stack without
  a successful final-frame premise. Local nondelegation, `NeutralFork`, entry
  registers, pointer bounds and structural SSTORE-freedom remain obligations;
  this generic theorem does not establish contract dispatcher coverage.
  The concrete `Usdc.recoveryV2_1_consumes` specialization in
  [`Blanc/Lift/Usdc/RecoveryV2_1.lean`](../Blanc/Lift/Usdc/RecoveryV2_1.lean)
  follows the actual checked V2_1 recovery entry to STATICCALL at PC `0x4a78`,
  derives its four-word input from the entry registers and memory writes,
  and connects the actual native invocation and nonzero canonical answer to
  the original checked caller's returned stack. Its entry, pointer,
  nondelegation and `NeutralFork` premises remain local producer
  obligations. It does not enumerate flag-zero invocations or establish
  complete historical permit coverage.
  For a later actual SSTORE with arbitrary final frame outcome,
  `Usdc.permitV2_1_recovery_answer_toward_sstore` in
  [`Blanc/Lift/Usdc/PermitRowRecoveryV2_1.lean`](../Blanc/Lift/Usdc/PermitRowRecoveryV2_1.lean)
  follows the real recovery return through the `0x471c` epilogue to the
  `0x421e` owner comparison, deriving that the native answer equals the saved
  owner. Its companion `permitV2_1_owner_comparison_toward_sstore` excludes
  the actual rejecting branch. Recovery-entry registers, pointer bounds,
  continuations and nondelegation remain local premises; root-to-entry
  coverage and pre-authentication nonce-slot separation are separate work.
  The actual original-frame producer is
  `Usdc.permitV2_1_root_recovery_toward_sstore` in
  [`Blanc/Lift/Usdc/PermitRowPrefixV2_1.lean`](../Blanc/Lift/Usdc/PermitRowPrefixV2_1.lean).
  From the fresh PC-zero permit frame and an observed later SSTORE, it derives
  the actual recovery entry, original prefix, calldata-derived owner/signature
  words, pointer geometry and preservation of address-1 code. It assumes no
  successful final outcome. The target stack head and explicit inequality
  between its key and the calldata owner's nonce slot remain premises of this
  local producer; the history consumer must discharge finite separation.
  `Usdc.permitV2_1_tracked_sstore_native` in
  [`Blanc/Lift/Usdc/PermitRowNativeV2_1.lean`](../Blanc/Lift/Usdc/PermitRowNativeV2_1.lean)
  discharges that inequality from the existing finite `RowSep.other` nonce site.
  For an actual successful tracked-row SSTORE with calldata owner equal to the
  Pair, it derives the original call occurrence, native execution/payment and
  Pair answer, preserving node, slot, result and return through `reRoot`.
  Address-1 nondelegation and `NeutralFork` remain explicit local premises;
  no enclosing-frame success or preselected recovery query is assumed.
  The actual query bytes remain existential; this theorem does not claim
  complete old-version coverage or the historical absence of Pair signatures.
  `RetainedOldOwnerNativeQuery` in
  [`Blanc/Lift/Usdc/RetainedOldRecovery.lean`](../Blanc/Lift/Usdc/RetainedOldRecovery.lean)
  is the independent actual native-query carrier for globally retained old
  owner-route parents. It keeps the parent position, original occurrence,
  version/site, message and arbitrary child result; membership never tests the
  desired answer or a tracked write. `global_retention` derives the same node's
  retention under an actual settled root. `retained_old_owner_pair_query_at`
  reuses the successful old-owner producer for both V2 and V2_1, deriving fresh
  entry from history. `retained_old_owner_not_pair` applies exclusion only over
  that retained universe. The corresponding `_effective` variants carry the
  actual parent fork's `delegatedCodeAddress(code1) = none` readiness through
  both recovery specializations, `ownerV2_query_consumed_effective` and
  `permitV2_1_query_consumed_effective`, the shared old-owner backend and all
  three retained endpoints (`pair_query_at`, `has_pair_query`, `not_pair`).
  Original pure-nondelegation APIs project to that same implementation; the
  independent query carrier is unchanged. Domain capabilities, BAL absence
  and actual routing readiness remain explicit producer obligations. This
  does not constrain discarded raw frames or finish the allowance-history fold.
  [`RetainedAllowanceWrites.lean`](../Blanc/Lift/Usdc/RetainedAllowanceWrites.lean)
  connects an actual retained storage write under an original settled root to
  its globally retained parent. `usdc_retainedRowWrite_nonInc_or_v2_2_owner`
  reuses the raw writer classifier and transports its exception by same-frame
  `sevm` equality, then applies retained old-query exclusion and initializer
  separation. The actual caller producer and scoped old routing readiness
  remain inputs; the exact V2_2 owner case remains in the conclusion.
  `usdc_retainedRowWrite_nonInc` closes that case with a separate retained
  V2_2 owner producer. These are local write inequalities, not a storage fold
  or a proof of the endpoint zero seed.
  The write-scoped caller input is supplied by `retained_caller_write_excluded`
  in [`UniswapV2PairUsdcCallersIn.lean`](../Blanc/Composition/UniswapV2PairUsdcCallersIn.lean).
  It follows actual retained parents, uses the Pair's historical child-selector
  theorem and proxy calldata inheritance, and permits the V2_2 library as an
  intermediate case. The library's no-SSTORE theorem excludes that case only
  at the original successful write. Actual root caller exclusion, the deployed
  USDC world, and installed Pair/representation/freshness remain inputs.
  `mid_retained_caller_write_excluded_of_mid_senderQueries` uses only the actual
  after-cut sender queries for root exclusion. Pair replay starts at
  `cut.afterBenv`; USDC world/library facts stay on the original full chronology.
  It shares the same retained-parent and successful-write proof; actual cut
  state and finite touched-key freshness remain inputs. The original
  `mid_retained_caller_write_excluded` is a compatibility wrapper that restricts
  its full-history exclusion through `senderQueries_subset_full`.
  `MidHistoryTraceIn.usdc_retainedRowWrite_nonInc_or_v2_2_owner` consumes that
  mid-history caller exclusion through the same retained-write classifier.
  It retains the original root, committed parent and write witnesses while
  embedding the mid frames into the full chronology. Raw facts, native-query
  exclusion and explicit old-owner routing stay on the full history; the V2_2
  owner exception remains an obligation.
  `UsdcDeployedWorld.active_library_code` shares the existing active-library
  selection with `ctxAt_step`; it derives actual code from the world facts.
  `Usdc.recoveryV2_consumes` in
  [`Blanc/Lift/Usdc/RecoveryV2.lean`](../Blanc/Lift/Usdc/RecoveryV2.lean)
  specializes the same engine at V2's actual `0x50a4` entry and `0x50ef` call.
  Its actual caller remains a producer obligation, including the `0x4d93`
  epilogue before any owner comparison.
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
  and complete `nonce_line` interface preserved. `seven_args_call_line`,
  `deadline_line` and `iszero_jump_line` share the argument shuffle and guard
  inversions between successful and raw cursor producers, with actual PUSH
  destination bytes as parameters.
  `mapped_byte_read_line` takes the actual indexed stack equality and proves
  the mapping read for that depth; the original `blacklist_read_line` is its
  permit specialization. `wrapper_line`, `selector_line`, `compare_gt_line`
  and `compare_eq_line` derive the ABI wrapper and selector-test stacks.
  The `selector_gt_zero`/`selector_gt_succ` and
  `selector_eq_zero`/`selector_eq_succ` cursor adapters require the actual
  source list, checked certificate and closed comparison result.
  `guardSucc` and `guardZero` exclude an actual rejected subtree through its
  `noOk` check and the original successful execution. These cursor adapters
  are available by name here; no new dispatch head is required or admitted.
  `guardSucc_pc` additionally derives the reached numeric PC from the actual
  decoded jump target. `masked_owner_line` inverts the four-instruction
  address-mask/equality prefix using the canonical returned address word;
  successful owner equality still requires the consumer's actual branch proof.
  `struct_memory_facts` and `seven_word_memory_facts` expose the ordered
  six- and seven-word writes, free pointer and exact struct hash preimages.
  `seven_word_head_line`, `seven_word_body_line` and `seven_word_tail_line`
  invert the actual authorization builder; its source tag, domain slot and
  return destination remain explicit parameters. `typed_memory_facts_at`
  handles the overlapping 66-byte typed image at either supported struct end,
  352 or 384, yielding `450/480` or `482/512` for the recovery pointer/size.
  `struct_hash_line_at`, `typed_words_line_at`, `typed_length_line_at` and
  `typed_hash_line_at` use the actual pointer, length and read bounds.
  The fixed permit APIs, including `typed_memory_facts`, specialize the shared
  proofs and retain their public statements. Consumers must derive every
  buffer fact and actual source route. Use the existing `line-run-split`
  recipe for line inversions and these named facts for memory goals. The
  helpers do not establish a whole selector path or historical occurrence.
  The concrete fresh-entry producer in
  [`Blanc/Lift/Usdc/PermitQueryV2_1.lean`](../Blanc/Lift/Usdc/PermitQueryV2_1.lean),
  `Usdc.permitV2_1_query_entry`, derives the recovery registers, pointer and
  actual continuations from PC zero, empty stack/memory and the permit selector
  on a successful checked V2_1 execution. Its digest uses the domain word
  after the actual nonce write, without a storage-separation premise.
  `Usdc.permitV2_1_query_consumed` connects that query's original native call
  slot and answer through the real `0x471c` return to the `0x421e` owner check,
  deriving the nonzero calldata-owner answer. Existing fork coverage and
  address-1 nondelegation remain local premises; proxy/history entry, other
  selectors and failed-call enumeration remain separate obligations.
  The V2 family in
  [`Blanc/Lift/Usdc/OwnerQueriesV2.lean`](../Blanc/Lift/Usdc/OwnerQueriesV2.lean)
  derives all four registered owner-selector prefixes through
  `Usdc.ownerV2_source_prefix`; `ownerV2_source_prefix_of_owner_selector`
  uses the existing `selV2.owners` table, including signed decrease.
  Fresh successful execution yields the decoded arguments, pause/blacklist
  facts, exact scratch memory, state, pointer and actual continuations.
  Permit reaches the source tail after its nonce increment; the other three
  paths return from authorization validation with strict time bounds,
  unused authorization state and no storage write. `ownerV2_query_entry`
  derives the actual six- or seven-word struct hash, typed-data digest,
  signature-guard route, full registers and continuations at `0x50a4`.
  `ownerV2_query_consumed` uses existing owner-selector membership to connect
  the actual `0x50ef` native call, its original slot, paid gas and canonical
  nonzero answer through `0x4d93` and each real owner comparison. The answer
  is the calldata owner; the native message and return observations remain
  in the conclusion. Fork coverage and address-1 nondelegation are explicit
  local premises. Historical transport, complete retained-query relevance
  and failed-call enumeration remain separate obligations.
  `Usdc.old_owner_query_nativeH` (on a `NeutralFork`; `old_owner_query_native` is its
  `CoveredFork` corollary) in
  [`Blanc/Lift/Usdc/OldRecoveryRelevance.lean`](../Blanc/Lift/Usdc/OldRecoveryRelevance.lean)
  composes both version families at their original fresh execution root. It
  preserves the actual call node, recursive slot, step result and returned
  derivation through `CallOccurrenceStep.reRoot`, and derives the real
  `initEvm msg` ECRECOVER answer, native entry, settlement and resume equations.
  Its version-specific conclusion retains exact inputs, call sites and owner
  comparisons. `implV1_allowLocality_observed`, `implV2_allowLocality_observed`
  and `implV2_1_allowLocality_observed` preserve the original `StepIn` and
  per-version `RowSep` in forward `RunP` protected-write observations. V1 has
  only caller/initializer exceptions; the signed versions replace the owner-word
  exception by `OldUsdcNativePairAnswer`, retaining the actual original-root
  call, native message and Pair answer; `old_owner_pair_native` produces it on a
  `NeutralFork`. This result predicate is not a universe
  of relevant queries. Local retention requires root commitment; complete
  historical scope, ancestor settlement and attribution of arbitrary retained
  SSTORE occurrences remain separate obligations.
  Discovery is manual for these concrete source-specific consumers.
- At an actual reached STATICCALL, use
  [`Blanc/Lift/RecoveryOccurrence.lean`](../Blanc/Lift/RecoveryOccurrence.lean).
  `recoveryInvocation_of_callOccurrence` preserves the real failure cause or
  supplies a `RecoveryInvocation` tied to the existing `CallOccurrenceStep`.
  The successful invocation retains exact memory input, spawn, synchronous
  `Frame.enter = .done`, absent child slot, paid gas, clean child, resumption
  and parent return data. `recoveryInvocation_of_successFlag` selects that
  branch from a proved nonzero returned flag; the answer can still be empty.
  `RecoveryInvocation.executed` binds the actual entered EVM's recovery to
  that return data, and `answer_ne_of_excluded` uses exclusion only for this
  query. Modern coverage and address-1 nondelegation remain explicit local
  premises. A failed flag can still follow an actual precompile invocation;
  this is neither a full query census nor a retained-write relevance proof.
  Concrete bytecode must separately prove consumption of an address answer.
  The `actual-recovery-invocation` recipe recognizes only direct
  `Nonempty (RecoveryInvocation ...)` goals.
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

- `Devm.memWrite_memory`, `Devm.memWrite_stack`, and Jaune's
  `Devm.memWrite_gasLeft` describe the primitive update.
- For source inversion of primitive word and byte stores, use
  `of_run_mstore_val` / `prefix_of_mstore_val` and
  `of_run_mstore8_val` / `prefix_of_mstore8_val`.  The byte-store result is
  the exact low-byte singleton write; `of_run_mstore8_state` supplies its
  persistent-state equation without widening the instruction invariance
  class.
- `Mem.size_write_of_le`, `Mem.size_read_snd_of_le`, and related extension
  lemmas live in [`Blanc/ForwardCall.lean`](../Blanc/ForwardCall.lean).
- For a finite layout, `MemoryStage.applyMemory` folds actual `Mem.write` in
  the same order as `applyImage`. `MemoryStage.wf_reads` carries the exact
  `Mem.Wf`/`Mem.Reads` correspondence; `applyMemory_size` computes allocation
  through `memExtsSize`, including empty writes and 32-byte rounding;
  `applyMemory_size_of_covered` preserves an existing allocation only from an
  explicit fit premise. Use `words`, `applyMemory_words_size`, and
  `read_written_word` for fixed word stores. These declarations live in
  [`Blanc/MemoryLayout.lean`](../Blanc/MemoryLayout.lean).
- For construction, `Ninst.runCompiled_mstore8_of` retains the exact singleton
  low-byte write and names its dynamic expansion charge. `func_run` uses the
  same rule for every supported compiled relation; pass that charge as the
  next numeric hint. `Func.runCompiledTo_mstore_step` covers word stores that
  need an exhibited outcome-general continuation.
- For scratch decoders that carry a proof image, use
  `of_run_mstoreAt_image` and `of_run_loadWordAt_image` to advance the stack,
  `Mem.Wf`, `Mem.Reads`, and the state equation together.  When the proof also
  carries event chronology, `of_run_loadWordAt_logs` supplies the exact
  successful two-instruction log-silence fact; `MLOAD` deliberately has no
  broader `Ninst.Hinv` instance for logs.
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
- `Blanc.ProrataWethVaultCapacities` owns the family-local supply/amount
  staging routes and full-width `maxMint`/`maxDeposit`/`maxWithdraw` seams.
  `Blanc.Composition.ProrataWethVaultCapacities` is the downstream owner that
  carries those selected words through the exact configured WETH balance
  query. Its unconditional `maxWithdraw` theorem states the real word
  saturation; `maxWithdraw_compiled_effect_exact` removes it only from the
  ledger fact `balance ≤ supply`.
- `Blanc.Composition.ProrataWethVaultAccounting` is the local accounting
  adapter for the exact four ERC-4626 quote directions. It records the local
  price recurrences, exposes the compiled inverse-quote mint and withdraw
  effects, and keeps a self-receiver outbound asset term distinct from an
  ordinary WETH debit. It does not yet supply compiled inbound or
  self-receiver snapshot projection, the configured history/provenance
  transport, or a coalition accounting theorem.
- For creation-code guards, `of_run_codesize` exposes the complete code-image
  length pushed by `CODESIZE`.
- For creation-code copies, `of_run_codecopy_mem` and
  `prefix_of_codecopy_val` expose the exact code slice written at the three
  known operands.  `of_run_codecopy_image` additionally advances the stack,
  `Mem.Wf`, `Mem.Reads`, persistent-state equality, and log equality in one
  proof-carrying decoder step.  `of_run_codecopy_logs` is the corresponding
  standalone successful-run log-silence fact, without widening the global
  instruction invariance class.
- For calldata copies with all three operands already known on the stack,
  `prefix_of_calldatacopy_val` consumes that prefix and exposes the exact
  `Sevm.data.sliceD` memory write.
- For stack operations that preserve memory and a size bound on memory growth,
  use [`Blanc/Lift/MemPotential.lean`](../Blanc/Lift/MemPotential.lean).
  `Devm.popToNat_memory` says `popToNat` leaves `memory` unchanged, and
  `Mem.write_size_le_ext` bounds a write's size by the charged extension.
- When a later step is priced or forwarded on the **whole** memory (an exact
  call profile's debit or successor is an arbitrary function of `Mem`),
  `Mem.Reads`, `Mem.Wf` and the logical size do not determine it: the
  materialised array may stop short of the logical size. Use
  [`Blanc/Lift/MemGlue.lean`](../Blanc/Lift/MemGlue.lean):
  `Mem.eq_of_size_dataSize_getD` is the extensional base; `Mem.EqExcept M N D`
  (one logical size, both well formed, equal bytes outside `D`) is seeded from a
  callee export by `Mem.KeepsOff.eqExcept` and shrunk by the *same* literal
  `.write`, `.extend`, `.writeWords` (word stores in order, `Mem.writeWords`) and
  `.restoreMem` on both sides; `Mem.Full` (array materialised to the logical
  size) comes from `Mem.full_write_of_grow`, `Mem.full_write_word_of_grow` or
  `Mem.full_writeWords_of_grow` and is kept by `.write`, `.writeWords` and
  `.restoreMem`; `.eq` and `.writeWords_eq` conclude literal equality.
  `Mem.write_getD`, `Mem.size_write_eq`, `Mem.getD_eq_of_memWord_eq` and
  `saveMem_succ_left` are the byte, size and save-chain facts underneath.
  `Mem.EqExcept.trans` composes two agreements (exceptions joined); `.writeD`, `.restoreMemD`
  and `.saveMemD` keep one exception set through the same store, restore chain or frame save.
  For memories equal at every byte (`D := fun _ => False`, what a crossed callee that keeps its
  scratch to itself leaves), `eqB_write`, `eqB_saveMem`, `eqB_memWord` carry the agreement and
  `eqB_write_grow` / `eqB_write_word_grow` conclude literal equality at the next growing store;
  `slice_memWord` / `slice_memWord_fun` name a word read off an image carrier as the literal
  memory's `memWord`. A callee export in `ScratchOut` form gives the agreement directly by
  `ScratchOut.eqExcept` in [`Blanc/Lift/VyperCheckedArith.lean`](../Blanc/Lift/VyperCheckedArith.lean).
  `sstoreCost_addLog` (`rfl`) prices an `SSTORE` after a `LOG` as before it.
  Boundary: coverage only discharges bytes both sides overwrite with the same
  literal values; it never compares independently computed stores.

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

For an exact event append from a fixed `logWith k x y` fragment, use
`of_logWith_val`: it consumes the known signature-plus-indexed topic prefix and
returns both the residual stack prefix and the precise `Log` appended from the
pre-LOG memory window.  `of_logWith_image` transports `Mem.Wf` and a
proof-carrying `Mem.Reads` image across that same fixed fragment.
`of_logWith201_val` remains the convenient specialized form for the common
ERC-20 three-topic, one-word event.

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

`constructorPairWindow_storageEffectRun` in
`Blanc/BeaconDepositConstructorStorageEffects.lean` is the scratch-layout
example: it carries the node window `[64,96)` across the disjoint constructor
write `[0,32)`, then deliberately stops carrying it before SHA output
overwrites `[64,96)`.

Boundary: `Bytes.WordFrameFrom.writeBefore` requires the explicit layout fact
`n + ys.length ≤ start`; it does not support a write crossing the suffix. Every
theorem here is frame-shaped — it carries an already-known
window and proves nothing about what the step computed.  The disjointness side
condition is always the caller's explicit premise; this module never infers
that a contract's scratch region sits below a window, and it supplies no
multi-region layout, footprint or staging algebra.  For goals about the
primitive update itself, stay in
[M2](#m2-the-goal-is-an-evm-memory-update-or-read).

One rung above those, `transferFromLog_effect_frame` proves the complete effect
of the shared `transferFromLog` fragment — the ERC-20 `Transfer` tail that
WETH, WETH10, and the PRORATA WETH vault's asset child all reach.  It returns
the residual stack prefix, the exact appended `transferLogEntry`, storage,
balance, code and output preservation, and the concrete post-log memory image,
so a following fragment can reuse the word written for the event data without
replaying the LOG walk.  WETH10's `emitTransfer_effect_frame` states the same
fact under its own qualified name and is a candidate for folding into this one;
that fold belongs to the WETH10 family rather than to a consumer.

`logTransfer_effect` is its sibling for the *direct* `transfer(dst, wad)` tail
reached through `transferCore`.  The two fragments differ in where the event's
three components come from: `transferFromLog` takes its source from the stack
and its data word from a stack word, while `logTransfer` takes its source from
the executing frame's caller and copies its data word straight out of calldata.
It returns the surviving stack prefix — the fragment is stack-neutral, so any
prefix, `nil_pref` included, passes through — and the exact appended
`transferLogEntry` naming the caller, ABI word zero and ABI word one.  WETH10's
`of_run_argCopy011` covers the calldata-copy step alone and is likewise a
candidate for folding into this walk, again as WETH10 family work.

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

`Msg.NoDel.initDevm` in `Blanc/CommonProofs.lean` requires the exact additional
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

- `processMessage.settle_ok_cases` in `Blanc/CommonProofs.lean` retains the
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
- For construction from a successful selected compiled walk, use
  [`Blanc/ForwardStorageEffects.lean`](../Blanc/ForwardStorageEffects.lean):
  annotate it with `Func.RunCompiledTo.StorageEffectPath`.  When construction
  must thread the run and annotation together through a long CPS-style walk,
  use `Func.StorageEffectRun` with `of_noRawSstorePath` for an already
  certified empty path and its `last`, `next`, `next_effectNeutral`, `zero`,
  `succ`, and `call` constructors; ordinary non-external steps can otherwise
  use `StorageEffectPath.next_of_not_exec`.  Its `.run` projection recovers the
  exact indexed `Func.RunCompiledTo` witness without rebuilding the selected
  walk; it does not turn an arbitrary source `Func.Run` into compiled evidence.
  The `storage_effect_run` tactic
  walks a childless non-SSTORE prefix with `func_run`'s state, gas, hint, and
  side-condition engine, deliberately returning an external instruction,
  SSTORE, internal call, or terminal to the caller.  To replace a designated
  successful `STOP` by an exact-effect continuation, certify the selected
  neutral walk with `RunCompiledTo.SuccessfulStopPrefix.of_execFree` and use
  `SuccessfulStopPrefix.splice`; `Func.SuccessStopOnly` rules out other
  successful terminal shapes and internal-call leaves.  Finish with
  `Prog.exists_exec_retainedStorageEffectTriples`, or its `_appended` variant
  when the compiled program is the exact prefix of creation code. The
  resulting list is exact execution order and intentionally retains successful
  no-op SSTOREs. An existing `NoRawSstorePath` converts directly with
  `StorageEffectPath.of_noRawSstorePath`; in the reverse direction, an exact
  empty annotation converts with `StorageEffectPath.noRawSstorePath_of_nil`,
  or directly from its packaged carrier with
  `Func.StorageEffectRun.noRawSstorePath`.  The reverse direction is indexed by
  the identical selected run, so it proves raw absence rather than inferring it
  from final storage equality.
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
`memCap` (the word-size allowance); `Exec.pot_le` (a complete derivation
never raises it), `Ninst.Run.pot` (one lifted step never raises it), and
`Pot.step`/`SFunc.RunP.withPot` (a run from a bounded-potential state
records it at every step).

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
  raw roots, in the whole run's. Worked use: the vault's
  `ConfiguredHistoryTrace.pairVisits` in
  `Blanc/Composition/ProrataWethVaultLedgerVisits.lean`. Membership goals over
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
  Worked use: the Uniswap V2 pair's `pair_trace_admitted`
  (`Blanc/Lift/UniswapV2Pair/PairHistory.lean`).
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
  `Exec.Frame.exists_ok` extracts the successful raw outcome already guaranteed
  by a retained frame's commitment; its qualified name is preserved after
  relocation from the USDC locality consumer. It does not prove transaction
  receipt identity or clean wrapper settlement.
  When the input is the actual clean settlement instead of a supplied successful
  raw execution, use `ProcessMessageTrace.exists_root_of_entered_clean`.
  It proves that the original trace retains exactly one root with the entered
  pc, static environment and initial machine state. For an ordinary call,
  `MessageCallTrace.exists_root_of_clean_call` transports the actual wrapper's
  clean error marker to that core and uses explicit no-delegation equations.
  The shared `callRun_logs_error` helper in
  [`Blanc/ExecutionSettledReceiptLogs.lean`](../Blanc/ExecutionSettledReceiptLogs.lean)
  exposes the same wrapper-to-core error and log equality independently.
  The concrete `original_factory_root_of_receipt` consumer in
  [`UniswapV2PairUsdcOriginSeed`](../Blanc/Composition/UniswapV2PairUsdcOriginSeed.lean)
  combines the original receipt lookup with the prepared transaction message;
  code survives the sender debit without a sender/Pair separation premise.
  `original_factory_preconditions_of_receipt` then composes that root with the
  actual same-transaction factory LOG/CREATE2 inverse and the admitted debit
  inverse. It derives the masked mapping guard, factory nonce bound and
  pre-debit Pair nonce/code collision exclusion. The concrete body/bloom/V1
  constructor-output allowance-seed chain consumes these derived facts from
  the original D receipt rather than taking the four conditions as inputs.
  `original_factory_admission_of_body` reuses the actual admission to derive
  the original transaction fields, funding and gas margin. Combined with the
  receipt-derived conditions, `original_pair_checkpoint_of_receipt` identifies
  the same forward transaction result with the actual after-D state and supplies
  its Pair runtime and initialized checkpoint.
  `pairUsdcAllowQuiet_of_original_receipts` in
  [`UniswapV2PairUsdcWeth9P1`](../Blanc/Composition/UniswapV2PairUsdcWeth9P1.lean)
  joins this Pair checkpoint and the original allowance seed to P1 for the exact
  post-B touched spenders. Full-history R3/R4 populations and post-D sender scope
  remain unchanged; no zero endpoint or initialized Pair state is supplied.
  Body, receipt and entry-code authentication, V1 constructor output,
  middle-history evidence and finite separation remain caller obligations.
  These existential trace inversions have no narrow tactic recipe trigger.
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
- When a consumer needs every entered frame's block environment (timestamp,
  number, …) to be the execution root's, import
  [`Blanc/ExecutionFrameTime.lean`](../Blanc/ExecutionFrameTime.lean):
  `Exec.frameAdmitted_benvStat` gives the block-environment statics inherited
  by every admitted frame from the execution root; use it with
  `Exec.FrameAdmitted.root` when lifting a root `benvStat` fact.
  For retained traces, `ExecutionTrace.RetainedXlot.frameAdmitted_benvStat_of_runFrame`
  admits every retained frame at the message's `benv.stat` (take `Q := (· = msg.benv.stat)`), and
  `ExecutionTrace.ConfiguredBlockTrace.frameAdmitted_time` admits every frame of
  a configured block at `block.header.timestamp.toB256`.  The same module fixes
  the new chain tip (`ConfiguredBlockTrace.post_blocks_getLast`) and orders a
  block strictly after its parent from Jaune's header validation
  (`ConfiguredBlockTrace.parent_timestamp_lt`).
  For the *settled* frames of a block or history, import
  [`Blanc/ExecutionHistoryFrameTime.lean`](../Blanc/ExecutionHistoryFrameTime.lean):
  `ConfiguredBlockTrace.settledFrames_time` (every settled frame reads the
  block's header timestamp), `ConfiguredHistoryTrace.blockFrames` (settled
  frames in trace order, each paired with its retaining block;
  `blockFrames_map_snd`), `blockFrames_time` and
  `ConfiguredHistoryTrace.settledFrames_time` (each settled frame of a history
  reads its own block's header timestamp), and the control
  `ConfiguredBlockTrace.settledFrame_time_ne_parent` (under the wire bound, no
  settled frame reads the parent's timestamp).
- `Exec.FrameAdmitted ca entry run` requires `entry` exactly at those roots
  whose `currentTarget = ca`. Its `root`, `mono`, `cont_of_ne`,
  `doneOk_of_ne`, `runErr_child`, `runOk_child`, and `runOk_next_of_ne`
  theorems are the supported restriction interface; do not reconstruct list
  membership inside a contract proof.
- `ExecutionTrace.RootEntry` in
  [`Blanc/ExecutionTraceEntry.lean`](../Blanc/ExecutionTraceEntry.lean) is the pair
  "pc zero on a covered fork"; every carrier from `ProcessMessageTrace` through
  `ConfiguredHistoryTrace` derives it for all its `rawFrames` (`.rootEntry`, from the
  fork of the carrier's opening benv). Use it to apply an execution-level theorem
  stated for `Exec 0 …` and `CoveredFork` to a raw frame of a retained trace.
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
  demanding them per frame: `Exec.rawFrameRoots_warm` and
  `ConfiguredHistoryTrace.txRawFrames_warm`
  ([`Blanc/ExecutionWarmth.lean`](../Blanc/ExecutionWarmth.lean),
  [`Blanc/ExecutionTraceWarmth.lean`](../Blanc/ExecutionTraceWarmth.lean)) show an
  address warm in every transaction-entered frame, including reverted subtrees,
  when it is a precompile of every covered fork (the accessed set only grows).
  `Exec.codeAt_avoid` and `ConfiguredHistoryTrace.codeAt_empty`
  ([`Blanc/ExecutionCodeAt.lean`](../Blanc/ExecutionCodeAt.lean),
  [`Blanc/ExecutionTraceCodeAt.lean`](../Blanc/ExecutionTraceCodeAt.lean)) keep the
  code at an address empty through a trace given no CREATE frame targets it and no
  authorization recovers to it (`NoAuthorityAt`). To settle a callee frame known only by an
  `Exec` derivation (a `CALL`/`STATICCALL` crossing needs `cpost.error = none`):
  `Exec.ok_error_eq` ([`Blanc/ExecutionErrorKeep.lean`](../Blanc/ExecutionErrorKeep.lean))
  says an execution ending `.ok post` keeps the error field it started with (the
  `ExecutionWarmth` walk for `Devm.ErrKeep`); `initDevm` starts at `none`. For transaction caller
  exclusion, `Exec.rawFrameRoots_caller_excluded` in
  [`Blanc/ExecutionCallerExclusion.lean`](../Blanc/ExecutionCallerExclusion.lean)
  tracks actual CALL/CREATE/DELEGATECALL callers and empty executing code.
  `ConfiguredHistoryTrace.txRawFrames_caller_excluded` in
  [`Blanc/ExecutionTraceCallerExclusion.lean`](../Blanc/ExecutionTraceCallerExclusion.lean)
  derives that exclusion from initially empty code, retained `NoSenderAt`,
  `NoAuthorityAt`, and trace-local CREATE avoidance (`ApplyTransactionsTrace.noSender_nil`
  supplies `NoSenderAt a` vacuously for an empty transaction list). Calls to the empty-code
  address remain allowed; system frames are outside the conclusion.
  The same shared proofs expose `Exec.rawFrameRoots_caller_excluded_noStateGas`,
  `TransactionTrace.caller_excluded_noStateGas` and
  `ApplyTransactionsTrace.caller_excluded_noStateGas`; existing covered-fork
  interfaces are compatibility wrappers. For selected historical traces, use
  [`Blanc/ExecutionHistoryInCallerExclusion.lean`](../Blanc/ExecutionHistoryInCallerExclusion.lean)'s
  `ConfiguredHistoryTraceIn.txRawFrames_caller_excluded_of_empty`.
  Its `txRawFrames_caller_excluded_prePrague_of_senderQueries` specialization
  derives disabled delegation and the sender fold from the actual selected
  forks and original admitted query population. It requires initial empty code
  and actual entered-creation avoidance; sender exclusion does not prove them.
  This is transaction-frame coverage, with no system-frame or exact partial-cut
  scope claim. These quantified context-dependent conclusions have no reliable
  automatic recipe trigger; use this branch to choose the required carrier.
  `SpawnFree` and
  `ConfiguredHistoryTrace.systemRawFrames_target_of_spawnFree`
  ([`Blanc/ExecutionTraceSystem.lean`](../Blanc/ExecutionTraceSystem.lean)) confine
  system-message frames to the four system addresses when their code spawns
  nothing. `Lift.BeaconDeposit.beaconEntry_of_env` is the worked consumer.
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
  `TransactionTrace.codeAt_keep` and `ApplyTransactionsTrace.codeAt_keep`
  ([`Blanc/ExecutionTraceCodeKeep.lean`](../Blanc/ExecutionTraceCodeKeep.lean)) keep
  *nonempty* non-delegating code through transactions (the empty-code
  `codeAt_empty` cannot), and `ConfiguredHistoryTrace.systemFrames_of_installed`
  ([`Blanc/ExecutionTraceSystemCode.lean`](../Blanc/ExecutionTraceSystemCode.lean))
  shows that with the canonical code installed at the checkpoint every system
  message enters no frame but its own. `Lift.BeaconDeposit.configuredHistory_solInv_sys`
  (and `_count_`/`_root_`) is the worked consumer.
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
  below the block gas limit (`TransactionTrace.rawFrames_gas_lt`). The same file holds
  `Exec.childFrames_codeAt_keep` (every committed direct child keeps the code at an address no
  entered CREATE frame targets, from `Exec.codeAt_avoid`) and
  `ExecutionTrace.not_mem_systemTargets_of_size` /
  `ConfiguredHistoryTrace.system_ne_of_size` (under the canonical system code and the trace-local
  system exclusions, no system frame targets a contract whose installed code differs in size from
  every canonical system code; hoisted from the Beacon deposit contract, whose
  `not_mem_systemTargets_of_installed` now instantiates it). Worked use: the Curve 3pool history
  (curve-3pool-stableswap-v1).
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
  fork-class hypotheses instead: `ConfiguredHistoryTraceIn.calldata_bound` /
  `frameAdmitted_calldata` (and staged/block forms) take
  `hdata : ∀ f, F f → 16 ≤ (Fork.ruleSet f).txr.dataNonZero`, and the strict
  `rawFrames_gas_lt` chain (`TransactionTrace.msg_gas_succ_le_noStateGas`,
  `intrinsicGas_bounds_noStateGas`, staged/block forms) takes
  `hbase : ∀ f, F f → (Fork.ruleSet f).gas.txBase = 21000`; the `_hist`
  corollaries discharge both for `HistFork` (`HistFork.dataNonZero_ge`,
  `HistFork.txBase_eq`, each proved by `cases f <;> decide`).
- To carry a trace-local premise over `trace.rawFrames` (such as "no CREATE frame targets `a`")
  to every frame below a raw frame: `ConfiguredHistoryTrace.rawFrames_closed` (the raw frames of
  a history are closed under descent, `RawFramesClosed`, layer by layer from
  `Exec.rawFrameRoots_trans`), and its trace-level consumer
  `ConfiguredHistoryTrace.childFrames_codeAt_keep` (every committed direct child of every raw
  frame keeps the code at `a`). For a precompile's readiness at every transaction frame (warm and
  undelegated, under empty code at the checkpoint, `NoAuthorityAt a` and no CREATE frame at `a`):
  `ConfiguredHistoryTrace.precompileReady`, the generic form of the Beacon `beaconEntry_of_env`
  route (all in [`Blanc/ExecutionTraceFrameEnv.lean`](../Blanc/ExecutionTraceFrameEnv.lean)).
  Worked use: `Lift.Curve3Pool.pool_trace_admitted`.
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
  `Exec.rawFrameRoots_data_bound` is the execution-level form. Worked
  consumers: `Lift.BeaconDeposit.configuredHistory_solInv_sys` (and
  `configuredHistory_count_sys`/`configuredHistory_root_sys`),
  `Lift.Curve3Crv.c3crv_history_committed_derived` and
  `Lift.UniswapV2Pair.pair_trace_admitted`.
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

For bounded actual CALL input, the same pinned module provides
`Jaune.call_step_returnData_length_lt_two_pow_160_of_input_size` on actual
`Ninst.StepRun` plus `Filled`, and
`Jaune.call_returnData_length_lt_two_pow_160_of_input_size` on actual `Ninst.Run`.
Both require the seven actual CALL operands, `stateGas = none`, and
`inputSize.toNat < 2^160`, and bound the complete reply below `2^160` on either
child outcome. They require no parent gas/memory potential or output-copy-window
bound. `pair_transfer_reply_cursor_stateH` in
`Blanc/Lift/UniswapV2Pair/PairTransferReplyCursor.lean` consumes the actual 68-byte
input operands and takes `stateGas = none` as a premise (`CoveredFork.rules_stateGas_none`
supplies it under a covered fork); `BurnFourCallsH.actualReply`
and `BurnFiveCallsH.actualReply` use it for the two actual Burn transfer replies.
The accepted `swapTransferCall_replyShort` in
`Blanc/Lift/UniswapV2Pair/SwapTransfer.lean` and `skim_raw_flag_inv` in
`Blanc/Lift/UniswapV2Pair/SkimSecondWalk.lean` use the same literal 68-byte
operand bound for Swap and Skim reply allocation.

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

#### I need a finite, root-fixed set containing a call's actual reply

Use [`Blanc/Lift/PrecompileAnswer.lean`](../Blanc/Lift/PrecompileAnswer.lean).
`precompileRun_gas_mono` shows remaining gas only gates a precompile's success,
so `precompileRun_ok_output_unique` makes the successful output a function of
calldata and the fork rules alone, named by `precompileAnswer` (and
`precompileAnswer_of_ok`); `precompileRun_ok_mem` bounds the succeeding
addresses by `precompileRunAddresses`. `ProcessMessage.ok_output` splits an
error-free successful call message into that precompile answer (empty slot) or
its entered frame's raw success (`callFrame_settle_ok`), up to the settlement's recorded touch of the current target (`Devm.recordTouch`). Together with
`Exec.rawFrameRoots` this gives a finite list, fixed by the root execution, that
contains any STATICCALL reply to a fixed request (consumer:
`UniswapV2Pair.mintFeeReplyKeys`).

### T2b. I need a contract's own ledger replay across retained settlement

A contract that reads one account and reports an *ordered* replay of the moves
it saw meets four obstacles that are about EVM settlement, not about its
ledger.  Use
[`Blanc/ExecutionAccountingReplay.lean`](../Blanc/ExecutionAccountingReplay.lean)
rather than restating them:

- `ExecutionAccountingReplay.SettlementCarrier ca` supports a boundary over
  any number of accounts. Its `storageOwners` predicate names the storages it
  may read; `worldSilent` requires equality at those owners and equality of
  the whole balance map. `entry_eq_ofState` additionally takes
  `EntryStorageSafe storageOwners msg`: a positive debit must be foreign to
  each observed owner or that owner must be `State.Protected`. The composition
  pair in `Blanc/Composition/ProrataWethVaultHistory.lean` lists both vault and
  WETH owners; it must not collapse to `ca` alone.
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

`Blanc/ProrataRealizedAccounting.lean`'s `ProrataAccountingReplay.carrier` is
the worked ledger-shaped example.  This module classifies no transition as a
deposit, withdrawal or attack step, and produces no step of its own beyond what
`credit` hands it; keep that interpretation in the contract-owned layer.

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

Minimal example: `Blanc/DripRealizedLadder.lean` builds
`ladder coalition ca : AccountingLadder dripSpec ca` (a `Unit` tag) and
restates the rungs as `retained…Replay` corollaries; `Blanc/DripTraceRealizes.lean` names its
`TraceRealizes` as DRIP's history carrier.  `Blanc/ProrataAccountingExec.lean`
is the ledger-shaped instance, whose `tag` records block and transaction
position.  Import `Blanc.ExecutionAccountingLadder`.

Boundary: the ladder classifies nothing as a deposit, withdrawal or attack
step and adds no step beyond `root`, `credit` and `ofAddBal_observed`.  It is
account-local: a boundary over several accounts (a `SettlementCarrier`), a
replay indexed by position, or an invariant that is not `S.StateInv` (for
example one threaded by fork rules) does not fit it; such a consumer reuses the
T2b seams and these wrapper facts and keeps its own ladder, as
`Blanc/Composition/ProrataWethVaultPairLadder.lean` does for the vault/WETH
pair.  It is a proof-cost
facility only: no rung changes an execution or a gas charge.

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

Two consumers exist. The beacon deposit contract observes deposit nodes
(`Blanc/Lift/BeaconDeposit/CommittedHistory.lean`); Curve 3Crv observes the
ordered writer invocations of its settlement-committed frames, with the storage
boundary as carrier and a model replay universally quantified over the opening
abstraction (`Blanc/Lift/Curve3Crv/CommittedReplay.lean`,
`CommittedHistory.lean`). A deployed contract whose certified bytes spawn only
by `STATICCALL` shares one descendant argument,
[`Blanc/Lift/StaticOnlyFrames.lean`](../Blanc/Lift/StaticOnlyFrames.lean):
`Xinst.isStaticcall` with `parentPrefix_exec_staticcall_of_cert` turns a
`SFunc.execsSatisfy Xinst.isStaticcall` check of each certificate function into
`x = .staticcall` at every same-frame location, and
`Exec.staticOnly_descendantFrames_flatMap_eq_nil` removes every observed
descendant of a target frame from that restriction and the ladder's lower-depth
hypothesis. The static callee may be the contract itself; it is then a static
lower-depth target frame closed by the same hypothesis.
The raw (all entered frames, committed or not) form is
[`Blanc/Lift/StaticOnlyRoots.lean`](../Blanc/Lift/StaticOnlyRoots.lean): a static frame is
never a CREATE frame (`Xinst.step_spawn_codeAddress_of_static`), every frame a static execution
enters is static with a code address (`Exec.static_rawFrameRoots`), and every frame entered
below a frame of such static-only certified code has a code address
(`Exec.staticOnly_rawFrameDescendants`), which is `Exec.codeAt_avoid`'s premise for every
address. Worked use: the 3Crv callee crossing in
`Blanc/Composition/Curve3PoolCalleeLive.lean` (`c3crv_msg_run`).
Its node-level companions are in [`Blanc/Lift/StaticOnlyPrefix.lean`](../Blanc/Lift/StaticOnlyPrefix.lean):
`Exec.Deriv.ParentStep.getStor_of_quiet` and `Exec.Deriv.ParentPrefix.getStor_of_quiet` (every
node of the chain of a frame that never decodes `SSTORE` and spawns only by `STATICCALL` carries the
root's storage maps), `Exec.descendantFrames_isStatic_of_staticOnly` (every retained descendant of
such a frame is static), and the byte facts `UInt8.toRinst_sstore`/`ByteArray.sstore_mem_of_getInst`
(no `0x55` byte, no `SSTORE`). Worked uses: `Blanc/Lift/Usdc/RefineSigned.lean`,
`HistorySlotsCore.lean`.

A target frame whose children may be non-static and may re-enter the contract
(Lido `pause`'s `CALL`, WETH9 `withdraw`'s ETH send) uses the entry carrier of
[`Blanc/ExecutionEntryAccounting.lean`](../Blanc/ExecutionEntryAccounting.lean):
`entryCarrier`/`entryObservation` observe every non-static committed frame at
`ca` with `EntryGood` (pc 0, covered fork, contract code, admission, the storage
invariant `I` at entry); `Exec.CoreAccounting.entryTarget` is the target handler
(target-parent spawn accounting) from three per-contract obligations —
`FramePreserves` (the frame theorem), `SpawnKinds` (only `CALL`/`STATICCALL`
along the frame's own chain) and `SpawnEntry` (`I` at each spawning node of a
successful target frame, a prefix fact); `entryLadder` and
`ConfiguredHistoryTrace.entryGood_settled` give the history form. Its generic
supports: `Evm.step_spawn_child_world` (a child opens on its parent's storage at
code-bearing accounts, balance total not growing), `Xinst.step_spawn_world`,
`Exec.Deriv.ParentStep.balSum_le`, `Exec.Deriv.ParentPrefix.balSum_le_getCode`.
The same-target direct-code facts are `Xinst.step_call_sameTarget_code` and
`Xinst.step_staticcall_sameTarget_code` in
[`Blanc/ExecutionDirectCode.lean`](../Blanc/ExecutionDirectCode.lean), which
specialize the target-free `Xinst.step_call_spawn_code` and
`Xinst.step_staticcall_spawn_code` there.

When the same target frame must be *replayed by a pure model* — its own model step
taken before the steps of the children it settles, as in WETH9 `withdraw`, which
debits and then sends ETH to a caller that may re-enter — use
[`Blanc/ExecutionModelAccounting.lean`](../Blanc/ExecutionModelAccounting.lean).
The carrier's boundary reads the target's storage only through its words
(`ofStateGet`); the contract supplies `Exec.CoreAccounting.SpawnReplay` (its own
steps `own`, and where they sit against the frame's chain nodes that decode an
external instruction: taken at each such node, only silent steps and no further
external instruction after it), plus `SpawnKinds`.
`Exec.CoreAccounting.spawnReplayTarget` composes `own` with the settled
children's replays using the ladder's lower-depth hypothesis and
`Exec.spawn_seam` (the storage across a spawning step, from
`Xinst.storageReplay_some_of_body`); `ExecutionAccountingReplay.modelLadder`
turns it into an `AccountingLadderAdmitted`. `Exec.Deriv.FirstExec` and
`Exec.Deriv.exists_firstExec_or_none` split a chain at its first external
instruction. Worked use: WETH9,
`Blanc/Lift/Weth9/CommittedSpawn.lean`, `CommittedHistory.lean`. Over a selected fork
domain `F` without state gas, for code whose frames spawn only by `CALL`/`STATICCALL`
(`SpawnKindsIn F`), the In forms live in
[`Blanc/ExecutionModelAccountingIn.lean`](../Blanc/ExecutionModelAccountingIn.lean):
`Exec.spawn_seam_callsIn` (the seam of a call-family spawning step from
`stateGas = none`; the create arm is excluded by the decoded instruction),
`Exec.CoreAccountingIn.modelFrameIn`, `SpawnReplayIn F`, `spawnReplayTargetIn` and
`ExecutionAccountingReplay.modelLadderIn` producing `AccountingLadderAdmittedIn F`.
Worked use: `Blanc/Lift/Weth9/CommittedHistoryIn.lean` (`weth9_history_committedIn`).

When the contract's own frame theorem already consumes the frame's *whole subtree* —
re-entered frames of the same contract run inside the frame's own model transcript, so
its own carrier effect is not complete at the first external instruction and the
children must not be replayed a second time — use
[`Blanc/ExecutionWholeFrameAccounting.lean`](../Blanc/ExecutionWholeFrameAccounting.lean).
The contract supplies `Exec.CoreAccounting.WholeFrameReplay` (every committed
non-static target frame replays from its entry to its post boundary with exactly the
observation of its committed frames) plus `SpawnKinds`;
`Exec.CoreAccounting.wholeFrameTarget` adds the static case
(`Exec.CoreAccounting.staticObservedNil`: below a static frame nothing is observed, by
the lower-depth hypothesis) and `ExecutionAccountingReplay.wholeFrameLadder` turns it
into an `AccountingLadderAdmitted`. The obligation receives the frame's commit proof, so
its step can name the committed frame. Over a selected fork domain `F`, the In forms
live in [`Blanc/ExecutionWholeFrameAccountingIn.lean`](../Blanc/ExecutionWholeFrameAccountingIn.lean):
`SpawnKindsIn F`, `spawnChildIn`, `staticObservedNilIn`/`staticFrameIn`,
`WholeFrameReplayIn F` (same binder order as `WholeFrameReplay`, so the Mac's
`pair_wholeFrameReplayWithIn` fits), and `wholeFrameLadderIn` producing
`AccountingLadderAdmittedIn F` (takes `hsgF`, `kinds`, `whole` and In `preserves`;
`messageRoot_facts` reused). Worked use: the Uniswap V2 pair
(`Blanc/Lift/UniswapV2Pair/PairHistory.lean`: `pair_wholeFrameReplayWith`, `pairLadderWith`,
`pair_history_committed`), whose parameterized `PairObservedReplayWith` (`mono`, `sourceReplay`, `append`),
`PairStep.AuthenticWith`, `PairReplayWith`, `pairCarrierWith`/`pairObservationWith`,
`pairSpec_soundAdmittedWith`/`pairSpec_preservesAdmittedWith`,
`pair_wholeFrameReplayWith`/`pairLadderWith` and `pair_history_committed_with`
retain one supplied source/admission relation through the existing traversal.
The public history headlines instantiate this traversal with `pairAdmittedSupply`
from `PairPositionalSupply.lean`: all eleven concrete operation families retain
`PairAdmittedConsumes` and actual `PairEntryAuth`. The public live/admin routes
carry this same admitted history and return `PairAdmittedOutcome` for the new
successful frame. Erasure into model laws preserves those selected steps and
their transcripts, including the steps quantified by `NoShrink`.
Its calling entries consume re-entered ERC-20 frames as nested
transcript turns; its carrier's boundary is the storage view `(getStor ca).get` (raw `Stor`
equality is not a function of the words), with representations transported by `WriterRep.congr`.

To read a contract's ledger at the **entry** of an arbitrary committed or settled frame (a static
read of a token by a foreign contract, a foreign frame between two target steps), use the positional
ladder in [`Blanc/ExecutionAccountingPositional.lean`](../Blanc/ExecutionAccountingPositional.lean):
`PositionalLadder` is an `AccountingLadderAdmitted` with an `Opaque` frame predicate and the
frame-level root law `rootAt` (a replay from the root's entry boundary to the entry of any committed
frame `f` whose prefix holds no opaque frame enclosing `f`, `Exec.Frame.Encloses`). The descent
invariant `Exec.PositionalAccounting` is proved for every admitted derivation by
`Exec.positionalAccounting`; the producers are `modelPositionalLadder` (`Opaque := False`) and
`wholeFramePositionalLadder` (`Opaque` = non-static target frames). Two generic helpers live there:
`Blanc.List.split_append_cons` and `Exec.descendantFrames_getStor_of_static`.
[`Blanc/ExecutionAccountingPositionalHistory.lean`](../Blanc/ExecutionAccountingPositionalHistory.lean)
lifts the root law along `settledFrames`' own structure: `PositionalLadder.At` with `At.nil`,
`At.append`, `At.prefix`, `At.ite`, the per-wrapper rungs (`processMessage_at`, `messageCall_at`,
`transaction_at`, `systemMessage_at`, `requests_at`, `body_at`, `configuredBlock_at`) and the
headline `PositionalLadder.configuredHistory_at` (with `modelPositionalLadder_configuredHistory_at`):
every split `before ++ f :: after` of a configured history's settled frames gives a replay from the
checkpoint to `f`'s entry that observes exactly `before`. Worked use: the Uniswap V2 pair
(`Blanc/Lift/UniswapV2Pair/PairPositionalState.lean`, `PairHistoryShape.lean`).

For mutable direct-child selectors alone, use `pair_replay_children_shape` in
[`PairPositionalCalls.lean`](../Blanc/Lift/UniswapV2Pair/PairPositionalCalls.lean).
It consumes the actual authentic connected replay and its observation equality,
including re-entered Pair frames, to prove the child caller and transfer/callback
selector. [`PairPositionalCallsIn.lean`](../Blanc/Lift/UniswapV2Pair/PairPositionalCallsIn.lean)
supplies `pair_history_children_shapeHist` and `pair_mid_history_children_shapeHist`
from the canonical historical replay producers. Installed code, initial
`WriterRep` and finite touched-key freshness remain obligations; lock state,
factory quietness and fixed token identities are unnecessary for this conclusion.

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
`configuredHistory_atPos`. The carrier such a family replays over when its boundary depends on
storage the family rewrites (an implementation slot) is the guarded book carrier of
[`Blanc/Lift/Token/FamilyReplay.lean`](../Blanc/Lift/Token/FamilyReplay.lean): it reads a book ledger off the owner's storage together
with a guard's verdict (`guardedBook_run`; `guardedBookCarrier_unguarded`: it says nothing at an
unguarded boundary), and `ObserverChain` pairs each non-static entry with its observer so that
`ObserverChain.run_eq` turns the book run over observer asks into the run over entry asks
(`ObserverChain.prefix`, `observerView_flatMap`; `ObserverChain.of_local` in
`Blanc/Lift/SettledFramePositions.lean` builds a chain from its two local conditions). Worked use:
USDC (`Blanc/Lift/Usdc/HistoryFamily.lean`, `HistoryReplay.lean`).

For a list induction over settled positions, use
[`Blanc/ExecutionTraceSettledForest.lean`](../Blanc/ExecutionTraceSettledForest.lean): the settled
frames are a pre-order forest, with no uniqueness of frames assumed.
`ConfiguredHistoryTrace.settledFrames_contig` (from `Exec.descendantFrames_contig` and
`rootFrames_forest`) says that at every split `before ++ F :: after` the list `after` begins with
`F`'s descendants; `ConfiguredHistoryTrace.settledFrames_parent` says a settled frame is a message
root or an earlier frame `G` spawned it as a direct child (`Exec.SpawnedBy`) at a position inside
`G`'s block of descendants; `Exec.Frame.committedFrames_self` places a committed frame in its own
expansion. Worked use: `Blanc/Composition/PairTokenStepFrames.lean`.
Further positional facts over that forest are in [`Blanc/Lift/SettledFramePositions.lean`](../Blanc/Lift/SettledFramePositions.lean):
`ConfiguredHistoryTrace.settledFrames_parent_of_codeAddress` (a settled frame at `ca` whose code
address is not `ca` has a positional parent, an earlier settled frame that spawned it and whose block
of descendants covers its position; `PositionalParents` with the one-rung `parentCarrier`/
`parentObservation` carries the order-local property), `Exec.descendantFrames_eq_flatMap` with
`List.flatMap_committed_split`, `Exec.Frame.not_mem_own_descendantFrames`,
`Exec.single_child_of_silentAfter` (a run that decodes no external instruction after its first one
has at most one child, which heads its descendants), and
`ConfiguredHistoryTrace.settled_mem_rawFrames` (a settled frame's root derivation is a raw frame;
the Lift-stratum form of the composition stratum's `mem_rawFrames_of_mem_settledFrames`). Worked
use: `Blanc/Lift/Usdc/HistoryReplayFrames.lean`.

Over a selected fork domain `F`, the In forms live in
[`Blanc/Lift/SettledFramePositionsIn.lean`](../Blanc/Lift/SettledFramePositionsIn.lean):
`parentLadderIn` (the same one-rung construction over `AccountingLadderAdmittedIn F`,
reusing `parentCarrier`/`parentObservation`) and
`ConfiguredHistoryTraceIn.settledFrames_parent_of_codeAddress` (via
`configuredHistoryIn`, admission from `frameAdmitted_iff_rawFrames`; takes
`capabilities`, `rewards`, `inv`, `K` and `image`).

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
- To recover an account before the debit from a zero nonce afterward, use
  `ExecutionTrace.TransactionTrace.account_eq_of_debit_nonce_zero` in
  [`Blanc/ExecutionTransactionDebitInverse.lean`](../Blanc/ExecutionTransactionDebitInverse.lean).
  It derives sender exclusion and equality of the entire target account from
  the same actual transaction trace. No concrete sender nonce or fork premise
  is needed. The caller must produce the debit-state zero nonce; this does not
  authenticate a historical state or infer freshness from a receipt alone.
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

For the converse (a transaction *succeeds*, and I have its stages) use
[`Blanc/TransactionForward.lean`](../Blanc/TransactionForward.lean):
`checkTransactionGasLimits_ok_of_room` and `checkTransaction_ok_of_parts` assemble the
admission check from its parts, `processMessageCall_call_of_message` settles a call message
(no authorizations, no delegation) over a successful `processMessage`, including the
touched-account output field, and `processTransaction_of_stages` is `processTransaction` from
the validation, admission, debit, prepared message and message-call outcome, with the exact
settled state (gas refund and coinbase fee credited, accounts deleted) under the selected
settlement facts (`CoveredFork.rules_touchedSweep`, `CoveredFork.rules_refundQuotient`). The
sender-account part is the rule-selected `checkTransactionSenderAccountFor`, and
`calculateIntrinsicCost_two_call` takes the nonzero-byte price and calldata floor
(`CoveredFork.rules_dataNonZero`, `CoveredFork.rules_calldataFloor`).  Worked use:
`Blanc/Lift/VyperNonreentrantDeployed/Vulnerable/Tx/Envelope.lean`.
For a *symbolic* type-2 call to a contract (no concrete transaction to evaluate) the same module discharges
the whole envelope from field-level facts: `processTransaction_call_value_of_exec` takes the fee, nonce, funds,
code-free sender, gas and signature facts (`hrecover` the only cryptographic premise) and the message's
interpreter run `hexec` (a success with no frame error and a non-negative refund counter, for the debited
state, `callMessage` and its entry environment), and returns `processTransaction`'s settled state and the
block's gas counters (`txGasUsed`); `processTransaction_call_value_of_exec_receipts` is the same
envelope that also returns the appended receipt key and the receipt at it (`makeReceipt tx none`, the
cumulative gas, the frame's logs) and that every other receipt key reads back as before (a later
transaction of the block carries the earlier receipts), and `processTransaction_of_stages_receipts` is the
stage form behind it. Its funds premise covers `tx.gas * maxFee + tx.value`;
it derives affordability after the gas debit and splits zero from nonzero value.
`Msg.benvAfterTransfer_of_value_zero` supplies the zero-value entry;
`Msg.benvAfterTransfer_of_affordable` constructs the nonzero transfer.
The signature and successful raw execution remain
premises; the theorem does not construct a signed transaction or a configured history.
`processTransaction_call_of_exec` retains the original zero-value interface as a specialization.
The shared parts are `checkTransactionGasFee_two`, `checkTransactionChainId_two`,
`checkTransactionBlobData_two`, `checkTransactionReceiver_two`, `checkTransactionAuthorizationList_two`,
`checkTransactionSenderAccount_ok_of_noCode`, `checkTransaction_sender`,
`validateTransaction_ok_of_facts`,
`calculateIntrinsicCost_two_call` (with `calldataTokens` and the covered-fork constants
`CoveredFork.rules_txBase`, `rules_floorTokenCost`, `rules_storageClearRefund`,
`CoveredFork.checkTransactionGasCap_ok`), `prepareMessage_call`/`callMessage`,
`benvAfterTransfer_get_of_value_zero`, `processCreateMessage_msg_afterTransfer_get` (a zero-value
CREATE frame's entry world, account by account), `processMessage_call_of_exec`, `debit_get_ne`/`debit_get_self`,
`addBal_get_self`/`addBal_get_ne`, `sender_net_toNat`, `txGasUsed_le` (bounds `txGasUsed ≤ gas` from `floor ≤ gas`),
`applyTransactions_two` (folds two sequential successful transactions into `applyTransactions`),
`processTransaction_receiptsTrie` (identifies the inserted receipt key), `receiptKey_zero`/`receiptKey_one`/`receiptKey_ne`
(evaluate and distinguish the receipt keys at index 0 and 1), and `processTransaction_of_stages_gasUsed` (the
stage lemma with the block output's gas counters).  Worked use: the deployed WETH9's
`Blanc/Lift/Weth9/LiveTx.lean` (`weth9_tx_withdraw`, `weth9_history_tx_withdraw`), which feeds it the frame of
`weth9_withdraw_live_post`.

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
For a positive index below 128, including deployment indices 22 and 38,
`TransactionTrace.receipt_of_settledRoots_after_later_indices` derives encoded-key
separation from strictly later suffix indices via `RlpConcrete.receipt_key_ne_of_small`.
For an actual `ApplyTransactionsTrace.TxSplit` on `xs.putIndex`,
`TxSplit.later_indices` derives this ordering from `putIndex_aux_mem_drop_index_ge`,
and `TxSplit.receipt_of_settledRoots_after_suffix` retains the selected receipt
through its actual suffix, preserving the selected transaction's cumulative gas.
The selected position must be positive and below 128.
`RequestsTrace.receiptsTrie_eq` and `RequestStageTrace.receiptsTrie_eq`
derive actual trie preservation for enabled and disabled request processing.
`RequestsTrace.receiptsTrie_and_blockLogs_eq` supplies both trie and block-log
preservation from the same original request result.
`StagedBodyTrace.receiptsTrie_eq_transactionBout` transports through the actual
withdrawal and final access-list fields to the body's final output.
`StagedBodyTrace.receipt_of_txSplit_settledRoots` and
`ConfiguredBlockTraceIn.receipt_of_txSplit_settledRoots` in
[`Blanc/ExecutionHistoryCommittedCuts.lean`](../Blanc/ExecutionHistoryCommittedCuts.lean)
therefore read the selected receipt at the actual final body/block output,
retaining the head's status and cumulative gas. They require `0 < i < 128`
and the selected no-state-gas rule; they assume no trie endpoint equality.
For all positions, use [`Blanc/ExecutionIndexedReceipts.lean`](../Blanc/ExecutionIndexedReceipts.lean):
`TransactionTrace.receipt_of_settledRoots_after_distinct_indices` proves encoded
key separation from distinct natural indices with the unrestricted byte encoder.
`TxSplit.receipt_of_settledRoots`, `StagedBodyTrace.receipt_of_txSplit`, and
`ConfiguredBlockTraceIn.receipt_of_txSplit` carry the original selected receipt
through its actual suffix and final body output without a positive or small-index
premise. The older bounded signatures remain available to existing consumers.
`ConfiguredBlockTraceIn.txSplit_logs_eq_of_receipt` identifies an actual looked-up
receipt's logs with the selected transaction's outer root logs, folded once;
`txSplit_root_logs_of_receipt` transports any log predicate to those roots.
`ApplyTransactionsTrace.exists_splitAt_of_mem_settledRoots` derives every root's
original indexed transaction occurrence. `ConfiguredBlockTraceIn.root_logs_of_receipts`
therefore transports a predicate on every in-range actual receipt to every root
when the actual system stages are disabled. It includes index zero and all later
positions; it does not assume a separate per-root log property.
Actual indexed inclusion and authentication of the block's receipt commitment
remain separate obligations. A whole-block receipt condition is not an exact
interval condition when the first or last block is only partially consumed.
For those endpoints, [`Blanc/ExecutionReceiptRanges.lean`](../Blanc/ExecutionReceiptRanges.lean)
provides `ApplyTransactionsTrace.root_logs_of_receipts_after_suffix`: an actual
consumed segment's receipt predicates survive its actual suffix without requiring
the suffix receipts to satisfy them. `putIndex_aux_pairwise` and
`putIndex_aux_mem_index_lt` derive positional separation and bounds.
`ConfiguredBlockTraceIn.after_txSplit_root_logs_of_receipts` consumes only indices
strictly after the original selected transaction; `before_txSplit_root_logs_of_receipts`
consumes only indices strictly before it, keeping the original head and suffix.
[`Blanc/ExecutionHistoryReceiptLogs.lean`](../Blanc/ExecutionHistoryReceiptLogs.lean)
defines `ConfiguredBlockTraceIn.receiptLogsBetween lo hi` by reading actual final
receipt tries at actual transaction positions, lower-inclusive and upper-exclusive.
`mem_receiptLogsBetween` retains every log from an actual in-range receipt;
`root_logs_of_receiptLogsBetween` and `ConfiguredHistoryTraceIn.root_logs_of_receiptLogs`
connect those scans to the original roots. `ConfiguredHistoryTraceIn.receiptLogs`
reads every actual intervening block. `root_logs_between_txSplits_of_receipts`
composes the first suffix, whole intermediate history and final prefix into exactly
the roots of the original after/before interval. Its mainnet specialization,
`root_logs_between_txSplits_of_mainnet_receipts`, derives stage premises from the
actual final pre-Cancun timestamp and accepted-header chronology. These scans
establish semantic transport, not independent archive/commitment authentication.
For original block-log membership, use
[`Blanc/ExecutionBlockLogs.lean`](../Blanc/ExecutionBlockLogs.lean).
`TransactionTrace.blockLogs_eq` and `ApplyTransactionsTrace.blockLogs_eq` append
the exact retained transaction-root logs in order. Request processing, withdrawals
and final access accounting preserve these logs;
`StagedBodyTrace.blockLogs_eq_transactionRoots` identifies the final sequence.
`ConfiguredBlockTraceIn.mem_blockLogs_of_txSplit`, `mem_blockLogs_of_receipt`, and
`mem_blockLogs_of_mem_receiptLogsBetween` place each selected original log in
the actual final `blockOutput.blockLogs`, including arbitrary prefix/suffix intervals.
These require only the selected no-state-gas rule and do not add system-call roots
or assume independent archive/header identification.
`ConfiguredHistoryTraceIn.receiptLogs_between_of_boundary_bloom_missing`
combines missing address bits in the original boundary headers with a predicate
on the middle history. It transports that predicate to arbitrary exact boundary
intervals when every log from another address satisfies it; no middle witness
is inferred from the two boundary blooms.
The joint trace/key query is documented here rather than dispatched from an
arbitrary expanded receipt equality, list membership or quantified log predicate.

For rules outside the covered forks (any schedule with `rules.stateGas = none` and
`rules.bal = none`, including the touched-sweep forks and refund quotient 2), use
[`Blanc/TransactionForwardH.lean`](../Blanc/TransactionForwardH.lean):
`processTransaction_of_stagesH` returns the settled state with the rules' own touched sweep and
refund quotient (`txGasUsedQ`), `processMessageCall_create_of_message` settles a top-level
creation with no collision over a successful `processCreateMessage`, and
`settled_getCode_getStor_of_code_nonempty` carries an account with nonempty code through the
credits, the deletion fold and the sweep; `processTransaction_installed_of_stagesH` combines the
two for an account the message installs and does not schedule for deletion. Worked uses:
`Blanc/Lift/Weth9/DeployTransaction.lean` (`weth9_creation_transaction_byzantium`) and
`Blanc/Lift/UniswapV2Pair/CreationTransaction.lean` (`pair_creation_transaction_settles_muirGlacier`).

Another worked use is
[`Blanc/Lift/UniswapV2Factory/CreatePairTransaction.lean`](../Blanc/Lift/UniswapV2Factory/CreatePairTransaction.lean):
`pair_createPair_transaction_muirGlacier_effects` retains the initialized Pair
and preserves code/storage at every other installed account except the factory.
It uses `createPair_frame_effects` for foreign-account equality and absence of
new deletions, derives sender inequality from admission with delegation disabled,
and applies `processTransaction_installed_of_stagesH` to the same actual result.
The original frame and transaction theorems remain compatibility projections.
[`Blanc/Lift/UniswapV2Factory/CreatePairForeignHistory.lean`](../Blanc/Lift/UniswapV2Factory/CreatePairForeignHistory.lean)
exports `createPair_block_preserves_foreign_installed` on the original retained
`TxSplit 38` at the Pair's deployment block and timestamp. Its full storage
equality transports an already-established foreign cell invariant across that
transaction; it does not establish the pre-transaction invariant or a prior
lifetime exclusion for the Pair address.

The raw `debit_get_self` account equation requires the sender nonce to differ
from `UInt64.max`; transaction admission supplies this nonwrap fact.
`debit_get_self_of_protected` is the same equation for a sender that is
`State.Protected` after its nonce increment (`incrNonce_protected_self` restates
that premise on the original account), so an extracted frame helper without
admission can take the weaker structural premise.
`addBal_get_self` is unconditional and returns the credited account followed
by `clearIfEmpty`. A balance write can clear an unprotected storage-only
account, so its full-account equation must retain that normalization.

### T4. The wrapper is a message call and I must see through delegation

For code preservation from exclusion of eligible authorization queries, use
[`Blanc/ExecutionDelegationEligibility.lean`](../Blanc/ExecutionDelegationEligibility.lean).
`AuthMayWrite` tests the actual intermediate state's chain, nonce and code
gates; fork enablement is retained by `MessageCallDelegationTrace` at the
wrapper. `exists_delegationOccurrence_at` covers every sequential tuple index,
including repeated tuples and zero-target clears. Extract the wrapper with
`exists_messageCallDelegationTrace`, then use
`messageCallDelegation_getCode_of_eligible` with its `NoEligibleAuthorityAt`
premise. The carrier retains the actual code refresh and refund conversion.
`excluded_of_all` converts the older all-tuples exclusion only in the sound
direction; eligible exclusion does not imply that stronger premise.

Along a selected-domain history, use
[`Blanc/ExecutionHistoryDelegationEligibility.lean`](../Blanc/ExecutionHistoryDelegationEligibility.lean).
`MessageCallTrace.NoEligibleAuthorityAt` asks it of every delegation phase of
an actual call arm (create arms have no phase);
`ApplyTransactionsTrace.NoEligibleAuthorityAt` and
`ConfiguredHistoryTraceIn.NoEligibleAuthorityAt` fold it over exactly the
actual transactions of every block. `MessageCallTrace.delegated_getCode`
reads it back as code preservation in the delegated message;
`noEligibleAuthorityAt_of_disabled` discharges it where the message's rules
disable delegation.

For canonical system messages, use
[`Blanc/ExecutionSystemDelegation.lean`](../Blanc/ExecutionSystemDelegation.lean).
`systemTransactionMessage_auths_nil` derives the empty list from Jaune's own
system preparation, `systemTransactionDelegationTrace` constructs the skipped
wrapper, and `systemTransactionMessage_delegation_eq` gives its exact unchanged
message and zero refund. `SystemMessageTrace.delegation_empty` consumes the
retained system message, excludes CREATE arms, and proves that every actual
delegation-phase witness has `NoEligibleAuthorityAt a`, for any address.
No fork coverage, state-gas, or cryptographic premise is needed. This says
nothing about the system VM's child calls, recovery queries, or storage writes.
The shared `MessageCallDelegationTrace.noEligibleAuthorityAt_of_auths_nil`
also works for any actual message whose authorization list is known empty;
its direct exclusion goal has no registered reliable recipe trigger.

For a whole-state balance preorder under `stateGas = none`,
`processMessageCall.call_balance_noninc` in `Blanc/CommonProofs.lean` follows
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
  provides `Exec.nonce_ne_zero_committedPost`, on covered forks. Its instruction
  donors are `Rinst.get_nonce_eq_of_ok`, `Ninst.nonce_ne_zero_of_none`,
  `Evm.step_cont_nonce_ne_zero` and `Linst.get_nonce_eq_of_ok`.
  `Evm.step_spawn_rollback_getStor` separately preserves all parent storage
  when complete child settlement discards the result, including unprotected
  owners; it requires no nonempty-code premise.
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
- `Blanc.getDelegatedCodeAddress_eq_none_of_size_ne` in
  [`Blanc/CodeDelegation.lean`](../Blanc/CodeDelegation.lean) discharges a
  wrapper's `getDelegatedCodeAddress code = none` obligation from the code's
  length alone (a designator is exactly `eoaDelegatedCodeLength` bytes); a
  concrete runtime closes the length side with one `decide +kernel`.
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
`StateInv.payRewards`. `ExecutionTrace.StagedBodyTrace.rewardCreditsFunded_of_budget`,
`ConfiguredBlockTraceIn.rewardCreditsFunded` (under `stateGas = none`) and
`ConfiguredHistoryTraceIn.rewardCreditsFunded` (under `BodyStageCapabilities F`)
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
EIP-2935 walks `Blanc/Lift/BeaconRoots/SystemWalk.lean` and
`Blanc/Lift/HistoryStorage/SystemWalk.lean` (`processUncheckedSystemTransaction_beaconRoots`,
`processUncheckedSystemTransaction_historyStorage`), and the EIP-7251 empty-queue walk
`Blanc/Lift/ConsolidationRequest/SystemWalk.lean`
(`processCheckedSystemTransaction_consolidationRequest_empty`, via the checked form).

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
and `ConfiguredHistoryTraceIn.toReachUsing` forget the nonnegative reward
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
   Pair that specialization with an executable lane witness tied to a
   kernel-decided timestamp pin; retain the former fixed-fork API as a thin
   audited compatibility corollary.

This pattern does not make the contract-local carrier common infrastructure.
A literal block/history adapter or repeated schedule-selection lemma is a
hoisting candidate only after another consumer needs the same shape.

The shared current-mainnet executable lane deliberately exposes no fork
override, so it cannot supply a cross-activation witness. Consumers deployed
before the current fork need a historical deployment root at the rule record
selected at their actual deployment timestamp, followed by one configured
history that crosses later activations; a fresh current-fork creation block is
evidence for a different claim. If a future fork changes execution semantics
rather than rule data already represented by Jaune, update Jaune and re-prove
the consumer instead of adding a premise that assumes the new semantics away.

### T7. I must construct a configured block forward from its parts

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
- Exact failed binary-dispatch walks:
  [`Blanc/ForwardDispatchMiss.lean`](../Blanc/ForwardDispatchMiss.lean).
  `DispatchTree.HasSelector` names membership in the selector census,
  `DispatchTree.dispatchMissGas` records the selector-dependent cost, and
  `DispatchTree.dispatchMiss_runCompiledTo_with_path` constructs the exact
  empty-revert walk together with raw-SSTORE freedom for the identical selected
  proof. Supply `sevm.benvStat.rules.op.push0 = true` for the zero pushes in
  the inline revert. No safety property of an unselected sibling is required.
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

- Generic deployment compilation:
  [`Blanc/DeploymentCompiled.lean`](../Blanc/DeploymentCompiled.lean).  Use
  `Prog.exec_of_runCompiled_appended` for successful creation prefixes and
  `Prog.exec_of_runCompiledTo_appended` when the retained compiled walk ends in
  an arbitrary success or failure outcome while runtime/ABI bytes follow it.
- Successful no-code-address message and CREATE settlement with the actual
  rules-selected touch retained:
  [`Blanc/DeploymentTouch.lean`](../Blanc/DeploymentTouch.lean).
  `processMessage_ok_touch_of_exec` consumes successful transfer, no separate
  code address, actual raw execution and a clean raw result.
  `processCreateMessage_ok_touch_of_exec_and_charge` additionally consumes
  successful code charging on that touched result and installs its charged
  output with the actual `setCode` normalization. Neither theorem assumes
  touch recording is disabled, nor proves constructor execution, affordability,
  final transaction sweeping or a historical starting state. The
  `touch-preserving-message-settlement` recipe recognizes only the direct
  successful outer forms; it does not establish the theorem's entry,
  execution, address, output or charge obligations.
- Generic deployment-message facts:
  [`Blanc/DeploymentMessage.lean`](../Blanc/DeploymentMessage.lean).  An inner
  creation error crosses through
  `processCreateMessage_ok_of_processMessage_error`; a raw creation-code
  REVERT with no separate code address crosses through
  `MessageExecution.processMessage_revert_of_exec_afterTransfer_of_noCodeAddress`
  without changing the message's precompile switch.
  `directCreateMessageOutputOf` is the shared projection from a charged direct
  CREATE post-frame to its outer `MsgCallOutput`; contract owners may retain a
  thin historical wrapper name, but must not restate its six fields.
  `benvAfterTransfer_stat` preserves the complete static block environment
  across a successful message-entry transfer.
  The same module owns the shared receipt key, intrinsic/calldata gas
  projections and type-2 effective gas price;
  `deploymentTxPreludeBout` delegates to the lower
  `ExecutionTrace.transactionPreludeBout`.  Redemption and deployment owners
  should retain compatibility names only as thin aliases to these primitives.
- To invert the nonzero word returned by an actual internal CREATE, use
  [`Blanc/ExecutionCreateResultInversion.lean`](../Blanc/ExecutionCreateResultInversion.lean).
  `Resume.create_nonzero_inv` identifies the same clean settled child;
  `GenericCreate.nonzero_inv` retains the canonical actual spawn, the original
  `Xlot`, same-slot `ProcessCreateMessage`, exact resume, returned address and
  installed child state. It derives target collision exclusion from the spawn
  and reuses `ProcessCreateMessage.ok_charge_of_clean` to retain the actual
  inner message and successful code-deposit charge. For a filled slot, apply
  `RunFrame.some_inv` to that same `ProcessCreateMessage` to recover its actual
  entry and settlement equations. `Xinst.create2_run_generic` exposes the actual
  popped, gas-paid and memory-extended generic step under explicit
  `rules.stateGas = none` and `rules.op.create2 = true`;
  `Xinst.create2_nonzero_inv` composes that step with clean-settlement inversion.
  `Ninst.RunCompiled.create2_run` preserves the single filled slot selected by
  the compiled run. No storage-emptiness premise or absence of code at address
  zero is needed. The consumer must produce the actual nonzero result word;
  successful receipt status alone does not supply it, and enclosing rollback
  retention remains separate. These existential inversion conclusions have no
  reliable narrow recipe trigger; discover them through this branch.
- Source attainment and source-step provenance:
  [`Blanc/SourceAttainment.lean`](../Blanc/SourceAttainment.lean).
- Source-occurrence attribution when the executing code is a compiled prefix
  followed by a retained runtime or ABI payload:
  [`Blanc/DeploymentOccurrence.lean`](../Blanc/DeploymentOccurrence.lean).
  `Prog.CompiledPrefix` states the exact placement (both the compiled prefix
  and the arbitrary suffix are explicit identities) and
  `Exec.Deriv.exactProgramPrefix`, `SourceCursor.mainToward_appended`,
  `callToward_appended`, `toward_appended`, `sourceSite_appended`,
  `nonPush_sourceSite_appended` and `sstore_sourceSite_appended` carry the cursor and source-site
  facts the whole-code bridge cannot, because it requires whole-code equality.
  Bytes in the appended suffix are deliberately granted no source authority
  even when they decode as an instruction also present in the prefix.

### C3. I need a parameter-neutral runtime or creation template

Use [`Blanc/CreationArtifact.lean`](../Blanc/CreationArtifact.lean):

- `CreationArtifact.differingByteOffsets` and
  `CreationArtifact.contiguousRunStarts` derive changed compiler spans.
- `CreationArtifact.wordByteOffsets`,
  `CreationArtifact.immutableWordOffsets`, and
  `CreationArtifact.immutableWordOffsetsValid` derive and fail-closed validate
  complete fixed-width immutable words.
- `CreationArtifact.patchWord` applies one validated 32-byte patch.
- `CreationArtifact.pushB256AsPush2OrPush32` emits an exact word as a
  fixed-width `PUSH2` when it is below `2^16`, and as a full-width `PUSH32`
  otherwise.  `Ninst.runCompiled_pushB256AsPush2OrPush32` proves that either
  branch pushes the same `B256`, costs `gVerylow`, and preserves memory under
  the ordinary stack-room premise.  This is deliberately different from
  `Ninst.pushB256`, whose compact encoding strips leading zeroes and may use
  `PUSH0`.  BeaconDeposit's `constructorPushWord` is the compatibility example.
- `CreationArtifact.finalizedConstructorProgram` closes a family-owned
  layout-parametric constructor over its compiled provisional prefix and
  parameter-neutral runtime template without restating the shared coordinate
  calculation in each contract namespace.
- `CreationArtifact.CreationCoordinatesCertificate` is the two-pass
  constructor-coordinate fixed point as a structure: the provisional
  compilation of `C 0 0 runtimeLength`, the prefix length it determines, the
  final compilation of `C n (n + runtimeLength) runtimeLength`, and the
  `finalBytes.length = prefixLength` fixed point.  `.finalProgram` and
  `.finalProgram_compile` project the certified program and its compiler
  witness.  `CreationArtifact.checkCreationCoordinates` is the executable
  adapter that produces one by running both passes and rejecting compilation
  failure or a width discrepancy, and
  `CreationArtifact.checkCreationCoordinates_isSome_of_cert` is the converse:
  a certificate established by contract-owned compiler theorems shows the
  executable adapter accepts the same program, which is how a family exercises
  the checker on a real constructor without kernel-evaluating both passes
  inside the decision procedure.  `LidoCircuitBreaker.circuitBreakerCreationCert`
  and `LidoCircuitBreaker.checkCreationCoordinates_constructorProgramForProof`
  are the worked consumer.

Contract families still own their marker worlds and the interpretation of
each generated span.  A `Nat` client must separately prove its source value is
below `2^256` before conversion to `B256`; full-width fallback prevents
truncation by the encoder but does not undo wrapping that happened earlier.
The encoder does not establish a provisional/final constructor-prefix fixed
point: a provisional value below `2^16` can cross the boundary in the final
pass, so every two-pass client retains an explicit prefix-length check. That
check is what `CreationCoordinatesCertificate` packages; the certificate
records the fixed point, it does not make the boundary crossing impossible.
The operational encoder theorem has a reliable goal shape: on an exact
`Ninst.RunCompiled` goal containing `pushB256AsPush2OrPush32`, the
`bounded-creation-word-encoder` recipe points to
`Ninst.runCompiled_pushB256AsPush2OrPush32`. The remaining byte/layout
operations have no proposition-shaped recipe.

### C4. I need to navigate the byte at a known compile shape

Import [`Blanc/CompiledShape.lean`](../Blanc/CompiledShape.lean) for a
`Func.byteAtByShape` goal whose compile shape, sizes and index bounds are
already known. Inside `namespace Blanc`, use `open CompiledShape`; outside it,
use `open Blanc.CompiledShape`. The goal-sensitive
`compiled-shape-byte-navigation` recipe reaches this branch for an explicit
`.next`/`.branch`, a direct function constructor under `compileShape`, or the
registered `CompiledShape.dispatchNode` wrapper. It never normalizes an
arbitrary closed function to find that shape; expose only the relevant wrapper
or constructor and invoke `blanc_suggest` again. An unknown, opaque, `.last`,
or `.call` shape stays on the general declaration-search route.

- `byteAt_prepend_*` handles a fixed instruction prefix and its tail.
- `byteAt_next_to_tail` moves past one reference instruction when
  `inst0.size ≤ i`, even when the executed instruction `inst` and the two
  tails are independent. The reference size determines the new base and
  subtracted index; the lemma does not equate instruction bytes or widths.
- `byteAt_branch_*` selects the branch header, left subtree, jump destination
  or right subtree without expanding the other subtree.
- `dispatchNodeByteAt_*` navigates the common selector-dispatch shape.
- `pushFullWord_opcode_eq` and `byteAt_pushFullWord_data` describe a fixed
  32-byte `Ninst.push w.toBytes` instruction.

Supply the existing shape, size and index-bound facts so only the addressed
subtree is traversed. These lemmas do not establish the compile-shape equality,
compile a function, or replace contract-specific selector, route or closed-size
facts. The fixed-width PUSH lemmas are distinct from value-dependent
`Ninst.pushB256` and its minimal-width encoding.

The owner imports only `Blanc.Forward` and `Mathlib.Tactic.IntervalCases`.
The WETH deployment, domain-slice and upper-slice proofs show the direct import
and application pattern while keeping their contract-specific facts local.

For an actual `Func.compile` equality, the same module provides
`CompiledShape.compile_prepend` and `compile_prepend_of` to compile a prefix
while retaining its continuation, and `compile_branch` to combine checked
children with an explicit jump location and its 16-bit bound.
`dispatchLeaf_size` sizes a selector leaf from its push width and body size;
`prefixByteSize_fsig` supplies the standard selector-prefix size.
The `compiler-structural-composition` recipe recognizes only an explicit
`prepend` or `Func.branch` argument of a direct compiler equality. It does not
unfold a closed function or prove table entries, child bytes, or jump bounds.
Contract-specific source decompositions and frozen byte slices stay local.

For a closed prefix's immediate-acceptance side condition, `open scoped
CompiledShape` enables `discharge_prepend_acceptance`. This tactic checks the
exact `∀ i ∈ (l : List Ninst), Ninst.immAccepted i = true` shape before kernel
evaluation and leaves other goals untouched. It is useful under `all_goals`
after compiler composition. The existing compiler recipe remains the route
for the original compiler equality; this guarded side-condition tactic does
not introduce another compiler-equation matcher or traverse a closed program.

### C5. I need to preserve a compile-shape equality under a known prefix

Import [`Blanc/CommonProofs.lean`](../Blanc/CommonProofs.lean) and apply
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

### C6. I need to link an auxiliary call table by name instead of by index

Import [`Blanc/SymbolicProgram.lean`](../Blanc/SymbolicProgram.lean) when a
program's auxiliary table is large enough that hand-maintained numeric call
targets are the thing going wrong.  `SymbolicFunc Label` mirrors `Func` with
`call` carrying a caller-chosen `Label`, `SymbolicProg Label` adds a
distinguished `root` and an ordered `aux` list, and `resolve` turns the
symbolic program into an ordinary `Prog` by assigning the root index `0` and
the `i`-th auxiliary entry index `i + 1`.

- `SymbolicProg.validateDefinitions` is the definition-domain half: no root
  reuse in the table and no duplicate labels, including unused duplicates.
  `resolve` additionally reports reference completeness, and a
  `ResolveError.missingLabel` records the enclosing body label and the
  `BranchArm` path to the offending call.
- `SymbolicProg.erase map` is the inverse direction — replace each label by
  `map label` and get a `Prog` back.  `resolve_eq_erase` identifies the two
  when the table agrees with `map` on the labels that actually occur, and
  `erase_eq_of_resolve` is its converse.  That converse is harder to use than
  it looks: its agreement premise is *total* over `Label`, and
  `cases target <;> simp_all` does not close it, because `simp` will not unfold
  `SymbolicProg.findLabel?` through a structure literal and leaves one
  `0 = n`-shaped goal per label.  Prove the per-label `findLabel?` equations
  separately — each is `rfl`, and every label the table does not define needs a
  `findLabel? = none` equation — and pass them all to `simp_all` explicitly.
  `workedProg_erase_of_resolve` is the worked discharge.
- `SymbolicProg.callsOk p map` is the decidable whole-program form of that
  agreement, and `resolve_eq_erase_of_callsOk` is the front end to use: one
  `decide +kernel` over `SymbolicProg.allCalls` discharges the agreement for
  every body at once.  Reach for this instead of proving per-body agreement
  when `Label` is an infinite type (a label carrying a `Nat` coordinate), where
  `cases target <;> rfl` is not available because agreement is not total.
- `Func.mapCalls g` lifts an existing numeric `Func` by naming its targets, and
  `Func.erase_mapCalls_eq_mapTargets` is the general erasure law: erasure of a
  lifted body lands on `Func.mapTargets t` of the original, where `t` is the
  composite of naming and coordinate assignment.  `Func.erase_mapCalls` and
  `Func.erase_mapCalls_of_inverse` are its `t = id` corollaries.  Use this one
  shared lifter rather than writing a four-arm structural recursion per
  contract.  `Func.toSymbolic?` / `Func.liftCallFree` are the deliberately
  different sibling: they *reject* calls at lift time, which is what lets a
  call-free wrapper be discharged by the generic `simp` lemma
  `Func.erase_liftCallFree` with no side condition at all.
- `symbolicLinearDispatchWith` is the shared symbolic selector chain and
  `erase_symbolicLinearDispatchWith` its erasure; both are generic in `Label`
  and in `map`, so a contract keeps only its own pivot topology.
- `checkLink` combines successful resolution with
  `Prog.compiles resolved = true` and yields a `LinkCertificate`, whose
  `bytes`, `compile_eq`, `isSome_compile`, `length_compile`, `table_get_root`
  and `table_get_aux` are the exact compiled-artifact interface.
  `LinkError.compileFailed` is the other outcome and
  `checkLink_eq_error_compileFailed` is its control.

Usage rule — what you must state for anything to transport.  A bare
`LinkCertificate` transports **nothing**: all it gives you is
`resolve p = .ok cert.resolved`, an equation against a `Prog` you never wrote
down and have proved nothing about.  Gas and execution facts transport only
when you write the numeric `Prog` out by hand and prove
`resolve p = .ok <that program>` against it.  At that point the agreement is
not *proved* by this module — it is made vacuous by syntactic identity, both
sides being the same term — and that is exactly what lets every gas,
`Func.Run`, `Func.RunCompiled` and compiled-byte fact about the hand-numbered
program rewrite across it.  A consumer that keeps only a certificate has linked
its table and transported nothing.  This is the rule, not a caveat.

Boundaries.  Resolution is a coordinate assignment, not a compiler: it does
not choose a table order, and because erasure discards labels, an erasure
theorem alone does not catch a reordered table — state the label list
separately, as `workedProg_auxLabels` and
`LidoTriggerableWithdrawalsGateway.symbolicBaseAux_labels` do.
Compilability is `checkLink`'s second half and nothing in `resolve` implies it;
a call target at or above `2 ^ 16` compiles to nothing, which
`call_target_65535_compiles` and `call_target_65536_rejects` pin exactly.  The
module says nothing about gas, execution or bytes beyond the compiler witness
the certificate carries: no `Func.Run`, `Func.RunCompiled`, gas, execution
outcome, storage effect, selector route or ABI fact follows from a
`LinkCertificate`, and those obligations remain ordinary work about the `Prog`
that `resolve` returns.

Cost.  `resolve`, `erase` and the erasure lemmas are structural and cheap.
`callsOk` is meant for `decide +kernel` over a closed call list and is the
cheap route; do **not** put `checkLink` or `resolve` of a production-sized
program under a decision procedure, because that forces kernel evaluation of
`Prog.compile` over the whole table.  The two production consumers prove
`resolve (symbolicRuntime dp) = .ok (runtime dp)` through
`resolve_eq_erase_of_callsOk` and then build the certificate over the existing
`runtime`; they do not re-anchor `runtime` on a certificate projection, because
that replaces a definitional unfolding with a structure projection and breaks
every downstream `unfold runtime`.

Minimal working example: `workedProg` in the module's own `Control` section,
with `workedProg_resolve : resolve workedProg = .ok workedNumbered` against the
hand-numbered `workedNumbered` written out in full.  That is the statement the
usage rule above demands, and it is the one to copy: it comes with both premises
of `resolve_eq_erase_of_callsOk`, the per-label `findLabel?` coordinates, two
`findLabel? = none` table bounds, the separate `workedProg_auxLabels` order
statement, the `erase_eq_of_resolve` discharge, and `workedProg_checkLink`.
`nestedBranch_checkLink`, `selfRecursion_checkLink` and
`mutualRecursion_checkLink` beside it prove only `(checkLink _).isOk = true`, so
they exercise the three recursion shapes but demonstrate nothing that
transports; do not take one of them as the example to follow.  The production
consumers are `LidoCircuitBreaker.symbolicLinkCert` and
`LidoTriggerableWithdrawalsGateway.symbolicLinkCert`, each against a
thousand-line runtime.

Goal-sensitive discovery.  The `symbolic-label-linking` recipe in
[`docs/PROOF_RECIPES.md`](PROOF_RECIPES.md) covers this facility, so
`blanc_suggest` reaches it from a goal.  Its two triggers follow the goal shapes
that actually occur here rather than the ones the module's names suggest:
`goal-shape:symbolic-label-linking` matches a target mentioning `resolve`,
`checkLink`, `SymbolicProg.findLabel?`, `SymbolicProg.validateDefinitions`,
`SymbolicProg.callsOk`, `SymbolicProg.erase` or `SymbolicFunc.erase`, because
every production obligation here (`resolve _ = .ok _`,
`SymbolicProg.erase _ _ = _`, `findLabel? _ = some _`, `callsOk _ = true`) is an
equation and therefore has `Eq` at its head; and `goal-head:LinkCertificate`
matches certificate construction, which is the one goal in the flow whose head
really is one of this module's declarations.  A `goal-head:resolve` trigger would
never have fired.

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
condition reads the block environment can discharge (DRIP's
`soundAdmitted_of_stepClosedAt`).

For deployed bytecode with a certified `CodeSem`, use `ContractSpecSem.ofStorageOnly`
in the same module. Its `ofStorageOnly_preInv_iff` and `ofStorageOnly_postInv_iff`
reduce semantic frame invariants to the supplied storage predicate. These adapters
supply only balance/transfer transport; the caller still proves concrete frame
preservation from the incoming invariant and independently established admission.

### C8. A `decide +kernel` over a committed artifact reports kernel deep recursion

Cut the equality rather than raising a ceiling. `eq_of_take_drop_eq` in
[`Blanc/ChunkedDecide.lean`](../Blanc/ChunkedDecide.lean) takes a cut point `n`
and reduces `l = r` to `l.take n = r.take n` and `l.drop n = r.drop n`, each of
which is decided on its own; nest it for more than two chunks. A closed
`decide +kernel` over a `List` equality unfolds `List.decEq` once per element,
so the cost is the list's length and nothing else, and the length is what
predicts the failure: on Lean 4.34, measured by A/B over one committed
artifact, a list of 3,813 elements is checked and one of 4,200 is not. Blanc's
call sites cut at 2,200, roughly half that cliff, so margin rather than the
fewest cuts is the chunk-size rule. An `Option`-valued compile equation is not
directly chunkable — move through the module's own compiler witness first to
turn `Prog.compile … = some X` into the underlying `Bytes` equality, then cut
that. Several cut chunks decided in one tactic block can exhaust the heartbeat
budget instead; split the conjunction into one declaration per chunk, because
both budgets are per-declaration. The lemma changes no statement, emits no
byte, and needs neither `native_decide` nor a `maxRecDepth`/`maxHeartbeats`
raise.

### C9. I need to verify deployed bytecode Blanc did not compile

The route is lift, then reason about the lifted program. A certificate is
checked against the bytes by the kernel, a generic theorem turns every real
execution into a run of the lifted program, and the contract's properties are
proved over that run. The deployed WETH9 (`Blanc/Lift/Weth9/`) and the deployed
beacon deposit contract (`Blanc/Lift/BeaconDeposit/`: loops, SHA-256 precompile calls,
dynamic ABI decoding, events) are the worked examples; every module below is
contract-neutral.

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
  by deployed Lido bytecode, `EXTCODEHASH` (USDC V2 and V2_1, whose exact pushed word
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
  copies `checkNodeT`/`jumpsOkNodeT` and rewrite back with `checkNodeT_eq`/
  `jumpsOkNodeT_eq` (`CodeTries.ofCode`) in
  [`Blanc/Lift/CheckFast.lean`](../Blanc/Lift/CheckFast.lean): plain byte reads
  are linear per instruction and a 1,474-node entry of the 6,358-byte beacon
  deposit contract passed 16 GiB, while the trie decides it in 6 s / 3.4 GiB
  (`Blanc/Lift/BeaconDeposit/Check.lean` is the template).
- Assemble a single-entry non-memory certificate with `Cert.check_singleton` in
  [`Blanc/Lift/CheckAssembly.lean`](../Blanc/Lift/CheckAssembly.lean). Supply the
  existing startup Boolean and sole `checkNode` result; the theorem preserves
  the ordinary `Cert.check` proposition. The registered producer uses it for
  singleton checks, including the final owner of split check files.
  Its jump counterpart `Cert.jumpsOk_singleton` takes the sole `jumpsOkNode`
  result; hand-written single-entry `Jumps` modules call it directly.
- Assemble a seven-entry non-memory certificate with `Cert.check_seven` and its
  jump counterpart `Cert.jumpsOk_seven` in the same module: supply the seven
  per-entry `checkNode`/`jumpsOkNode` results plus the startup Boolean (check
  only). The registered producer emits a call to `check_seven` in its opt-in
  `seven` assembly mode (`check.assembly`), so sibling seven-entry
  certificates share the assembly instead of repeating the generic
  conjunction; hand-written `Jumps` modules call `jumpsOk_seven` directly.
- Assemble a two-entry non-memory certificate with `Cert.check_two` (the two node checks plus
  the startup Boolean) in [`Blanc/Lift/CheckAssemblyPair.lean`](../Blanc/Lift/CheckAssemblyPair.lean),
  emitted by the registered producer in its opt-in `two` assembly mode (`check.assembly`); its own
  module, so adding it rebuilt no existing certificate.
- Assemble a long non-memory certificate (180 entries, the USDC implementation) without
  unfolding its entry list: `Cert.checkAll`/`Cert.jumpsAll` over the tails `c.drop k`, the chain
  steps `Cert.checkAll_drop`/`Cert.jumpsAll_drop`, the ends `Cert.checkAll_drop_length`/
  `Cert.jumpsAll_drop_length` and the assemblies `Cert.check_of_checkAll`/`Cert.jumpsOk_of_jumpsAll`
  in [`Blanc/Lift/CheckChain.lean`](../Blanc/Lift/CheckChain.lean), emitted by the registered producer in its opt-in `chain`
  assembly mode (`check.assembly`/`jumps.assembly`); the non-memory counterparts of
  `Cert.checkEntriesM_drop`/`Cert.jumpsEntriesM_drop`. Worked use: `Blanc/Lift/Usdc/Impl/Check.lean`.
- Assemble the free-pointer check of a long certificate from per-entry kernel decisions: `fpEntry`
  (entry `k` under its annotation, `false` past either end), `fpFrom` over the tails
  `(c.zip ann).drop k`, the step `fpFrom_step`, the end `fpFrom_of_le` and the assembly
  `fpCert_of_fpFrom` in [`Blanc/Lift/FreePtrChain.lean`](../Blanc/Lift/FreePtrChain.lean), emitted by
  the registered `scripts/lift/fp_annot.py` (registry key `fp`). Worked use:
  `Blanc/Lift/Usdc/ImplFp/Check.lean`, `Blanc/Lift/Usdc/ImplFp.lean`. For any other annotated
  per-entry check, instantiate the generic kit there: `chainEntry`/`chainFrom` over a check
  function, with `chainFrom_step` and `chainFrom_of_le`.
- Assemble the write-site check of a long certificate the same way: `wsEntry`, `wsFrom`,
  `wsFrom_step`, `wsFrom_of_le` and `wsCert_of_wsFrom` in
  [`Blanc/Lift/WriteSiteChain.lean`](../Blanc/Lift/WriteSiteChain.lean), emitted by the registered
  `scripts/lift/ws_annot.py` (registry key `ws`). Worked use: `Blanc/Lift/Usdc/ImplWs/Check.lean`,
  `Blanc/Lift/Usdc/ImplWs.lean`.
- To relate the unsigned ABI word-length guards to a natural calldata bound,
  use `word_calldata_guards_iff` in
  [`Blanc/Lift/CalldataGuards.lean`](../Blanc/Lift/CalldataGuards.lean).
  With both the actual calldata length and argument-byte count below `2^256`,
  the guards `4 ≤ length` and `n ≤ length - 4` on words are equivalent to
  `n + 4 ≤ length` on naturals. The representability hypotheses are explicit;
  a modular length alone does not establish the natural bound. This arithmetic
  equivalence has no execution-relation trigger, so discovery stays here.
- Execution to lifted run (safety): `lift_sound`, and `lift_sound_in`, which
  keeps each step's derivation (`StepIn`) for arguments about re-entrant child
  frames, in [`Blanc/Lift/Sound.lean`](../Blanc/Lift/Sound.lean).
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
- For crossing solc's word-copy loop without knowing the copied bytes, use
  [`Blanc/Lift/CopyLoopKeep.lean`](../Blanc/Lift/CopyLoopKeep.lean):
  `copy_loop_keep` (under the memory potential the loop leaves every byte below
  the destination alone and exits with `len ≤ i'`).
  `copy_loop_keep_nonstorage` shares that proof without a fork premise; the
  original interface remains a compatibility projection.
- For the free-pointer checker's memory effect, use
  [`Blanc/Lift/FreePtrMem.lean`](../Blanc/Lift/FreePtrMem.lean): `FpWord`
  (the pointer word's meaning), `memEff_fpWord`, `memEff_touched`,
  `memEff_obs` and `memEff_mload_top`. `memEff_fpWord_noStateGas` uses the
  executing rules' state-gas absence with the same checker and memory-effect
  proof; `memEff_fpWord` retains its original covered-fork interface.
- For the static code an instruction reads, use
  [`Blanc/Lift/MemPotential.lean`](../Blanc/Lift/MemPotential.lean):
  `Ninst.step_withCode` (only `CODESIZE`/`CODECOPY` read the static code),
  `codeAt`/`codeAt_at`/`codeAt_size` (the code that decodes to one
  instruction at `pc` and to the implicit `STOP` after it),
  `getInst_of_size_le` (past the end of the code the decoder yields that
  `STOP`), and `Evm.step_stop_of_size_le` (the implicit `STOP` halts with
  the machine unchanged).
- For the free-pointer checker's facts and their soundness, use
  [`Blanc/Lift/FreePtr.lean`](../Blanc/Lift/FreePtr.lean),
  [`Blanc/Lift/SymTransfer.lean`](../Blanc/Lift/SymTransfer.lean), and
  [`Blanc/Lift/FreePtrFacts.lean`](../Blanc/Lift/FreePtrFacts.lean):
  `Fact.Holds`/`AllHold` (the meaning of facts under a symbol valuation),
  `bnd2_sound`/`entails_sound` (the interval reading and entailment),
  `opFacts_sound` (the facts about an instruction's fresh result),
  `learn1_sound` (what a `JUMPI` arm learns), and `transfer_val` (symbols
  through an instruction's stack transfer). The interval folds both bound
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
  frame-size, one-fresh-result and index-map hypotheses; the original modern
  `transfer_val` statement remains a wrapper. Its existential result requires
  these joint transfer/run premises, so discovery remains in this registry.
- For the free-pointer checker's soundness, use
  [`Blanc/Lift/FreePtrSound.lean`](../Blanc/Lift/FreePtrSound.lean) and
  [`Blanc/Lift/FreePtrSoundStep.lean`](../Blanc/Lift/FreePtrSoundStep.lean):
  `fpRun_sound` (every run of an accepted certificate reads a good free
  pointer, `FpStep`), `lift_sound_fp` (the same from `Cert.check` and a
  successful frame), `fp_run` (the big-step recursion), `fstep_sound`
  (one accepted step keeps the invariant `FpInv`), and the frame-length facts
  `mapM_length` (an `Option` `mapM` keeps length), `foldTop_length` and
  `transfer_length_mono`. The `rdsKeep_sound_noStateGas`,
  `fstep_sound_noStateGas`, `fp_run_noStateGas`, `fpRun_sound_noStateGas`
  and `lift_sound_fp_noStateGas` variants use the executing rules'
  `stateGas = none`. They share the original induction and checker, retaining
  the actual `Exec` and `StepIn` witnesses; modern interfaces remain projections.
  The USDC worked specialization `implRun_fp_noStateGas` in
  `Blanc/Lift/Usdc/ImplFp.lean` applies that capability to the existing checked
  annotations and the same original successful implementation run.
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
  (every run of an accepted certificate's entry `0` is a `WsStep` run), `lift_sound_ws` (the
  same from `Cert.check` and a successful frame), `ws_run` (the big-step recursion: `WsStep`
  steps, `RetObs` at a return), `goto_run` (an accepted goto: `compat` or a tail call, under a
  summary below the jumper's, via `retLe_steps`, `argFree_steps`, `RetObs.of_retLe`,
  `RetObs.of_callee` and `tail_entry`), `Term.eval_argFree` (an entry-word-free term reads the
  same in every environment of a frame), and `SFunc.RunP.mono_at` (a run under a step relation
  implied at the run's own frame).
  The capability forms `WriteSite.wstep_keeps_noStateGas`,
  `WriteSite.ws_run_noStateGas`, `WriteSite.wsRun_sound_noStateGas` and
  `WriteSite.lift_sound_ws_noStateGas` require selected `stateGas = none`
  instead of modern coverage. They retain the original accepted certificate,
  frame/run and summary premises, with the same `WsStep`/`RetObs` meanings;
  the byte-facing endpoint still takes an actual successful frame and
  preserves its `StepIn` relation. Historical membership supplies the
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
  `SProg.RunP.point` turns any run transformer (e.g. a locality law proved by
  `SProg.RunP.mono`) into a step transformer. At a history frame,
  [`Blanc/Lift/WriteSiteReachHistory.lean`](../Blanc/Lift/WriteSiteReachHistory.lean):
  `ConfiguredHistoryTraceIn.exists_retainedSstore_frame_wsObs` adds, to the attribution of
  `exists_retainedSstore_frame_sstoreCursor`, the `WsObs` at the write's node for every
  certified code and accepted write-site annotation of the attributing frame.
  For a successful raw store, `WriteSite.successfulSstore_site` takes the checked
  code and write-site annotation, pc-zero entry, `stateGas = none`, and the actual
  `ParentPrefix` and `successfulSstore?` equation. It returns a root site with its
  slot denotation, guards and nonincrease implication at the same node's current
  storage cell. `ConfiguredHistoryTraceIn.rawFrame_successfulSstore_site` obtains
  the entry facts from raw-frame membership and the history's capabilities.
  This also covers stores in frames that later revert; it does not assert
  retention, hash separation, or coverage of unexecuted descriptors. The V1
  mapping producer and all-version raw allowance classifier use this shared
  extraction. These existential site results have no reliable registered
  goal-head trigger; use this branch rather than a broad `Exists` recipe.
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
- For a `DELEGATECALL` whose child must be inspected, use
  [`Blanc/Lift/DelegateCallChild.lean`](../Blanc/Lift/DelegateCallChild.lean): `ri_delegatecall_child`
  (after a lifted `DELEGATECALL` step: the success flag, and when set a successful child `Exec 0` that runs
  the target's code on the input window from an empty machine with the parent's code and `benvStat`, its
  output written into the output window), `delegatecall_generic` and `Frame.ofCall_enter_not_done`.
  `delegatecall_generic_noStateGas` and `ri_delegatecall_child_noStateGas`
  use the executing access/delegation rules and state-gas absence, retaining
  the same actual child, block statics, code and output-window witnesses.
- For crossing a silent internal call under any step relation, use
  [`Blanc/Lift/SilentCallP.lean`](../Blanc/Lift/SilentCallP.lean): `ricP_call_silent`, the `RunCutP P` form
  of `ric_call_silent`, with a no-halt set so the callee must return.
  `ricP_call_silent_noStateGas` consumes the executing rules' state-gas absence
  and keeps the same state equality and returned stack.
- For a callee that cannot return, use
  [`Blanc/Lift/NodeRet.lean`](../Blanc/Lift/NodeRet.lean): `RetClosed` (a node
  predicate with `checkNode`'s return discipline), `SFunc.RunP.ret_mem` (a
  returning run starts from a frame holding `.ret`) and
  `SFunc.RunP.not_returned_of_noRet` (a callee whose frame has no `.ret` never
  returns), bytes-free and for any step relation.
- For write-site provenance terms and the generic locality corollary, use
  [`Blanc/Lift/WriteSite.lean`](../Blanc/Lift/WriteSite.lean),
  [`Blanc/Lift/WriteSiteTerm.lean`](../Blanc/Lift/WriteSiteTerm.lean),
  [`Blanc/Lift/WriteSiteObs.lean`](../Blanc/Lift/WriteSiteObs.lean), and
  [`Blanc/Lift/WriteSiteLocality.lean`](../Blanc/Lift/WriteSiteLocality.lean):
  `Term.den_subst` (instantiating a callee's term at a call site is sound)
  and `ws_locality_keys` (every `SSTORE` at a protected slot is
  non-increasing or happens in an allowed frame).
- For write locality at one owner's rows of a solc two-level mapping
  (`m[p][g]` at `mapSlot g (mapSlot p b)`) over a certificate's root sites, use
  [`Blanc/Lift/WriteSiteRows.lean`](../Blanc/Lift/WriteSiteRows.lean):
  `ws_row_locality` (`ws_locality_keys` at a row-or-raw key type, so every
  listed site, `top` included, names a key) under the frame-local collision
  premise `RowSep`, with `rowOf`/`rowOf_eval` (a row slot term's owner and key)
  and `GuardObs.mono`.
- To identify a slot term from a site's leading selector guard, use
  [`Blanc/Lift/WriteSiteSelector.lean`](../Blanc/Lift/WriteSiteSelector.lean):
  `Site.slotSelectorCheck` checks the selector/slot correspondence over a
  supplied descriptor list, and `Site.slot_eq_iff_of_selectorCheck` applies
  it to a member whose actual guards hold. Additional guards are permitted;
  the first guard must still be the specified selector term, and the checked
  slot/selector equivalence is unchanged. Supply the known selector term;
  the conclusion concerns its evaluated word. This does not produce an
  execution occurrence, hash witness, or separation premise. It serves the
  existing V1 adapter, V2/V2_1 blacklist collectors and modern caller-key
  collector (including V2_2 descriptors with extra guards).
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
  the concrete destination bytes and back edge. The USDC clearing consumer
  specializes this common proof. These observations need no slot separation,
  but neither establish an initial zero seed nor preserve an arbitrary
  nonzero administrative word when a cleared cell aliases it.
  For the legacy layout with extra push/swap staging and an indirect return,
  `legacyBody_store_cut` derives the actual zero store and its continuation;
  `legacyRunP_zeroStores_noExec` follows both the head and return table entries.
  It shares the comparison and back-edge fold with the compact layout. The
  concrete [`OldInitializerV1Clearing`](../Blanc/Lift/Usdc/OldInitializerV1Clearing.lean)
  theorems `v1Clear_zeroStores_noExec` and `v1ClearEntry_zeroStores_noExec`
  instantiate the actual V1 clearing head and helper prefix, retaining the
  original `StepIn R` relation and outcome. They require no memory bounds,
  nonwrapping arithmetic or initial zero seed; whole-initializer coverage
  and historical execution remain separate obligations.
  For a string allocation that stores a length header then copies bytes,
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
  state-silent prefix under any stronger step relation (`lstep`, `ldest`,
  `Lifts.trans`). `Blanc/Lift/Usdc/OldInitializerV1Staging.lean`
  (`wrapper_strengthen`, `wrapper_stage`) is the worked three-string example
  and `Blanc/Lift/Usdc/OldInitializerV1Callee.lean` (`initialize_observed`)
  uses the rebuild to classify the whole wrapper run.
  For the source-shaped memory-to-storage payload loop, use
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
  The concrete V2 consumer in
  [`Blanc/Lift/Usdc/OldInitializerEffects.lean`](../Blanc/Lift/Usdc/OldInitializerEffects.lean)
  derives `implV2_initializeV2_observed` from successful fresh execution with
  `stateGas = none` and the actual initializer selector: every store targets metadata key4/15/18,
  writes zero, or targets a bounded modular payload word of the actual long
  decoded name; the same route has no external instruction. The wrapper
  derives its calldata bounds. `implV2_initializeV2_writeClass` projects
  the write classification. `implV2_initializeV2_short_nonInc` and
  `implV2_initializeV2_short_zero` require an actual decoded length at most31
  and separation from the three fixed keys; the latter also requires the
  initial zero seed. They do not establish the historical name profile,
  seed, long-payload separation or arbitrary nonzero-word preservation.
  When a caller continues after such a storage-string helper, use
  [`Blanc/Lift/SolcStorageReturn.lean`](../Blanc/Lift/SolcStorageReturn.lean)
  for what the helper returns: `legacyRunP_returned` gives the returned stack
  and unchanged memory of a legacy clearing run, `payload_exit` reaches the
  payload loop's exit tail with the same stack tail under `Keeps` memory, and
  `runCutP_done` turns a finished cut run into an ordinary run. It also holds
  fork-free `SLOAD`/`SSTORE` walk inversions with exact memory
  (`ri_sload_any`, `ri_sstore_any`) and the branch/jumpdest rebuilders
  `qdest`, `qbranch`, `qbranchTo` for strengthening a run in place.
  [`Blanc/Lift/Usdc/OldInitializerV1Callee.lean`](../Blanc/Lift/Usdc/OldInitializerV1Callee.lean)
  is the worked V1 consumer (`callee_obs`).
  [`Blanc/Lift/Usdc/OldInitializerV1Root.lean`](../Blanc/Lift/Usdc/OldInitializerV1Root.lean)
  composes it with the original successful fresh V1 execution as V2 does:
  `implV1_initialize_observed` walks the actual dispatcher (free-pointer
  store, `div`/`and` selector, comparison chain, nonpayable entry 60), which
  derives the wrapper-entry seams, and lifts by `lift_sound_in_noStateGas`
  and `FreePtr.SFunc.RunP.withPot`. Its local premises are `stateGas = none`
  (`_hist` discharges it from `HistFork`) and the initial potential
  `pre.gasMeasure < 2 ^ 256`. `implV1_initialize_writeClass`,
  `implV1_initialize_short_nonInc` and `implV1_initialize_short_zero`
  (fork-free, through `progRunP_zero_noExec`) mirror the V2 consumers; they
  do not establish the historical string profile, seed or payload-key
  separation.
  At a raw frame of a `ConfiguredHistoryTraceIn`, the root form of both
  classifiers comes from the history:
  [`Blanc/ExecutionStagedRootFacts.lean`](../Blanc/ExecutionStagedRootFacts.lean)
  `ConfiguredHistoryTraceIn.rawFrame_entryFacts` gives pc zero, the selected
  fork, `stateGas = none`, fresh stack and memory and `gasMeasure < 2 ^ 256`
  from `BodyStageCapabilities` alone. For historical initializer writes, use
  `ConfiguredHistoryTraceIn.initFrame_sstore` and `initRowWritesNonInc` in
  [`Blanc/Lift/Usdc/InitRowsHistory.lean`](../Blanc/Lift/Usdc/InitRowsHistory.lean):
  the node-level classifier covers prefixes of raw frames, including delegated
  children and reverted executions, with the explicit finite `InitRowsApart`
  separation premise.
  [`Blanc/ExecutionStagedSstoreAttribution.lean`](../Blanc/ExecutionStagedSstoreAttribution.lean)
  `ConfiguredHistoryTraceIn.rawFrames_closed` (with the stage and staged-body
  forms) closes the raw frames under descent, and
  `ConfiguredHistoryTraceIn.exists_retainedSstore_frame` attributes a cell
  changed by a committing raw frame's own derivation, at an owner with code at
  its entry, to the last retained successful `SSTORE` of that cell: the write
  lies on the same-frame prefix of a committed frame of that derivation, which
  is a raw frame of the history executing at the owner. It is per raw frame;
  relating checkpoint and endpoint storage across transaction settlement is
  not part of it.
  The allowance-locality laws have the same historical form in
  [`Blanc/Lift/Usdc/AllowLocalityHistory.lean`](../Blanc/Lift/Usdc/AllowLocalityHistory.lean):
  `implV1Run_ws_noStateGas`, `implV2Run_ws_noStateGas`,
  `implV2_1Run_ws_noStateGas` and `implRun_ws_noStateGas` instantiate
  `lift_sound_ws_noStateGas`; `implV1/V2/V2_1/V2_2_allowLocality_noStateGas`
  and `implV1_allowLocality_observed_noStateGas` take `stateGas = none` in
  place of `CoveredFork` with unchanged conclusions. For V2, V2_1 and V2_2 the
  `_selectorObserved_noStateGas` forms read the exception at the frame's
  selector. V2 and V2_1 take a `NeutralFork`, a fresh entry and a non-delegated
  address 1, and their owner arm is the native `OldUsdcNativePairAnswer`, as in
  `implV2_allowLocality_observed`; V2_2's owner arm stays calldata word 4. The
  `implV*_allowLocality_rawFrame` forms take `stateGas = none` and the fresh
  entry from `rawFrame_entryFacts` and keep success, code and `RowSep` as frame
  facts; V2 and V2_1 add `rules.bal = none` on the history's forks and address
  1's code without a delegation designator.
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
  per-instruction facts `absMem_sound`, `memTop_sound`, `step_mem_sound` (covered
  fork), `staticcall_run_memory` (a `STATICCALL` changes memory only inside its
  output window), `Mem.write_agree` (needs no `Mem.Wf`), `Mem.extends_agree` and
  `Mem.AgreeOutside.trans`/`.mono` in
  [`Blanc/Lift/MemMap.lean`](../Blanc/Lift/MemMap.lean); `lift_soundM` in Sound,
  `lift_exactM`/`Cert.jumpsOkM` in Exact, trie mirrors `checkNodeMT`/`jumpsOkNodeMT`
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
- Every execution prefix to a certificate node (all outcomes, no success
  premise): the certificate cursor `Cursor`/`Cont`, its invariant `CursorOK`
  (checked node, pc, stack segments matched per pending function), the
  synthetic step `SStep`, `cursor_start`, `cursor_step` (one `ParentStep`,
  including a `CALL` over a child of any outcome, is one `SStep`) and
  `cursor_of_parentPrefix`, with `CursorOK.exec_spawn` (a reached node spawns
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
- To discharge `SpawnKinds ca sem` without a certificate cursor (a `Cert.checkM`
  certificate has none), decide `callKindsCheck code` for the runtime bytes and apply
  `spawnKinds_of_callKindsCheck` (needs only `sem.Run sevm pre post → sevm.code = code`):
  `Exec.Deriv.ParentPrefix.noPush` keeps every same-frame chain node at a position no
  `PUSH` immediate covers, and `callKinds_of_check` refuses every external instruction but
  `CALL`/`STATICCALL` there; the walk reads `code.data.toList`, so the kernel decision is
  linear, in [`Blanc/Lift/SpawnKindsM.lean`](../Blanc/Lift/SpawnKindsM.lean).
- To show that every raw frame a successful frame enters lies under a direct *committed*
  child (no failed or reverted child frames), when its code tests every call's success flag,
  decide `guardCheck code` for the runtime bytes (each `CALL`/`STATICCALL` at an instruction
  start is followed by `PUSH2; JUMPI` falling through to `PUSH1 0; DUP1; REVERT`, or is an
  identity copy `PUSH1 4; GAS; CALL`) and apply `Exec.rawFrameDescendants_of_guardCheck_entry`
  (premises: covered fork, `4` a precompile and undelegated at entry, committed children keep the
  code at `4`), in [`Blanc/Lift/GuardedCalls.lean`](../Blanc/Lift/GuardedCalls.lean).  The same
  module proves the linear walk's predecessors unique (`PushReach.succ_inj`) and where a continued
  step lands (`Evm.step_cont_succ`).
- To know what a direct committed child of a call-only frame runs, use
  `Exec.childFrames_code` (a child at an address holding nonempty undelegated code at the frame's
  entry runs that code; `Xinst.step_staticcall_spawn` is the `STATICCALL` sibling of
  `Xinst.step_call_spawn`), and for a child of spawn-free code `Exec.Frame.keeps_of_spawnFree`
  (it keeps every other address's code and the storage of every other address with code), in
  [`Blanc/Lift/ChildFrameCode.lean`](../Blanc/Lift/ChildFrameCode.lean).
- To know what a direct committed child of a depth-`1` frame keeps whatever code it runs, use
  `Exec.childFrames_keeps_of_depth_one` (it keeps every other address's code and the storage of
  every other address with code: a depth-`0` frame enters no frame,
  `Exec.rawFrameDescendants_eq_nil_of_depth_zero`; `Exec.childFrames_depth` bounds a child's depth),
  in [`Blanc/Lift/ChildFrameDepth.lean`](../Blanc/Lift/ChildFrameDepth.lean).
- To know where every log of a committed execution came from, use `Exec.log_addresses` (each
  post log is an entry log or was emitted at the current target of one of the execution's raw
  frames), e.g. to show no log comes from the deposit contract when the raw frames' targets are
  known, in [`Blanc/Lift/LogAddresses.lean`](../Blanc/Lift/LogAddresses.lean).
- A frame predicate at every reachable cursor node: [`Blanc/Lift/CursorFrames.lean`](../Blanc/Lift/CursorFrames.lean).
  `SFunc.framesSat es P` walks a tree with the abstract frames the checker computes and checks
  `P n a` at every straight-line node; `Cert.framesSat` over every entry gives
  `Cursor.framesSat_of_reachable` (through `SStep.framesSat`), `CursorOK.framesSat_exec` applies `P`
  to a cursor-placed node's actual instruction and abstract frame, and `CursorOK.stack_const` with
  `FrameMatches.getElem?_const` reads a `.const` frame position as the actual stack word. Worked
  uses: `Blanc/Lift/QuietDelegateSkip.lean`, `Blanc/Lift/Usdc/ImplFrames.lean`.
- Sharpening a checked certificate's declared entry frames without re-deciding every entry:
  [`Blanc/Lift/CertRefine.lean`](../Blanc/Lift/CertRefine.lean). `Cert.refine c k i v` replaces position `i` of entry `k`'s
  frame and keeps every tree (`Cert.refine_prog`, `Cert.refine_getElem?_ne`);
  `Cert.check_of_agree` reduces the refined certificate's `Cert.check` to the entries of a list `T`
  (re-decided through `Cert.entryOk`, trie form `Cert.entryOkT` with `Cert.entryOkT_eq`) when every
  other entry is unchanged and references no refined entry (`checkNode_congr`). Worked use:
  `Blanc/Lift/Usdc/ImplFrames.lean`.
- To carry an exact fact forward from one certificate node to a later one along a frame's chain
  (for example, that a `CALL`'s target operand is the result of an earlier `CREATE2`), use a
  *window* in [`Blanc/Lift/CursorWindow.lean`](../Blanc/Lift/CursorWindow.lean): a finite list of
  trees, each with its one predecessor and an index (`WindowEntry`); `Cert.windowOk E sites` checks
  over the whole certificate that a window tree occurs only as a child of its predecessor and that
  every `CALL` node is one of `sites`; along a checked chain (`Cursor.Checked`, `.step`,
  `.entrance`, `.callSite`) `window_track` carries a property `Track j` one window edge at a time,
  with no backward walk. Decide `Cert.windowOk` in its own module. The exact stack words the window
  edges carry come from [`Blanc/Lift/PrefixTransfer.lean`](../Blanc/Lift/PrefixTransfer.lean):
  `prefixTransfer` runs `ninstTransfer` on a prefix pattern of the stack, keeping `PUSH` literals
  and `AND`s of known words (`padPattern` extends a short prefix for `DUP`/`SWAP`), with
  success-only soundness `prefixTransfer_run`; `create2_run_result` and `genericCreate_result` give
  the word a successful `CREATE2` leaves (the new address or zero). Worked use:
  `Blanc/Lift/UniswapV2Factory/Window.lean` and `CallShape.lean` (`factory_call_target`).
- To retain an observation of each full synthetic configuration edge, use
  [`Blanc/Lift/ObservedReach.lean`](../Blanc/Lift/ObservedReach.lean).
  `ObservedReach` pairs the existing `ConfStep` with a before/after `Conf`
  predicate; `.forget` erases observations and `.of_reach` instantiates them
  with `True`. This relation adds no interpreter or actual-node premise;
  the observation producer must supply provenance. No automatic recipe is
  registered for this relation-construction interface.
  To isolate an internal callee under a continuation that may itself store, use
  [`Blanc/Lift/ObservedReachSplit.lean`](../Blanc/Lift/ObservedReachSplit.lean).
  `ObservedReach.split` keeps every edge observation: either the target remains
  inside the callee under the lifted observation predicate, or its returning
  `RunPS` has both the original observed prefix and continuation suffix.
  `ObservedReach.return_of_sstoreFree` specializes the return case when only
  the callee is checked store-free, retaining both observed cuts and its actual
  returning run. `ObservedReach.below` restores lower continuations; `ObservedKeccak.below`
  lifts the same successful hash edge with unchanged input and source shape.
  The general split assumes neither store-free continuations nor final-frame
  success or fresh hashes.
  The joint reach/continuation decomposition has no reliable goal-only trigger,
  so this interface has no automatic recipe.
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
  exact read input and source shape. Its `.of_next` and `.actual` adapters in
  [`Blanc/Lift/CursorKeccak.lean`](../Blanc/Lift/CursorKeccak.lean) retain the successful
  `Exec.NinstOccurrence`, same source cursor and explicit cut before the
  original stop. `KeccakBefore` packages that actual successful occurrence,
  its pc, exact input, 0/64 stack and ordered raw-prefix edge before the stop.
  These facts do not produce a hash census or freshness.
  For two hashes whose relative order matters, use
  [`Blanc/Lift/CursorKeccakOrder.lean`](../Blanc/Lift/CursorKeccakOrder.lean).
  `ObservedKeccak.of_next_linked` retains the first hash's after-configuration;
  `ObservedReach.withPrefix` carries the remaining segment into the second
  observation. `ObservedKeccakPair.actual` converts that joined pair to
  `KeccakPairBefore`: successful original occurrences with the first successor
  preceding the second occurrence and the second successor preceding the stop.
  `ObservedKeccakPair.forget` projects the individual observations. The proof
  uses `Cursor.RawEdgeAt.gasMeasure_lt`, `ObservedReach.raw_gasMeasure_le`,
  `parentPrefix_of_gasMeasure_le` and `keccakOccurrence_of_parentPrefix` to
  relate the observed segment to actual derivation positions. No hash
  injectivity, final-frame success or numeric pc order is assumed.
  `KeccakPairBefore.forget` projects both individual earlier-occurrence witnesses.
  The `ordered-observed-keccak-pair` recipe matches the ordered package goal.
- To identify the pc of an already supplied checked cursor from a literal
  byte prefix, use [`Blanc/Lift/CursorCheckPrefix.lean`](../Blanc/Lift/CursorCheckPrefix.lean).
  `bytesAt_append` joins adjacent checked slices; `checkNode_bytesAt_prefix`
  reads the bytes of a literal `List Ninst` prefix from the same final check.
  `CursorOK.bytesAt_of_prefix` uses the actual cursor and tree identity, and
  `CursorOK.pc_eq_of_prefix_singleton` shortens those bytes and applies an
  exact `BytePattern.occurrences` singleton, with no pc bound premise.
  `checkNode_nexts` also projects the check after the literal lead;
  `CursorOK.pc_add_eq_of_prefix_singleton` fixes its endpoint offset against
  a unique anchor from that same check. This is a static check projection,
  not an assertion that execution reaches a later instruction.
  These projections do not traverse execution, establish family reachability,
  or identify computed storage keys. No recipe is registered: the joint cursor,
  literal tree and singleton premises are not a reliable equality-goal trigger.
  The concrete [`Usdc/V1MinterReach.lean`](../Blanc/Lift/Usdc/V1MinterReach.lean)
  consumer derives the V1 removeMinter dispatcher/body path and retains the
  same final cursor: `successfulSstore_source` pairs each actual source pc
  with its computed base-12/base-13 key and exact SSTORE tail. Its first-store
  stop branch precedes any continuation to the second hash.
  [`Usdc/V1ConfigureMinterReach.lean`](../Blanc/Lift/Usdc/V1ConfigureMinterReach.lean)
  proves the configureMinter twin through its distinct V1 entry-65 wrapper,
  paused/master-minter guards and body, pairing 0x20b2/base12 or 0x20f6/base13
  at the same actual cursor, with the same first-store stopping boundary.
  Both family walks have observed variants; the original interfaces project them.
  [`Usdc/V1MinterHashOccurrences.lean`](../Blanc/Lift/Usdc/V1MinterHashOccurrences.lean)
  uses one synchronized prefix and the same final cursor to derive actual
  successful hashes before each reached store. `remove_successfulSstore_hashes`
  pairs 0x15f5→0x160b/base12 or 0x164d→0x1650/base13;
  `configure_successfulSstore_hashes` pairs 0x209c→0x20b2/base12 or
  0x20f3→0x20f6/base13. Each retains the exact account-word/base-word 64-byte
  input and original parent-prefix cuts. Hash pcs come from the same checked
  hash cursor's literal lead and the existing singleton store anchors.
  Collection and freshness remain separate. No recipe is registered for these
  contract-specific producers: their joint raw-prefix and selector inputs
  are not a reliable generic goal trigger.
- To advance a checked certificate cursor through an actual successful raw
  suffix, use [`Blanc/Lift/CursorCuts.lean`](../Blanc/Lift/CursorCuts.lean).
  `cursor_next_forward` derives the actual `ParentStep`, instruction witness
  with `Cursor.DescOf`, `SStep`, `ConfStep` and successor `CursorOK`.
  `cursor_jinst_forward` reuses the decoded jump edge; `cursor_branch_forwardH`
  (from `rules.stateGas = none`; `cursor_branch_forwardH_covered` is the `CoveredFork` form)
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
  `CursorStateAt.lineH` in `HistCursorCuts.lean` and its `jump` method apply
  source inverses to the actual primitive line or `ConfStep`, deriving the
  successor state and tree. Its `call` method and
  `CursorStateAt.retH` retain and consume the actual mapped internal continuation,
  preserving the complete non-gas state without requiring a gas schedule.
  `memory_eq` projects the symbolic memory without unfolding a concrete state.
- To cross a checked referenced goto while preserving the complete actual
  state and return continuation, use
  [`Blanc/Lift/CursorJump.lean`](../Blanc/Lift/CursorJump.lean).
  `CursorOK.jumpAt_of_jump` derives the actual JUMP byte from the checked node;
  `CursorStateAt.gotoH` (`gotoH_covered` is the `CoveredFork` form) consumes its actual
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
  frame, use `CursorOK.sourceRunReturn` in
  [`Blanc/Lift/CursorSourceRunReturn.lean`](../Blanc/Lift/CursorSourceRunReturn.lean).
  It keeps the supplied actual successful node and either its halted source
  outcome or the actual internal continuation `Exec`, complete returned state,
  checked caller cursor and structural subderivation relation. That relation
  alone does not assert a call-free predecessor gap; use `quietReturnH` for a
  body whose checked region excludes external instructions.
- To cross a checked reply flag and decode a physical memory word, use
  [`Blanc/Lift/HistCursorCalls.lean`](../Blanc/Lift/HistCursorCalls.lean).
  `CursorStateAt.callFlagH` derives success from the same actual suffix and
  crosses the literal flag guard. `CursorStateAt.returnWordH` derives the
  complete returndata width from that same checked node, then crosses the
  width guard and memory decoder. Both retain the complete world, symbolic
  memory, and mapped continuation. Consumers supply their literal source
  shapes and closed reverting arms; call identity remains with the actual
  occurrence carrier. Instantiate the pointer and allocated size explicitly
  when the physical memory is a nested image.
  Literal `returnWordGuardLine` and `callFlagGuardLine` definitions remain in
  [`Blanc/Lift/CursorBalanceReply.lean`](../Blanc/Lift/CursorBalanceReply.lean).
- To bind a GAS word and external call to an actual parent execution, use
  [`Blanc/Lift/HistCursorCalls.lean`](../Blanc/Lift/HistCursorCalls.lean).
  `CursorStateAt.gasCallH` derives the actual remaining gas from the supplied
  cursor and returns a `CallOccurrenceStep` owned by the supplied original
  root. It keeps the relative call-free gap, full request state, actual filled
  slot, returned cursor, and mapped continuation. Its same-frame prefix may
  start at an earlier returned parent; no gas schedule is assumed.
  [`Blanc/Lift/CursorGasCall.lean`](../Blanc/Lift/CursorGasCall.lean) remains an import
  compatibility module; the historical module owns the forwarder.
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
  `cursor_next_call_occurrence_forwardH` in `HistCursorCuts.lean` derives a
  `CallOccurrenceStep root x`
  from the supplied same-frame prefix, checked cursor and successful suffix.
  The carrier keeps the exact `NinstOccurrence`, decoded external instruction,
  same-frame `ParentStep` and complete returned `Devm`; its
  `occurrence_stepRun_unique` comparison preserves both recursive slot and
  step result. `CallOccurrenceStep.reRoot` transports that same call along a
  supplied earlier same-frame `ParentPrefix`; `reRoot_identity` exposes exact
  preservation of the node, instruction, recursive slot, step result and
  returned derivation. It changes only root-indexed reachability evidence.
  `CallOccurrenceStep.retained` additionally requires root
  commitment. Raw occurrence identity alone does not establish settlement,
  call-free predecessor gaps or a child's queue/path origin. The
  `SyncCanonicalResult.firstOccurrenceStep`/`secondOccurrenceStep` projections
  in [`SyncOccurrence.lean`](../Blanc/Lift/UniswapV2Pair/SyncOccurrence.lean)
  reuse the canonical witnesses definitionally and retain their ordered
  `ExecFreeUntil` gaps. This joint path/cursor/tree seam is discovered here;
  its existential result does not provide a reliable recipe trigger.
  On `stateGas = none` (historical forks) use
  [`Blanc/Lift/CursorOccurrenceNoStateGas.lean`](../Blanc/Lift/CursorOccurrenceNoStateGas.lean):
  `cursor_next_forward_noStateGas` and
  `cursor_next_call_occurrence_forward_noStateGas` take `stateGas = none` in
  place of `CoveredFork`. At a raw frame of a `ConfiguredHistoryTraceIn`,
  `ConfiguredHistoryTraceIn.rawFrame_reach_of_parentPrefix` places every
  same-frame node at a checked cursor reached by `StepIn` steps of that frame
  (entry facts from `rawFrame_entryFacts`), and
  `exists_retainedSstore_frame_reach` adds that cursor, for any certified code
  of the frame, to the attribution of `exists_retainedSstore_frame`;
  `exists_retainedSstore_frame_sstoreCursor` adds that the cursor's tree there is
  the checked `SSTORE` next node, with the write's key and value on top of the
  node's stack. A cursor-placed node decoding any instruction other than `PC`
  sits at that instruction's checked `next` node (`CursorOK.tree_of_ninst`,
  `CursorOK.tree_of_sstore`; `CursorOK.tree_of_exec` is the external case) in
  [`Blanc/Lift/CursorTreeNinst.lean`](../Blanc/Lift/CursorTreeNinst.lean).
- To preserve the original child-root predicate on a supplied actual call
  slot, use
  [`Blanc/Lift/CursorOccurrenceRoots.lean`](../Blanc/Lift/CursorOccurrenceRoots.lean).
  `CallOccurrenceStep.slotFilledWith` proves that exact occurrence slot is
  filled with `InRoots root`; `toStepIn` is its compatibility projection and
  keeps the same slot. Neither selects another call or filters the raw queue.
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
  `of_branchTo`/`of_callNext` are the supporting inversions. Worked use:
  `syncPc0_canonical_live` in
  [`Blanc/Lift/UniswapV2Pair/SyncGasCanonical.lean`](../Blanc/Lift/UniswapV2Pair/SyncGasCanonical.lean).
- To expose the six actual STATICCALL operands, use
  `cursor_staticcall_operands` in
  [`Blanc/Lift/CursorCuts.lean`](../Blanc/Lift/CursorCuts.lean). `CursorOK` and
  the exact next-staticcall tree force a six-word concrete stack prefix.
  No successful outcome, child context or settlement premise is needed.
  The existing forward-cut consumers can retain these operands at the same
  actual occurrence; the projection alone supplies no occurrence order.
- Every same-frame node with its machine state (all outcomes): the stateful
  prefix lift `reach_of_parentPrefix` (from `cursor_stepS`, which adds one
  `ConfStep` to each `cursor_step`) places the node at a `Reach (StepIn R)` from
  entry `0`, and `CursorOK.tree_of_exec` puts an external instruction at its
  `next` node, in `Blanc/Lift/Cursor.lean`. The configurations, steps and walk
  inversions (`Conf`, `ConfStep`, `Reach`, `AtExec`, `Reach.next`/`exec`/`dest`/
  `branch`/`branchTo`/`jump`/`call`/`pcAt`, and `Reach.split`, which turns a
  returning callee into an ordinary big-step `SFunc.RunP … (.returned d)` so the
  big-step callee specs are reused) are in
  [`Blanc/Lift/Reach.lean`](../Blanc/Lift/Reach.lean). Use them for a prefix
  fact of a certified frame, e.g. a storage invariant at a spawning node.
  The walk kit over the state `St b S M G` (`rr_next`, `rr_dest`, `rr_branch`,
  `rr_callOver` for an exec-free callee crossed as a big-step run, `rr_callInto`
  when the target lies inside the callee), the exec-free region refutation
  `Reach.false_of_execFree` with its decidable `ExecFreeSet`/`SFunc.execFreeIn`,
  the dispatcher lemma `Reach.gotoTree` and `Reach.lastExec` (register steps up
  to the last external instruction, `regSilent`) are in
  [`Blanc/Lift/ReachWalk.lean`](../Blanc/Lift/ReachWalk.lean); worked use: Lido
  `lido_spawnEntry` in `Blanc/Lift/LidoCircuitBreakerDeployed/Reentry.lean`. Use it for safety facts
  about reverting or out-of-gas frames, which `lift_sound` cannot see.
- The same walk to an `SSTORE` target (`AtSstore`): `Reach.nextS`/`destS`/`branchS`/
  `branchToS`/`jumpS`/`callS`/`not_lastS`/`not_ret_nilS`, `Reach.sstoreS` (stop at the
  `SSTORE` or step past it), the `SSTORE`-free refutation `Reach.false_of_sstoreFree`
  with its decidable `SstoreFreeSet`/`SFunc.sstoreFreeIn`, and the state kit `rs_next`,
  `rs_dest`, `rs_branch`, `rs_branchTo`, `rs_jump`, `rs_callOver`, `rs_callInto` in
  [`Blanc/Lift/ReachWalkSstore.lean`](../Blanc/Lift/ReachWalkSstore.lean); with
  `reach_of_parentPrefix_noStateGas` and `CursorOK.tree_of_sstore` it names the key and
  value of every `SSTORE` a certified frame reaches, whatever its outcome. Worked use: USDC
  `Proxy.proxy_sstoreNodeH` in `Blanc/Lift/Usdc/ProxySstoreH.lean`.
  The shared `Proxy.proxy_sstoreCursorH` also retains the checked cursor and
  continuation geometry. `Proxy.proxy_implSstore_emitsUpgraded` in
  [`Blanc/Lift/Usdc/ProxyUpgradeLog.lean`](../Blanc/Lift/Usdc/ProxyUpgradeLog.lean)
  follows that continuation to an actual retained `Upgraded` log for a committing
  proxy frame (`stateGas = none`, `bal = none`). Its same-frame prefix identifies
  an implementation-slot write; the result specifies address and topic with an
  existential payload. It does not assert receipt correspondence or history-wide
  implementation continuity. `ConfiguredHistoryTraceIn.implSlot_change_emitsUpgraded`
  in [`Blanc/Lift/Usdc/ProxyCommittedUpgradeLog.lean`](../Blanc/Lift/Usdc/ProxyCommittedUpgradeLog.lean)
  composes this with retained-write attribution and frame-log inclusion: a
  committing raw frame changing the implementation slot yields that log at the
  proxy address. Its premises include nonempty proxy code at the frame entry,
  `ImplSlotApart`, and the history's body-stage capabilities and BAL restriction.
  The same module's `retained_implSstore_emitsUpgraded_of_proxyCode` instead
  takes the actual retained node's proxy-code identity directly and proves
  the log occurs in the same committed root. It does not require global
  implementation-slot separation; establishing the node's code remains the
  caller's obligation.
  [`Blanc/Lift/Usdc/ProxyRetainedContextCodes.lean`](../Blanc/Lift/Usdc/ProxyRetainedContextCodes.lean)'s
  `ConfiguredHistoryTraceIn.retained_proxyV1_context` couples strict earlier
  retained-write exclusion with current Proxy/V1 code classification in one
  committing root. It derives the unchanged implementation word and excludes
  each current write using the same root's absence of an Upgraded log. Its
  explicit remaining inputs are installed Proxy/V1 code and implementation
  address at that root, own-code at the actual input root, and local separation
  for actual writes already known to run V1. It requires no global raw-write
  apartness; supplying that local V1 separation and the actual root/receipt
  facts remains a separate obligation.
  For an actual `R ∈ history.settledRoots`, use
  `ConfiguredHistoryTraceIn.settledRoot_retained_proxyV1_context`. It supplies
  raw-frame membership, commitment and conditional own-code from that same
  root. Installed Proxy/V1 code, the implementation word, the same-root
  absence of Upgraded logs and local known-V1 write separation remain explicit.
- Storage loops and straight-line steps on such a reach, in
  [`Blanc/Lift/ReachSstoreLoops.lean`](../Blanc/Lift/ReachSstoreLoops.lean): the step
  function `stepR`/`ri_stepR` with the tactics `rsx` (one straight-line step), `rsd`
  (a `JUMPDEST`), `rsw` and `rsld` (over `run`, `hT`, `erase`); the loop principles
  `reach_loop_measure` and `reach_loop_index`; `Reach.withPot` (the memory potential at
  every step of a reach); `Reach.sstoreNode_pot` (a raw `SSTORE` node under a fresh certified
  frame as the end of such a reach from the entry tree; worked use: USDC
  `initFrame_sstore` in `Blanc/Lift/Usdc/InitRowsHistory.lean`); the solc storage-string copy loop over `MLOAD` or `CALLDATALOAD`
  (`ReachPayload.bodyR`/`headB`/`headJ`, `payloadB_reach`/`payloadJ_reach`: a store of the
  loop writes `base + j` for `j < count fin p`, with `mload_rdStep`/`mload_win` and
  `cdload_rdStep`/`cdload_win` for its read), and both clearing layouts
  (`ReachClear.clear_reach`, `legacyClear_reach`: a store of the loop writes zero).
  `ReachClear.legacyClear_reach_range` additionally preserves the actual initial
  key and end word: a reached zero-store key lies at or above the initial key
  and strictly below the end, or the original pending continuation is reached.
  `legacyClear_reach` projects this single traversal to its original interface;
  no old-header shape or additional gas assumption is required.
  `ReachPayload.payloadB_reach_exact` retains equality of the exit index to
  `count fin p`; the original `payloadB_reach` projects the same traversal.
  USDC's `InitReachV1.tail7_reach_range` and `helper46_reach_range` in
  [`Blanc/Lift/Usdc/InitReachV1.lean`](../Blanc/Lift/Usdc/InitReachV1.lean)
  carry the clearing interval through the old initializer helper, retaining
  the old endpoint computed from its actual input storage word. Their original
  interfaces remain projections. These range facts do not by themselves prove
  that a clearing key differs from a control slot.
  [`Blanc/Lift/Usdc/InitV1KeyBounds.lean`](../Blanc/Lift/Usdc/InitV1KeyBounds.lean)
  bounds the decoded old length and clearing count for any stored header.
  `helper46_reach_ne_implSlot` consumes the helper range with explicit numeric
  hash-base bounds and the new-length cap.
  [`Blanc/Lift/Usdc/InitV1ConcreteBounds.lean`](../Blanc/Lift/Usdc/InitV1ConcreteBounds.lean)
  proves the exact Keccak values for initializer headers 4, 5 and 7 in the kernel.
  Its `bounds` theorem supplies header separation, the hash-base margin and
  the implementation-slot exclusion interval for those three headers.
  `InitReachV1.callFrag_reach_range`, `callee_reach_range`, `wrapper_reach_range`
  and `initV1_reach_range` propagate the actual clearing ranges through the
  initializer; `BoundedRange` retains the three length caps derived from actual
  staging. The original caller interfaces project that same traversal.
  `InitV1KeyBounds.initV1_reach_ne_implSlot_concrete` combines these ranges and
  checked hashes to exclude the implementation slot at every reached initializer
  store, with no numerical-bound, length-cap or old-header-format premise.
  Also there: `rs_callIn`/`rs_ret` (enter a callee with its continuation pending, return into
  it), `rs_callOverAny` (an `SSTORE`-free callee from any machine), `rsk` (one step taken
  without inverting it), `rsa` (`rsd`, `rsx` or `rsld`, for `repeat rsa`), `mapSlot_scratch`
  (a mapping slot from solc's scratch words at any closed offsets) and `Reach.selWalk_inlS` (a
  solc dispatcher's comparison walk). The
  solc 0.6 `string storage = string calldata` helper and the `f(string calldata)` external
  wrapper, as shapes over their jump tags (`StrStoreCd.helper`, `CdStrWrap.wrapper`), with
  `StrStoreCd.reach` (a store writes the slot, zero, or `keccak(slot) + j` for
  `j < (len + 31) / 32`) and `CdStrWrap.reach` (the reach lies in the body, entered with the
  decoded length and data pointer, both below `2 ^ 32`), are in
  [`Blanc/Lift/ReachSolcStringStore.lean`](../Blanc/Lift/ReachSolcStringStore.lean); worked use:
  USDC `InitReachV2.initV2_reach` in `Blanc/Lift/Usdc/InitReachV2.lean`. The same module
  has the memory form (`StrStore.reach` over `MLOAD`, memory kept outside scratch), solc 0.6's
  string allocation fragment (`alloc06Frag`, `alloc06Frag_reach` into `Alloc06`: header at the
  old free pointer, free pointer advanced past the rounded payload, lower memory kept) and
  `memWord_write_far` (a word read clear of a write); worked use: USDC
  `Init06.wrap06_reach` in `Blanc/Lift/Usdc/InitReach06.lean`. The solc ABI string decoder
  fragments of `Blanc/Lift/SolcAbiStringStaging.lean` on a reach (`ReachAbi.strFrag_reach`,
  `rotFrag_reach`, `staticFrag_reach`; the allocation is `allocMem` by `strFrag_mem`, its size
  bounded by the potential) are there too; worked use: USDC `InitReachV1.wrapper_reach` in
  `Blanc/Lift/Usdc/InitReachV1.lean`.
- Further prefix-reach facts for a certified frame: the goto inversions `rr_branchTo`/`rr_jump`
  and the instruction inversions `ri_address`/`ri_dup_any` in
  [`Blanc/Lift/RunPWalk.lean`](../Blanc/Lift/RunPWalk.lean); the first external instruction of a store-free region
  (`SFunc.preIn`, `PreSet`, `Reach.firstExec`: the reach keeps the world up to the instruction;
  `CursorOK.state_post_of_silent`) in [`Blanc/Lift/ReachFirstExec.lean`](../Blanc/Lift/ReachFirstExec.lean), with its big-step
  companion `SFunc.RunP.stor_of_preIn` (a protected account's storage across a whole run of the
  region, to its halt or its return) in [`Blanc/Lift/RegionStor.lean`](../Blanc/Lift/RegionStor.lean); the world at the first
  external instruction of a reach from a tree whose paths run silent code, silent closures and at
  most one external instruction (`SFunc.preExec`, `PreExecSet`, `Reach.preExec_state`) in
  [`Blanc/Lift/ReachPreExec.lean`](../Blanc/Lift/ReachPreExec.lean); a silent tail after an external instruction
  (`silent_after_exec`: the frame's post state is the state right after the instruction and no
  later node decodes another, from the decidable checks `ExecSilent`/`SFunc.nodesSatisfy` and
  `SFunc.contsIn`; `Reach.conts_silent`) in [`Blanc/Lift/ReachSilentTail.lean`](../Blanc/Lift/ReachSilentTail.lean); the route
  of a selector word through a solc binary-search dispatcher (`SFunc.selWalk σ f`, computed by the
  kernel for a concrete selector; `Reach.selWalk_inl`/`_inr`, `SFunc.RunCut.selWalk_inl`/`_inr`,
  `SFunc.selWalk_mem_pairs`/`_leaves`; `SFunc.toCall` with `SFunc.RunP.callee_of_toCall` for a
  wrapper's ABI decoding before its body call) in [`Blanc/Lift/SelectorRoute.lean`](../Blanc/Lift/SelectorRoute.lean); and the
  reach forms of the two route-C skips below, `rr_shuffle` and `rr_call_silent`, in
  [`Blanc/Lift/ReachSkip.lean`](../Blanc/Lift/ReachSkip.lean). Worked uses: USDC (`Blanc/Lift/Usdc/RefineSignedAuth.lean`,
  `RefineSignedPermitNodes.lean`, `RefineAdminRescue.lean`, `HistoryFamilyProxy.lean`).
- Preserve an actual external-instruction target while routing a literal
  comparison dispatcher: [`Blanc/Lift/ReachDispatch.lean`](../Blanc/Lift/ReachDispatch.lean)
  provides `rr_cmp_gt` and `rr_cmp_eq` for `DUP`/`PUSH4`/comparison/`PUSH2`
  branches. They preserve arbitrary instruction relation `P`, its soundness
  projection, the original `AtExec` target and continuation stack; the equality
  variant consumes the actual function lookup; the proof recipe for
  `Exec.NoRetainedWriteTo` registers them. They have no in-tree consumer
  since the single-frame Uniswap V2 history walk was superseded. These
  projections alone do not identify a retained occurrence or child outcome.
- From a cursor-placed node to *later* nodes of the same frame:
  [`Blanc/Lift/ReachChain.lean`](../Blanc/Lift/ReachChain.lean).
  `reach_between` is `reach_of_parentPrefix` started at any cursor-placed node;
  `noExec_after_of_cursor` says no later node decodes an external instruction
  when the tree from the cursor on is exec-free; `getStor_post_of_silent` says the
  frame's post storage at an observed owner is the node's storage when the
  owner is `State.Protected` at that node and the remaining tree is state-silent
  (`Reach.silentTo`, `SFunc.silentTree`). The accepted terminal tree includes
  `SELFDESTRUCT`, so a certificate alone does not protect every world owner.
  `Evm.step_halt_getStor_eq` likewise takes protection at the pre world.
  `StepIn.exec_getStor_eq_of_noDescendants` preserves a protected observed
  owner in a frame with no raw descendants (a child would be the frame itself,
  yet strictly shallower). When the remaining source suffix is `SFunc.silent`
  (which excludes `SELFDESTRUCT` terminals) no protection is needed: WETH9
  `weth9_exec_node` takes the actual source run from the node's cursor
  (`CursorOK.sourceRunReturn`) and concludes `post.state = N'.devm.state` by
  `SFunc.RunP.state_of_silent`, for every owner.
- Restrict external instruction families along a checked certificate cursor:
  [`Blanc/Lift/CallRestriction.lean`](../Blanc/Lift/CallRestriction.lean) defines
  `SFunc.execsSatisfy` and `Cursor.ExecsSatisfy` (active function and pending
  returns). `SStep.execsSatisfy` preserves the restriction;
  `Cursor.execsSatisfy_of_reachable` starts it from the checked certificate;
  `CursorOK.execsSatisfy` turns actual instruction decoding into `allowed x = true`.
  This constrains same-frame instruction families, not child commitment or
  effects, and requires the check on every certificate function.
  `Xinst.notDelegatecall` with `CursorOK.exec_spawn_undelegated` is the restriction the
  `OwnSpawns` producers use: a cursor whose `ExecsSatisfy Xinst.notDelegatecall` decodes only
  `CALL`, `STATICCALL` or `CREATE2`.
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
- For concrete WETH9 or Uniswap V2 Pair code that must exclude terminal
  `SELFDESTRUCT`, use
  [`Weth9/TerminalSafety.lean`](../Blanc/Lift/Weth9/TerminalSafety.lean) and
  [`UniswapV2Pair/TerminalSafety.lean`](../Blanc/Lift/UniswapV2Pair/TerminalSafety.lean).
  Each namespace supplies `cert_noSelfdestruct` for its actual checked runtime
  certificate and `runtime_not_selfdestruct` for an actual same-frame prefix
  from pc-zero entry of its installed code with selected state-gas absence.
  The conclusion excludes decoded `Linst.At ... .selfdestruct` for every
  eventual frame outcome. It does not assert deletion safety or a contract
  invariant; child routing, admission and inherited deletions remain separate.
  Each also supplies `cert_callOnly`, `code_not_delegation`,
  `runtime_call_or_staticcall` (fork-free spawn restriction) and `exec_noDel`:
  all-outcome `Execution.NoDel wa` for any execution under `stateGas = none`
  where `wa` holds the checked runtime (via `Exec.inv_noDel_of_installedCert`).
  `code_toList_ne_nil` and `transaction_noDel` (one selected transaction under
  `stateGas = none` keeps `wa` undeleted and holding the runtime) follow,
  with `installedCert` and `history_noDel` for a configured In-history.
- A reentrancy lock's `LockSpec.Dominance` from a certificate (all outcomes):
  the checker `LockCheck.Spec`/`LockCheck.lockCert` (one Boolean walk with
  producer annotations from `scripts/lift/lift.py --lock-spec`) in
  [`Blanc/Lift/LockCheck.lean`](../Blanc/Lift/LockCheck.lean); the fact
  semantics in [`Blanc/Lift/LockCheckSound.lean`](../Blanc/Lift/LockCheckSound.lean);
  `LockCheck.dominance`, its strong form `LockCheck.dominance_strong` (only
  release pcs write the slot after a mutating body start) and
  `LockCheck.no_forbidden`, over the invariant `LockOK`/`LConts`,
  `lock_step` and `lock_of_parentPrefix`, in
  [`Blanc/Lift/LockCheckFlow.lean`](../Blanc/Lift/LockCheckFlow.lean), which
  also holds the step facts `LockCheck.pp_back` (a node strictly before a
  successor precedes the node), `LockCheck.lockAt_edge` (one cell across a
  same-frame edge that spawns nothing and stores elsewhere) and
  `LockCheck.cursor_sstore_node`. The continuing arm uses the generic
  `Evm.step_cont_getStor_get` directly; no separate no-executable-opcode
  storage bridge is needed. Worked use:
  `Blanc/Lift/VyperNonreentrantDeployed/Fixed/LockDominance.lean`; the full
  `lock_exclusion` instance (dominance, `ownerDiscipline_of_world` for a
  forwarder owner, `NoDelegateFrom` from the cursor, release-pc activity) is
  `Blanc/Lift/VyperNonreentrantDeployed/Fixed/Exclusion.lean`; its transaction
  and history forms (`vplus_excludes`, `TransactionTrace.vplus`,
  `ConfiguredHistoryTrace.vplus`: the well-formed-root premise derived from the
  prepared message, every raw root of a history covered) are
  `Blanc/Lift/VyperNonreentrantDeployed/Fixed/ExclusionTrace.lean`.
- Lifted run to execution (liveness, exact gas): `SFunc.RunExact`,
  `Cert.jumpsOk` and `lift_exact` in [`Blanc/Lift/Exact.lean`](../Blanc/Lift/Exact.lean);
  the per-instruction walk steps (`rx_push`, `rx_sload_cold`, `rx_callRet`, …)
  over the gas-carrying state `St`, a frame's entry state as an `St` (`pre_eq_St`), the
  word read-back facts `sliceD_word_same` and `read_covered`, and one solc dispatcher
  comparison (`cmp_miss`, `cmp_hit`) are in
  [`Blanc/Lift/ExactWalk.lean`](../Blanc/Lift/ExactWalk.lean). The fixed-cost
  `rx_sload_cold` and `rx_sload_warm` constructors require both
  `sevm.benvStat.rules.stateGas = none` and selected access pricing
  `sevm.benvStat.rules.access = .eip2929`; flat historical schedules do not
  have their exact 2100/100 charges. More steps
  (`rx_shl`, `rx_xor`, `rx_byte`, `rx_mstore8`, `rx_calldatacopy`, `rx_log1`, …) are in
  [`Blanc/Lift/ExactWalkOps.lean`](../Blanc/Lift/ExactWalkOps.lean). `rx_shl`/`rx_shr`
  require the selected `rules.op.shifts = true` capability. Beacon's `le_half1`,
  `le_mid`, and `to_little_endian_64_run` in
  [`LittleEndian.lean`](../Blanc/Lift/BeaconDeposit/LittleEndian.lean) carry that
  condition through their forward walks; arbitrary continuation evidence does
  not supply it. The generic success-inversion statements remain unchanged.
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
  (`toB256_add_toB256`, `toB256_sub_toB256`, `toB256_div_two`, `one_add_toB256`), the
  SHA-256 precompile step's premises and world facts (`ShaReady`, `ShaCallPost`,
  `staticcall_sha_step`), and `BaseRel`, the world a step that writes no storage and emits
  no log keeps.
- Successful lifted run to facts (safety, the inversion walk): per-node `ric_*`
  (control, over `SFunc.RunCut`; `SFunc.Run.cut`/`SFunc.RunCut.uncut` for uncut
  runs) and per-instruction `ri_*` (successor as an `St`, `ri_xor` among them; numeral-offset forms
  `ri_mstore_nat`/`ri_calldatacopy_nat`, `ri_val` to name a successor's top word, and
  `ri_sstore_nonstatic`: a completed `SSTORE` proves the frame non-static) in
  [`Blanc/Lift/InvWalk.lean`](../Blanc/Lift/InvWalk.lean) and
  [`Blanc/Lift/InvWalkOps.lean`](../Blanc/Lift/InvWalkOps.lean), which also holds the
  `ri_returndatacopy` inverse, which derives the actual returndata range bound
  and complete `St` successor with its physical memory write, and the
  solc word-copy loop inverted (`ric_copy_step`, `ric_copy_exit`, the converses of
  `copy_step`/`copy_exit`) and the facts a failed comparison guard leaves
  (`toNat_le_of_gtCheck_eq_zero`, `toNat_ge_of_ltCheck_eq_zero`,
  `eq_zero_of_iszero_ne_zero`); failing arms
  (`SFunc.noOk`, `SFunc.RunCutP.false_of_noOk`), trees that cannot halt (`SFunc.noHalt`,
  `NoHaltSet`, `SFunc.RunP.not_halted`, `SFunc.RunP.not_halted_entry`), conditional gotos
  (`ric_branchTo`), internal calls (`ric_call`), `ri_sload` and
  `ri_log1` in [`Blanc/Lift/InvWalkWorld.lean`](../Blanc/Lift/InvWalkWorld.lean);
  on a historical fork, where the access schedule may be flat (Istanbul, Muir Glacier)
  rather than EIP-2929, invert `SLOAD` with `ri_sloadH` from `rules.bal = none` alone; its
  successor `afterSloadH` is `afterSload` under EIP-2929 (`afterSloadH_of_eip2929`) and the
  unchanged base under flat access, with `afterSloadH_getStor`/`afterSloadH_logs`/
  `afterSloadH_output`, `getStorVal_afterSloadH`/`getStorVal_afterStoreH`,
  `getStor_afterStoreH`/`getStor_afterStore_neH`/`logs_afterStoreH` and the storage-walk
  steps `StorStep.sloadH`/`StorStep.sstoreH`; invert
  `SSTORE` with `ri_sstoreH` (`rules.stateGas = none`, `rules.bal = none`) over
  `afterSstoreH`, whose refund is `sstoreRefundH` (legacy, flat net-metered, or EIP-2929) and
  which is `afterSstore` under EIP-2929 net metering (`afterSstoreH_of_eip2929`); get the
  frame's non-static flag from `ri_sstore_nonstaticH`; invert or run `EXTCODESIZE` with
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
  committed post by `Execution.committedPost_of_okFact`), and the return-data bounds
  `ReturnDataBound.staticcall_returnData_length_ltH`/`call_returnData_length_ltH`; the
  `_covered`/`of_covered` forms recover the modern statements; the value-carrying `CALL`
  inversions `of_step_call_val_with_depth_frameH`/`of_run_call_val_with_depth_frameH` and the
  caller-visible `ri_call_postH`, all in
  [`Blanc/Lift/HistStaticCall.lean`](../Blanc/Lift/HistStaticCall.lean); the call-success guard
  steps `staticCallGuard_invPH`/`staticCallGuard_exactH` and a static child's entry
  (`Evm.step_spawn_child_dataH`; its opening world is `Evm.step_spawn_child_world_noStateGas`) in
  [`Blanc/Lift/HistStaticCallGuard.lean`](../Blanc/Lift/HistStaticCallGuard.lean);
  the forward cursor cuts from `rules.stateGas = none` alone (`cursor_next_forwardH`,
  `cursor_jinst_forwardH`, `cursor_nexts_line_cont_free_forwardH`, `cursor_nexts_forwardH`,
  `cursor_branch_forwardH`, `cursor_next_call_occurrence_forwardH`, and the state cuts
  `CursorStateAt.lineH`/`jumpH`/`destH`/`branchZeroH`/`branchSuccH`/`toZeroH`/`toSuccH`/`callH`/
  `retH`/`gotoH`) in
  [`Blanc/Lift/HistCursorCuts.lean`](../Blanc/Lift/HistCursorCuts.lean). For an actual
  call return before a later same-frame SSTORE, without a successful final
  outcome, use `cursor_call_occurrence_of_parentStep_noStateGas` or
  `cursor_call_occurrence_toward_sstore_noStateGas` in
  [`Blanc/Lift/CursorOccurrenceToward.lean`](../Blanc/Lift/CursorOccurrenceToward.lean).
  They preserve the original recursive slot and actual return/cursor edge;
  they assert neither a success flag nor child commitment. For checked steps
  and literal SSTORE-free lines forced by a later same-frame SSTORE, use
  `cursor_step_toward_sstore_noStateGas` and
  `cursor_line_toward_sstore_noStateGas` in
  [`Blanc/Lift/CursorCutsToward.lean`](../Blanc/Lift/CursorCutsToward.lean).
  `CursorOK.returnBeforeSstore_noStateGas` in
  [`Blanc/Lift/CursorReturnToward.lean`](../Blanc/Lift/CursorReturnToward.lean)
  crosses an SSTORE-free helper to its original caller and retains its
  completed source run, including external calls. Its source-freedom and
  closed-helper checks remain explicit; it needs no successful final outcome.
  `Reach.false_of_sstoreFree_halting` in the same module excludes a later
  SSTORE inside a halting, SSTORE-free branch with saved callers.
  For state-shaped producers, `CursorStateToward` in
  [`Blanc/Lift/CursorStateToward.lean`](../Blanc/Lift/CursorStateToward.lean)
  extends the existing `CursorStateAt` with the actual remaining prefix to the
  observed SSTORE. Its line, branch, destination, internal call and return cuts
  retain both spans. Guards exclude actual halting SSTORE-free branches; the
  single-primitive cut requires a distinct target node, allowing an earlier
  write only after the producer proves its separation from the tracked write.
  Source runs and
  returns (`CursorOK.sourceRunH`/`sourceRunReturnH`), exec-free suffixes
  (`cursor_reach_of_parentPrefixH`, `CursorOK.noExecSuffixH`, `CursorOK.revertLineNoOkH`,
  `reach_betweenH`, `noExec_after_of_cursorH`), call-free internal returns
  (`CursorOK.quietReturnH`, over the fork-free `SFunc.ReturnRegion`/`ConfStep.returnRegion`) in
  [`Blanc/Lift/HistCursorReturn.lean`](../Blanc/Lift/HistCursorReturn.lean); the GAS-to-call
  and reply forwarders `CursorStateAt.gasCallH`/`callFlagH`/`returnWordH` in
  [`Blanc/Lift/HistCursorCalls.lean`](../Blanc/Lift/HistCursorCalls.lean); each `_covered`
  form there is the modern statement from `CoveredFork`; on every fork,
  `ecrecover_activeH` activates address 1 and
  `ecrecover_output_of_processMessage_cleanH` (from `rules.stateGas = none`; its `_covered`
  form is the modern statement) reads a clean address-1 child's output, while
  `CallCodeH.direct_of_nodeleg`/`CallCodeH.of_nodeleg` resolve a non-delegated callee's code
  under either delegation flag. `CallCodeH.direct_of_effective`/`CallCodeH.of_effective`
  use the selected rules' effective lookup-none result, including arbitrary
  code bytes when delegation is disabled. These helpers live in
  [`Blanc/Lift/HistEcrecover.lean`](../Blanc/Lift/HistEcrecover.lean); the world facts
  `afterSloadH_state` and `afterSstoreH_state`/`afterSstoreH_getCode` in
  [`Blanc/Lift/HistAccessFacts.lean`](../Blanc/Lift/HistAccessFacts.lean);
  the forward creation kit under
  historical rule facts (the `SLOAD`/`SSTORE` charges `sloadCostH`/`sstoreCostH` with the
  `sloadCostH_of_eip2929` equation and their `_le` bounds, the exact steps `rx_sload_selH`/`rx_sstoreH`, the
  settlement `processMessage_ok_of_execH`/`liftCreate_postH`/`liftCreate_okH` from
  `rules.stateGas = none` with the target's EIP-161 touch recorded, and `CREATE2` as
  `create2ChargeH`/`Xinst.step_create2_spawnH`/`create2_runCompiledH`) in
  [`Blanc/Lift/HistCreate.lean`](../Blanc/Lift/HistCreate.lean); the bookkeeping fields a
  settled frame reads across those steps (`afterSloadH_accountsToDelete`,
  `afterSloadH_refundCounter`, `afterSstoreH_accountsToDelete`, and
  `afterSstoreH_refundCounter_legacy` under the legacy `SSTORE` refund schedule for a nonzero
  write) in [`Blanc/Lift/HistAccessMeta.lean`](../Blanc/Lift/HistAccessMeta.lean);
  a zero-value `CALL` into a known child under a flat (pre-Berlin) access schedule with delegation
  disabled (`Xinst.step_call_zero_flat`, `Ninst.runCompiled_call_zero_child_flat`, the child
  settled with its target's EIP-161 touch) and a top-level call message settled from its raw
  execution (`processMessage_call_of_execH`) and the code-free sender of a historical admission
  check (`checkTransaction_sender_code_emptyH`) in
  [`Blanc/Lift/HistCallFlat.lean`](../Blanc/Lift/HistCallFlat.lean); the refund counter kept from
  falling by a store whose slot started at zero or is non-zero now (`sstoreRefundH_ge`,
  `afterSstoreH_refundCounter_ge`) in
  [`Blanc/Lift/HistSstoreRefund.lean`](../Blanc/Lift/HistSstoreRefund.lean); the window kit from
  rule facts (`prefixTransfer_runH`, `create2_run_resultH`, `window_trackH`,
  `Xinst.step_call_spawn_stackH`, `Xinst.step_call_spawn_targetH`,
  `Xinst.step_create2_spawn_unprotectedH`), with a successful `SWAP`'s length facts
  (`List.swap_some_length`), every body of a window-checked certificate passing the edge check
  (`Cert.windowOk_mem`) and dropping words from a pattern-over-rest match
  (`matches_append_drop`), in
  [`Blanc/Lift/HistWindow.lean`](../Blanc/Lift/HistWindow.lean);
  the remaining historical successor projections (`afterSloadH_getCode`/`_accessedAddresses`/
  `_error`/`_createdAccounts`/`_accessedStorageKeys`, `afterSstoreH_getCode`/
  `_accessedStorageKeys`, the `ite` form `getStor_afterSstoreH`) and the quiet frame theorem
  `SFunc.Run.world_of_quietH` from `rules.stateGas = none` alone in
  [`Blanc/Lift/HistAccessWalkFacts.lean`](../Blanc/Lift/HistAccessWalkFacts.lean);
  the historical SHA-256 kit from `rules.stateGas = none`/`rules.bal = none` (`ShaReadyH`,
  `ShaReady.toH`, `meta_of_processMessage_sha256_64_clean_noStateGas`, the charged tail
  `ri_staticcall_sha_of_charge`, `ri_staticcall_shaH` cased on access schedule and delegation
  flag, and `ri_staticcall_shaH_covered`; the solc packed-SHA site `ric_shaCallH`,
  `ric_copy_shaH`, `ric_pack_shaH`) in
  [`Blanc/Lift/HistShaWalk.lean`](../Blanc/Lift/HistShaWalk.lean);
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
  The Pair scalar getter inversions consume both helpers.
  Their relation-preserving variants, `ric_cmp_gtP` and `ric_cmp_eqP`, take
  an explicit projection from the instruction relation to `Ninst.Run` and
  retain that relation, stack suffix, cut set and final segment in the
  selected continuation. EQ also requires the same target lookup and
  non-cut proof. The Pair `syncSelector_inv` consumes both variants with
  `StepIn D`, preserving the actual execution derivation for child calls.
  For a cut run over an arbitrary instruction relation, `ric_nextP`, `ric_destP`
  and `ric_branchP` in
  [`Blanc/Lift/InvWalkProvenance.lean`](../Blanc/Lift/InvWalkProvenance.lean)
  retain that relation in the exposed instruction and the continuation. Use these
  projections when a walk must preserve execution-derivation provenance.
  A conditional goto to an entry outside the cut list, `ric_branchToP` in
  [`Blanc/Lift/InvWalkBranchToP.lean`](../Blanc/Lift/InvWalkBranchToP.lean), is the
  relation-preserving form of `ric_branchTo`; the Pair swap front consumes it with
  `StepIn D` at its output, liquidity, recipient and callback gotos.
  For a complete linear prefix, `SFunc.RunCutP.split_nexts` exposes its actual
  intermediate state and `Line.Run`, using an explicit projection to `Ninst.Run`.
  The residual cut keeps the original instruction relation, program, cut set and
  final segment. Use it when an existing instruction inverse consumes a line
  while the remaining cut must retain provenance. Split a line itself with the
  existing `Blanc.of_run_append`; no second cut relation is needed.
- Big-step node inversions under an arbitrary step relation, for a run
  `SFunc.RunP P fs sevm d f o` over the walk state `St b S M G` (`rpw_next`, `rpw_dest`,
  `rpw_branch`, `rpw_branchTo`, `rpw_jump`, `rpw_call`, `rpw_callOver` for a `NoHaltSet` callee,
  `rpw_callRet` in a returning run, `rpw_ret`, `rpw_revert`; `SFunc.haltsOnly` with
  `SFunc.RunP.not_returned_of_haltsOnly`; `St.self'`) in [`Blanc/Lift/RunPWalk.lean`](../Blanc/Lift/RunPWalk.lean).
  Worked uses: Lido `pause` under `StepIn R` (`Blanc/Lift/LidoCircuitBreakerDeployed/Pause.lean`),
  the USDC proxy (`Blanc/Lift/Usdc/ProxyWalk.lean`, `ProxyHalt.lean`).
- One-lemma straight-line steps and the inversion helpers of solc walks:
  [`Blanc/Lift/InvWalkStep.lean`](../Blanc/Lift/InvWalkStep.lean). `stepX` computes the successor walk state of the
  straight-line instructions a walk crosses and `ri_stepX` inverts any of them at once; the
  `ri_stepX_nonstorage` projection needs no fork premise when the actual instruction
  is neither `SLOAD` nor `SSTORE`. It shares the original inversion body and leaves
  the `stepX` definition unchanged; storage walks still need their actual fork semantics.
  The
  `istep h` tactic runs one such step (or a `JUMPDEST`) of a cut run, so a straight segment is
  `repeat istep h`; `ibranch h c` crosses a conditional jump whose other arm only reverts;
  `ric_callR` enters a callee that cannot halt; `SFunc.noExit`/`NoExitSet` with
  `SFunc.RunP.false_of_noExit` close an arm that can only revert through loops and gotos;
  `ret_named` names a returned state by its storage; `keccak_scratch` is solc's fresh mapping hash;
  the word facts read solc's comparison flags, address masks and SafeMath guards
  (`toNat_lt_of_shr_ne_one`, `add_nof_of_ltCheck`, `le_of_gt_check`, `word_ff20`, `sub_word`,
  `add_word`, `adr_ne_zero_of_mask`). The cut-run kit of [`Blanc/Lift/WalkCutKit.lean`](../Blanc/Lift/WalkCutKit.lean) adds
  the terminals `ric_stop`/`ric_return`, `ric_callRet` into a `NoHaltSet` callee, a solc
  dispatcher's comparison rows decided by a closed comparison (`ric_gt_le`/`ric_gt_gt`/
  `ric_eq_miss`/`ric_eq_hit` and the `rr_*` reach forms), the storage projections of the walk
  bases, and solc's reuse of the previous hash's key word (`keccak_scratch2`, from
  `Mem.read_after_right_write`). Worked uses: USDC (`Blanc/Lift/Usdc/RefineTransferCallees.lean`,
  `RefineAdminBits.lean`), the USDC leg of the Pair (`Blanc/Composition/UniswapV2PairUsdcWeth9LegsKit.lean`).
- Crossing code without walking it, the route-C skip theorems. A checked synthetic run never
  touches the stack below its frame, [`Blanc/Lift/FrameSkip.lean`](../Blanc/Lift/FrameSkip.lean): `FrameAt`,
  `SFunc.RunP.stack_below`, `SFunc.RunCutP.stack_below` (every stop satisfies `CutStop`),
  and `SFunc.RunP.entry_stack_below`. The `FrameAt.next_noStateGas`,
  `SFunc.RunP.stack_below_noStateGas` and `SFunc.RunP.entry_stack_below_noStateGas`
  variants share the original induction with actual state-gas absence.
  `ric_call_silent` crosses any state-silent internal
  call (hashing, ABI encoding, view-like helpers) with the continuation's stack
  `Y ++ S.drop e.frame.length`, `Y.length = e.rets` (worked example:
  `Blanc/Lift/UniswapV2Pair/FrameSkipExample.lean`, the Pair's `kLast()` getter). A silent
  stack-shuffling segment crossed by one kernel decision, [`Blanc/Lift/ShuffleSkip.lean`](../Blanc/Lift/ShuffleSkip.lean):
  the abstract words `SVal` (`arg i`, `lit w`, `unk`), `Carried`, the checker `shuffle` (every
  instruction state-silent, its stack effect the lift's own `ninstTransfer` on index labels,
  literal `JUMPI`s followed, reverting arms pruned, gotos into an entry list `Fw` disjoint from the
  cut list) and `ric_shuffle`. The `shNinst_run_noStateGas`,
  `shuffle_sound_noStateGas` and `ric_shuffle_noStateGas` variants share those
  proofs with actual state-gas absence and the same checker/fuel.
  A `DELEGATECALL` into quiet code,
  [`Blanc/Lift/QuietDelegateSkip.lean`](../Blanc/Lift/QuietDelegateSkip.lean): `ProcessMessage.getStor_of_quietCode` (a call
  message running `QuietCode` with no value transfer keeps its storage owner's storage),
  `Ninst.delegatecall_getStor_of_quiet`, `Ninst.Run.getCode_eq`, `ric_delegatecall_quiet`,
  framed runs (`SFunc.RunP.framed` over `Cert.framesSat`), `SFunc.RunP.qdKeep` over a
  `QuietDelegateSet` closure whose every `DELEGATECALL` names one constant word (`QDKeep`), and
  `ric_call_quietDelegate`. Worked uses: USDC (`Blanc/Lift/Usdc/ShuffleSegments.lean`,
  `SignedSkip.lean`, `RefineSignedPermitNodes.lean`).
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
  through account warming. `temporalAccountAccessBase_getStor` and
  `temporalAccountAccessBase_getCode` in
  [`Blanc/Lift/AccountAccessState.lean`](../Blanc/Lift/AccountAccessState.lean)
  preserve storage and code at every address. Use these facts to compose an observed call without
  unfolding the nested world update; the Pair mint prefix consumes all three.
  The existing Lido temporal access names are compatibility declarations over
  this common owner.
  For the separate flat-pricing route, use
  `Ninst.runCompiled_extcodesize_flat` in
  [`Blanc/ForwardFlatAccess.lean`](../Blanc/ForwardFlatAccess.lean), with explicit
  flat prices and disabled BAL recording. Its successor retains the original
  base and actual code-size word; use `Ninst.exec_of_stepRun` for continuation.
  Neither route proves nonzero code size, callee liveness or the concrete
  constructor execution.
- A callee that fails on every input: `revertingCode` (`PUSH0 PUSH0 REVERT`); every pc-zero
  frame over it ends in an error (`revertingCode_exec_error`, via the generic non-spawning
  step inversion `Exec.ofExecution_inv`); an ordinary non-precompile message over it never
  settles cleanly (`processMessage_not_clean_of_reverting`); and no static child message to
  an account holding it answers (`not_staticAnswered_of_reverting`), which refutes the
  `StaticAnswered` witness a successful-flag `STATICCALL` inversion retains. Use it for
  failing-callee (callee-premise) controls, in
  [`Blanc/Lift/RevertingCallee.lean`](../Blanc/Lift/RevertingCallee.lean).
- A callee silent on one selector, whatever its code: `NoStaticAnswer code sel` (no
  static child message to a non-precompile account holding `code` answers calldata
  with selector `sel`), which refutes the same `StaticAnswered` witness. The Pair
  proves the `0x1626ba7e` instance in its own stratum; the USDC library side takes it
  as a hypothesis. Use it for selector-silence (answered-call) refutations, in
  [`Blanc/Lift/StaticSilent.lean`](../Blanc/Lift/StaticSilent.lean).
  `NoStaticAnswerH` uses `NeutralFork` and the actual-rule `StaticAnsweredH`
  witness; `NoStaticAnswerH.toCovered` recovers the original interface.
  `UniswapV2Pair.not_staticAnswered_pairH` shares the same message-entry and
  settlement proof, using `staticView_bytecode_invH` and canonical actual-flag
  call-code resolution. The modern Pair theorem projects from it. This supplies
  the historical silence boundary for contract-signature consumers; it does
  not by itself migrate the USDC library or establish owner rejection.
  The first library consumers in `Blanc/Lift/Usdc/LibReject.lean` are
  `lib_run_cut_noStateGas` (the actual successful bytecode cut) and
  `lib_e8_invH` (the `isContract` branch with the executing rules' account-access
  successor). The shared nonstorage memory walks retain their modern interfaces;
  the static-call tail uses actual `StaticAnsweredH` and silence restricted to
  the same executing environment, preserving the old global silence interface.
  `Usdc.lib_rejects_pairH` now supplies the complete raw historical rejection
  under `NeutralFork` and historical Pair silence, sharing the original decoder
  and selection proof. In `Blanc/Lift/Usdc/LibSeam.lean`, `LibRejectsH` and
  `LibSeam.lib_rejects_pairH` expose its fresh-frame interface. `LibRejectsAt`
  restricts rejection to actual children with the same `benvStat`;
  `LibRejects.at_of_covered` and `LibRejectsH.at_of_neutral` supply it without
  converting the old global capability into a stronger one.
  In `Blanc/Lift/Usdc/SignedSites.lean`, `tail3_false_nonstorage`,
  `tail2_false_noStateGas` and `tail1_falseH` reuse the original result-word,
  delegate-child and account-access tails with that same-environment capability.
  `sx_nonstorage` orchestrates canonical nonstorage inversions;
  `usdcLib_not_precompile_any` proves the fixed library address exclusion for
  each actual fork. The original covered interfaces remain projections.
  Selected permit consumers `ric_seg_e8digest_noStateGas` in
  `Blanc/Lift/Usdc/ShuffleSegments.lean` and `ric_seg_w149_noStateGas` in
  `Blanc/Lift/Usdc/RefineSignedPermitFrames.lean` reuse the original shuffle
  checks. `skipP_78_noStateGas` and `skipP_79_noStateGas` in
  `Blanc/Lift/Usdc/SignedPathsKit.lean` preserve the exact silent-call frames,
  returned stacks and world-state equalities. `preambleP_nonstorage` preserves
  the actual entry-to-dispatcher run without a fork premise. The encoding chain
  `tail0_falseH`, `enc_falseH` and `site9_falseH` in SignedSites uses actual
  state-gas/BAL absence and the same local rejection capability; it preserves
  the original memory bounds, free-pointer observations and copy-loop proof.
  `walk8H`, `walk94H`, `path_permitVrsH` and `path_permitBytesH` in
  `Blanc/Lift/Usdc/SignedPathsPermit.lean` use actual SLOAD/SSTORE inversions
  at the certified instruction positions, with canonical historical code
  preservation and unchanged owner-word cleanup. Their original covered
  interfaces remain projections. `impl_permit_pair_not_okH` in
  `Blanc/Lift/Usdc/SignedPaths.lean` excludes successful Pair-owned calls for
  the canonical V2_2 permit selectors, preserving the actual execution and
  entry-world library/Pair code premises. Its dispatcher adaptation is shared
  with the original covered endpoint.
  `Blanc/Composition/UniswapV2PairUsdcOwnersIn.lean` supplies
  `mid_retained_owner_excluded` for the same actual retained V2_2 frame: library
  code comes from the original full-world prefix, and Pair code from the
  genuine mid-cut installation. It preserves that frame’s execution, entry
  world and commitment; actual installation and world facts remain inputs.
  Its `mid_retainedRowWrite_nonInc` removes the V2_2 owner residual from the
  existing classifier while retaining the same root, frame, write and parent
  prefix, and the original full-history R3/R4 populations. This is a local
  retained-write inequality. `mid_root_allowance_zero` in
  [`UniswapV2PairUsdcZeroIn.lean`](../Blanc/Composition/UniswapV2PairUsdcZeroIn.lean)
  consumes it through `Exec.cell_zero_of_retained_nonInc_noStateGas`, deriving
  root code from the full deployed world and caller exclusion from the genuine
  mid-cut Pair replay. Its incoming-zero premise is an implication for each
  actual retained root, not a supplied zero at every history boundary. The
  original full-history sender/native-query exclusions and R4 remain explicit;
  `mid_history_allowance_zero` in
  [`UniswapV2PairUsdcHistoryZeroIn.lean`](../Blanc/Composition/UniswapV2PairUsdcHistoryZeroIn.lean)
  composes that root law over the exact after-cut suffix and later blocks using
  the existing `MidHistoryTraceIn.cell_property_of_settledRoots`. Its proxy code
  at the cut and output deletion exclusions come from
  `mid_proxy_code_and_outputNotDeleted` and the same original full world.
  The single actual after-cut zero seed remains explicit; no root-by-root zero,
  replacement block-end cut or additional proxy installation is assumed.
  `pairUsdcAllowQuiet_of_mid_history` in
  [`UniswapV2PairUsdcWeth9P1.lean`](../Blanc/Composition/UniswapV2PairUsdcWeth9P1.lean)
  specializes those tracked rows to the exact `PairTouchedSpenders` of the
  consumed post-checkpoint trace and returns its existing `PairUsdcAllowQuiet`
  premise. It retains the same original full-history world/upgrades and R3/R4
  scope; no broader pre-deployment F2′ restriction or supplied
  `NoPairExceptionWrites` premise is introduced. Actual cut identity, initial
  zero and finite freshness remain explicit instance obligations.
  For an exclusion supplied on the exact post-deployment interval, use
  `mid_root_allowance_zero_of_mid_senderQueries`,
  `mid_history_allowance_zero_of_mid_senderQueries`, and
  `pairUsdcAllowQuiet_of_mid_history_of_mid_senderQueries` in those same modules.
  Their sender premise is precisely the original after-cut suffix followed by
  later blocks, including failed/reverted transactions. It excludes neither
  the selected deployment transaction nor an earlier transaction. The original
  APIs remain full-history compatibility wrappers. Native-query exclusion, R4,
  full-world and upgrade premises are unchanged; this restriction of one
  consumer does not redefine R3 for other consumed intervals.
- The Pair's deployed runtime bytes as shared data: `UniswapV2Pair.codeChunk0-2` and
  `UniswapV2Pair.code`, emitted by the registered certificate generator from the
  `uniswap-v2-pair` row, in [`Blanc/Lift/PairCode.lean`](../Blanc/Lift/PairCode.lean).
  Both contract strata name the same bytes through this module; `Check.cert_check`
  checks them.
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
  the child derivation. The Pair swap callback consumes it.
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
  inverted (`ri_return`), the memory facts `Mem.reads_data`/`Mem.read_write_word_of_wf`, and
  the world projections after a store, log or return (`getStor_afterStore`,
  `getStor_afterStore_ne`, `getStorVal_afterStore`, `logs_afterStore`, `getStor_addLog`,
  `logs_addLog`, `getAcct_addLog`, `output_addLog`, `getStor_St_return`,
  `logs_St_return`, `output_St_return`) are in
  [`Blanc/Lift/WalkSteps.lean`](../Blanc/Lift/WalkSteps.lean), which also holds
  exact forward `TIMESTAMP` (`rx_timestamp`, actual block-header time and two gas),
  `SLT`, `TIMESTAMP`, `LOG2`, `TLOAD` and `TSTORE` inverted (`ri_slt`, `ri_timestamp`,
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
- Concrete runs checked by kernel evaluation of Jaune's own `Evm.step`:
  `ConcreteRun.stepN` (at most `n` continuing steps), `stepN_add`, `stepN_sta`, and the
  bridges into the canonical derivation `ConcreteRun.exec_of_stepN`,
  `exec_of_stepN_halt` and `exec_of_stepN_spawn_runOk` (across one `.spawn`), in
  [`Blanc/ConcreteRun.lean`](../Blanc/ConcreteRun.lean). Worked use:
  `Blanc/Lift/VyperNonreentrantDeployed/Concrete/ProxyConcrete.lean`.
- A concrete frame run over a lifted certificate, as a gas-exact `SProg.RunExact`
  (an executable witness: liveness from one start state, by kernel evaluation): the
  interpreter `Witness.wrun` over the certificate's decoded tree, its single step
  `wstep`, the configuration `Cfg` with the accessed-set and storage/account shadows
  (`StorShadow`, `AcctShadow`, `storOf`, `AcctAgree`), Jaune's `State.set`
  directly (kernel-reducible at the pinned Jaune), the kernel-cheap memory write
  `memWriteB` (with `mem_write_eq_B`), the `CALL`
  preparation `callPrep`/`callPrep_spec`, and chunk composition `wrun_add`/`wrun_add_cont`
  in [`Blanc/Lift/WitnessArms.lean`](../Blanc/Lift/WitnessArms.lean). Transfer
  shadows use `storSetBal` and `storTransfer`: account deletion filters every
  cell at that owner, debit precedes credit, and zero value leaves the shadows
  unchanged. `lookupS_filter_owner`, `storSetBal_agree`, and
  `benvAfterTransferS_stor` prove these exact storage projections;
  `acctView_clearIfEmpty` preserves the account-view fields. The raw
  `storOf_setBal` now returns a conditional zero for deletion, and
  `benvAfterTransferB_stor` concludes agreement with the transferred shadow.
  `frameEnterB_done_acc` preserves accessed sets; use the separate
  `frameEnterB_done_ok_state` for a successful child's actual transfer world.
  The soundness theorem `Witness.wrun_exact` (from `wrun_cont`/`wrun_done` over `RunK`/`Agree`), the
  shadow seeds `stateFoldAcct`/`stateFoldStor`, and code children supplied as data
  (`ChildOk`, `ChildAgree`, `callResume`) in
  [`Blanc/Lift/Witness.lean`](../Blanc/Lift/Witness.lean). A code child discharged by its
  own witness run: `childStart`/`childStart_agree`, `childRun`, `childOk_of_start`,
  `childOk_of_childRun`, `frame_of_wrun`, `childAgree_of_halt`, and the DELEGATECALL
  preparation `dcallPrep`/`dcallPrep_spec`, in
  [`Blanc/Lift/WitnessChild.lean`](../Blanc/Lift/WitnessChild.lean). `frame_settle_ok` and
  `frame_of_wrun` require the frame's selected `settle.touchedSweep = false` capability;
  `childOk_of_start` and `childOk_of_childRun` derive it from their existing covered-fork
  evidence. `Witness.wrun_exact` remains generic. Historical settlement still needs a
  producer that retains `recordTouch` and the touched-account metadata. Child starts
  (`childStart`, `NodeWalk.childCfg`, and explicit `frame_of_wrun` inputs) use
  `storTransfer` alongside `acsTransfer`; reusing the pre-transfer storage
  shadow requires a separate no-change proof. That proof is
  `transferKeepsStor m acs` (decided by evaluation: no value moves, or both
  endpoints have a nonzero shadow nonce) with `storTransfer_of_keeps`, and
  `frameStart_agree_keep` is `frameStart_agree` with the parent's storage shadow
  itself (`storSetBal_of_nonce`, `lookupA_acsSetBal_nonce` underneath);
  `haltCreated` projects a run's halted created set for a kernel decision. A
  settled child supplied as data is restored by `Devm.withCreatedAccounts_of_eq`
  (`Blanc/CommonProofs.lean`). The frame-level spawn
  fact `SpawnedBy sevm devm x child` (`Xinst.step` spawns a frame entering as `child`) and
  `spawnedBy_of_callPrep`, `spawnedBy_of_childStart`, `spawnedBy_of_dcallPrep` in
  [`Blanc/Lift/WitnessSpawn.lean`](../Blanc/Lift/WitnessSpawn.lean); reading a run's final
  shadow expressed as a prefix appended to a base shadow, without enumerating addresses or keys:
  `lookupA_append_of_restate` (a prefix restating the start's views changes no account),
  `lookupS_append_of_ne` (writes elsewhere leave an address's storage),
  `lookupS_append_of_absent` (a start with nothing at the address leaves the prefix's values)
  and `lookupS_eq_zero_of` (only zero entries at a key) in
  [`Blanc/Lift/WitnessShadow.lean`](../Blanc/Lift/WitnessShadow.lean); the literal-free
  scaffolding for deciding a long `wrun` as kernel chunks between literal boundaries
  (`Boundary.Bnd`/`obsB`/`cfgOf`/`obsD`/`obsDOk`, their composition `obsD_chain`,
  `obsD_chain3`, `obsB_of_obsD`, `run_of_obsB` (every boundary also records that the frame's
  accounts to delete are still empty and that the transaction's created accounts are empty,
  `AtdClean`: `SSTORE`'s original read consults the created set, so a chunk over free
  bookkeeping is decided with it fixed; a settled child supplied as data must likewise carry
  an empty created set, e.g. `childObs … (d.withCreatedAccounts .emptyWithCapacity)`);
  `Bnd1`/`cfgOf1`/`obsD1`/
  `obsDOk1` with the refund counter and the accounts to delete optional (the created set always
  empty); and a two-code-child frame's staging `callPairFrom`/`callPairA`/`callPairB`/
  `callPairFrom_stages`) in
  [`Blanc/Lift/WitnessBoundary.lean`](../Blanc/Lift/WitnessBoundary.lean). Code tries given as
  generated literals (checked once by kernel `rfl`): `CodeTries.ofData` in
  [`Blanc/Lift/CodeTriesData.lean`](../Blanc/Lift/CodeTriesData.lean). Worked use:
  `Blanc/Lift/VyperNonreentrantDeployed/Vulnerable/Top.lean` (`vminus_witness`).
- Hashed storage slots: `mapSlot key base = keccak256(pad32 key ‖ pad32 base)`, solc's mapping
  slot and, with the arguments swapped (slot first), Vyper's, in
  [`Blanc/Lift/MapSlot.lean`](../Blanc/Lift/MapSlot.lean).
- Vyper 0.2.x runtimes: the frame prologue (`vyPrologue`, `ric_vyPrologue`, `rx_vyPrologue`,
  memory `vyMem`/`vyImg`), the clamp constants as an image invariant (`VyClamps`,
  `vyImg_clamps`, `VyClamps.clamp`), the non-payable guard and address-argument clamp every body starts with
  (`vyNonpayable`, `vyAddrArg`, their `rx_`/`ric_` forms), and the `HashMap` slot scratch window
  (`vySlot_read`, `vySlot_keccak`) with its whole macro (`vySlot`, `ric_vySlot`, `rx_vySlot`),
  the checked storage subtract/add macros (`vySubStore`, `vyAddStore`, their `rx_`/`ric_`
  forms, `B256.nof_iff_not_add_lt`), the selector read (`vyImg_selector`), and word facts
  (`B256.xor_zero`, `B256.xor_eq_zero_iff`, `B256.toAdr_toB256_of_lt`), the `String` copy
  loops with the counter in memory at `0x120`: storage to memory (`vyLoadLoopTree`,
  `rx_vyLoadStep`, `rx_vyLoadLast`, `rx_vyLoadExit`) and memory to storage (`vyStoreLoopTree`,
  `rx_vyStoreStep`, `rx_vyStoreLast`, `rx_vyStoreExit`, one pass inverted `ric_vyStoreIter`
  (a storing pass also proves the frame non-static),
  and the set-up `vyStoreHead` with `rx_`/`ric_vyStoreHead`), unrolled per pass since the cap
  bounds the count, the load loop's pass inverted (`ric_vyLoadIter`), a stored-`String` view's
  body up to its load loop (`vyStrView`) with the join's `ceil32_eq` and the zero-fill read
  `sliceD_data_end`, and `sstoreCost_le`, `Mem.read_write_disjoint`, `vy_mul32`, in
  [`Blanc/Lift/Vyper.lean`](../Blanc/Lift/Vyper.lean).
- Loops: a back-edge to entry `k` is reasoned about one iteration at a time on
  runs cut at `k` (`SFunc.RunCutP`, `SFunc.RunExactCut`). Safety:
  `SFunc.RunCutP.loop` (invariant; `SFunc.RunP.loop`), which
  nests because the outer cut list is a parameter; liveness:
  `SFunc.RunExactCut.iterate` builds a whole loop run from per-iteration cut
  runs; both in [`Blanc/Lift/Loop.lean`](../Blanc/Lift/Loop.lean).
- Fuel-bounded loops (a `range(cap)` loop that stops early on a test and
  otherwise returns its last iterate, e.g. Newton loops): the model
  `fuelLoop body close fuel D` and its gas `fuelCost`; safety
  `RunCut_fuelLoop_sound` from a per-pass inversion `FuelStep` at the head
  (`At n D` with counter `n < cap`; leaving runs satisfy `Out`), liveness
  `RunExactCut_fuelLoop_exact` from per-branch exact passes (`cStep`, `cStop`,
  `cCap`); peeled head copies whose back edge targets the next copy via
  `RunCut_fuelLoop_peel` / `RunExactCut_fuelLoop_peel`; the inversion split
  `SFunc.RunCutP.split_at`; all in
  [`Blanc/Lift/FuelLoopWalk.lean`](../Blanc/Lift/FuelLoopWalk.lean).
- Internal calls (`callNext`): `ric_callNext` removes `ric_call`'s halting arm under the
  kernel scan `calleeNeverHalts fs k fuel` (`decide`: the callee's entry closure
  `entryReach` is a `NoHaltSet`); the `PC` node `ric_pcAt`/`rxc_pcAt`; the Vyper call idiom
  `PUSH1 6; PC; ADD; PUSH2 t; JUMP` as `pcCallTree p t0 t1 k f`, inverted by `ric_pcCall` (a
  callee run from return address `p + 6` and the continuation) and built by `rxc_pcCall`
  (cost 19); all in [`Blanc/Lift/InvWalkCallNext.lean`](../Blanc/Lift/InvWalkCallNext.lean).
- Unrolled Vyper frame save/restore chains (a counter word walks a frame `[lo, lo + 32 n)`,
  pushing or popping one word per copy): templates `frameSaveIter`/`frameRestoreIter`,
  constants `FrameLoopTpl`, one-`rfl` chain facts `FrameSaveChain`/`FrameRestoreChain`;
  safety `ric_frameSave_chain`/`ric_frameRestore_chain`, liveness
  `rxc_frameSave_chain`/`rxc_frameRestore_chain` (cost `67 (n-1) + 56`, `70 (n-1) + 59`);
  memory `saveMem`, `restoreMem` and `restoreMem_frameWords` (the restored frame reads as the
  saved one), and the word-slot carrier `Words M L` (`Words.write`, `.agree`, `.read`) over
  `memWord`/`Mem.AgreeOutside`; all in
  [`Blanc/Lift/VyperFrameLoop.lean`](../Blanc/Lift/VyperFrameLoop.lean).
- Vyper 0.2.x checked `uint256` arithmetic and word-slot frames: the idiom trees
  `vyMulT`/`vyAddT`/`vySubT`/`vyDivT` (guard, `PUSH2 ok JUMPI` over `vyRevertT`, clean-up),
  inverted by `ric_vyMulT`/`ric_vyAddT`/`ric_vySubT`/`ric_vyDivT` (the guard as a `Nat` fact:
  `B256.Nofm`, no-wrap sum, no underflow, nonzero divisor) and built by
  `rxc_vyMulT`/`rxc_vyAddT`/`rxc_vySubT`/`rxc_vyDivT` (69/51/45/38 gas); the bridges to the
  checked naturals of `StableSwapNewton/Defs.lean` (`chkMul_toNat_of_nofm`, `chkAdd_toNat_of_lt`,
  `chkSub_toNat_of_le`, `chkDiv_toNat_of_ne` and their inverses `chkMul_inv` … `chkDiv_inv`);
  the frame carrier `WordFrame M0 M lo ws` (`ws` at `lo + 32 j`, `M0`'s size, agreement off the
  window, `Mem.Wf` kept) with `ric_mloadF`/`ric_mstoreF` (and `PUSH2` forms) and their forward
  `rxc_*F` (3/6 gas); `ScratchOut` for a callee's result in scratch word `0`
  (`WordFrame.scratch`, `ScratchOut.keepsOff` to `Mem.KeepsOff`, `ScratchOut.words`); the
  `int128` range check `B256.toNat_lt_three_of_slt` (`ri_sltV`); comparison flags
  (`toNat_lt_of_iszero_gt_eq_zero`, `eq_zero_of_iszero2_eq_zero`, `gtCheck_toNat`,
  `iszero_eq3_ne` / `iszero_eq3_eq` for a three-iteration word counter, …) and the
  forward `JUMPI` into a goto entry `rxc_branchTo_zero`/`_cut`/`_taken`; the tracked-memory
  frame kit over `MemTrack` (`MemTrack.saveMem'`/`MemTrack.restoreMem` across the frame
  save/restore chains, `Words.restoreMem'`, `Words.of_frameSlots`, `Mem.KeepsOff.widen`,
  `MemTrack.withWords`), the bridges `WordFrame.keepsOff`/`WordFrame.memTrack`/
  `WordFrame.words1`, the untracked load `ric_mloadU` (`imloadU`), `isltV`, the forward
  `rxc_slt`/`rxc_xor`, and `xname` (name the tracked memory of a forward walk); all in
  [`Blanc/Lift/VyperCheckedArith.lean`](../Blanc/Lift/VyperCheckedArith.lean).
  The fuel-loop kit's `RunExactCut_fuelLoop_peelAt` (one peeled pass at one counter, for a copy
  whose last-pass fall-through is unreachable) is in `FuelLoopWalk.lean`.
- Indexed loads from three consecutive carried words: `pickWord3` selects the word,
  `word3_indexAddr` converts `32 * i + base` to its natural offset under the explicit
  index/base bounds, and `ri_mloadWord3` inverts the actual `MLOAD` over `Words` plus
  aligned allocation. It requires all three membership facts and the exact address
  equation; it does not prove the index or any contract's array layout. Owner:
  [`Blanc/Lift/ThreeWordFrame.lean`](../Blanc/Lift/ThreeWordFrame.lean).
- Walking a successful frame along its own derivation (`XAt sevm post pc d L`: the actual state
  at `pc` and the direct children `L` still to come): `XAt.of_exec`, `xa_next`, `xa_jump`,
  `xa_jumpi`, `xa_jumpdest`, `xa_halt`, the `St`-state forms and the `CALL`/`STATICCALL` steps
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
  reply a forward run consumed is the reply `Exec.childFrames` records): the walk invariant
  `WalkAt` (derivation at `pc`, subtree checked over a matched frame and memory map) with its
  step lemmas `WalkAt.next`/`.dest`/`.zero`/`.succ`/`.toZero`/`.toSucc`/`.jump`/`.pcAt`/`.ret`/
  `.call`; `xa_retExact` (a walked exec-free tree whose gas-exact run returns puts the walk at
  the return address in the returned state, same remaining children: an internal callee crossed
  on the actual derivation); `xa_cutAt` / `xa_cutAt_start` (a walked checked node and a
  `SFunc.RunExact` run of a cut of its tree, `SFunc.CutCall`, halting in `s` put the walk at the
  cut subtree in state `s`, same remaining children; the cut may cross internal calls into an
  `ExecFreeSet` that is also a `NoHaltSet`), the cut-by-steps helpers `CutStep` (`.cl` crosses a
  call, `.pc` a return-address `PC` push), `SFunc.cutPath`, `SFunc.subAt`, `SFunc.cutPathOk`, `SFunc.cutCall_of_cutPathOk`, the
  checked-step invariant `checkNodeM_next_step` / `checkNodeM_next_at`, `NoHaltSet.lookup`, and
  `xa_staticcall_runCompiled` (a compiled `STATICCALL` from a walked state is the frame's step;
  the head child's output is its return data), in
  [`Blanc/Lift/FrameWalkCut.lean`](../Blanc/Lift/FrameWalkCut.lean). The 3pool's
  `remove_liquidity_imbalance` liveness (`RliLiveCut`, `LiveLink`) is the worked example.
- Memory across a crossed callee: `Mem.KeepsOff M M' W` (no shrink; every byte off the windows
  `W` kept) with `refl`/`trans`/`mono`/`of_agreeOutside`, the image transport
  `Mem.Reads.keepsOff`, `Words.keepsOff`, `MemMatches.keepsOff`, `memWord_keepsOff`, and the
  read algebra `Mem.read_split`, `Mem.read_split64`, `Mem.read_two_word_writes_wf`,
  `Mem.read_write_word_disjoint`, `Mem.read_write_word_inside`, in
  [`Blanc/Lift/MemGlue.lean`](../Blanc/Lift/MemGlue.lean).
- Vyper 0.2.x internal-callee walks (a callee's value contract without concrete memory
  terms, windows as `Mem.KeepsOff` of `Blanc/Lift/MemGlue.lean`): the tracked walk memory
  `MemTrack M₀ M W L` (kept off the windows `W`, carrying the words `L`, well formed) with the
  steps `ric_mloadT`/`ric_mstoreT`/`ric_mstoreO` (overwrite, `wordsOff`)/`ric_keccakT` (tactics
  `imload`/`imstore`/`imstoreO`/`ikeccak`, `wmem`, `iassert`) and the
  node-directed inversion step `istep`; load-only bases `SloadsOnly sevm b B` (`.state`,
  `.getStor`, `.logs`, `.output`, `.getCode` in `VyperCallee.lean`; `.idReady` in
  `IdentityCallGas.lean`); the checked-arithmetic guards read back as
  `chkSub`/`chkAdd`/`chkMul`/`chkDiv` (`vyChkSub`, `vyChkAdd`, `vyChkMul`, `vyChkDiv`) and the
  `ISZERO (LT …)`/`ISZERO (GT …)` branch readings; forward twins over a covered memory with the
  final memory named at the return (`∃ M', RunExactCut … ∧ facts`): `xlift`, `rxc_mloadT`,
  `rxc_mstoreT`, `rxc_keccakT`, `rxc_retT`, the guards forward (`fwdChkSub`/`Add`/`Mul`/`Div`),
  and the node-directed forward tactic `xstep` (`xmload`, `xmstore`, `xkeccak`, `xassert`,
  `xzero`, `xjump`, `xgoto`, `xret`); all in
  [`Blanc/Lift/VyperCallee.lean`](../Blanc/Lift/VyperCallee.lean).
- Vyper 0.2.x walk kit (inversion `ric_*`/`ri_*` over cut runs, forward `rxc_*` over exact
  cut runs):
  fixed-array storage slots `mstore(0xc0, s); sha3(0xc0, 0x20) + i` (`vyArrayBase`,
  `vyArraySlot`; pushed word `Bytes.keccak s.toBytes + i`) in
  [`Blanc/Lift/VyperArraySlot.lean`](../Blanc/Lift/VyperArraySlot.lean);
  a value-0 `CALL` of the identity precompile (`IdReady`, `processMessage_identity_clean`,
  `ri_call_identity`, `call_identity_step` / `rxc_call_identity` at cost
  `100 + memExp + 15 + 3·⌈is/32⌉`, world relation `ShaCallPost`) in
  [`Blanc/Lift/IdentityCall.lean`](../Blanc/Lift/IdentityCall.lean); an unchecked identity
  copy that forwarded `gas()` and failed at a nonzero depth leaves no gas
  (`ri_call_identity_gas_fail`, `gasLeft_of_run_pop`), and `IdReady` survives `SLOAD`/`SSTORE`
  bases (`IdReady.afterSload`/`afterSstore`; `SloadsOnly.idReady` across a load-only base), in
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
- Forward runs to *some* outcome, for walks through a call answered only by an `∃ d` premise
  (the outcome is learned midway, so it cannot be fixed up front): `SFunc.RunEx` /
  `SFunc.RunExCut` (`∃ r, RunExact … r ∧ Q r`), the lift `SFunc.RunEx.of` with the tactics
  `xr (rx_push rfl h ·)` / `xrc …` for any fixed-outcome step, `SFunc.runEx_iff_runExCut_nil`,
  and the fresh-state twins `rxce_call_identity`, `rxce_vyRawCallJoin`, `rxce_vyRawCallTail` in
  [`Blanc/Lift/RunEx.lean`](../Blanc/Lift/RunEx.lean).
- Frame walks keeping memory word-aligned (`M.size % 32 = 0`, which callee contracts such as
  `getDMem_spec` need): `Mem.size_write_mod32`, `Mem.size_extends_mod32`, the image steps
  `ri_mload_imgAtA`/`ri_mstore_imgAtA`/`ri_calldatacopy_imgAtA`/`ri_keccak_imgAtA` and the
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
  The same site as solc emits it under its size-favouring constant optimiser
  (creation code: `-32` as `PUSH1 0x1f NOT`, the all-ones mask as `PUSH1 0 NOT`;
  `mcpyTreeN`, `mergeTreeN`, `copy_shaN_gen`, `copy_shaN`, `packed_sha_pairN`) in
  [`Blanc/Lift/PackedShaSize.lean`](../Blanc/Lift/PackedShaSize.lean).
- Deploying lifted creation code: a gas-exact run of a checked creation certificate's
  constructor from the creation frame's start state settles through Jaune's
  `processCreateMessage`, installing the constructor's output and exposing the
  installed account's normalized storage (`liftCreate_ok`, with creation frame
  `createSeed`). `liftCreatePost_facts` identifies the target account as the raw
  target with its code replaced, followed by `Acct.clearIfEmpty`; nonempty
  installed code recovers the original raw storage equality. Arbitrary creation
  messages do not supply the nonce-zero collision premise of an actual CREATE.
  `liftCreate_post` names the exact settled world `liftCreatePost`: deposit-charged
  gas, installed code, and every other account unchanged from the constructor's
  final state. The constructor walk steps
  the shared kits lack (`rx_codecopy`, `rxc_sstore`, `rxc_callvalue`, `rx_return_any` and
  `rxc_return_any`, with the halting state `returnPost` named over a variable state;
  `returnPost_state` and `St_state` project the persistent world before substituting
  concrete memory images) in
  [`Blanc/Lift/Deploy.lean`](../Blanc/Lift/Deploy.lean); and the further steps solc 0.8
  constructors need (`rx_push0`, `rx_slt`, `rx_codesize`, `rx_log2`, and `read_covered_len`, a
  window of any length inside an aligned image) in
  [`Blanc/Lift/CreationOps.lean`](../Blanc/Lift/CreationOps.lean).
  A concrete consumer of `rx_codecopy` and `rx_return_any` is
  `ProxyCreation.runtimeReturn_runExact` in
  [`Blanc/Lift/Usdc/ProxyCreation/RuntimeReturn.lean`](../Blanc/Lift/Usdc/ProxyCreation/RuntimeReturn.lean).
  It copies and returns the executing code's 2186-byte window at offset 671,
  with 226 fixed gas plus the actual memory-expansion charge. It requires
  aligned incoming memory and stack room, and derives zero further expansion
  at RETURN from the copied memory. The separate kernel-checked
  `ProxyCreation.runtime_window` in
  [`Blanc/Lift/Usdc/ProxyCreation/RuntimeWindow.lean`](../Blanc/Lift/Usdc/ProxyCreation/RuntimeWindow.lean)
  identifies that window in the registered creation input with the registered
  proxy runtime. The companion `ProxyCreation.prefix_runExact` and
  `adminPrefix_runExact` in
  [`Blanc/Lift/Usdc/ProxyCreation/Prefix.lean`](../Blanc/Lift/Usdc/ProxyCreation/Prefix.lean)
  consume the shared `rx_callRet` API to compose the actual registered entry
  and admin-label guard with their actual internal callees and continuations.
  They derive the constructor argument, fixed label hashes, memory image and
  gas charges; the admin argument is the executing message's caller.
  `terminal_runtimeReturn` connects the final caller continuation to the
  accepted runtime return. For inversion of a successful whole registered
  constructor run, `ProxyCreation.constructor_effects_of_run` in
  [`Blanc/Lift/Usdc/ProxyCreation/Effects.lean`](../Blanc/Lift/Usdc/ProxyCreation/Effects.lean)
  derives the implementation-slot write, admin-slot write using the actual
  caller, returned runtime window, and preservation of every other account's
  storage. Its internal-callee inversions consume actual successful runs and
  work without a fork restriction. `ProxyCreation.constructor_message_zero` in
  [`Blanc/Lift/Usdc/ProxyCreation/Settlement.lean`](../Blanc/Lift/Usdc/ProxyCreation/Settlement.lean)
  composes the actual zero-value CREATE entry, the source constructor run at
  that same entry and raw result, and successful touch/code-charge settlement.
  A row distinct from both literal slots is zero in the installed result,
  including the empty-account deletion branch of code installation.
  `ProxyCreation.constructor_message_effects` uses the same actual entry,
  source run, raw result and successful charging to derive the installed
  registered proxy runtime and the entire target storage: empty storage with
  the initial implementation and actual caller admin written. Runtime length
  rules out account deletion and preserves those administrative words; no new
  nonempty-code, nonce, fork or desired-state premise is required. Actual
  bytecode-to-source lifting, historical occurrence and transaction settlement
  remain separate obligations; the local source run is an explicit premise.
  At a raw frame of a `ConfiguredHistoryTraceIn`,
  [`Blanc/Lift/Usdc/ProxyCreation/HistoryFrame.lean`](../Blanc/Lift/Usdc/ProxyCreation/HistoryFrame.lean)
  derives that source run from the frame (`constructor_run_of_exec` over
  `lift_sound_noStateGas`, entry facts from `rawFrame_entryFacts`):
  `constructor_effects_rawFrame` and `constructor_row_preserved_rawFrame`
  need only success and the registered creation code. Installation by
  `processCreateMessage` is not part of them.
  `ProxyCreation.constructor_effects_of_createTrace` in Settlement starts
  from the same clean `ProcessCreateMessageTrace`: it derives the actual
  interpreted run, source run and successful code deposit, then reuses the
  existing effects composer to obtain the installed proxy code and two-slot
  storage. `constructor_zero_of_createTrace` projects any row distinct from
  those slots to zero. Both reuse `constructor_witness_of_createTrace`, which
  retains the exact raw source run, touch, charge and installed result.
  `constructor_deletions_of_createTrace` derives preservation of inherited
  deletions from the shared balance-silent frame theorem, with no installed-code
  premise. In Transaction, `transaction_constructor_deletions` derives the empty
  deletion set from actual preparation and clean CREATE; both transaction-effect
  theorems consequently need no caller-supplied deletion exclusion. Actual
  transaction identity, success and the chain-boundary seed remain obligations.
  `ProxyCreation.original_constructor_effects_after_cut22` in
  [`Blanc/Lift/Usdc/ProxyCreation/HistoryCut.lean`](../Blanc/Lift/Usdc/ProxyCreation/HistoryCut.lean)
  applies those effects to the selected head of a configured block's actual
  `TxSplit 22`, at `cut.afterBenv.state` immediately after settlement.
  `original_constructor_seed_after_cut22` packages that code, exact two-slot
  storage and tracked zero allowance rows as `OriginalConstructorSeed`, using
  explicit separation from the implementation and admin slots.
  `original_constructor_seed_of_receipt_cut22` derives that same head's clean
  message outcome from a successful receipt at the final block output, through
  the existing bounded receipt-preservation API. Constructor receiver, input,
  value, recovered sender and nonce remain explicit; identifying the supplied
  block with historical C, authenticating its receipt commitment and placing
  it in the consumed history remain caller obligations. No C-to-D continuity
  or pre-D governance restriction follows from this seed adapter.
- The settled world of a zero-value CREATE as a closed term of its input world (so a later
  message that takes it as `origState` can evaluate it): the entry world `entryState` and
  `entry_state` (target storage cleared and nonce incremented; zero-value entry
  then preserves that environment, without a caller debit or target credit),
  and `liftCreatePost_state` (the constructor's world with its output installed) in
  [`Blanc/Lift/CreateEntry.lean`](../Blanc/Lift/CreateEntry.lean).
- Creating an EIP-1167 clone of any implementation `I` by the 9-byte copier `602d3d8160093d39f3`:
  `creationCode I` (copier ++ `forwarderCode I`), its certificate `copierCert`, the 28-gas walk
  `run`, and `create` — a zero-value CREATE on every covered fork leaves `msg.gas - 28 - 9000`,
  installs `forwarderCode I` with empty storage (`cloneAcct`), keeps every other account, and states
  the settled world exactly — given the consumer's registered `Cert.check` of its input, in
  [`Blanc/Lift/Clone1167.lean`](../Blanc/Lift/Clone1167.lean). A modeled harness: a consumer labels
  its registered input synthetic (worked use: `Lift/VyperNonreentrantDeployed/Vulnerable/Reach/Deploy.lean`).
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
  Worked use: `pair_create2` in
  [`Blanc/Lift/UniswapV2Pair/Creation/Deploy.lean`](../Blanc/Lift/UniswapV2Pair/Creation/Deploy.lean).
- Free-pointer memory with a pointer independent of allocation: `PtrMem p n M`
  in [`Blanc/Lift/ExactWalkMemory.lean`](../Blanc/Lift/ExactWalkMemory.lean)
  combines aligned size, `Mem.Wf` and the existing `MemMatches` word at offset64.
  It permits pointer128 with allocated size96. `PtrMem.init`, `word`, `write`,
  `set` and `read_self` expose initialization, disjoint word writes, pointer
  replacement and reads within the allocation. The Pair's `GetterMemory` and
  `GetterWalk` consume it for the actual one-word return at offset128; use this
  carrier when the fixed pointer96 of `FpMem` does not describe the bytecode.
  For arbitrary byte writes, `PtrMem.write_bytes_of_le` in
  [`Blanc/Lift/ByteWindowMemory.lean`](../Blanc/Lift/ByteWindowMemory.lean)
  preserves that same pointer/allocation carrier when the whole write fits
  inside the allocation and is disjoint from the pointer word at offsets64..95.
  It consumes the actual byte list and does not restrict it to a word-sized
  reply. The bare `PtrMem` head cannot distinguish this byte-write obligation
  from initialization, word writes or pointer changes; this is registry-only.
  The same module's `mergeFour_bytes` gives the fixed high-four/low-twenty-eight
  byte image of a masked word merge; see the M1 manual codec route above.
- Free-pointer word without an allocation size: `PtrWord p M` in
  [`Blanc/Lift/PtrWordMemory.lean`](../Blanc/Lift/PtrWordMemory.lean) keeps only
  `Mem.Wf M` and the pointer word at offset64. Use it instead of `PtrMem` when a
  walk's allocation grows by an unbounded reply (for example a moved free pointer
  after a full-returndata copy), so no size bound is owed. `PtrWord.of_ptrMem`
  enters it; `write` (any byte list at offset96 or above), `extend`, `extends`
  and `set` (pointer replacement) preserve it; `memRead_extend_fst` reads through
  a read's extension. The Pair's skim walk consumes it for its second query and
  transfer after transfer0's allocation.
- Four consecutive word stores read back as one window: `Mem.read_four_word_writes` in
  [`Blanc/Lift/WordWindowMemory.lean`](../Blanc/Lift/WordWindowMemory.lean) reads the
  128 bytes at `s` after word stores at `s`, `s+32`, `s+64`, `s+96` (over a well-formed
  memory) as the four words' concatenation, the payload of a four-word ABI event staged at
  the free pointer. The Pair's swap tail consumes it for the `Swap` log.
- Gas-exact writer walks for solc-0.4-style runtimes: the scratch-memory invariant `FpMem n M` (word-aligned,
  free pointer `0x60`, kept for an arbitrary `M`; `FpMem.init`, `FpMem.write`, `FpMem.write_out`,
  `FpMem.readback`, `scratchW`), its steps (`rx_mstoreF`, `rx_mstoreOut`, `rx_mloadFp`, `rx_keccakF`,
  `rx_log2W`, `rx_log3W`, `rx_returnW`, `rx_stop`, `rx_mask20`, `rx_mask20_adr`, `rx_swap4`), `SLOAD`/`SSTORE` with
  named charges (`rx_sload_selC`, `rx_sstoreC`), the account facts after a selected `SSTORE`
  (`afterSstore_getAcct`, `afterSstore_getBal`, `afterSstore_empty`, `afterSload_getAcct`), `require(x >= y)`
  (`ltCheck_zero_of_le`) and the tactic macros that apply one step to the head instruction (`rdest`, `rpush`,
  `rdup`, `rswap`, `rpop`, `radd`, `rsub`, `riszero`, `rmask`, `rmst`, `rmld`, `rkec`, `rhash`, `rsloadC`,
  `rsstoreC`, `rsent`, `rlog2`, `rlog3`, `rreq`) in [`Blanc/Lift/ExactWalkSolc.lean`](../Blanc/Lift/ExactWalkSolc.lean);
  a value-bearing (`callNZ_ex`, `rx_callNZ`) or zero-value (`callZ_ex`, `rx_callZ`) `CALL` to a recipient without
  code, at its net charge `callNet`, with what it leaves (`CallPost`: output, logs, error, refund counter, emptiness of
  the accounts to delete and the value-sensitive state relation) in
  [`Blanc/Lift/ExactWalkCall.lean`](../Blanc/Lift/ExactWalkCall.lean).
  `CallPost.state` is exact state identity at zero value and the debit/credit
  relation otherwise. `CallPost.getStor` preserves an observed owner when
  the value is zero or `State.Protected` holds in the entry world; an emptied
  unprotected account can lose storage under a nonzero transfer.
  Worked use: the deployed WETH9's writers,
  `Blanc/Lift/Weth9/LiveApprove.lean` … `LiveHistory.lean`.
- Jump destinations: Jaune's own `jumpable_eq_jumpdestOk` (`Jaune/Machine.lean`)
  replaces its exponential `jumpable` by the linear `jumpdestOk` scan, for every
  byte string; Blanc keeps no copy.
- Properties of the lifted program without per-path walks: a state-silent
  entry set (`SilentSet`, `SFunc.Run.state_of_silent`) in
  [`Blanc/Lift/Silent.lean`](../Blanc/Lift/Silent.lean), its balance analogue
  (`BalSilentSet`, `SFunc.RunP.getBal_of_balSilent`) in
  [`Blanc/Lift/BalSilent.lean`](../Blanc/Lift/BalSilent.lean). Its stronger
  `SFunc.RunP.balance_deletion_frame_of_balSilent` also preserves both
  deletion-tracking sets through the same induction, with the old balance
  theorem as a projection; no fork or installed-code premise is added. A quiet entry set
  that may make static calls (the SHA-256 precompile) but writes no storage and
  emits no log (`QuietSet`, `SFunc.Run.world_of_quiet`) in
  [`Blanc/Lift/Quiet.lean`](../Blanc/Lift/Quiet.lean), which also proves that a static
  frame on a covered fork keeps its log list on every successful outcome, committing or
  not (`Exec.logs_eq_of_static_ok`; committed form `Exec.logs_committedPost_eq_of_static`),
  a storage-local entry set that may store and log but whose only call is `STATICCALL`
  (`StorLocalSet`, `SFunc.Run.foreignStor_of_storLocal`: every account other than the
  executing one keeps its storage) in
  [`Blanc/Lift/LocalStorage.lean`](../Blanc/Lift/LocalStorage.lean),
  and Hoare-style
  composition across one internal call or an ABI wrapper
  (`SFunc.RunP.hoare_single_call`, `hoare_single_call_with_gotos`,
  `hoare_wrapper`) in [`Blanc/Lift/Hoare.lean`](../Blanc/Lift/Hoare.lean).
- The preservation ladder over a code image instead of `Prog.compile`:
  `CodeSem` (image, run relation, `correct`) in
  [`Blanc/CommonCore.lean`](../Blanc/CommonCore.lean); `ContractSpecSem`, its
  `Sound`/`Preserves` rungs, `preserves_lift_sem` and `post_of_call_self` in
  [`Blanc/LadderSem.lean`](../Blanc/LadderSem.lean); the admitted forms
  `SoundAdmitted`/`PreservesAdmitted`/`preserves_inv_admitted` in
  [`Blanc/ContractAdmissionSem.lean`](../Blanc/ContractAdmissionSem.lean) and
  `lift_inv_admitted_sem` in
  [`Blanc/ExecutionAdmissionSem.lean`](../Blanc/ExecutionAdmissionSem.lean),
  which carry a frame-local premise (such as WETH9's allowance-slot collision
  premise) up the message, transaction, body and history rungs. The
  `Prog.compile` ladder in [`Blanc/Ladder.lean`](../Blanc/Ladder.lean) is the
  instance of this one at `Prog.compile`, with byte-identical statements;
  [`Blanc/LadderBase.lean`](../Blanc/LadderBase.lean) holds the
  code-independent vocabulary both share.
- A booked-sum solvency invariant (the sum over *distinct* balance slots, as a
  hashed Solidity mapping needs) with its slot obligations proved once:
  `BookedInv` and `ContractSpecSem.ofBookedSum` in
  [`Blanc/Lift/BookedSpec.lean`](../Blanc/Lift/BookedSpec.lean).
- The same with a storage-only conjunct (for example a footprint's `Support`):
  `ContractSpecSem.ofBookedSumWith` in
  [`Blanc/Lift/BookedSupportSpec.lean`](../Blanc/Lift/BookedSupportSpec.lean), whose obligations are
  those of `ofBookedSum` plus the fact that ether movements leave the contract's storage alone.

There is no recipe: the entry points are whole-contract theorems, not goal
shapes a trigger could match.

The Pair cursor, source-call and positional statements named below are the
historical `H` forms, which take `rules.stateGas = none` (and `rules.bal = none`
where it appears) as premises instead of `CoveredFork`. The `CoveredFork` forms
were removed as unconsumed. Under a covered fork recover one by applying the `H`
form to `CoveredFork.rules_stateGas_none` and `CoveredFork.rules_bal_none`,
bridging the world argument with the `…H_of_covered` equations (for example
`swapPrefixWorldH_of_covered`) and converting an `H` carrier back with its
`toCovered` conversion (for example `SwapCallbacksH.toCovered`).

Shared Pair adapters retain their supplied original-bytecode cursor and actual
world rather than selecting a call through a source run. The reusable fee
request/reply carrier in
[`PairFeeObservation.lean`](../Blanc/Lift/UniswapV2Pair/PairFeeObservation.lean)
keeps the original-root occurrence, raw slot, complete physical reply and decoded
word. Its `returnCursor`, `returnState`, `returnCutData` and `returnCutExact` in
[`PairFeeReturn.lean`](../Blanc/Lift/UniswapV2Pair/PairFeeReturn.lean)
transport that same reply through the actual internal return with arbitrary
caller and outer continuations; `returnCutExact` retains `cut.node = N` for
consumers which sample storage from the returned world. `returnCutData` also
retains the fee guards and full physical `feeBranchPost` at that exact node;
`returnCutExact` and `returnCut` project the same witness. The ordinary guarded
static-call adapter `static_source_call_atH`
in [`StaticSourceCall.lean`](../Blanc/Lift/UniswapV2Pair/StaticSourceCall.lean)
binds the supplied occurrence to the request, reply and original per-spawn
partition through its actual slot queue. These are registry entries: their
compound occurrence and cursor obligations have no reliable single goal-head
trigger.

`CallOccurrenceStep.sourceSlotQueue` in
[`SourceSlotQueueExistence.lean`](../Blanc/Lift/UniswapV2Pair/SourceSlotQueueExistence.lean)
derives a complete selected queue from the supplied actual call and parent index,
including the synchronous `.none` case and settlement pruning. Its proof uses
that call's original slot and spawning derivation; no guessed queue, code or
commit premise is required.

`feeBranchSourceKeys_contains` in
[`PairFeeSourceKeys.lean`](../Blanc/Lift/UniswapV2Pair/PairFeeSourceKeys.lean)
preserves every incoming tracked key through the fee branch's conditional
recipient extension. `lpMintTouched_rows`, `feeMintFresh_of_universe` and
`pairFeeSourceKeys_sub` derive recipient freshness and key containment in a
supplied separated universe; `feeBranchSourceFee_unlocked` preserves the lock
word. The old Mint helpers and Burn lock helper delegate to these same proofs.
The existing Burn pricing source proof consumes the inclusion when deriving
LP-row freshness.

[`PairTraceKeys.lean`](../Blanc/Lift/UniswapV2Pair/PairTraceKeys.lean) owns the
unchanged `mintReplyRow`, `mintFeeReplyKeys`, `mintTraceKeys`,
`mintTraceKeys_frame` and `mintTraceKeys_rows` definitions and laws.
`mint_feeReply_memH` places the supplied actual fee primitive's own reply row
in that trace, covering entered child roots and synchronous precompile answers.
The original names remain available through Mint's imports. The actual Burn
consumer applies this only to the primitive projected from its retained slot;
it does not use trace membership to select an occurrence. These compound
trace/universe obligations have no reliable single recipe trigger.

`SourceCallAt.noCodeMutableTranscript` in
[`SourceSlotEventsEmpty.lean`](../Blanc/Lift/UniswapV2Pair/SourceSlotEventsEmpty.lean)
derives the empty mutable transcript for an ordinary missing-entry reply from
the same original absent slot and its complete events mapped to selected turns.
It preserves synchronous call positions and does not assume an empty queue.

[`PairPositionalEntry.lean`](../Blanc/Lift/UniswapV2Pair/PairPositionalEntry.lean)
provides `PairEntryAt` for the actual selector and decoded entry, and
`PairRootedConsumes`/`PairPositionalOutcome` bind the same original root,
transcript, result and output. Entry decoding alone does not establish nested
admission. The ready family producers in
[`PairPositionalReady.lean`](../Blanc/Lift/UniswapV2Pair/PairPositionalReady.lean)
consume the supplied incoming checkpoint and the same recursively admitted positional results.
`pair_admitted_ready_supply` assembles `PairAdmittedReadySupply` for the lock-free families,
Mint, Sync and views; Swap, Skim and Burn have separate canonical producers.
The separate `pair_admitted_skim_supply` in
[`PairPositionalSkim.lean`](../Blanc/Lift/UniswapV2Pair/PairPositionalSkim.lean)
retains the same four-slot canonical result, recursively admitted mutable
queues, actual output and represented state. It is below the final all-family
instance. The separate `pair_admitted_burn_supply` in
[`PairPositionalBurn.lean`](../Blanc/Lift/UniswapV2Pair/PairPositionalBurn.lean)
retains the same seven-call canonical result, both recursively admitted mutable
queues, actual payout bytes and represented state under the original separated
universe. The separate `pair_admitted_swap_supply` in
[`PairPositionalSwap.lean`](../Blanc/Lift/UniswapV2Pair/PairPositionalSwap.lean)
retains the same optional-call canonical result and recursively admitted queues,
with actual output and represented state. `pairAdmittedSupplyRules` and
`pairAdmittedSupply` in
[`PairPositionalSupply.lean`](../Blanc/Lift/UniswapV2Pair/PairPositionalSupply.lean)
assemble all eleven concrete families through the existing selector dispatcher,
without an additional supply premise for callers.

`transfer_source_call_atH` in
[`TransferSourceCall.lean`](../Blanc/Lift/UniswapV2Pair/TransferSourceCall.lean)
binds an ordinary transfer request to the supplied actual CALL, its complete
slot queue and per-spawn partition. Its entered bit is the actual slot's
`isSome`; the selected-step CALL inverse derives the same message, process,
spawn and resume. It does not select a different model call.
`pair_code_guard_cursor_stateH` in
[`PairCodeGuardCursor.lean`](../Blanc/Lift/UniswapV2Pair/PairCodeGuardCursor.lean)
advances the supplied actual code-size guard, derives code presence from its
successful branch and retains the full warmed world and K. The existing fee
cursor theorem delegates to this same proof.
For a checked referenced branch, `pair_code_guard_to_cursor_stateH` retains
the same guard data and advances to the certificate-selected successor;
the original literal-branch interface is preserved.

The shared dispatcher entry `pair_dispatch_selector_cursor_stateH` in
[`PairDispatchCursor.lean`](../Blanc/Lift/UniswapV2Pair/PairDispatchCursor.lean)
retains the actual root state before either selector comparison route; the
existing upper-comparison wrapper projects it. Its pure `pair_initial_line_state`,
`pair_size_line_state` and `pair_selector_line_state` inverses also serve raw
routing without final success. `pair_raw_reach_call_selector` in
[`PairRawDispatch.lean`](../Blanc/Lift/UniswapV2Pair/PairRawDispatch.lean)
starts at the actual PC-zero source entry and routes any reached external
instruction through one of the six call-capable wrappers, retaining its selector,
world, initialized memory and remaining reach. It excludes fallback and quiet
entries using checked source regions. It does not classify the wrappers' calls
or establish callback-to-token exclusion.
`pair_raw_reach_call_sites` and `pair_raw_node_call_sites` in
[`PairRawCallSites.lean`](../Blanc/Lift/UniswapV2Pair/PairRawCallSites.lean)
classify every reached external instruction through the certificate-wide
`nodesSatisfy` check: STATICCALL, or CALL with the exact safeTransfer or callback
continuation. The actual-node form retains the original `StepIn` reach and
checked cursor under state-gas absence, with no final-outcome premise. It rejects
other external instruction families but does not determine CALL operands or
supply callback target exclusion.
The parameterized quiet-entry
cuts and checked closed regions in
[`PairNoCallEntries.lean`](../Blanc/Lift/UniswapV2Pair/PairNoCallEntries.lean)
derive `PairNoCallEntry.root_noExecH` from that same supplied successful root.
[`PairNoCallSource.lean`](../Blanc/Lift/UniswapV2Pair/PairNoCallSource.lean)
consumes this raw certificate to couple the selected source frame to the
empty actual child queue; it does not assume a caller-provided no-call suffix.

For the Pair's shared internal callees, use
[`PairReservesCursor.lean`](../Blanc/Lift/UniswapV2Pair/PairReservesCursor.lean),
[`PairCheckedSubCursor.lean`](../Blanc/Lift/UniswapV2Pair/PairCheckedSubCursor.lean),
[`PairCheckedMulCursor.lean`](../Blanc/Lift/UniswapV2Pair/PairCheckedMulCursor.lean)
and [`PairLPBurnCursor.lean`](../Blanc/Lift/UniswapV2Pair/PairLPBurnCursor.lean).
They retain arbitrary original caller/outer continuations and derive residual
gas and complete return state from the supplied actual execution. The transfer
initializer and copy/partial-merge inverses live in
[`PairTransferInitialize.lean`](../Blanc/Lift/UniswapV2Pair/PairTransferInitialize.lean)
and [`PairTransferPreparation.lean`](../Blanc/Lift/UniswapV2Pair/PairTransferPreparation.lean);
their actual cursor consumers are
[`PairTransferCursor.lean`](../Blanc/Lift/UniswapV2Pair/PairTransferCursor.lean)
and [`PairTransferCopyCursor.lean`](../Blanc/Lift/UniswapV2Pair/PairTransferCopyCursor.lean).
`pair_transfer_request_cursor_stateH` in
[`PairTransferRequestCursor.lean`](../Blanc/Lift/UniswapV2Pair/PairTransferRequestCursor.lean)
normalizes the physical transfer payload at a moving free pointer;
`pair_transfer_call_of_gas_cursorH` in
[`PairTransferCallCursor.lean`](../Blanc/Lift/UniswapV2Pair/PairTransferCallCursor.lean)
binds it to the supplied root's actual call slot and returned cursor. Use the
literal line inverses through `CursorStateAt.line`, and retain the occurrence
carrier when subsequent consumers need raw child identity.
For raw helper reaches to an external instruction, use
`safeTransfer_raw_reach_call` in
[`SafeTransferRawCall.lean`](../Blanc/Lift/UniswapV2Pair/SafeTransferRawCall.lean).
From the actual local helper entry, pointer bounds and a primitive-run projection,
it identifies the sole CALL, its seven operands and exact 68-byte transfer input.
It assumes neither final success nor child commitment. Entry coverage from PC zero
and callback exclusion remain separate obligations. Both raw and successful
wrappers reuse `pair_transfer_initialize_line_state` and
`pair_transfer_partial_line_state` in the existing cursor modules.
The generic literal-line cut is `Reach.split_nexts` in
[`Blanc/Lift/ReachLine.lean`](../Blanc/Lift/ReachLine.lean); it retains the shared
endpoint between the completed non-external line and residual raw reach.
`pair_transfer_reply_cursor_stateH` in
[`PairTransferReplyCursor.lean`](../Blanc/Lift/UniswapV2Pair/PairTransferReplyCursor.lean)
uses that supplied actual slot and returned cursor to derive the success flag,
unchanged parent memory/output, the operand-derived full-reply bound, optional
bool acceptance and the complete actual internal return allocation. Its quiet
span stops at the original caller, which may make further calls; it does not
replace the raw slot entry bit with a code-existence assumption.
The already reached optional-bool decoder is inverted by
`safeTransfer_decodedReturned_inv` in
[`SafeTransferWalk.lean`](../Blanc/Lift/UniswapV2Pair/SafeTransferWalk.lean).
It derives acceptance and the complete physical return allocation without
selecting an external call; the original whole-helper inverse delegates to it.

The same file's `safeTransfer_call_invH`, `safeTransfer_dynamicCall_post_invH`,
`safeTransfer_dynamicReply_invH` and `safeTransfer_dynamicReturned_invH` require
only state-gas absence for the actual CALL, full reply and physical return image.
The remaining modern inverses project these shared bodies. No BAL, access schedule or delegation premise is added; helper entry,
pointer geometry and an actual successful helper continuation remain explicit.

For the historical raw Swap token/recipient segment,
`swap_raw_recipient_guardsH` in
[`SwapRawRecipientH.lean`](../Blanc/Lift/UniswapV2Pair/SwapRawRecipientH.lean)
derives both recipient-versus-token inequalities and the actual remaining reach
at the optimistic-transfer branch. It keeps the cached token words and the
successor state after the two historical SLOADs, requiring only BAL absence for
those reads and no final success or assumed guard. The common literal owner is
`swapTokenLoadLine_invH` in `SwapFront.lean`. Root-to-body coverage and callback classification remain separate.

For the original Swap prefix, `swap_prefix_cursor_stateH` in
[`SwapPositionalPrefix.lean`](../Blanc/Lift/UniswapV2Pair/SwapPositionalPrefix.lean)
derives the selector, ABI, lock/write, packed-reserve return, liquidity and
recipient route from original code, fork, selector and successful PC-zero
execution. It retains the full world, raw cached locals, initialized memory,
original stop continuation and call-free root gap. The five ABI and eight body
literal line inverses are shared with the unchanged legacy source inverses in
`SwapAbi.lean` and `SwapFront.lean`; no desired endpoint or residual gas is a
public premise.

The moved final balance output uses the original memory image facts
`burnBalanceReplyMemory_extended`, `burnBalanceReplyMemory_ptr` and
`burnBalanceReplyMemory_word` in
[`BurnBalanceWalk.lean`](../Blanc/Lift/UniswapV2Pair/BurnBalanceWalk.lean).
They preserve the supplied physical free pointer and identify the decoded
word; the original whole-read inverse and actual final reply cursor share
these facts.

`swap_transfers_cursor_stateH` in
[`SwapPositionalTransfer.lean`](../Blanc/Lift/UniswapV2Pair/SwapPositionalTransfer.lean)
composes both optional optimistic transfers from those same original public
premises. `SwapTransfers` retains each real amount branch, original-root CALL
slot, complete payload/reply, caller cursor and moving memory/pointer bounds;
transfer1 starts from transfer0's own world, memory and returned node. A skipped
amount retains an actual call-free gap; an executed CALL with an absent child
slot still has its physical occurrence. The shared transfer request/call/reply
cursors supply each occurrence rather than searching by an equal payload.

`swap_callback_cursor_stateH` in
[`SwapPositionalCallback.lean`](../Blanc/Lift/UniswapV2Pair/SwapPositionalCallback.lean)
adds the optional callback to that same original-root chain. `SwapCallbacks`
starts its callback at transfer1's actual result; the executed branch retains
its own derived code guard, warmed CALL, exact variable calldata, full physical
reply and checked caller join. The empty-data branch selects no CALL. Pointer
and ABI length bounds are derived internally. Callback preparation and join
lines are shared with the unchanged legacy callback inverses.

`swap_balances_cursor_stateH` in
[`SwapPositionalBalance.lean`](../Blanc/Lift/UniswapV2Pair/SwapPositionalBalance.lean)
adds both required observations to the same optional-call carrier, from the
same four original premises. Each `SwapBalanceOccurrence` keeps its own guarded
STATICCALL, full reply and actual word decoder at the moving pointer. The
second starts from the first returned node, memory and decoded local.
`SwapBalances.noExecTail` excludes all further external instructions after the
actual final reply, including the original pending wrapper STOP.

[`SwapPositionalSuffix.lean`](../Blanc/Lift/UniswapV2Pair/SwapPositionalSuffix.lean)
finishes the same two decoded balance replies through the actual body return and
pending wrapper STOP. `swap_physical_result` retains the complete original-root
optional-call chain, the same acceptance and range facts, final machine image
and actual output under only code equality, covered fork, Swap selector and
successful original `Exec 0`. Empty output follows only with a fresh input output
buffer in the canonical integration.

[`SwapPositionalRefinement.lean`](../Blanc/Lift/UniswapV2Pair/SwapPositionalRefinement.lean)
exports the original `swap_bytecode_exact_consumes` and `_own` names under
unchanged caller premises. Both retain one `SwapPositionalCanonicalResult`,
including its actual optional slots, full recursively admitted queues, output,
storage and foreign-storage fields. `swap_bytecode_forward_consumes` returns
that same carrier for its original constructed raw execution.
The Mint positional carrier also retains `SourceAdmission` on its own selected
positional proof; the concrete Mint supplier projects that field directly.
[`MintPositionalLogs.lean`](../Blanc/Lift/UniswapV2Pair/MintPositionalLogs.lean)
derives the fee-prefix and complete raw/source log image from that same Mint
canonical result. The original `mint_bytecode_exact_consumes` and `_own` names
in [`MintPositionalRefinement.lean`](../Blanc/Lift/UniswapV2Pair/MintPositionalRefinement.lean)
retain the admitted result with these log images and, for `_own`, foreign-storage
silence, under unchanged caller premises.

[`SwapSourceOccurrenceTransfer.lean`](../Blanc/Lift/UniswapV2Pair/SwapSourceOccurrenceTransfer.lean)
binds each supplied Swap transfer to its typed request and complete actual slot
queue. `swapObservedTransferReply` retains that slot's entered bit, and
`swap_resume_observed_transfer` transports both accepted optional-bool replies
through the same typed continuation without changing the entered bit.

[`SwapSourceOccurrenceCallback.lean`](../Blanc/Lift/UniswapV2Pair/SwapSourceOccurrenceCallback.lean)
binds the guarded callback request and successful full-byte reply to its same
physical CALL, message, process, partition and complete queue. The code bit is
justified by the actual guard rather than by the entered slot bit.

[`SwapPositionalCanonical.lean`](../Blanc/Lift/UniswapV2Pair/SwapPositionalCanonical.lean)
exports `swap_positional_canonical` under the original canonical public premises.
Its one result carries the original physical chain, same recursively admitted
source transcript/result, actual output, finite storage/key growth, full logs
and child returns, bounds, unlocked/checkpoint/context and foreign storage.
`positional`, `admission` and `forget` project that same admitted proof;
`terminal_logs` exposes actual post-callback Sync-then-Swap order. Actual
unguarded transfer entry bits are retained; compatibility does not force them
into the old hardcoded-true legacy transcript.

[`SwapPositionalSourceSuffix.lean`](../Blanc/Lift/UniswapV2Pair/SwapPositionalSourceSuffix.lean)
uses the same two balance replies and carried finite frame for pricing, update
acceptance and admitted static continuations. Its actual no-call suffix finishes
that same frame, with unlocked storage, checkpoint/context, full source/raw log
images and foreign storage transported through the same physical post image.

[`SwapSourceOccurrenceBalance.lean`](../Blanc/Lift/UniswapV2Pair/SwapSourceOccurrenceBalance.lean)
binds both actual guarded STATICCALLs to their full replies and complete static
view queues. `SwapBalancePairSource` retains their same authentic paths and the
second source frame resumed from the first exact request; finite key freshness
is projected from the carried representation and original root universe.

[`SwapPositionalMutableCallback.lean`](../Blanc/Lift/UniswapV2Pair/SwapPositionalMutableCallback.lean)
retains the same guarded callback's complete events and recursively admitted
children. `swap_source_callbacksH` composes all optional mutable calls from the
original decoded source entry to the same actual post-callback node and frame.

[`SwapPositionalMutableTransfer.lean`](../Blanc/Lift/UniswapV2Pair/SwapPositionalMutableTransfer.lean)
retains each transfer's same complete event queue, mapped selected turns,
recursively admitted children, checkpoint, finite locked representation and log
images. `swap_optional_transfer_admittedH` shares both optional-transfer source
phases and composes only `nextMutableCall` with the same selected queue; its
source index increases exactly when that external instruction executes.

The Pair mutable fold's `mutable_selected_root_with` in
[`MutableTurns.lean`](../Blanc/Lift/UniswapV2Pair/MutableTurns.lean)
parameterizes child consumption and turn introductions while the existing
`mutable_selected_root` projects the original interface. For same-occurrence
nested consumption, use `mutable_source_slot_turns` in
[`MutablePositionalFold.lean`](../Blanc/Lift/UniswapV2Pair/MutablePositionalFold.lean).
It binds the actual selected slot, its full queue, and each same-witness
child's positional consumption and committed output.

For recursive entry admission on that same selected proof, use
`AdmittedSourceConsumes` and `SourceAdmission` in
[`SourceAdmission.lean`](../Blanc/Lift/UniswapV2Pair/SourceAdmission.lean),
then `admitted_source_slot_turnsH` and `AdmittedMutableTurns` in
[`AdmittedMutableFold.lean`](../Blanc/Lift/UniswapV2Pair/AdmittedMutableFold.lean).
These acyclic adapters parameterize child authentication, retain the complete
actual slot event queue and its selected turns, and index each recursive
admission by the same child consumption proof. The Pair endpoint
`PairAdmittedConsumes` uses `PairSourceAdmission` in
[`PairPositionalAdmission.lean`](../Blanc/Lift/UniswapV2Pair/PairPositionalAdmission.lean).
For actual locked children, `lockedPairAdmittedSupplyH` and
`locked_admitted_mutable_source_slot_turnsH` in
[`MutablePositionalLockedSupply.lean`](../Blanc/Lift/UniswapV2Pair/MutablePositionalLockedSupply.lean)
retain the same child selector admission, positional proof, committed output,
incoming representation and complete mutable event/turn queues.
`AdmittedSourceConsumes.nextMutableCall` in `AdmittedMutableFold.lean`
composes that same selected turn proof and its recursive admission.

Under the historical rule facts (`rules.stateGas = none`, `rules.bal = none`)
in place of `CoveredFork`: the fold is proved once over any admitted block
rules that rule out state gas (`PairFrameSupplyWithOn`,
`mutable_selected_root_withOn`, `mutable_retained_fold_inv_withOn`,
`mutable_source_slot_turns_withOn`); the modern `_with` forms are its
`CoveredFork` instance. The historical supplies are `PairFrameSupplyH` and
`PairFrameSupplyWithH` (`PairFrameSupplyWithH.on`), with
`PairFrameOutcome.mono` to weaken a frame's authentication; the slot fold is
`admitted_source_slot_turnsH`. For locked children, `LockedAuthH` (the permit
authenticated by `PermitRecoveryAuthH`; `LockedAuthH.toCovered` recovers
`LockedAuth`), `lockedPairSupplyH`, `lockedPairAdmittedSupplyH` and
`locked_admitted_mutable_source_slot_turnsH` in `LockedSupply.lean` and
`MutablePositionalLockedSupply.lean`. Every frame admitted below a root runs at
the root's block statics (`SourceSlotEvents.located_benvStat`, from the generic
`Exec.retainedTargetFramesFromAt_rawFrameRoot` and `Exec.frameAdmitted_benvStat`),
so `SourceAdmission.mono_benvStat` and `MutableAdmission.mono_benvStat` in
`SourceAdmission.lean` weaken the authentication wherever it holds under a
predicate of those statics. The Pair endpoint under the historical facts is
`PairAdmittedConsumesH` (`LockedAuthH` admission) with `PairAdmittedSupplyH`;
`PairAdmittedConsumesH.covered` and `PairAdmittedSupplyH.covered` recover the
modern forms under `CoveredFork`. The same weakening for one retained fold or
queue is `AdmittedSourceConsumes.mono_benvStat`,
`AdmittedMutableTurns.mono_benvStat` (`AdmittedMutableFold.lean`),
`SourceSlotEvents.located_inherits` and `SourceSlotEvents.turns_mono_benvStat`;
`LockedAuthH.toCovered` and `PermitRecoveryAuthH.toCovered` convert the
historical authentication to the covered one under a covered fork. Skim's historical supply is
`pair_admitted_skim_supplyH` in `PairPositionalSkim.lean`, over
`skim_positional_canonicalH`; the cached token and reserve words read storage
only, so `skimToken0_eqH`, `skimToken1_eqH` and `skimReserve0_eqH` in
`SkimWalk.lean` restate them over the historical lock world without a fork fact.

For a retained factory fee observation, `PairFeeObservationH.sourceCall` in
[`PairFeeSourceCall.lean`](../Blanc/Lift/UniswapV2Pair/PairFeeSourceCall.lean)
binds the supplied original slot, complete physical reply, literal feeTo
request and code guard to the supplied model frame and full path queue.
Burn and Mint supply their own finite factory-word and frame bindings;
the adapter preserves the observation's actual call and paths.

## Common-library-first workflow

A needed definition, lemma, tactic, or instance has a **generic shape** when
its statement nowhere mentions the contract immediately being worked on — when
that contract's own names could be abstracted away without changing what it
says. Every generic-shaped need triggers this workflow. It is the standing
default for all Blanc work, not per-goal advice, and it exists because the
point of each new contract is to leave the common library stronger than it
found it, not merely to add the contract.

1. **Search before writing.** Follow the branches above, run
   `lean_local_search`, and run `blanc_suggest` at the goal. A `blanc_suggest`
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
   first needed it.
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

`writerRep_absorb` in
[`PairWriterAbsorb.lean`](../Blanc/Lift/UniswapV2Pair/PairWriterAbsorb.lean)
extends a represented finite footprint inside the same separated universe to
include every incoming tracked row. The existing Pair supply outcome builder
imports this same proof. An actual-call consumer can apply it at a selected
returned checkpoint before consuming later static queries. Its quantified footprint
conclusion has no reliable registered single goal-head trigger.

[`BurnLogImage.lean`](../Blanc/Lift/UniswapV2Pair/BurnLogImage.lean) owns the
shared `burnOwnedRaw` image and `burn_pending_logs_preserves`, which transports
the existing locked-child pending log image into the Burn/Sync image without
changing foreign logs. The original Burn source donor imports the same proofs.

### Swap original source prefix and admitted transfers

[`SwapPositionalSourcePrefix.lean`](../Blanc/Lift/UniswapV2Pair/SwapPositionalSourcePrefix.lean)
derives the initial source guards, cached words and starting segment from the
original successful execution. `swap_source_transfersH` composes both optional
transfers from that same physical chain and the same admitted queue witnesses;
only executed calls advance the source index.
