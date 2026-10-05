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
  [`Blanc/Basic.lean`](../Blanc/Basic.lean). Both are the substrate the
  branches below are stated over, so read the declaration and its module
  documentation there rather than expecting a need-first branch for it.
- Fork coverage: `CoveredFork f` (`f ∈ coveredForks`) in `Blanc/Semantics.lean`.
  Consume it only through `CoveredFork.stateGas_none`, `bal_none`,
  `rules_stateGas_none`, `rules_bal_none`, `requests_eq`,
  `beaconRoots_not_precompile`, `historyStorage_not_precompile`, `of_eq` and,
  where a per-fork case split is unavoidable, `CoveredFork.cases`. Discharge a
  schedule premise with `mainnetChainConfig_covered` or a concrete config lemma
  such as `Drip.concreteConfig_covered`.
  To move an execution *between* covered forks, use
  [`Blanc/ForkUniform.lean`](../Blanc/ForkUniform.lean): `withFork` replaces the fork on
  `Sevm`/`Evm`/`Msg`/`Frame`; `evm_step_withFork` (one step commutes at an
  `InstNeutralAt` node: not `CLZ`, and `BLOBBASEFEE` only at zero excess blob gas),
  `frame_enter_withFork` (a `Frame.PrecompNeutral` frame: no `MODEXP`/`P256VERIFY`),
  `settle_withFork`, `Exec.withFork` (an `ExecNeutral` derivation, node for node) and
  `exec_withFork`, `exec_out_withFork`, `runFrame_withFork`, `processMessage_withFork`,
  `processCreateMessage_withFork` (same outcome). A closed `*_deploy` instance needs none of
  this when its general `*_create` already quantifies `CoveredFork`.
- Build a configured block *forward* from proof-produced evidence about its
  parts (a reachable history, a counterexample, a liveness witness): go to
  [T7](#t7-i-must-construct-a-configured-block-forward-from-its-parts).

## E — execution

### E1. I need to construct a source or compiled execution term

- Ordinary source `Func.Run` walk:
  `func_execute`, `func_execute_with`, and the split lemmas in
  [`Blanc/Tactics.lean`](../Blanc/Tactics.lean).
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
- Compiled walk with an arbitrary terminal outcome (`Func.RunCompiledTo`):
  [`Blanc/Reverts.lean`](../Blanc/Reverts.lean).
- A selected `LOG` step that exposes unchanged storage, balances, code,
  access sets, output, and error while threading an arbitrary continuation:
  `Func.runCompiledTo_log_step_ext` and its exhibited-state form
  `Func.runCompiledTo_log_step_exists` in
  [`Blanc/ForwardLog.lean`](../Blanc/ForwardLog.lean).
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
- `sstoreNewRefundCounter_ge_of_original_eq_current` proves an SSTORE whose
  original and current slot values agree cannot decrease an arbitrary refund
  counter; `afterSstore_refundCounter_ge_of_original_eq_current` carries this
  to the selected warm/cold SSTORE state for checked-message settlement; more
  generally `RefundSafe orig cur` (original equals current, original zero, or
  current nonzero) rules out the clearing-reversal branch:
  `sstoreNewRefundCounter_ge_of_safe` / `afterSstore_refundCounter_ge_of_safe` in
  [`Blanc/StorageRefund.lean`](../Blanc/StorageRefund.lean).
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
  already-built dispatcher walk.  When a family builds its own dispatcher
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
  four-instruction selector prefix before the residual function.
- `Func.ExecSat` / `Prog.ExecSat` package predicates over outcomes.
- The `Ninst.runCompiled_*call*` family constructs concrete call crossings.
- When the walk already holds the callee's own exact run, use
  [`Blanc/Lift/ExactWalkCallChild.lean`](../Blanc/Lift/ExactWalkCallChild.lean):
  `Ninst.runCompiled_call_nonzero_child` resumes a nonzero-value `CALL` into a
  non-precompile callee from `exec (initEvm (callChildMsg …)) = .ok cpost` with
  `cpost.error = none`, the child message being the parent-built message over
  the debited world; the parent lands in `callChildPost` (child world and
  warm sets adopted, gas returned, flag `1` pushed, output copied), and
  `callChildPost_facts` projects every field when the child returned nothing.
  A lifted callee supplies `exec … = .ok _` through `exec_iff_exec_eq` from its
  `Exec` derivation; a code-free callee is `Ninst.runCompiled_call_nonzero_codeFree`.
  `adrSet_union_isEmpty` carries an empty deletion set through the resumed
  parent's `accountsToDelete` union.
  The zero-value sibling is `Ninst.runCompiled_call_zero_child` (child message
  `callChildMsg … 0 …`); `callChildPost_facts_zero` projects the resumed parent
  when the output window is empty, whatever the child returned.
  For a loop that calls once per iteration (`GAS; CALL` forwarding everything),
  `calculateMsgCallGas_all` closes `calculateMsgCallGas` to all but one 64th of
  the gas left after the fixed charge (plus the stipend), and the cut-run steps
  `rxc_push0` / `rxc_calldataload` complete the `rxc_*` kit for
  `SFunc.RunExactCut.iterate` bodies; the EIP-7002 flood looper
  (`Blanc/Lift/WithdrawalRequest/FloodRun.lean`) is the worked example.
- `accessDelegation_worldMeta` carries transient storage and the storage-access
  warm set through the exact delegation-resolution equation.
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
- `AcceptedCallerPayout` in the same module: the entered, clean, success-consumed value
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
  transaction settlement also needs the crossing's exact refund preservation
  and account-deletion-set emptiness preservation.
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
in `Blanc/Lift/CallChildren.lean`, described below. The first consumer is
`Blanc/Composition/UniswapV2PairWeth9Calls.lean`.

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
use `ConfiguredHistoryTrace.settledFrames_callerTarget_of_children`. The first
consumer is `Blanc/Composition/Weth9SettledCallers.lean`.

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
`ChainMemoryBelow R bound` is the memory bound such content facts take. The
first consumer is `Blanc/Lift/UniswapV2Pair/PairCallShape.lean`.

### E4. I need a common terminal walk

Use [`Blanc/ExecutionTerminal.lean`](../Blanc/ExecutionTerminal.lean):

- `Func.runCompiledTo_return_word_at_zero` for a known 32-byte return at offset 0.
- `Func.runCompiledTo_revert_empty_at_zero` for an empty revert at offset 0.

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
[`Blanc/Reverts.lean`](../Blanc/Reverts.lean).

For a nonzero branch flag that tail-calls a constant `Error(string)`
auxiliary, use `errorBodyCost`, `errorCallCost`, `errorGuardCost`, and
`Func.runCompiledTo_errorGuard` in
[`Blanc/RevertPayload.lean`](../Blanc/RevertPayload.lean). The cost remains a
function of the entry state, so arbitrary aligned prior memory and its exact
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
  the real `Evm.step`. `pwalkH_cont` and `pwalkH_halt` then hold for *any* derivation node
  at the start configuration: a `ParentPrefix` successor at the end configuration, every
  node in between passing a pc check and satisfying the policy (`NodeOKH`; at `.refuse` it
  is `NodeOK`: no `KECCAK256`), unchanged `Exec.rawFrameDescendants`, and for a halting
  walk the frame's outcome (`pwalk_cont`/`pwalk_halt` are the `.refuse` cases).
  `hashAvoid_of_hashOK` (trace-local `HashAvoid` from `.avoid slot` nodes) and
  `hashAvoid_of_noKeccak` close chain arguments with `parentPrefix_total`.
  `scallPrep`/`staticcall_node`, `callPrepP`/`call_node` and `dcallPrep`/`delegatecall_node`
  (over `spawn_node`) cross a call-family spawn; `PrepFacts` supplies the settle
  (`PrepFacts.settle_ok`/`settle_error`) and resume (`resume_agree_ok_of`/
  `resume_agree_error_of`; `resume_agree_ok`/`_error` for `STATICCALL`) facts.
  [`Blanc/Lift/NodeWalkFrames.lean`](../Blanc/Lift/NodeWalkFrames.lean) builds on it:
  `spawn_resume_ok`/`spawn_resume_err` cross a spawn on any derivation (the child's node, the
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
- To state a closed walk witness under every covered fork rather than the one its machine
  fixes, transport its kernel facts with
  [`Blanc/Lift/NodeWalkFork.lean`](../Blanc/Lift/NodeWalkFork.lean): `pwalk_withFork`
  (`pwalkH_withFork`) leaves a walk unchanged from `s.withFork g` for covered forks when
  `s.benvStat.excessBlobGas = 0` (walks never run `CLZ`: it is not an `ninstAccKeeps`
  instruction), `scallPrep_withFork`/`callPrepP_withFork`/`dcallPrep_withFork` spawn the same
  frame with its fork changed, `frameEnterS_withFork` commutes with the change for a
  `Frame.PrecompNeutral` frame (`Frame.precompNeutral_of_codeAddress` from a kernel fact on the
  frame's `codeAddress`), and `scallPrep_stat`/`callPrepP_stat`/`dcallPrep_stat`/
  `frameEnterS_stat` carry the block environment into children. The bundles
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
- `ExecutionTrace.messageCreateCollision`, `messageCallDelegation`, and
  `messageCallExecutionMessage` name the three message-call routing cuts.
- `ExecutionTrace.transactionPreludeBout`, `transactionBlobGasFee`, and
  `transactionTenv` expose transaction preparation;
  `TransactionTrace`, `exists_transactionTrace`, and
  `TransactionTrace.exists_finalStateForm` retain the whole transaction.
- `ExecutionTrace.ApplyTransactionsTrace`, `SystemMessageTrace`,
  `RequestsTrace`, and `AppliedBodyTrace`, together with their `exists_*Trace`
  theorems, retain transaction lists, system messages, requests, and the full
  block body. `RequestsTrace.state_eq_consolidationState` identifies the final
  request state, and `AppliedBodyTrace.decodedTxs_nil` / `AppliedBodyTrace.decodedTxs_of_mapM`
  decode `trace.decodedTxs` from empty or mapped `txs.mapM decodeTx` runs.

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

To relate a configured history to a later one, use
`ExecutionTrace.ConfiguredHistoryTrace.ExtendsBy` in
[`Blanc/ExecutionHistoryExtension.lean`](../Blanc/ExecutionHistoryExtension.lean):
`base.ExtendsBy trace n` says `trace` is `base` followed by exactly `n`
configured blocks. Its lemmas `settledFrames` (base frames are a prefix),
`rawFrames_mem`, `blockCount` (`trace.blockCount = base.blockCount + n`),
`noSenderAt` and `noAuthorityAt` restrict an extension's retained frames and
caller/authority exclusion premises to the history it extends.

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
  committed-frame list.
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
- [`Blanc/ExecutionBodyStateTrace.lean`](../Blanc/ExecutionBodyStateTrace.lean)
  for system messages, transaction lists, direct withdrawals, requests, and
  `AppliedBodyStateChronology`;
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
boundaries never duplicate child logs.

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
arbitrary callee code: storage of a code-bearing owner (`Evm.step_cont_getStor_foreign`,
`Evm.step_done_getStor`, `Xinst.spawn_run_getStor`/`Evm.step_run_getStor`: the settled
child's committed endpoint or the rollback, pointwise), logs (`Exec.cont_logs_eq`,
`Exec.doneOk_logs_eq`, `Exec.runOk_logs_eq`, path-independent `Exec.committed_logs_at`,
and `Xinst.call_run_logs`: a CALL/STATICCALL appends exactly its committed child's
logs), the installed image (`CodeSem.At.parentStep`, `CodeSem.At.spawnChild`,
`CodeSem.At.callChild`, self-calls included), child entry (`Xinst.spawn_child_world`,
`Xinst.spawn_child_logs`, `Xinst.call_spawn_ofCall`, `Frame.ofCall_settle_clean`),
`Exec.retainedTargetFramesFromAt_rawFrameRoot` and `Lift.StepIn.codePreserve`.
For a successful nonzero-flag call with the actual recursive slot `.none`, use
`Xinst.call_none_precompile` (seven operands) or `Xinst.staticcall_none_precompile`
(six operands). They identify an enabled precompile at the original target;
the STATICCALL form preserves the supplied slot through
`of_step_staticcall_val_with_depth_frame_cause`. An empty retained view queue
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
  `Rinst.gasFree` whitelists the `regularTransfer` opcode family minus `gas`;
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
  `of_addLog`, `of_popList`, `of_popBurnList`, and gas-independence of the
  forward cost helpers (`sloadCost_congr`, `sstoreCost_congr`, `afterSload`,
  `afterSstore`). A dispatcher that reaches a non-gas-free entry needs a
  two-run walk to the selected entry first (see
  `Blanc/Composition/UniswapV2PairWeth9GasFree.lean` for WETH9).

### I2. The property concerns a complete execution or child frames

- Message-entry projections: `processMessage_entry_facts` carries the code,
  target, calldata, time, storage and `Mem.Wf` facts, with `pre.stack = []` and
  `pre.memory = Mem.empty` kept separate as `processMessage_entry_stack` and
  `processMessage_entry_memory` so a walk that reads scratch words can take the
  image rather than only well-formedness.
- Generic execution noninterference:
  [`Blanc/ExecutionNoninterference.lean`](../Blanc/ExecutionNoninterference.lean).
  For `Exec.NoRetainedWriteTo`, first split on `Execution.commits out = true`:
  `Exec.noRetainedWriteTo_of_not_commits` closes the rollback arm;
  `Exec.noRetainedWriteTo_of_no_execOccurrence`,
  `Exec.noRetainedWriteTo_of_sourceSites_no_exec`, and
  `Exec.noRetainedWriteTo_of_frame_owners_ne` are the committing routes.
- Reentrancy-lock exclusion over the all-outcome frame tree:
  [`Blanc/LockExclusion.lean`](../Blanc/LockExclusion.lean).
  `LockExclusion.LockSpec.lock_exclusion` says an active lock frame's spawned
  child (any outcome) enters no guarded body of the same owner and code;
  `LockSpec.locked_core` keeps the lock cell fixed, slot-addressed owner
  `SSTORE`s absent and `NoRetainedWriteTo` true below any locked node.  Both
  take the per-code `LockSpec.Dominance` and the per-world
  `OwnerDiscipline`/`HashAvoidIn` as hypotheses.  Reusable step facts there:
  `Evm.step_cont_getStor_get` (one cell across a continuing step unless an
  owner `SSTORE` hits its key), `Evm.step_doneOk_getStor_eq`,
  `Evm.step_spawn_enter_getStor` (an entered child starts from the parent's
  storage), `Ninst.none_getStor_eq_of_ne_sstore`,
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
  address), `Xinst.step_directCall_spawn_code` (`CALL`/`STATICCALL`, including
  a call back into the current account), `Xinst.step_create_spawn_fresh`
  (`CREATE*` only enters a codeless account) and `Jinst.runCore_ok_pc`.
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
  `Exec.rawNodes_isStatic_of_static`, `Exec.retainedStorageWrites_eq_nil_of_static`
  and `Exec.storageView_committedPost_eq_of_static` are the execution-level
  facts underneath: the static flag reaches every entered child frame and no
  `SSTORE` completes in one.  It says nothing about transient storage, logs,
  balances or gas.
- Representation-exact storage silence of static execution:
  [`Blanc/StaticCallStorage.lean`](../Blanc/StaticCallStorage.lean).  Use it
  when the boundary is the `Stor` tree itself (a replay carrier that meets at
  *equal* storages) rather than the extensional `Devm.storageView`.
  `Exec.getStor_committedPost_eq_of_static` says a committing execution of a
  static frame ends with exactly its entry storage map at every account,
  children included on a fork named by the `CoveredFork` predicate (the four
  pre-Amsterdam forks Prague, Osaka, BPO1 and BPO2; Amsterdam is excluded);
  `Ninst.staticcall_inv_getStor_exact` lifts that to one successful
  `STATICCALL` under the same explicit premise.
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

If several updates form a familiar semantic post-state, continue to S2.

### S2. I need a reusable composite projection cut

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
  installation. `Devm.setCode_logs`,
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
  preparation cuts.

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

Use the primitive word facts in
[`Blanc/MachineDataFacts.lean`](../Blanc/MachineDataFacts.lean) before
destructing a `B256`: `B256.mul_comm` covers word multiplication, including
wrapping products, and `B256.not_lt_of_ltCheck_eq_zero` turns a zero unsigned
comparison flag into the negated strict comparison. The latter does not
assert that arithmetic producing either operand was overflow-free. Import
this owner directly; CommonProofs and Ladder do not reexport it.

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
freshness of every touched key.  The key type, its slot function and the fixed slots are parameters.
For an explicit query list and write list, `checkFaithfulOn slot observed written`
checks that a written key shares its raw slot only with itself among the requested
observations; `checkFaithfulOn_eq_true` gives its exact finite soundness statement.
`checkApartOn slot observed foreign` and `checkApartOn_eq_true` check raw foreign
slots against those same explicit observations. These require neither a
`Support` premise nor zero values for keys outside the observation list.
WETH9's `Blanc/Lift/Weth9/Footprint.lean` is the first consumer (with `tracked`/`trackedSum` over
`sum`); Curve's `Layout.lean` keeps its own copy of the same notions.

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
`RlpConcrete.splitAt_append` retains an arbitrary payload and suffix;
`encode_bytes_many` selects the ordinary length-prefixed byte encoder;
`decode_bytes_long_two`, `decode_bytes_short`, `decode_bytes_32`, and `decode_list_long_two`
apply Jaune's actual parser equations while keeping payload bytes abstract.
`decode_byte`, `decode_empty_bytes`, `decode_empty_list`, and
`decode_bytes_three` cover the small field headers; `parse_cons` composes
the actual first-item and remaining-list equations.
`decode_hash` proves the fixed-width header-word roundtrip, including leading
zero bytes. The list lemma requires the actual recursive child parse. These
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
  `ecrecover_output_of_processMessage_clean` turns a clean synchronous
  non-delegated address-1 child (the `ProcessMessage` a `StaticAnswered` witness
  exhibits) into `gasEcrecover ≤ gas` and that output, and `ecrecover_active`
  discharges activation of address 1 on every covered fork by `CoveredFork.cases`.
  It identifies the executed answer; it never asserts that recovery succeeds or
  that signatures are unforgeable. Consumers: the Uniswap V2 Pair permit
  canonical corollary; `Blanc/Weth10Permit.lean`'s two address-1 clean-child
  theorems can become corollaries (proposed migration). Discovery is manual.
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
  entry storage, and memory well-formedness from the actual retained frame;
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

### T2. I need to know which child effects survive settlement

Use Jaune's `Jaune/ExecSettlement.lean` and `Jaune/ExecChronology.lean`
(imported by [`Blanc/ExecutionSettlement.lean`](../Blanc/ExecutionSettlement.lean)
and [`Blanc/ExecutionOccurrence.lean`](../Blanc/ExecutionOccurrence.lean)) and
Blanc's [`Blanc/ExecutionOccurrence.lean`](../Blanc/ExecutionOccurrence.lean):

- `Execution.commits` and `Frame.settlementCommits` distinguish raw success
  from complete frame settlement.
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
Neither request-call outcome is consumed by this prefix proof.  Import
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
  authorization recovers to it (`NoAuthorityAt`). For transaction caller
  exclusion, `Exec.rawFrameRoots_caller_excluded` in
  [`Blanc/ExecutionCallerExclusion.lean`](../Blanc/ExecutionCallerExclusion.lean)
  tracks actual CALL/CREATE/DELEGATECALL callers and empty executing code.
  `ConfiguredHistoryTrace.txRawFrames_caller_excluded` in
  [`Blanc/ExecutionTraceCallerExclusion.lean`](../Blanc/ExecutionTraceCallerExclusion.lean)
  derives that exclusion from initially empty code, retained `NoSenderAt`,
  `NoAuthorityAt`, and trace-local CREATE avoidance (`ApplyTransactionsTrace.noSender_nil`
  supplies `NoSenderAt a` vacuously for an empty transaction list). Calls to the empty-code
  address remain allowed; system frames are outside the conclusion.
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
  consumers: `Lift.BeaconDeposit.configuredHistory_solInv_env` (and
  `_count_env`/`_root_env`) and `Lift.Curve3Crv.c3crv_history_committed_derived`.
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

#### I need a finite, root-fixed set containing a call's actual reply

Use [`Blanc/Lift/PrecompileAnswer.lean`](../Blanc/Lift/PrecompileAnswer.lean).
`precompileRun_gas_mono` shows remaining gas only gates a precompile's success,
so `precompileRun_ok_output_unique` makes the successful output a function of
calldata and `MODEXP` pricing alone, named by `precompileAnswer` (and
`precompileAnswer_of_ok`); `precompileRun_ok_mem` bounds the succeeding
addresses by `precompileRunAddresses`. `ProcessMessage.ok_output` splits an
error-free successful call message into that precompile answer (empty slot) or
its entered frame's raw success (`callFrame_settle_ok`). Together with
`Exec.rawFrameRoots` this gives a finite list, fixed by the root execution, that
contains any STATICCALL reply to a fixed request (consumer:
`UniswapV2Pair.mintFeeReplyKeys`).

### T2b. I need a contract's own ledger replay across retained settlement

A contract that reads one account and reports an *ordered* replay of the moves
it saw meets four obstacles that are about EVM settlement, not about its
ledger.  Use
[`Blanc/ExecutionAccountingReplay.lean`](../Blanc/ExecutionAccountingReplay.lean)
rather than restating them:

- `ExecutionAccountingReplay.SettlementCarrier ca` is the settlement-facing
  interface, and it is exactly what the three seams below consume: `Snap`,
  `Step`, `Replay`, `ofState`, `frameEntry`, and the three laws `nil`,
  `worldSilent` and `entry_eq_ofState`.  `worldSilent` is the one to read
  first: it says only that a transition fixing **every** account's storage and
  balance moves no boundary — `post.getStor = pre.getStor` and
  `post.bal = pre.bal` as whole-world function equalities.  That is all a
  settlement seam ever knows at its three silent sites (CREATE fresh-account
  preparation, clean code deposit, the prepared CREATE world), and stating the
  law at that strength is what lets a boundary read **more than one account**.
  A law keyed to `ca` alone would be false for such a boundary, which is why
  `Blanc/Composition/ProrataWethVaultHistory.lean`'s two-storage pair boundary
  is a `SettlementCarrier` and not a `ReplayCarrier`.  `ca` survives only in
  the two value-transfer side conditions of `entry_eq_ofState`.
- `ExecutionAccountingReplay.ReplayCarrier ca` is the account-local carrier:
  the same fields plus credit provenance `Tag`, with the account-local `silent`
  (storage and balance fixed *at `ca`*) and `credit` (a storage-fixed strictly
  increasing balance is some replay) in place of `worldSilent`.  It reaches the
  seams through `ReplayCarrier.toSettlementCarrier`, which discharges
  `worldSilent` by reading the whole-world equalities at `ca`; the seam
  theorems are then restated at `ReplayCarrier` under their own names, so an
  existing account-local consumer needs no change.  **Which to use:** a
  boundary that reads one account and wants the balance-monotone step
  classifier (`ofStorageEqBalanceMono`) takes `ReplayCarrier`; a boundary over
  several accounts, or one that produces its steps some other way, takes
  `SettlementCarrier` directly and simply never gains `credit`.
- `ReplayCarrier.processMessage_of_body` and
  `ReplayCarrier.processCreateMessage_of_body` take the *committed body's*
  replay to the whole retained CALL or CREATE, splitting on settlement: a
  noncommitting child rolls the world back and contributes nothing, and
  fresh-account preparation and code deposit are projection-silent.
- `ReplayCarrier.xinstForeignSome` does the same for one filled executable slot
  in a foreign frame, so CALL and CREATE share a single child replay and their
  instruction prefixes and resumptions stay silent.
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
  is one positive credit at `ca` or no step) and the word-bound transports
  `ExecutionTrace.TransactionTrace.msg_sum_nof` and
  `ExecutionTrace.processWithdrawalsState_sum_nof`.  Four more wrapper facts
  live beside them for ladders that do not fit this one:
  `ExecutionTrace.TransactionTrace.msg_caller` (the prepared message's caller
  is the checked sender), `ExecutionTrace.ApplyTransactionsTrace.stat_eq` (a
  transaction list changes the block environment only through state),
  `ExecutionTrace.processWithdrawalsState_getStor_eq` (direct withdrawals move
  balances only) and `ExecutionTrace.AppliedBodyTrace.transactionBound` (the
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
  `ofStorageEqBalanceMono_observed` and `ofAddBal_observed`.

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
the old ladder reexports them by import.

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
[`Blanc/ExecutionDirectCode.lean`](../Blanc/ExecutionDirectCode.lean).

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
`Blanc/Lift/Weth9/CommittedSpawn.lean`, `CommittedHistory.lean`.

### T3. The wrapper is a transaction and the fact is about an installed contract

Use
[`Blanc/ExecutionTransactionEffects.lean`](../Blanc/ExecutionTransactionEffects.lean):

- `ExecutionTrace.TransactionTrace.sender_ne` rules out a checked sender equal
  to the contract, and `ExecutionTrace.TransactionTrace.msgInv` carries an
  arbitrary `ContractSpec` invariant onto the prepared message.
- `ExecutionTrace.TransactionTrace.debitState_bal_eq` and
  `ExecutionTrace.TransactionTrace.debitState_getStor_eq` project the nonce
  bump and up-front gas debit;
  `ExecutionTrace.TransactionTrace.msg_shouldTransferValue` records that a
  transaction message always transfers its value.
- `ExecutionTrace.TransactionTrace.accountsToDelete_ne` and
  `ExecutionTrace.foldl_destroyAccount_get_eq` cover the final deletion fold.
- `ExecutionTrace.TransactionTrace.settlement_sum_bounds` funds the sender
  refund and the coinbase priority fee out of the transaction's own up-front
  debit, so neither credit needs a wrap-around side condition.
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
(no authorizations, no delegation) over a successful `processMessage`, and
`processTransaction_of_stages` is `processTransaction` from the validation, admission, debit,
prepared message and message-call outcome, with the exact settled state (gas refund and coinbase
fee credited, accounts deleted).  Worked use:
`Blanc/Lift/VyperNonreentrantDeployed/Vulnerable/Tx/Envelope.lean`.
For a *symbolic* type-2 call to a contract (no concrete transaction to evaluate) the same module discharges
the whole envelope from field-level facts: `processTransaction_call_value_of_exec` takes the fee, nonce, funds,
code-free sender, gas and signature facts (`hrecover` the only cryptographic premise) and the message's
interpreter run `hexec` (a success with no frame error and a non-negative refund counter, for the debited
state, `callMessage` and its entry environment), and returns `processTransaction`'s settled state and the
block's gas counters (`txGasUsed`); `processTransaction_call_value_of_exec_receipts` is the same
envelope that also returns the appended receipt key and the receipt at it (`makeReceipt tx none`, the
cumulative gas, the frame's logs), and `processTransaction_of_stages_receipts` is the stage form behind
it. Its funds premise covers `tx.gas * maxFee + tx.value`;
it derives affordability after the gas debit and constructs the value transfer with the shared
`Msg.benvAfterTransfer_of_affordable` lemma. The signature and successful raw execution remain
premises; the theorem does not construct a signed transaction or a configured history.
`processTransaction_call_of_exec` retains the original zero-value interface as a specialization.
The shared parts are `checkTransactionGasFee_two`, `checkTransactionChainId_two`,
`checkTransactionBlobData_two`, `checkTransactionReceiver_two`, `checkTransactionAuthorizationList_two`,
`checkTransactionSenderAccount_ok_of_noCode`, `checkTransaction_sender`,
`validateTransaction_ok_of_facts`,
`calculateIntrinsicCost_two_call` (with `calldataTokens` and the covered-fork constants
`CoveredFork.rules_txBase`, `rules_floorTokenCost`, `rules_storageClearRefund`,
`CoveredFork.checkTransactionGasCap_ok`), `prepareMessage_call`/`callMessage`,
`benvAfterTransfer_get_of_value_zero`, `processMessage_call_of_exec`, `debit_get_ne`/`debit_get_self`,
`addBal_get_self`/`addBal_get_ne`, `sender_net_toNat`, `txGasUsed_le` (bounds `txGasUsed ≤ gas` from `floor ≤ gas`),
`applyTransactions_two` (folds two sequential successful transactions into `applyTransactions`),
`processTransaction_receiptsTrie` (identifies the inserted receipt key), `receiptKey_zero`/`receiptKey_one`/`receiptKey_ne`
(evaluate and distinguish the receipt keys at index 0 and 1), and `processTransaction_of_stages_gasUsed` (the
stage lemma with the block output's gas counters).  Worked use: the deployed WETH9's
`Blanc/Lift/Weth9/LiveTx.lean` (`weth9_tx_withdraw`, `weth9_history_tx_withdraw`), which feeds it the frame of
`weth9_withdraw_live_post`.

### T4. The wrapper is a message call and I must see through delegation

Use
[`Blanc/ExecutionMessageEffects.lean`](../Blanc/ExecutionMessageEffects.lean):

- `ExecutionTrace.messageCallDelegation_fields` and its named projections
  (`_caller_eq`, `_target_eq`, `_currentTarget_eq`,
  `_shouldTransferValue_eq`) carry a routing or value field across the
  EIP-7702 authorization prefix; `_getStor_eq` and `_bal_eq` carry the world,
  while `_benv_stat` carries the complete static block environment.
- `ExecutionTrace.messageCallExecutionMessage_caller_eq` and its siblings
  (`_target_eq`, `_currentTarget_eq`, `_shouldTransferValue_eq`,
  `_getStor_eq`, `_bal_eq`, `_benv_stat`) do the same across delegated-code
  resolution.
- `ExecutionTrace.TransactionTrace.exists_callRun_of_target` eliminates the
  CREATE and collision constructors of an actual transaction message whose
  target is a CALL, exposing that trace's exact delegation, resolved message,
  core trace, and settlement equation for a consumer that must classify it.
- `ExecutionTrace.benvAfterTransfer_getStor_eq`,
  `ProcessMessage.none_ok_getStor_eq`,
  `ProcessCreateMessage.none_ok_getStor_eq_of_empty`,
  `ExecutionTrace.setDelegation_getStor_eq`, and
  `ExecutionTrace.setDelegation_bal_eq` are the lower storage/balance seams
  used by those packaged projections.
- `ExecutionTrace.messageCreateCollision_false_getStor_eq_empty` and the three
  `processMessageCall_*_state_eq` theorems expose the collision, CREATE, and
  CALL wrapper endpoints exactly.
- `ContractSpec.MessageRunReady` and the `ContractSpec.MsgInv` transport
  family (`runReady_of_call`, `runReady_of_foreign`,
  `processCreateMessage_msg`, `of_messageCallDelegation`, and
  `messageCallExecutionMessage`) package the conditions needed to run an
  arbitrary installed contract invariant through the wrapper.

### T5. The wrapper is a block body and the fact is about an installed contract

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
`afterSstore_getAcct_ne`, `State.get_setStorVal_ne` and `State.getStor_setStorVal_self`
read a store's world-state effect and account/storage preservation. Worked uses: the EIP-4788 and
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
schedule-parametric, so a history crossing fork activations is one derivation
and no fork is hard-coded anywhere:

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

For schedule-parametric block/history state boundaries and replay, use
`ExecutionTrace.ConfiguredBlockStateChronology` and
`ExecutionTrace.ConfiguredHistoryStateChronology` from E8.

#### Contract-local fixed-fork to configured-schedule migration

When a contract-local carrier still fixes one fork, keep the common carrier as
the schedule-neutral spine and make the local extension follow its fields:

1. Replace the local `chainId`/fixed-fork parameter with `cfg : ChainConfig`.
   Each block retains its selected `rules`, the equation
   `cfg.rulesAt block.header.timestamp = .ok rules`, the
   `stateTransitionUsing cfg` result, and the body trace produced from
   `initBenv rules`. Project literally to `ConfiguredBlockTrace cfg`; recurse
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
  proof.  It deliberately requires no safety property of an unselected sibling.
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
argument once: Jaune's `getStor_addBal` and `getStor_subBal_addBal` say balance movement
never moves storage, `ofStorageOnly_preInv_iff`/`ofStorageOnly_postInv_iff`
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
  Vyper's `!=`, and the `SLT`, `EXTCODESIZE`, `TLOAD`, and `TSTORE` steps needed
  by deployed Lido bytecode; these success-only lifted transfers do not extend
  native `regularTransfer_safe`). Decide
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
- Bytecode whose control flow runs through `PC`, constant arithmetic, constant
  `JUMPI` conditions or memory (Vyper 0.2 internal calls keep the return tag in
  memory): `SFunc.pcAt` (a `PC` carrying its own pc) in `Blanc/Lift/Basic.lean`;
  constant arithmetic, comparison and bitwise `AND` folds (`foldConst`) and
  decided `JUMPI`s (`AVal.jumps?`) are part of `checkNode`; the memory-tracking
  checker `checkNodeM`/`Cert.checkM` over declared
  maps (`absMem`, `memTop`, `memCompat`; `checkNode_eq_checkNodeM` with tracking
  off) in [`Blanc/Lift/CheckMem.lean`](../Blanc/Lift/CheckMem.lean); the invariant
  `MemMatches`, the return address in frame or map (`RetIn`) and the
  per-instruction facts `absMem_sound`, `memTop_sound`, `step_mem_sound` (and
  `Mem.write_agree`, which needs no `Mem.Wf`) in
  [`Blanc/Lift/MemMap.lean`](../Blanc/Lift/MemMap.lean); `lift_soundM` in Sound,
  `lift_exactM`/`Cert.jumpsOkM` in Exact, trie mirrors `checkNodeMT`/`jumpsOkNodeMT`
  in CheckFast. Produce with `scripts/lift/lift.py --memret callnext --const-mem`.
- Every execution prefix to a certificate node (all outcomes, no success
  premise): the certificate cursor `Cursor`/`Cont`, its invariant `CursorOK`
  (checked node, pc, stack segments matched per pending function), the
  synthetic step `SStep`, `cursor_start`, `cursor_step` (one `ParentStep`,
  including a `CALL` over a child of any outcome, is one `SStep`) and
  `cursor_of_parentPrefix`, with `CursorOK.exec_call_or_staticcall` (a reached
  node spawns only by `CALL`/`STATICCALL`), in
  [`Blanc/Lift/Cursor.lean`](../Blanc/Lift/Cursor.lean).
- To advance a checked certificate cursor through an actual successful raw
  suffix, use [`Blanc/Lift/CursorCuts.lean`](../Blanc/Lift/CursorCuts.lean).
  `cursor_next_forward` derives the actual `ParentStep`, instruction witness
  with `Cursor.DescOf`, `SStep`, `ConfStep` and successor `CursorOK`.
  `cursor_jinst_forward` reuses the decoded jump edge; `cursor_branch_forward`
  derives the faithful branch disjunction from the checked tree and literal
  abstract target, without choosing the branch as a premise.
  `cursor_nexts_line_forward` composes a literal instruction list into a real
  `ParentPrefix`, pc sum, preserved static environment/outcome, checked tail
  cursor and `Line.Run` to the same actual endpoint.
  `cursor_nexts_line_cont_forward` additionally preserves the identical full
  continuation stack, including each pending tag, frame and return metadata.
  `cursor_nexts_line_cont_free_forward` additionally derives `ExecFreeUntil`
  when every instruction in that literal list is non-exec. It owns the single
  list induction; the older forms project it. `CursorOK.ninstAt_of_next`
  exposes the actual decoded instruction from the checked next node and is
  shared by the single-step and exec-free cuts.
  `cursor_nexts_forward`
  is its cursor-only compatibility projection. These are certificate/SFunc
  cuts, not the compiled Func prefix API. They require raw success and a
  covered fork; they do not establish child context, settlement or ordered
  history. The joint node/tree premises are discovered here because the
  existential result alone is not a reliable recipe trigger.
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
- From a cursor-placed node to *later* nodes of the same frame:
  [`Blanc/Lift/ReachChain.lean`](../Blanc/Lift/ReachChain.lean).
  `reach_between` is `reach_of_parentPrefix` started at any cursor-placed node;
  `noExec_after_of_cursor` says no later node decodes an external instruction
  when the tree from the cursor on is exec-free; `getStor_post_of_silent` says the
  frame's post storage is the node's storage when the tree from the cursor on is
  state-silent (`Reach.silentTo`, `SFunc.silentTree`).
  `StepIn.exec_getStor_eq_of_noDescendants`: in a frame with no raw descendants a
  lifted external step keeps storage (its child would be the frame itself, and a
  child is shallower). Worked use: WETH9 `weth9_exec_node`.
- Restrict external instruction families along a checked certificate cursor:
  [`Blanc/Lift/CallRestriction.lean`](../Blanc/Lift/CallRestriction.lean) defines
  `SFunc.execsSatisfy` and `Cursor.ExecsSatisfy` (active function and pending
  returns). `SStep.execsSatisfy` preserves the restriction;
  `Cursor.execsSatisfy_of_reachable` starts it from the checked certificate;
  `CursorOK.execsSatisfy` turns actual instruction decoding into `allowed x = true`.
  This constrains same-frame instruction families, not child commitment or
  effects, and requires the check on every certificate function.
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
  `LockCheck.cursor_sstore_node`. Worked use:
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
  [`Blanc/Lift/ExactWalk.lean`](../Blanc/Lift/ExactWalk.lean), with more steps
  (`rx_shl`, `rx_xor`, `rx_byte`, `rx_mstore8`, `rx_calldatacopy`, `rx_log1`, …) in
  [`Blanc/Lift/ExactWalkOps.lean`](../Blanc/Lift/ExactWalkOps.lean) and the
  cut-run forms (`rxc_*`, `SFunc.RunExact.toCut`) in
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
  the SHA-256 precompile call (`ri_staticcall_sha`) and the solc packed-SHA
  site (`ric_copy_sha`, the converse of `copy_sha_gen`) in
  [`Blanc/Lift/InvWalkSha.lean`](../Blanc/Lift/InvWalkSha.lean).
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
  through account warming. Use these facts to compose an observed call without
  unfolding the nested world update; the Pair mint prefix consumes all three.
  The existing Lido temporal access names are compatibility declarations over
  this common owner.
- A callee that fails on every input: `revertingCode` (`PUSH0 PUSH0 REVERT`); every pc-zero
  frame over it ends in an error (`revertingCode_exec_error`, via the generic non-spawning
  step inversion `Exec.ofExecution_inv`); an ordinary non-precompile message over it never
  settles cleanly (`processMessage_not_clean_of_reverting`); and no static child message to
  an account holding it answers (`not_staticAnswered_of_reverting`), which refutes the
  `StaticAnswered` witness a successful-flag `STATICCALL` inversion retains. Use it for
  failing-callee (callee-premise) controls, in
  [`Blanc/Lift/RevertingCallee.lean`](../Blanc/Lift/RevertingCallee.lean).
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
  in [`Blanc/Lift/WitnessArms.lean`](../Blanc/Lift/WitnessArms.lean); the soundness
  theorem `Witness.wrun_exact` (from `wrun_cont`/`wrun_done` over `RunK`/`Agree`), the
  shadow seeds `stateFoldAcct`/`stateFoldStor`, and code children supplied as data
  (`ChildOk`, `ChildAgree`, `callResume`) in
  [`Blanc/Lift/Witness.lean`](../Blanc/Lift/Witness.lean). A code child discharged by its
  own witness run: `childStart`/`childStart_agree`, `childRun`, `childOk_of_start`,
  `childOk_of_childRun`, `frame_of_wrun`, `childAgree_of_halt`, and the DELEGATECALL
  preparation `dcallPrep`/`dcallPrep_spec`, in
  [`Blanc/Lift/WitnessChild.lean`](../Blanc/Lift/WitnessChild.lean); the frame-level spawn
  fact `SpawnedBy sevm devm x child` (`Xinst.step` spawns a frame entering as `child`) and
  `spawnedBy_of_callPrep`, `spawnedBy_of_childStart`, `spawnedBy_of_dcallPrep` in
  [`Blanc/Lift/WitnessSpawn.lean`](../Blanc/Lift/WitnessSpawn.lean); the literal-free
  scaffolding for deciding a long `wrun` as kernel chunks between literal boundaries
  (`Boundary.Bnd`/`obsB`/`cfgOf`/`obsD`/`obsDOk`, their composition `obsD_chain`,
  `obsD_chain3`, `obsB_of_obsD`, `run_of_obsB` (every boundary also records that the frame's
  accounts to delete are still empty, `AtdClean`); `Bnd1`/`cfgOf1`/`obsD1`/
  `obsDOk1` with the refund counter and the accounts to delete optional; and a two-code-child frame's staging `callPairFrom`/`callPairA`/`callPairB`/
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
  `processCreateMessage`, installing the constructor's output and keeping its storage
  (`liftCreate_ok`, with the creation frame `createSeed`), and the constructor walk steps
  the shared kits lack (`rx_codecopy`, `rxc_sstore`, `rxc_callvalue`, `rx_return_any` and
  `rxc_return_any`, with the halting state `returnPost` named over a variable state) in
  [`Blanc/Lift/Deploy.lean`](../Blanc/Lift/Deploy.lean); and the further steps solc 0.8
  constructors need (`rx_push0`, `rx_slt`, `rx_codesize`, `rx_log2`, and `read_covered_len`, a
  window of any length inside an aligned image) in
  [`Blanc/Lift/CreationOps.lean`](../Blanc/Lift/CreationOps.lean).
- Contract-neutral composition of the `CREATE2` opcode under a covered fork lives in
  [`Blanc/Lift/Create2Deploy.lean`](../Blanc/Lift/Create2Deploy.lean).
  `create2AddressOfHash` computes the CREATE2 address from an init-code digest
  (with `create2NewAddress_eq_ofHash` its identity against Jaune's
  `create2NewAddress`). An admitted `CREATE2` (non-static, affordable endowment,
  creator nonce below the maximum, positive depth, empty target) steps to
  `.spawn` via `Xinst.step_create2_spawn`, creating the frame over `create2Prepared`
  at that address. When the creation message succeeds without error
  (`processCreateMessage … = .ok child`, `child.error = none`),
  `create2_runCompiled` closes the spawn into a compiled step (`Ninst.RunCompiled`)
  to `create2Post` with the new address on the stack and the child's world installed.
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
  the accounts to delete and the moved balances; `CallPost.getStor`) in
  [`Blanc/Lift/ExactWalkCall.lean`](../Blanc/Lift/ExactWalkCall.lean).  Worked use: the deployed WETH9's writers,
  `Blanc/Lift/Weth9/LiveApprove.lean` … `LiveHistory.lean`.
- Jump destinations: Jaune's own `jumpable_eq_jumpdestOk` (`Jaune/Machine.lean`)
  replaces its exponential `jumpable` by the linear `jumpdestOk` scan, for every
  byte string; Blanc keeps no copy.
- Properties of the lifted program without per-path walks: a state-silent
  entry set (`SilentSet`, `SFunc.Run.state_of_silent`) in
  [`Blanc/Lift/Silent.lean`](../Blanc/Lift/Silent.lean), its balance analogue
  (`BalSilentSet`, `SFunc.RunP.getBal_of_balSilent`) in
  [`Blanc/Lift/BalSilent.lean`](../Blanc/Lift/BalSilent.lean), a quiet entry set
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
