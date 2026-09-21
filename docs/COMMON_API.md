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
- Relate raw execution to message/frame settlement: go to
  [T — settlement](#t--settlement).
- Relate source programs, compiled code, and deployed artifacts: go to
  [C — compilation and deployment](#c--compilation-and-deployment).
- Link an auxiliary call table by name instead of by index: go straight to
  [C6](#c6-i-need-to-link-an-auxiliary-call-table-by-name-instead-of-by-index),
  the last branch of that section rather than its head.
- None matches: search public declarations in `Blanc/CommonCore.lean`,
  `Blanc/CommonProofs.lean`, and `Blanc/Ladder.lean`; a helper found only in a
  contract module is a hoisting candidate, not a cross-contract import target.
- Looking for a *definition* rather than a lemma: the compiled-program language
  (`Func`, `Prog`, `Line`, `Ninst`, `Linst`, `Stack`) and the EVM seam over
  Jaune's machine live in [`Blanc/Semantics.lean`](../Blanc/Semantics.lean),
  whose banners mark which layer a statement belongs to; Blanc's own list
  prefix/split algebra (`Split`, `Pref`, `Frel`) lives in
  [`Blanc/Basic.lean`](../Blanc/Basic.lean). Both are the substrate the
  branches below are stated over, so read the declaration and its module
  documentation there rather than expecting a need-first branch for it.

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
  one-write primitive is `setStorVal_getStor_ne` in
  [`Blanc/CommonProofs.lean`](../Blanc/CommonProofs.lean).
- For TWG trigger packets, local-call rebasing commutes with constant-store
  prefixes by `Trigger.rebaseLocalCalls_prependStoresRev` and is the identity
  on constant-data reverters by `Trigger.rebaseLocalCalls_revertData` in
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
  the low-word projection to the ordinary address conversion.  The
  value-carrying inversions
  `of_loadAddressWordAt_val` and `of_storeAddressWordAt_val` live in
  [`Blanc/AddressSlotProofs.lean`](../Blanc/AddressSlotProofs.lean).
  Use it when delegated code can make a nominal address slot raw-dirty; a plain
  full-word `SSTORE` is observably different in that state.
- **Four-bit tagged logical storage keys.** `Blanc.TaggedStorage.encode` in
  [`Blanc/TaggedStorage.lean`](../Blanc/TaggedStorage.lean) combines a region
  with a payload after masking the payload to 252 bits.  Use
  `encode_eq_of_payload_lt` when bridging an existing unmasked `OR` encoder,
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
  the instruction-neutral `Xinst.step_spawn_benvStat` in
  [`Blanc/Semantics.lean`](../Blanc/Semantics.lean), then combine it with
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
[`Blanc/Ladder.lean`](../Blanc/Ladder.lean) — do not re-derive the
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
  (`f.inner.currentTarget = sevm.currentTarget`) is explicitly open: no shared
  step-level lemma resolves a same-target child, so report the open disjunct
  rather than forcing the inversion. Message-level same-target resolution with
  the callee word known goes through `not_delegation_of_compile` instead.
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
[`Blanc/Ladder.lean`](../Blanc/Ladder.lean).

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
- Raw nodes, raw frame roots, and instruction occurrence:
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
- Determinism of execution witnesses:
  [`Blanc/ExecDeterminism.lean`](../Blanc/ExecDeterminism.lean).

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
  request state.

Configured transitions and histories continue in
[`Blanc/ExecutionHistory.lean`](../Blanc/ExecutionHistory.lean):
`ExecutionTrace.ConfiguredBlockTrace`,
`exists_configuredBlockTrace_of_transition`,
`ConfiguredHistoryTrace`, `ConfiguredHistoryTrace.toReachUsing`, and
`exists_configuredHistoryTrace_of_reachUsing` retain the schedule-selected
rules and body traces without hard-coding a fork.

To identify the literal block in a retained configured transition, use
`ExecutionTrace.ConfiguredBlockTrace.block_eq_of_transition` in
[`Blanc/ExecutionHistoryExact.lean`](../Blanc/ExecutionHistoryExact.lean).
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
  instance with `exact Linst.Hinv.inv`; `Blanc/Ladder.lean` registers
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
  is the extensional `Stor.get` observation the contract invariants use, and
  the module already supplies its `PopBurn.Inv`, `Burn.Inv`, `Linst.Hinv`,
  `Ninst.Hinv` and `Ninst.staticcall` instances, so a read-only contract
  consumes them rather than restating static propagation.
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
  children included; `Ninst.staticcall_inv_getStor_exact` lifts that to every
  successful `STATICCALL`, entering arbitrary code or not; and the instance
  `staticcall_getStor_hinv : Ninst.Hinv Devm.getStor Ninst.staticcall` is what
  `Func.SilentIn Devm.getStor` certificates consume.  Worked use:
  `Blanc/Composition/ProrataWethVaultPairVaultSegment.lean` discharges the
  vault's live-quoting read-only paths through it.  Import
  `Blanc.StaticCallStorage` (it imports only `Blanc.StaticStorage`).  Like its
  parent it says nothing about transient storage, logs, balances or gas.
- Transient-state invariance and settlement:
  [`Blanc/TransientInvariance.lean`](../Blanc/TransientInvariance.lean) and
  [`Blanc/TransientSettlement.lean`](../Blanc/TransientSettlement.lean).
- If the invariant is specifically over entered raw frame roots, return to E3.

### I3. A foreign or childless frame must preserve a contract precondition

Use the generic frame lemmas in [`Blanc/Ladder.lean`](../Blanc/Ladder.lean):

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
`getStor_eq_of_state_eq` in `Blanc/Ladder.lean`.

Use [`Blanc/CommonProofs.lean`](../Blanc/CommonProofs.lean):

- `Devm.addAccessedStorageKey_setMach_setMach` cancels an obsolete machine
  component across an access-key update followed by the final `setMach`.
- `of_run_sload_state` and `of_run_sload_logs` expose the persistent-state
  and log silence of a successful `SLOAD`, including its cold access-list
  warming path.  Use these instead of widening the global `Ninst.Hinv`
  instance set: access metadata changes even though these projections do not.
- `Devm.getStorVal_setStorVal_self` is persistent storage read-after-write.
- `Devm.setStorVal_getCode` carries account code across a persistent storage
  write. `Devm.setCode_getStor`, `Devm.setCode_logs`,
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
  `State.setCode_bal` in
  [`Blanc/ExecutionSettlement.lean`](../Blanc/ExecutionSettlement.lean)
  preserve the complete world-balance map across balance-neutral account
  updates. `genericCreate_prepared_bal`, `genericCreate_prepared_getStor`, and
  `processCreateMessage_msg_bal_eq` package the corresponding CREATE
  preparation cuts.

### S3. I need state-relation or write-frame composition

Use `Devm.StateWriteFrame` and its reflexive/transitive/composition lemmas in
`Blanc/CommonProofs.lean`, then inspect higher-level relation combinators in
[`Blanc/Ladder.lean`](../Blanc/Ladder.lean).

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
laws live in [`Blanc/Ladder.lean`](../Blanc/Ladder.lean):

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

### S6. I need a basic EVM-word identity

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
destructing a `B256`. `wordModulusN`, `maxWordN`, `wordModulusN_pos`,
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
- Decode an exact word without losing bytes with
  `Bytes.toBytes_toB256_of_length`; shorten a padded read with
  `List.take_takeD_of_le`. The limb-level codec proofs are private
  implementation details of the public round-trip theorem.
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

Use [`Blanc/MessageExecution.lean`](../Blanc/MessageExecution.lean):

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
  `Frame.settle_eq_settleMsg_handleErrorWith` in
  [`Blanc/Semantics.lean`](../Blanc/Semantics.lean) to expose it, then identify
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
- `Msg.initDevm_*` and `Msg.initSevm_*` expose canonical message-entry fields.

### T2. I need to know which child effects survive settlement

Use [`Blanc/ExecutionSettlement.lean`](../Blanc/ExecutionSettlement.lean) and
[`Blanc/ExecutionOccurrence.lean`](../Blanc/ExecutionOccurrence.lean):

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
- `processCreateMessage.chargeCodeGas_bal_eq` and
  `ProcessCreateMessage.ok_state_eq_inner_of_no_error` expose the
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
invariant proofs.  Import
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
- When a consumer needs every entered frame's block environment (timestamp,
  number, …) to be the execution root's, import
  [`Blanc/ExecutionFrameTime.lean`](../Blanc/ExecutionFrameTime.lean):
  `Exec.frameAdmitted_benvStat` gives the block-environment statics inherited
  by every admitted frame from the execution root; use it with
  `Exec.FrameAdmitted.root` when lifting a root `benvStat` fact.
  For retained traces, `ExecutionTrace.ProcessMessageTrace.frameAdmitted_benvStat`
  admits every retained frame at the message's `benv.stat`, and
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
- `Exec.FreshEntry sevm pre` records only `pre.stack = []` and
  `pre.memory = Mem.empty`. `Exec.FrameAdmitted.fresh_of_enter` derives it
  from one actual frame entry, and `Exec.FrameAdmitted.and` combines it with
  an independently established contract-specific condition.
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
- Every retained carrier from `ProcessMessageTrace` through
  `ConfiguredHistoryTrace` has `freshFrameAdmitted`; its matching
  `FrameAdmitted.and` combines that trace-derived fact with another admission
  over the same retained roots.

This layer does not manufacture environment, storage, routing, delegation, or
precompile facts, constrain an execution's result, or filter by settlement.
A consumer must derive every independent admission from its actual trace and
use the retained/committed APIs when rollback matters.

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
- Small additions it needed: `ReplayCarrier.ofAddBal` (a direct balance credit
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
step and adds no step beyond `root`, `credit` and `ofAddBal`.  It is
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
  ([`Blanc/Semantics.lean`](../Blanc/Semantics.lean)); accepted-immediate
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
  projections, type-2 effective gas price and the
  `jauneListCompare_eq_compareLex` list-comparator bridge;
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
  `nonPush_sourceSite_appended`, `sstore_sourceSite_appended` and
  `successfulSstore_sourceSite_appended` carry the cursor and source-site
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
argument once: `getStor_addBal`/`getStor_subBal_addBal` say balance movement
never moves storage, `ofStorageOnly_preInv_iff`/`ofStorageOnly_postInv_iff`
reduce the frame invariants to the storage predicate, and
`ofStorageOnly_funcSound` reduces each per-target obligation to the bare
storage walk, declining the `nof`-class side condition a storage-determined
invariant never needs.  The module's no-write and `STATICCALL` sections
discharge targets that never write storage, and `ofStorageOnly_of_call`
carries the invariant across a child `call` under the deeper-frame
hypothesis.  `ofStorageOnly_of_call_sameBenv` is its general form: the
deeper-frame hypothesis need only cover frames at the caller's `benvStat`,
which is what a trace-admitted consumer whose entry condition reads the block
environment can discharge (DRIP's `soundAdmitted_of_stepClosedAt`).

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
