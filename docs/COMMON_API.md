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
- None matches: search public declarations in `Blanc/CommonCore.lean`,
  `Blanc/CommonProofs.lean`, and `Blanc/Ladder.lean`; a helper found only in a
  contract module is a hoisting candidate, not a cross-contract import target.

## E — execution

### E1. I need to construct a source or compiled execution term

- Ordinary source `Func.Run` walk:
  `func_execute`, `func_execute_with`, and the split lemmas in
  [`Blanc/Tactics.lean`](../Blanc/Tactics.lean).
- Ordinary compiled success walk (`Func.RunCompiled`): `func_run` and the
  opcode constructors in [`Blanc/Forward.lean`](../Blanc/Forward.lean).
- Compiled walk with an arbitrary terminal outcome (`Func.RunCompiledTo`):
  [`Blanc/Reverts.lean`](../Blanc/Reverts.lean).
- Invert an existing arbitrary-outcome compiled walk:
  [`Blanc/CompiledWalkInversion.lean`](../Blanc/CompiledWalkInversion.lean).
  Use `runCompiledTo_next_inv`, `runCompiledTo_branch_inv`,
  `runCompiledTo_call_inv`, and `runCompiledTo_prepend_inv` for structural
  nodes; `runCompiledTo_last_inv`, `runCompiledTo_rev_inv`, and
  `runCompiledTo_revSelector_inv` for terminal/revert nodes.  The shared
  `iszero_stack_inv` also transports the unchanged memory and return data.
  Known impossible successful terminals/calls use `Linst.not_run_rev_ok`,
  `Func.RunCompiledTo.not_ok_revData`,
  `Func.RunCompiledTo.not_ok_call_revData`,
  `Func.RunCompiledTo.not_ok_call_rev`, and
  `Func.RunCompiledTo.not_ok_call_revSelector`; successful `STOP` identity is
  `Func.RunCompiledTo.stop_eq`.  For a known branch-head prefix use
  `Func.RunCompiledTo.zero_branch_of_prefix` or
  `Func.RunCompiledTo.succ_branch_of_prefix`, both outcome-polymorphic.  A
  successful shared `nonpayable` wrapper is peeled by
  `Func.RunCompiledTo.nonpayable_body_of_ok`, which also derives zero value and
  preserves the known stack tail and storage.
  This remains COMMON_API-only: the same `Func.RunCompiledTo` head is also the
  reliable trigger for construction recipes, so an automatic recipe would
  conflate constructing and inverting a walk.
- Recover a selected body from a linear selector dispatcher:
  [`Blanc/LinearDispatch.lean`](../Blanc/LinearDispatch.lean) defines the
  shared `Blanc.linearDispatchWith` and `Blanc.selectorUnique`; the companion
  [`Blanc/LinearDispatchCorrectness.lean`](../Blanc/LinearDispatchCorrectness.lean)
  owns `dispatchBodyWitness_of_runCompiledTo`.  Supply selector uniqueness,
  selected-entry membership, the initial `selector :: tail` stack, and the
  exact `RunCompiledTo` walk; it returns the exact selected-body walk and a
  `DispatchFramePreserved` witness before any contract-specific ABI, role, or
  storage reasoning.  Compose adjacent witnesses with
  `Devm.DispatchFramePreserved.trans`.  When a family builds its own dispatcher
  walk it can also consume the frame steps directly:
  `dispatchFrame_of_pushBurn`, `dispatchFrame_of_popBurnBy`, and
  `dispatchFrame_of_diffBurn` carry a `DispatchFramePreserved` across one push,
  one burning pop, and a stack difference respectively.
- Calls, delegate calls, or child-frame resumption: go to E2.
- A predicate must hold for every entered child root: go to E3.
- Only the terminal RETURN/REVERT remains: go to E4.

### E2. The walk crosses a child frame

Use [`Blanc/ForwardCall.lean`](../Blanc/ForwardCall.lean):

- `Func.ExecWitness` / `Prog.ExecWitness` package raw call outcomes.
- `Func.ExecSat` / `Prog.ExecSat` package predicates over outcomes.
- The `Ninst.runCompiled_*call*` family constructs concrete call crossings.
- `Func.exec_of_runCompiledTo` and its program bridge recover an `Exec`
  derivation from a completed arbitrary-outcome compiled walk.

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

### E4. I need a common terminal walk

Use [`Blanc/ExecutionTerminal.lean`](../Blanc/ExecutionTerminal.lean):

- `Func.runCompiledTo_ret_word_at_zero` for a known 32-byte return at offset 0.
- `Func.runCompiledTo_rev_empty_at_zero` for an empty revert at offset 0.

For different offsets, sizes, stack tails, or payloads, use the general
`Func.runCompiledTo_ret_word` in `ForwardCall` or
`Func.runCompiledTo_rev` / `Func.runCompiledTo_rev_of` in `Reverts`.

### E5. I need to inspect what happened in an `Exec`

- Raw nodes, raw frame roots, and instruction occurrence:
  [`Blanc/ExecutionOccurrence.lean`](../Blanc/ExecutionOccurrence.lean).
- Determinism of execution witnesses:
  [`Blanc/ExecDeterminism.lean`](../Blanc/ExecDeterminism.lean).

## I — invariance and noninterference

### I1. One instruction/line/function preserves an observation

- `Ninst.Inv`, `Rinst.Inv`, and `Line.Inv`: use `line_inv` plus the registered
  `Ninst.Hinv` / `Rinst.Hinv` instances in `Blanc/Tactics.lean`.
- `Func.Inv`: use `func_inv`; it intentionally refuses arbitrary `Func.call`.
- For direct stack-prefix transport through shared line instructions, use the
  `prefix_of_*` family in [`Blanc/CommonProofs.lean`](../Blanc/CommonProofs.lean),
  including `prefix_of_timestamp` for the block-time push and `prefix_of_xor`
  for `XOR`.  These declarations are also registered with the
  `stack-prefix-transport` recipe.
- `Devm.state` is preserved by `mstore` and `mload`; a walk that tracks a
  single account's balance states its invariant as the pointwise projection
  `fun d => Devm.getBal d a`, for which `Rinst`/`Ninst` instances are
  registered beside the whole-family ones.
- A missing contract-neutral instance belongs in a shared module below every
  consumer, not in the first contract that needs it.

### I2. The property concerns a complete execution or child frames

- Generic execution noninterference:
  [`Blanc/ExecutionNoninterference.lean`](../Blanc/ExecutionNoninterference.lean).
  For `Exec.NoRetainedWriteTo`, first split on `Execution.commits out = true`:
  `Exec.noRetainedWriteTo_of_not_commits` closes the rollback arm;
  `Exec.noRetainedWriteTo_of_no_execOccurrence`,
  `Exec.noRetainedWriteTo_of_sourceSites_no_exec`, and
  `Exec.noRetainedWriteTo_of_frame_owners_ne` are the committing routes.
- Write-freedom across cycles:
  [`Blanc/CycleWriteFree.lean`](../Blanc/CycleWriteFree.lean).
- Transient-state invariance and settlement:
  [`Blanc/TransientInvariance.lean`](../Blanc/TransientInvariance.lean) and
  [`Blanc/TransientSettlement.lean`](../Blanc/TransientSettlement.lean).
- If the invariant is specifically over entered raw frame roots, return to E3.

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

Use [`Blanc/CommonProofs.lean`](../Blanc/CommonProofs.lean):

- `Devm.addAccessedStorageKey_setMach_setMach` cancels an obsolete machine
  component across an access-key update followed by the final `setMach`.
- `Devm.getStorVal_setStorVal_self` is persistent storage read-after-write.
- `Devm.retPost_world`, `Devm.retPost_getStorVal`, and
  `Devm.retPost_transientStorage` project through the common
  `setMach`/`memRead`/`withOutput` return post.
- `Devm.sstoreBase_state`, `Devm.sstoreBase_error`,
  `Devm.sstoreBase_transientStorage`, and `Devm.sstoreBase_logs` project the
  common warm/refund/storage-write post.

### S3. I need state-relation or write-frame composition

Use `Devm.StateWriteFrame` and its reflexive/transitive/composition lemmas in
`Blanc/CommonProofs.lean`, then inspect higher-level relation combinators in
[`Blanc/Ladder.lean`](../Blanc/Ladder.lean).

### S4. I need a basic EVM-word identity

Use the word/arithmetic declarations in
[`Blanc/CommonProofs.lean`](../Blanc/CommonProofs.lean) before destructing a
`B256`.  In particular, `B256.and_comm` and `B256.xor_comm` provide the shared
commutativity facts for bitwise conjunction and exclusive-or, while
`B256.and_idem_right` removes a repeated identical mask.

For the pause face specifically, `compact_pause_word_eq_projection` in
[`Blanc/PinnedPauseTarget.lean`](../Blanc/PinnedPauseTarget.lean) identifies the
branch-free compiled pause word `time * ((sentinel =? duration) =? 0) + duration`
with `pauseForProjection`.  Every faithful `PausableUntil` port compiles that
arithmetic, so consume it there rather than restating it per family.

## M — bytes and memory

### M1. The goal is a `sliceD` normalization

- Full source from offset zero: `Bytes.sliceD_zero_length` in
  `Blanc/CommonProofs.lean`.
- Recover a selector from calldata described as
  `abiSelectorBytes selected ++ tail` with
  `selector_eq_of_data_eq_abiSelectorBytes_append`; discharge its explicit
  canonicality premise `Bytes.toB256 (abiSelectorBytes selected) = selected`
  for the concrete four-byte selector.
- Read back a `Bytes.writeAt`: `Bytes.sliceD_writeAt` and the neighboring
  pointwise/write-layout laws in `Blanc/CommonProofs.lean`.
- Fixed or padded memory windows: use `Mem.Wf` and `Mem.Reads` before adding a
  local take/drop proof.

### M2. The goal is an EVM memory update or read

- `Devm.memWrite_memory`, `Devm.memWrite_stack`, and Jaune's
  `Devm.memWrite_gasLeft` describe the primitive update.
- `Mem.size_write_of_le`, `Mem.size_read_snd_of_le`, and related extension
  lemmas live in [`Blanc/ForwardCall.lean`](../Blanc/ForwardCall.lean).
- `Func.runCompiledTo_mstore_step` and other compiled memory steps live in the
  forward construction modules.

## T — settlement

### T1. I have `exec (initEvm msg)` and need `processMessage msg`

Use [`Blanc/MessageExecution.lean`](../Blanc/MessageExecution.lean):

- `MessageExecution.processMessage_eq_settle_exec` exposes the common frame
  settlement boundary.
- `processMessage_clean_of_exec`, `processMessage_revert_of_exec`, and
  `processMessage_halt_of_exec` cover the three raw outcomes.
- `settledRevert` and `settledHalt`, with their projection lemmas, name the
  canonical settled error machines.
- For the inversion direction, use
  [`Blanc/MessageExecutionInversion.lean`](../Blanc/MessageExecutionInversion.lean):
  `processMessage_clean_rawPost` recovers a clean successful raw post, while
  `processMessage_entry_facts` recovers code, target, calldata, timestamp,
  entry storage, and memory well-formedness from the actual retained frame;
  `processMessage_entry_stack` separately recovers its empty operand stack
  without changing the established conjunction returned by the former.
- `Msg.initDevm_*` and `Msg.initSevm_*` expose canonical message-entry fields.

### T2. I need to know which child effects survive settlement

Use [`Blanc/ExecutionSettlement.lean`](../Blanc/ExecutionSettlement.lean) and
[`Blanc/ExecutionOccurrence.lean`](../Blanc/ExecutionOccurrence.lean):

- `Execution.commits` and `Frame.settlementCommits` distinguish raw success
  from complete frame settlement.
- `Exec.descendantFrames`, `Exec.committedFrames`, and retained-node APIs
  traverse only effects that survive the relevant settlement boundary.

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

### C2. I need deployment/message correspondence

- Generic deployment compilation:
  [`Blanc/DeploymentCompiled.lean`](../Blanc/DeploymentCompiled.lean).
- Generic deployment-message facts:
  [`Blanc/DeploymentMessage.lean`](../Blanc/DeploymentMessage.lean).
- Source attainment and source-step provenance:
  [`Blanc/SourceAttainment.lean`](../Blanc/SourceAttainment.lean).

## Maintenance rule

When hoisting a reusable declaration, add it to the narrowest branch above (or
add a new sub-branch), register a goal-sensitive proof recipe when a reliable
goal shape exists, and remove contract-local copies. Do not add a contract
module as a registry destination: that is evidence the declaration has not yet
reached its common owner.
