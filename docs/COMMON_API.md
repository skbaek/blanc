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
- A missing contract-neutral instance belongs in a shared module below every
  consumer, not in the first contract that needs it.

### I2. The property concerns a complete execution or child frames

- Generic execution noninterference:
  [`Blanc/ExecutionNoninterference.lean`](../Blanc/ExecutionNoninterference.lean).
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

## M — bytes and memory

### M1. The goal is a `sliceD` normalization

- Full source from offset zero: `Bytes.sliceD_zero_length` in
  `Blanc/CommonProofs.lean`.
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
- `Msg.initDevm_*` and `Msg.initSevm_*` expose canonical message-entry fields.

### T2. I need to know which child effects survive settlement

Use [`Blanc/ExecutionSettlement.lean`](../Blanc/ExecutionSettlement.lean) and
[`Blanc/ExecutionOccurrence.lean`](../Blanc/ExecutionOccurrence.lean):

- `Execution.commits` and `Frame.settlementCommits` distinguish raw success
  from complete frame settlement.
- `Exec.descendantFrames`, `Exec.committedFrames`, and retained-node APIs
  traverse only effects that survive the relevant settlement boundary.

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

`ContractSpec.StateInv.ne_of_messageCreateCollision_false` in
[`Blanc/ExecutionMessageEffects.lean`](../Blanc/ExecutionMessageEffects.lean)
is the message-level companion: a CREATE wrapper that does not collide is
running at an address other than the installed contract.

### T4. The wrapper is a message call and I must see through delegation

Use
[`Blanc/ExecutionMessageEffects.lean`](../Blanc/ExecutionMessageEffects.lean):

- `ExecutionTrace.messageCallDelegation_fields` and its named projections
  (`_caller_eq`, `_target_eq`, `_currentTarget_eq`,
  `_shouldTransferValue_eq`) carry a routing or value field across the
  EIP-7702 authorization prefix; `_getStor_eq` and `_bal_eq` carry the world.
- `ExecutionTrace.messageCallExecutionMessage_caller_eq` and its siblings
  (`_target_eq`, `_currentTarget_eq`, `_shouldTransferValue_eq`,
  `_getStor_eq`, `_bal_eq`) do the same across delegated-code resolution.

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
