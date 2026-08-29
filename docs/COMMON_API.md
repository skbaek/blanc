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
