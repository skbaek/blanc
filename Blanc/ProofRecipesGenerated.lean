-- ProofRecipesGenerated.lean : goal-shape recipe data for Blanc tactics.
--
-- GENERATED FILE — do not edit by hand. Regenerate with:
--
--     python3 scripts/generate-proof-recipes.py --write

namespace Blanc.ProofRecipes

/-- A generated proof-engineering suggestion. All matching is advisory. -/
structure Recipe where
  id : String
  status : String
  triggers : List String
  preferredPath : String
  symbols : List String
  boundary : String
  deriving Repr, Inhabited

/-- Recipes generated from `scripts/proof-recipes.toml`, in registry order. -/
def recipes : List Recipe := [
  {
    id := "runcompiled-construction"
    status := "active"
    triggers := ["goal-head:Func.RunCompiled", "goal-head:Func.RunCompiledTo", "goal-head:Func.ExecTo", "goal-head:Func.ExecWitness"]
    preferredPath := "Use `func_run` and its registered opcode arms. Before walking a large concrete body, apply the term-size breaker: the pathological case is a walk whose intermediate term carries the whole concrete remaining program, memory or value, and its signature is a `maxRecDepth`/`maxHeartbeats` ceiling over a multi-`MSTORE` staging run. Factor such a walk into named sub-components, abstract each over the memory or value it threads — a carrier structure over a variable, as `ConstructorPatchInvariant` does in `Blanc/LidoCircuitBreakerDeploymentTrace.lean` — and instantiate the concrete facts through named top-level lemmas, so one layer over a variable stays small instead of composing multiplicatively. Build each certificate separately and abstract only those that cross the breaker; the abstraction is not free and a short bounded walk does not need it. For residual-cost attribution, opt in with the default-off `Blanc.Forward.discharge` trace and aggregate it with `scripts/read-discharge-trace.py` before changing a fallback."
    symbols := ["tactic:func_run", "declaration:Func.RunCompiled", "declaration:Func.RunCompiledTo", "declaration:Func.ExecTo", "declaration:Func.ExecWitness"]
    boundary := "This constructs a compiled walk; it does not invert an existing run, replace an already completed continuation with a summary, synthesize a parallel path certificate such as `DirectPausePath`, or optimize route data before the proof begins. A three-module inventory found the gas class heterogeneous (1,180 tactic / 90 residual) and every expensive value class heterogeneous, so no shared discharge fold is licensed. `LidoCircuitBreakerAttainment` instead measured repeated underconstrained `SourceStep` constructors and its one-path typed-helper pilot reduced 10.321 s to 5.971 s; that result does not license other route retrofits. Wave 4 found that exact proof-copy deletion moved `PauseWorldRunKit` only -1.1%, while a body-from-kernel summary moved `UnregisterRegistration` 38.482 to 21.610 s but required a new recursion ceiling and was reverted. Moving the same helper into `RegistrySubstrate` made that row 35.288 s and the gate red, so the cross-module extension is also closed. Those Wave 4 verdicts close two specific routes — a body-from-kernel summary and cross-module helper placement — and do not close the sub-component abstraction route in the preferred path. That route was measured separately on the 2026-08-23 deployment walk: a three-op prefix went from a 14.5 GiB store wall to a 0.8 s build, and the constructor body from a 15.5-minute hard stop with 12.6 GiB swap to a 737 ms compile. Those are whole-artifact build times recorded in that goal working log, not `check-elab.sh` rows, and no controlled measurement isolates the separate `DeploymentProof` privacy facade effect. The 2026-08-25 retrofit then dispositioned every named backport site. `pause_stageArgs_runCompiled` gained a local memory carrier: its target profiler entry fell from 29.898 s below the 2 s reporting threshold and its sequential owner row moved 47.842 to 31.984 s. A local Replacement carrier shared the guard-prefix composition over the existing staging suffix of the two replacement-registration body walks: their target entries fell from 28.371 and 41.545 s below 2 s and their owner row moved 30.441 to 2.326 s. All six associated recursion/heartbeat scopes disappeared. Cure 2 also ported the same leafwise construction route to the fresh-nonzero and absent-zero registration bodies: their owner rows moved 17.331 to 4.077 s and 15.033 to 3.190 s, and their remaining raised recursion/heartbeat scopes were removed. `registerPauser_stageArgs_runCompiled` retained its original concrete proof: a four-method carrier improved isolated attribution from 15.638 to 10.531 s but regressed the authoritative three-owner closure from Registry/Pause/Replacement 23.655/47.842/30.441 s to 37.989/67.316/53.222 s, so it was reverted. This is a measured non-candidate, not evidence that the technique is invalid; judge the owning closure, not a target-only profile. The 2026-08-21 `already_shared_cps` and `timing_refuted` screening rows answered whether these families could share a common helper, not whether the walked prefix carried an oversized concrete term. `ConstructorPatchInvariant`, `PauseStageMemory`, the Replacement guard-prefix certificates, `freshRegisterPauserBody_fromStage_runCompiled`, and `absentZeroRegisterPauserBody_fromStage_runCompiled` are the current local carrier/leaf-composition examples. `UnregisterRegistration` already contains an earlier hand-built equivalent, and an audit found no compelling WETH10 target. Cure 3 then executed that permitted local route on `pause_body_runCompiled`: eight private guard-prefix helpers reduced the fresh sequential owner row from 39.336 s to 11.819 s and its five-module owning closure from 79.790 s to 53.192 s, with no comparable failing `assumption` inside the factored helpers. The heartbeat scope was deleted after two clean default-heartbeat elaborations, and deterministic recursion-depth bisection right-sized the remaining command scope from 32768 to 1150 (1149 red, 1150 green). Cure 4's separate cold-entry case selected the narrow private `removeTarget_holeStorePrefix_runCompiled` boundary after four viable shapes; `PauseWorldRunKit` moved from 23.010 to 14.716 seconds. Reuse that narrow boundary only when the same accumulated cold-entry prefix recurs in a measured owner, before considering a broader continuation abstraction."
  },
  {
    id := "linear-dispatch-selection"
    status := "active"
    triggers := ["goal-shape:linear-dispatch-selection"]
    preferredPath := "For an existing `Func.RunCompiledTo` walk rooted at `Blanc.linearDispatchWith`, apply `dispatchBodyWitness_of_runCompiledTo` after supplying selector uniqueness, the selected entry, and the initial `selector :: tail` stack. The result is the exact selected-body walk plus stack removal and `DispatchFramePreserved`; compose the public frame facts with `Devm.DispatchFramePreserved.trans` and the push/pop/diff-burn adapters."
    symbols := ["module:Blanc/LinearDispatch.lean", "module:Blanc/LinearDispatchCorrectness.lean", "declaration:Blanc.linearDispatchWith", "declaration:Blanc.selectorUnique", "declaration:Blanc.Devm.DispatchFramePreserved", "declaration:Blanc.Devm.DispatchFramePreserved.trans", "declaration:Blanc.dispatchFrame_of_pushBurn", "declaration:Blanc.dispatchFrame_of_popBurnBy", "declaration:Blanc.dispatchFrame_of_diffBurn", "declaration:Blanc.DispatchBodyWitness", "declaration:Blanc.dispatchBodyWitness_of_runCompiledTo"]
    boundary := "The neutral theorem discharges only the dispatcher opcode inversions. It does not know a contract's selector census, calldata ABI, role storage, auxiliary rebasing, or selected-body semantics."
  },
  {
    id := "line-run-split"
    status := "active"
    triggers := ["implication-premise:Line.Run"]
    preferredPath := "Use `line_execute` or `line_execute_with`; revert a named run premise first when needed."
    symbols := ["tactic:line_execute", "tactic:line_execute_with", "declaration:Line.Run"]
    boundary := "The tactic performs one split and does not automatically transport an arbitrary set of observations."
  },
  {
    id := "func-run-prefix-split"
    status := "active"
    triggers := ["implication-premise:Func.Run"]
    preferredPath := "Use `func_execute n` or `func_execute_with line` to expose a known prefix."
    symbols := ["tactic:func_execute", "tactic:func_execute_with", "declaration:Func.Run"]
    boundary := "This targets the older implication-shaped `Func.Run`; it is not `RunCompiled` construction and does not invert an arbitrary named derivation without first reverting it."
  },
  {
    id := "stack-prefix-transport"
    status := "active"
    triggers := ["goal-shape:stack-prefix-line-run"]
    preferredPath := "Use `line_prefix` or `generalize_line_prefix`, with `show_pref` for concrete prefix goals. For a known MUL, DIV, TIMESTAMP, XOR, or non-address argument-check step, use the corresponding `prefix_of_*` declaration directly when the tactic has no registered arm."
    symbols := ["tactic:line_prefix", "tactic:generalize_line_prefix", "tactic:show_pref", "declaration:prefix_of_mul", "declaration:prefix_of_div", "declaration:prefix_of_timestamp", "declaration:prefix_of_xor", "declaration:prefix_of_argCheckNonAddress"]
    boundary := "`line_prefix` supports a finite instruction set and refuses instructions without a registered case. The direct `prefix_of_*` lemmas transport only the named stack prefix; combine them with a separate observation invariant when more state must be carried."
  },
  {
    id := "state-context-cleanup"
    status := "active"
    triggers := ["context-shape:intermediate-devm"]
    preferredPath := "Use `clear_state hState` after transporting every fact that must survive."
    symbols := ["tactic:clear_state"]
    boundary := "This is destructive context cleanup: it removes the state and all local facts that depend on it. The continuation-summary pilot found this trigger to be a false positive after a continuation was already complete; direct reuse of the existing generic summary added two source lines and no measurable elaboration win. Wave 4 supplied a second eligible false positive in the exact-helper reuse experiment: the goal was discharged by an existing `RunCompiled` summary, so clearing state would only destroy usable hypotheses. The trigger deliberately remains the bare more-than-two-`Devm` heuristic because summary availability is semantic, not recoverable from the context count; narrowing by goal head would introduce false negatives in real construction goals. Treat the trigger as a prompt to check for a completed summary first, never as an automatic cleanup command."
  },
  {
    id := "line-observation-invariance"
    status := "active"
    triggers := ["goal-head:Line.Inv", "goal-head:Ninst.Inv", "goal-head:Rinst.Inv"]
    preferredPath := "Use `line_inv` through the registered `Ninst.Hinv` and `Rinst.Hinv` instances."
    symbols := ["tactic:line_inv", "declaration:Line.Inv", "declaration:Ninst.Inv", "declaration:Rinst.Inv", "declaration:Ninst.Hinv", "declaration:Rinst.Hinv"]
    boundary := "A missing contract-neutral instance belongs in the lowest common upstream layer; contract-specific semantic facts do not."
  },
  {
    id := "function-observation-invariance"
    status := "active"
    triggers := ["goal-head:Func.Inv", "goal-head:Linst.Inv"]
    preferredPath := "For `Func.Inv`, use `func_inv` to assemble the function invariant from registered line and terminal invariants. For a terminal `Linst.Inv`, use the registered instance directly with `exact Linst.Hinv.inv`."
    symbols := ["tactic:func_inv", "declaration:Func.Inv", "declaration:Linst.Inv", "declaration:Linst.Hinv"]
    boundary := "`func_inv` deliberately refuses `Func.call`, whose callee is arbitrary under `Func.Inv`; fix the context or factor through the entry. A missing terminal instance belongs in the lowest common shared module, not in a contract consumer."
  },
  {
    id := "call-boundary-outcomes"
    status := "active"
    triggers := ["goal-head:Func.ExecSat", "goal-head:Prog.ExecSat", "goal-head:Func.ExecWitness"]
    preferredPath := "Use the `ForwardCall` module and the live `ExecSat`/`ExecWitness` layer to cross calls or package multiple outcomes."
    symbols := ["module:Blanc/ForwardCall.lean", "declaration:Func.ExecSat", "declaration:Prog.ExecSat", "declaration:Func.ExecWitness", "declaration:Prog.ExecWitness"]
    boundary := "Do not duplicate the settlement/determinism tail, and do not infer deadness from qualified-name grep alone."
  },
  {
    id := "devm-projection-bridge"
    status := "active"
    triggers := ["goal-shape:devm-update-projection"]
    preferredPath := "Rewrite with the matching Jaune update-first projection lemma, named `Devm.<update>_<projection>`, for the column in the goal. Never bridge a concrete effect tower or compiled artifact through `withOutput`, `setMach`, `setMeta`, `setWorld`, or another `with*` update using bare `change`, `show`, `rfl`, or `exact`."
    symbols := ["declaration:LidoCircuitBreaker.officialConstructorPost_refundCounter"]
    boundary := "A succeeding concrete `getStor` walk can expose the same projection mechanism after the effect tower has already been built. Cure 4 routed that case through the shared `Devm.withRefundCounter_getStor` and `Devm.addLog_getStor` semantic cuts plus a private cold-store boundary, moving `LidoCircuitBreakerDeploymentTrace` from 62.173 to 17.050 seconds. Reuse the earliest matching semantic projection cut; do not reorder `Meta` fields. This does not reopen `successor-projection-normalization`: that measured refutation attacked `setMach` chains in an owner dominated by unrelated kernel checks. Resource ceilings neither detect nor bound this kernel-side class. The matcher needs an explicit `Devm` update head in the target; when a local definition hides the chain, unfold only that binding and invoke `blanc_suggest` again."
  },
  {
    id := "bytesize-composition"
    status := "active"
    triggers := ["goal-shape:compileshape-bytesize"]
    preferredPath := "Prove one small `decide +kernel` fact per leaf, then derive internal `compileShape.byteSize` facts arithmetically through `dispatchNode_size`-style composition. `dispatchCae9_size` is the canonical example: with its children available, its composition closes in 0.004 s."
    symbols := ["declaration:Weth10.dispatchCae9_size"]
    boundary := "The measured law is approximately 2.6 ms per compiled byte of the addressed object; byte-range width predicts nothing because `byteAtByShape` is lazy. Cure 2 applied the existing composition route in `Weth10Deploy`: named size facts replaced repeated closed decisions and moved its owner row from 43.283 to 29.463 s. The narrower `Weth10DeployDomainSlices` packet first had to add its missing child facts and then regressed from 16.628 to 17.734 s, so it was reverted; reopen that family only with a broader child-fact or representation change whose owner row wins. `weth10MainEmit_drop_3950` costs approximately 0.011 s and should remain unchanged."
  },
  {
    id := "successor-projection-normalization"
    status := "partial"
    triggers := ["goal-shape:successor-projection"]
    preferredPath := "Use an existing named, oriented, one-layer projection lemma when one already serves the goal; otherwise keep the explicit local normalization."
    symbols := ["declaration:Devm.getStorVal_setMach"]
    boundary := "Do not replace deep state towers with transparent abbreviations or broad unfolding; `RegistrySubstrate` records why that diverges. On the heartbeatAfterCount/Expiry/Interval tower, adding six one-layer projection lemmas and six retrofits regressed module elaboration from 40.075 s to 41.944 s. Wave 3 then found `LidoCircuitBreakerAccess` dominated by 27–28 s kernel checks, not its secondary setMach chains. Wave 4 attributed the Registry tail to `directPauseControl_gas` (defeq/whnf plus kernel checking) and `directPauseControl_run` (kernel checking); all later declarations stayed below 2 s and none of the module's 212 `Devm.setMach_setMach` citations occurs after that obstacle. This does not reopen S3, S1, S2, or a module split."
  },
  {
    id := "runcompiled-family-compression"
    status := "partial"
    triggers := ["goal-shape:runcompiled-family-compression"]
    preferredPath := "When expensive bodies repeat the same post-kernel walk, freeze a committed-row decision rule, factor the body-from-kernel boundary, and preserve the old statements as instantiations. If a one-shot `func_run` needs a local resource ceiling, promote its exact tactic-produced residual states to named theorem boundaries, reducing the chunks as far as needed; compare against the original declarations' limits before rejecting the factorization. Profile the generic, chunks, and instances, run the bare elaboration gate, withhold the generic in an isolated falsifier, and reject any split that materially regresses its owner row or adds a proof-resource ceiling."
    symbols := ["declaration:Blanc.LidoCircuitBreaker.registerPauser_stageArgs_runCompiled"]
    boundary := "G1: deleting 687 exact proof-copy lines moved `PauseWorldRunKit` 23.536 to 23.273 s (-1.1%) and raised `RegistrySubstrate` 17.513 to 26.909 s, so exact source duplication alone is not a timing signal. G2 correction: the earlier rejection was not like-for-like because the original registration bodies already carried `maxRecDepth 16384` and `maxHeartbeats 2400000`. The 24-step generic and a 4+20 same-declaration split failed at default limits, but named two-instruction mask chunks plus named argument, branch, admin, and static-prefix summaries succeeded. Reusing one private body-from-kernel theorem across all four zero-pauser bodies removed eight resource scopes and moved `UnregisterRegistration` 38.482 to 5.318 s (-86.2%); the two-old-last intermediate measured 21.359 s. G3 remains refuted: shared placement for `ReplacementRegistration.oldLastNonzero` made `RegistrySubstrate` 35.288 s (>2x baseline), so cross-module reuse still needs independent ancestor headroom. G4: the Registry tail is sparse and kernel/defeq-owned, not a compression family. G5: `PauseWorldRun` (8.995 s), the WETH accounting pair (25.573 s combined), and the rich/local twin (4.424 s) are maintainability-only; source symmetry does not license a timing retrofit."
  },
  {
    id := "shared-subject-kernel-decision"
    status := "active"
    triggers := ["goal-shape:shared-subject-kernel-decision"]
    preferredPath := "When several kernel-decidable facts inspect the same expensive closed subject, bind that subject once, decide the facts as one tuple or conjunction, and project the results; alternatively prove one normalized equality and derive the views with `congrArg`."
    symbols := ["declaration:Blanc.LidoCircuitBreaker.runtimeSourceEffectPcs_official"]
    boundary := "This applies only when normalization of one identical closed subject dominates every fact. It does not license bundling facts about different subjects, and it is not a term-size or definitional-equality cure. In cure 2, six Attainment pins bundled over `runtimePersistentSourceSites officialParams` cost the sum rather than the max and regressed the owner row from 32.134 to 53.652 s; for that family, free-variable aliases and conjunction elaboration defeated the rule. Reopen Attainment only with a shared closed-subject representation that avoids those costs."
  },
  {
    id := "selector-separation"
    status := "active"
    triggers := ["goal-shape:selector-separation"]
    preferredPath := "Hoist a reviewed literal separation table ahead of repeated consumers and transport its facts directly; the ExecAccounting pilot reduced its module profile from 46.28 s to 17.74 s across 16 retrofits."
    symbols := ["declaration:Weth10.selector_name_ne_approveSelector"]
    boundary := "Cure 2 completed the module-local retrofit: the remaining 28 name-selector kernel decisions now rewrite through the existing numeral bridges, and the approve straggler uses its hoisted separation certificate. Together those changes moved `Weth10HolderFlowExecAccounting` from 17.056 to 13.067 s at the final checkpoint. This does not establish I3's cross-domain canonical selector list, `Nodup` theorem, extractor, named simp set, or cross-module placement; those are separate designs and no blocking rule may require them. The earlier whitespace-only compaction remains a source-size result with no timing claim. `blanc_suggest` still misses the literal `SelectorWordNoPrimaryFlow` certificate goal, so callers must consult this recipe manually for that shape."
  },
  {
    id := "fixed-byte-offsets"
    status := "active"
    triggers := ["goal-shape:fixed-byte-offset"]
    preferredPath := "Use `Bytes.sliceD_writeAt` for the written window, `Bytes.sliceD_writeAt_before` or `Bytes.sliceD_writeAt_after` for disjoint neighboring windows, and `Bytes.readWord_writeAt_self` or `Bytes.readWord_writeAt_of_disjoint` for word reads. For padded or abstract memory, start from `Mem.Wf` and `Mem.Reads`. Keep compiled-emitter `List.drop` equalities local unless a profile proves that a structural helper moves their kernel cost."
    symbols := ["module:Blanc/CommonProofs.lean", "declaration:Bytes.sliceD_writeAt", "declaration:Bytes.sliceD_writeAt_before", "declaration:Bytes.sliceD_writeAt_after", "declaration:Bytes.readWord_writeAt_self", "declaration:Bytes.readWord_writeAt_of_disjoint", "declaration:Mem.Wf", "declaration:Mem.Reads"]
    boundary := "These laws cover byte-array writes and fixed-width word reads. They do not turn arbitrary compiled-emitter `List.drop` identities into a shared API. `LidoCircuitBreakerEnumeration` was dominated by 34–35 s kernel checks unrelated to byte offsets. On `Weth10Deploy`, a two-next/branch helper changed its 41.5–41.7 s proof by only 0.6–1.1%, and a later top-level private tail theorem moved the owner median only from 48.11 to 46.85 s (-2.62%); both pilots were reverted. Reopen that separate emitter route only for a change whose serialized owner median improves by the licensed win rule."
  },
  {
    id := "frame-root-carrying-execution"
    status := "active"
    triggers := ["goal-shape:frame-root-carrying"]
    preferredPath := "Use `rootedRunCompiledTo` to carry a predicate through a compiled walk, discharge childless instructions with `ninstAllChildRoots_of_not_exec` or `NonExecInstruction`, establish spawning children with `ninstAllChildRoots_of_exec_spawn`, and finish a whole program with `Prog.exec_of_rootedRunCompiledTo`."
    symbols := ["module:Blanc/RootedExecution.lean", "declaration:rootedRunCompiledTo", "declaration:ninstAllChildRoots", "declaration:ninstAllChildRoots_of_not_exec", "declaration:ninstAllChildRoots_of_exec_spawn", "declaration:funcExecFree", "declaration:rootedRunCompiledTo_of_execFree", "declaration:Prog.exec_of_rootedRunCompiledTo", "declaration:NonExecInstruction"]
    boundary := "This API preserves predicates over raw entered-frame roots. It does not apply settlement/commit filtering; use `ExecutionSettlement` and `ExecutionOccurrence` for retained or committed histories."
  },
  {
    id := "message-execution-settlement"
    status := "active"
    triggers := ["goal-shape:message-execution-settlement"]
    preferredPath := "Use `MessageExecution.processMessage_eq_settle_exec` for the raw-to-settled bridge, then the clean/revert/halt adapters and canonical `settledRevert` or `settledHalt` machines instead of unfolding message settlement at the contract site. For an already-retained `ProcessMessage`, use `processMessage_clean_rawPost` to recover the successful raw post, `processMessage_entry_facts` for the actual entry frame projections, and the separate `processMessage_entry_stack` / `processMessage_entry_memory` empty-entry projections."
    symbols := ["module:Blanc/MessageExecution.lean", "module:Blanc/MessageExecutionInversion.lean", "declaration:MessageExecution.processMessage_eq_settle_exec", "declaration:MessageExecution.processMessage_clean_of_exec", "declaration:MessageExecution.processMessage_revert_of_exec", "declaration:MessageExecution.processMessage_halt_of_exec", "declaration:MessageExecution.processMessage_clean_rawPost", "declaration:MessageExecution.processMessage_entry_facts", "declaration:MessageExecution.processMessage_entry_stack", "declaration:MessageExecution.processMessage_entry_memory", "declaration:MessageExecution.settledRevert", "declaration:MessageExecution.settledHalt", "declaration:Msg.initDevm_stack", "declaration:Msg.initSevm_data"]
    boundary := "The forward bridge requires entry-state identity and disabled precompiles. The retained-frame inversion exposes storage equality rather than whole-state equality because value transfer may change balances. These facts describe ordinary call-message settlement, not CREATE settlement."
  },
  {
    id := "raw-sstore-free-compiled-path"
    status := "active"
    triggers := ["goal-shape:raw-sstore-free-compiled-path"]
    preferredPath := "Build `Func.RunCompiledTo.NoRawSstorePath` over the exact selected compiled derivation, supplying childlessness for every reached external instruction. Use `NoRawSstorePath.of_execFree` for an execution-free, locally SSTORE-free body and `NoRawSstorePath.of_revWith` for a symbolic constant-error body. For a warm fixed-width SHA-256 precompile step, preserve the empty child slot with `Ninst.childlessRunCompiled_statcall_sha256_64_warm_ext`; finish with `Prog.exists_exec_noRawSstore`."
    symbols := ["module:Blanc/ForwardNoRawSstore.lean", "declaration:Blanc.Ninst.ChildlessRunCompiled", "declaration:Blanc.Ninst.ChildlessRunCompiled.toRunCompiled", "declaration:Blanc.Ninst.childlessRunCompiled_exec_doneFrame", "declaration:Blanc.Ninst.childlessRunCompiled_statcall_doneFrame", "declaration:Blanc.Ninst.childlessRunCompiled_statcall_sha256_64_warm_ext", "declaration:Blanc.Exec.NoRawSstore", "declaration:Blanc.Func.RunCompiledTo.NoRawSstorePath", "declaration:Blanc.Func.RunCompiledTo.NoRawSstorePath.of_execFree", "declaration:Blanc.Func.RunCompiledTo.NoRawSstorePath.of_revWith", "declaration:Blanc.Prog.exists_exec_noRawSstore", "declaration:Blanc.Exec.NoRawSstore.no_successfulSstoreOccurrence", "declaration:Blanc.Exec.NoRawSstore.retainedStorageWrites_eq_nil"]
    boundary := "This is raw construction-direction chronology, not rollback reasoning. An empty retained-write list or reverted terminal state does not prove the certificate because an earlier raw SSTORE may have executed and then rolled back. Entered child frames require their own evidence; synchronously resolved childless precompiles may use the explicit done-frame constructor."
  },
  {
    id := "retained-write-noninterference"
    status := "active"
    triggers := ["goal-shape:retained-write-noninterference"]
    preferredPath := "For `Exec.NoRetainedWriteTo`, split first on `Execution.commits out = true`. Close the rollback arm with `Exec.noRetainedWriteTo_of_not_commits`; on a committing execution use `Exec.noRetainedWriteTo_of_sourceSites_no_exec` for a source-childless program, `Exec.noRetainedWriteTo_of_no_execOccurrence` for an occurrence-level proof, or `Exec.noRetainedWriteTo_of_frame_owners_ne` when entered child frames have distinct storage owners."
    symbols := ["module:Blanc/ExecutionNoninterference.lean", "declaration:Exec.NoRetainedWriteTo", "declaration:Exec.noRetainedWriteTo_of_not_commits", "declaration:Exec.noRetainedWriteTo_of_no_execOccurrence", "declaration:Exec.noRetainedWriteTo_of_sourceSites_no_exec", "declaration:Exec.noRetainedWriteTo_of_frame_owners_ne"]
    boundary := "The noncommitting theorem proves retained-write absence by rollback, not raw instruction absence. The committing routes still need exact invocation/source or entered-frame ownership evidence; do not infer childlessness merely from a static call flag."
  },
  {
    id := "devm-common-update-laws"
    status := "active"
    triggers := ["goal-shape:devm-common-update-law"]
    preferredPath := "Before proving a record projection by `rfl`, search the public `Devm` laws in `CommonProofs`: memory writes, accessed-storage/setMach cancellation, storage read-after-write, and the reusable RETURN/SSTORE post projection cuts are named there. Jaune also supplies update-first projection laws such as `Devm.memWrite_gasLeft` and `Devm.setMach_accessedStorageKeys`."
    symbols := ["module:Blanc/CommonProofs.lean", "declaration:Devm.memWrite_memory", "declaration:Devm.memWrite_stack", "declaration:Devm.addAccessedStorageKey_setMach_setMach", "declaration:Devm.getStorVal_setStorVal_self", "declaration:Devm.retPost_getStorVal", "declaration:Devm.sstoreBase_state"]
    boundary := "Use the smallest abstract-base law that matches the goal. Do not unfold a concrete effect tower merely because these laws themselves are definitionally simple."
  },
  {
    id := "compiled-terminal-at-zero"
    status := "active"
    triggers := ["goal-shape:terminal-return-revert"]
    preferredPath := "For an offset-zero 32-byte RETURN or empty REVERT, use `Func.runCompiledTo_ret_word_at_zero` or `Func.runCompiledTo_rev_empty_at_zero`; use the more general `Func.runCompiledTo_ret_word` and `Func.runCompiledTo_rev` only when the offset, size, stack tail, or payload differs."
    symbols := ["module:Blanc/ExecutionTerminal.lean", "declaration:Func.runCompiledTo_ret_word_at_zero", "declaration:Func.runCompiledTo_rev_empty_at_zero"]
    boundary := "These are construction lemmas for two common terminal shapes, not inversion theorems and not a replacement for the general terminal APIs."
  },
  {
    id := "full-length-slice"
    status := "active"
    triggers := ["goal-shape:full-length-slice"]
    preferredPath := "When a padded `sliceD` begins at zero and its requested width is the source length, rewrite with `Bytes.sliceD_zero_length` instead of reproving the take/drop normalization locally."
    symbols := ["module:Blanc/CommonProofs.lean", "declaration:Bytes.sliceD_zero_length"]
    boundary := "The theorem needs exact equality between source length and requested width. It does not characterize nonzero offsets or shorter/longer windows."
  },
  {
    id := "retained-wrapper-trace"
    status := "active"
    triggers := ["goal-shape:retained-wrapper-trace"]
    preferredPath := "Choose the carrier at the wrapper boundary you actually have, then use its matching `exists_*Trace` theorem to retain Jaune's deterministic recursive witness. Start with `RetainedXlot` for a filled execution slot; use `MessageCallTrace`, `TransactionTrace`, `AppliedBodyTrace`, or the configured block/history carriers instead of reconstructing a trace from only the terminal state."
    symbols := ["module:Blanc/ExecutionTrace.lean", "module:Blanc/ExecutionHistory.lean", "declaration:ExecutionTrace.RetainedXlot", "declaration:ExecutionTrace.exists_retainedXlot_of_filled", "declaration:ExecutionTrace.ProcessMessageTrace", "declaration:ExecutionTrace.exists_processMessageTrace", "declaration:ExecutionTrace.ProcessCreateMessageTrace", "declaration:ExecutionTrace.exists_processCreateMessageTrace", "declaration:ExecutionTrace.MessageCallTrace", "declaration:ExecutionTrace.exists_messageCallTrace", "declaration:ExecutionTrace.TransactionTrace", "declaration:ExecutionTrace.exists_transactionTrace", "declaration:ExecutionTrace.ApplyTransactionsTrace", "declaration:ExecutionTrace.exists_applyTransactionsTrace", "declaration:ExecutionTrace.SystemMessageTrace", "declaration:ExecutionTrace.exists_systemMessageTrace", "declaration:ExecutionTrace.RequestsTrace", "declaration:ExecutionTrace.exists_requestsTrace", "declaration:ExecutionTrace.AppliedBodyTrace", "declaration:ExecutionTrace.exists_appliedBodyTrace", "declaration:ExecutionTrace.ConfiguredBlockTrace", "declaration:ExecutionTrace.exists_configuredBlockTrace_of_transition", "declaration:ExecutionTrace.ConfiguredHistoryTrace", "declaration:ExecutionTrace.exists_configuredHistoryTrace_of_reachUsing"]
    boundary := "These carriers remember execution and wrapper structure but assign no contract-specific meaning to effects. Use the `Execution*Effects` modules for `ContractSpec` transport, `ExecutionPath` for stable call-tree locations, and the `Execution*StateTrace` modules for ordered world-state replay."
  },
  {
    id := "retained-state-replay"
    status := "active"
    triggers := ["goal-head:StateReplay"]
    preferredPath := "Build the chronology at the narrowest retained layer and finish with its `stateReplay` theorem. Use `Exec.committedStateReplay` for a recursive execution, then the message, transaction, body, block, or history chronology module to retain wrapper boundaries in their exact execution order. Compose or relabel an existing replay with `StateReplay.append`, `StateReplay.mapOrigin`, and `StateTransition.mapOrigin`."
    symbols := ["module:Blanc/ExecutionStateTrace.lean", "module:Blanc/ExecutionMessageStateTrace.lean", "module:Blanc/ExecutionTransactionStateTrace.lean", "module:Blanc/ExecutionBodyStateTrace.lean", "module:Blanc/ExecutionHistoryStateTrace.lean", "declaration:StateTransition", "declaration:StateReplay", "declaration:StateReplay.append", "declaration:StateTransition.mapOrigin", "declaration:StateReplay.mapOrigin", "declaration:Exec.committedStateReplay", "declaration:ExecutionTrace.MessageCallTrace.stateReplay", "declaration:ExecutionTrace.TransactionStateChronology.stateReplay", "declaration:ExecutionTrace.AppliedBodyStateChronology.stateReplay", "declaration:ExecutionTrace.ConfiguredHistoryStateChronology.stateReplay"]
    boundary := "A `StateReplay` proves endpoint continuity and preserves exact provenance; it does not classify a transition as a contract deposit, withdrawal, or attack step. Apply that interpretation only in the contract-owned layer above the generic chronology."
  },
  {
    id := "constant-error-guard"
    status := "active"
    triggers := ["goal-shape:constant-error-guard"]
    preferredPath := "Use `Func.runCompiledTo_errorGuard` when a nonzero branch flag tail-calls an auxiliary equal to `Func.revWith reason`. Supply the auxiliary lookup, exact entry-state memory image and alignment, payload bounds, gas expressed through `errorGuardCost`, and stack room; the theorem returns the complete ABI `Error(string)` payload with exact final memory, stack, and gas."
    symbols := ["module:Blanc/RevertPayload.lean", "declaration:Blanc.errorBodyCost", "declaration:Blanc.errorCallCost", "declaration:Blanc.errorGuardCost", "declaration:Blanc.Func.runCompiledTo_revWith", "declaration:Blanc.Func.runCompiledTo_errorGuard"]
    boundary := "This proves the branch-and-internal-call walk only. It does not select a contract route, establish which flag is nonzero, authenticate a contract-specific reason/slot table, or turn the local revert into a public endpoint theorem. Keep `errorGuardCost` indexed by the actual entry state so memory expansion is not silently weakened."
  },
  {
    id := "one-word-source-return"
    status := "active"
    triggers := ["goal-head:ReturnsWord"]
    preferredPath := "For the source fragment `mstoreAt 0 +++ returnMemoryRange 0 32`, use `of_storeReturnWord` when a `Mem.Wf`/`Mem.Reads` image is already available, or `returnsWord_of_storeReturn` when no memory side condition is in context. Both prove `ReturnsWord` from the known stack head and preserve code."
    symbols := ["module:Blanc/Ladder.lean", "declaration:ReturnsWord", "declaration:of_storeReturnWord", "declaration:returnsWord_of_storeReturn"]
    boundary := "This is the source-level one-word ABI observation. For a compiled terminal walk use `Func.runCompiledTo_ret_word_at_zero`; for other offsets, sizes, or payloads use the general return APIs."
  },
]

end Blanc.ProofRecipes
