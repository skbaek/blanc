<!-- GENERATED FILE — do not edit by hand. -->
<!-- Regenerate with: python3 scripts/generate-proof-recipes.py --write -->

# Blanc proof recipes

Generated from scripts/proof-recipes.toml; do not edit by hand.

Consult these recipes before beginning a manual multi-step walk or inversion.
A suggestion is guidance, not a proof that its recipe applies at a particular goal.

## `runcompiled-construction`

- Status: `active`
- Triggers: `goal-head:Func.RunCompiled`, `goal-head:Func.RunCompiledTo`, `goal-head:Func.ExecTo`, `goal-head:Func.ExecWitness`
- Preferred path: Use `func_run` and its registered opcode arms. Before walking a large concrete body, apply the term-size breaker: the pathological case is a walk whose intermediate term carries the whole concrete remaining program, memory or value, and its signature is a `maxRecDepth`/`maxHeartbeats` ceiling over a multi-`MSTORE` staging run. Factor such a walk into named sub-components, abstract each over the memory or value it threads — a carrier structure over a variable, as `ConstructorPatchInvariant` does in `Blanc/LidoCircuitBreakerDeploymentTrace.lean` — and instantiate the concrete facts through named top-level lemmas, so one layer over a variable stays small instead of composing multiplicatively. Build each certificate separately and abstract only those that cross the breaker; the abstraction is not free and a short bounded walk does not need it. For residual-cost attribution, opt in with the default-off `Blanc.Forward.discharge` trace and aggregate it with `scripts/read-discharge-trace.py` before changing a fallback.
- Boundary: This constructs a compiled walk; it does not invert an existing run, replace an already completed continuation with a summary, synthesize a parallel path certificate such as `DirectPausePath`, or optimize route data before the proof begins. A three-module inventory found the gas class heterogeneous (1,180 tactic / 90 residual) and every expensive value class heterogeneous, so no shared discharge fold is licensed. `LidoCircuitBreakerAttainment` instead measured repeated underconstrained `SourceStep` constructors and its one-path typed-helper pilot reduced 10.321 s to 5.971 s; that result does not license other route retrofits. Wave 4 found that exact proof-copy deletion moved `PauseWorldRunKit` only -1.1%, while a body-from-kernel summary moved `UnregisterRegistration` 38.482 to 21.610 s but required a new recursion ceiling and was reverted. Moving the same helper into `RegistrySubstrate` made that row 35.288 s and the gate red, so the cross-module extension is also closed. Those Wave 4 verdicts close two specific routes — a body-from-kernel summary and cross-module helper placement — and do not close the sub-component abstraction route in the preferred path. That route was measured separately on the 2026-08-23 deployment walk: a three-op prefix went from a 14.5 GiB store wall to a 0.8 s build, and the constructor body from a 15.5-minute hard stop with 12.6 GiB swap to a 737 ms compile. Those are whole-artifact build times recorded in that goal working log, not `check-elab.sh` rows, and no controlled measurement isolates the separate `DeploymentProof` privacy facade effect. The 2026-08-25 retrofit then dispositioned every named backport site. `pause_stageArgs_runCompiled` gained a local memory carrier: its target profiler entry fell from 29.898 s below the 2 s reporting threshold and its sequential owner row moved 47.842 to 31.984 s. A local Replacement carrier shared the guard-prefix composition over the existing staging suffix of the two replacement-registration body walks: their target entries fell from 28.371 and 41.545 s below 2 s and their owner row moved 30.441 to 2.326 s. All six associated recursion/heartbeat scopes disappeared. Cure 2 also ported the same leafwise construction route to the fresh-nonzero and absent-zero registration bodies: their owner rows moved 17.331 to 4.077 s and 15.033 to 3.190 s, and their remaining raised recursion/heartbeat scopes were removed. `registerPauser_stageArgs_runCompiled` retained its original concrete proof: a four-method carrier improved isolated attribution from 15.638 to 10.531 s but regressed the authoritative three-owner closure from Registry/Pause/Replacement 23.655/47.842/30.441 s to 37.989/67.316/53.222 s, so it was reverted. This is a measured non-candidate, not evidence that the technique is invalid; judge the owning closure, not a target-only profile. The 2026-08-21 `already_shared_cps` and `timing_refuted` screening rows answered whether these families could share a common helper, not whether the walked prefix carried an oversized concrete term. `ConstructorPatchInvariant`, `PauseStageMemory`, the Replacement guard-prefix certificates, `freshRegisterPauserBody_fromStage_runCompiled`, and `absentZeroRegisterPauserBody_fromStage_runCompiled` are the current local carrier/leaf-composition examples. `UnregisterRegistration` already contains an earlier hand-built equivalent, and an audit found no compelling WETH10 target. Cure 3 then executed that permitted local route on `pause_body_runCompiled`: eight private guard-prefix helpers reduced the fresh sequential owner row from 39.336 s to 11.819 s and its five-module owning closure from 79.790 s to 53.192 s, with no comparable failing `assumption` inside the factored helpers. The heartbeat scope was deleted after two clean default-heartbeat elaborations, and deterministic recursion-depth bisection right-sized the remaining command scope from 32768 to 1150 (1149 red, 1150 green). Cure 4's separate cold-entry case selected the narrow private `removeTarget_holeStorePrefix_runCompiled` boundary after four viable shapes; `PauseWorldRunKit` moved from 23.010 to 14.716 seconds. Reuse that narrow boundary only when the same accumulated cold-entry prefix recurs in a measured owner, before considering a broader continuation abstraction.
- Owner module: [Blanc/Forward.lean](../Blanc/Forward.lean)
- Canonical example: [Blanc/Weth10Redeemable.lean](../Blanc/Weth10Redeemable.lean) — `withdrawTo_progExecSat`
- Registered symbols: `tactic:func_run`, `declaration:Func.RunCompiled`, `declaration:Func.RunCompiledTo`, `declaration:Func.ExecTo`, `declaration:Func.ExecWitness`
- Review: `proof-infrastructure` on `2026-08-25`

## `linear-dispatch-selection`

- Status: `active`
- Triggers: `goal-shape:linear-dispatch-selection`
- Preferred path: For an existing `Func.RunCompiledTo` walk rooted at `Blanc.linearDispatchWith`, apply `dispatchBodyWitness_of_runCompiledTo` after supplying selector uniqueness, the selected entry, and the initial `selector :: tail` stack. The result is the exact selected-body walk plus stack removal and `DispatchFramePreserved`; compose the public frame facts with `Devm.DispatchFramePreserved.trans` and the push/pop/diff-burn adapters.
- Boundary: The neutral theorem discharges only the dispatcher opcode inversions. It does not know a contract's selector census, calldata ABI, role storage, auxiliary rebasing, or selected-body semantics.
- Owner module: [Blanc/LinearDispatchCorrectness.lean](../Blanc/LinearDispatchCorrectness.lean)
- Canonical example: [Blanc/LinearDispatchCorrectness.lean](../Blanc/LinearDispatchCorrectness.lean) — `dispatchBodyWitness_of_runCompiledTo`
- Registered symbols: `module:Blanc/LinearDispatch.lean`, `module:Blanc/LinearDispatchCorrectness.lean`, `declaration:Blanc.linearDispatchWith`, `declaration:Blanc.selectorUnique`, `declaration:Blanc.Devm.DispatchFramePreserved`, `declaration:Blanc.Devm.DispatchFramePreserved.trans`, `declaration:Blanc.dispatchFrame_of_pushBurn`, `declaration:Blanc.dispatchFrame_of_popBurnBy`, `declaration:Blanc.dispatchFrame_of_diffBurn`, `declaration:Blanc.DispatchBodyWitness`, `declaration:Blanc.dispatchBodyWitness_of_runCompiledTo`
- Review: `proof-infrastructure` on `2026-08-29`

## `line-run-split`

- Status: `active`
- Triggers: `implication-premise:Line.Run`
- Preferred path: Use `line_execute` or `line_execute_with`; revert a named run premise first when needed.
- Boundary: The tactic performs one split and does not automatically transport an arbitrary set of observations.
- Owner module: [Blanc/CommonProofs.lean](../Blanc/CommonProofs.lean)
- Canonical example: [Blanc/Conserved.lean](../Blanc/Conserved.lean) — `Fmint.of_prepApprove`
- Registered symbols: `tactic:line_execute`, `tactic:line_execute_with`, `declaration:Line.Run`
- Review: `proof-infrastructure` on `2026-08-20`

## `func-run-prefix-split`

- Status: `active`
- Triggers: `implication-premise:Func.Run`
- Preferred path: Use `func_execute n` or `func_execute_with line` to expose a known prefix.
- Boundary: This targets the older implication-shaped `Func.Run`; it is not `RunCompiled` construction and does not invert an arbitrary named derivation without first reverting it.
- Owner module: [Blanc/Tactics.lean](../Blanc/Tactics.lean)
- Canonical example: [Blanc/Solvent.lean](../Blanc/Solvent.lean) — `withdraw_preserves_solvent`
- Registered symbols: `tactic:func_execute`, `tactic:func_execute_with`, `declaration:Func.Run`
- Review: `proof-infrastructure` on `2026-08-20`

## `stack-prefix-transport`

- Status: `active`
- Triggers: `goal-shape:stack-prefix-line-run`
- Preferred path: Use `line_prefix` or `generalize_line_prefix`, with `show_pref` for concrete prefix goals. For a known MUL, DIV, TIMESTAMP, XOR, or non-address argument-check step, use the corresponding `prefix_of_*` declaration directly when the tactic has no registered arm.
- Boundary: `line_prefix` supports a finite instruction set and refuses instructions without a registered case. The direct `prefix_of_*` lemmas transport only the named stack prefix; combine them with a separate observation invariant when more state must be carried.
- Owner module: [Blanc/Tactics.lean](../Blanc/Tactics.lean)
- Canonical example: [Blanc/Weth10HolderFlowCompiled.lean](../Blanc/Weth10HolderFlowCompiled.lean) — `recognized_of_run_dispatchWith`
- Registered symbols: `tactic:line_prefix`, `tactic:generalize_line_prefix`, `tactic:show_pref`, `declaration:prefix_of_mul`, `declaration:prefix_of_div`, `declaration:prefix_of_timestamp`, `declaration:prefix_of_xor`, `declaration:prefix_of_argCheckNonAddress`
- Review: `proof-infrastructure` on `2026-08-20`

## `state-context-cleanup`

- Status: `active`
- Triggers: `context-shape:intermediate-devm`
- Preferred path: Use `clear_state hState` after transporting every fact that must survive.
- Boundary: This is destructive context cleanup: it removes the state and all local facts that depend on it. The continuation-summary pilot found this trigger to be a false positive after a continuation was already complete; direct reuse of the existing generic summary added two source lines and no measurable elaboration win. Wave 4 supplied a second eligible false positive in the exact-helper reuse experiment: the goal was discharged by an existing `RunCompiled` summary, so clearing state would only destroy usable hypotheses. The trigger deliberately remains the bare more-than-two-`Devm` heuristic because summary availability is semantic, not recoverable from the context count; narrowing by goal head would introduce false negatives in real construction goals. Treat the trigger as a prompt to check for a completed summary first, never as an automatic cleanup command.
- Owner module: [Blanc/Tactics.lean](../Blanc/Tactics.lean)
- Canonical example: [Blanc/Conserved.lean](../Blanc/Conserved.lean) — `Fmint.of_prepApprove`
- Registered symbols: `tactic:clear_state`
- Review: `proof-infrastructure` on `2026-08-21`

## `line-observation-invariance`

- Status: `active`
- Triggers: `goal-head:Line.Inv`, `goal-head:Ninst.Inv`, `goal-head:Rinst.Inv`
- Preferred path: Use `line_inv` through the registered `Ninst.Hinv` and `Rinst.Hinv` instances.
- Boundary: A missing contract-neutral instance belongs in the lowest common upstream layer; contract-specific semantic facts do not.
- Owner module: [Blanc/Tactics.lean](../Blanc/Tactics.lean)
- Canonical example: [Blanc/Weth10HolderFlowCompiled.lean](../Blanc/Weth10HolderFlowCompiled.lean) — `Devm.DispatchSilent.of_pushEq`
- Registered symbols: `tactic:line_inv`, `declaration:Line.Inv`, `declaration:Ninst.Inv`, `declaration:Rinst.Inv`, `declaration:Ninst.Hinv`, `declaration:Rinst.Hinv`
- Review: `proof-infrastructure` on `2026-08-20`

## `function-observation-invariance`

- Status: `active`
- Triggers: `goal-head:Func.Inv`, `goal-head:Linst.Inv`
- Preferred path: For `Func.Inv`, use `func_inv` to assemble the function invariant from registered line and terminal invariants. For a terminal `Linst.Inv`, use the registered instance directly with `exact Linst.Hinv.inv`.
- Boundary: `func_inv` deliberately refuses `Func.call`, whose callee is arbitrary under `Func.Inv`; fix the context or factor through the entry. A missing terminal instance belongs in the lowest common shared module, not in a contract consumer.
- Owner module: [Blanc/Tactics.lean](../Blanc/Tactics.lean)
- Canonical example: [Blanc/Solvent.lean](../Blanc/Solvent.lean) — `approve_preserves_bal`
- Registered symbols: `tactic:func_inv`, `declaration:Func.Inv`, `declaration:Linst.Inv`, `declaration:Linst.Hinv`
- Review: `proof-infrastructure` on `2026-08-20`

## `call-boundary-outcomes`

- Status: `active`
- Triggers: `goal-head:Func.ExecSat`, `goal-head:Prog.ExecSat`, `goal-head:Func.ExecWitness`
- Preferred path: Use the `ForwardCall` module and the live `ExecSat`/`ExecWitness` layer to cross calls or package multiple outcomes.
- Boundary: Do not duplicate the settlement/determinism tail, and do not infer deadness from qualified-name grep alone.
- Owner module: [Blanc/ForwardCall.lean](../Blanc/ForwardCall.lean)
- Canonical example: [Blanc/Weth10Redeemable.lean](../Blanc/Weth10Redeemable.lean) — `withdrawTo_progExecSat`
- Registered symbols: `module:Blanc/ForwardCall.lean`, `declaration:Func.ExecSat`, `declaration:Prog.ExecSat`, `declaration:Func.ExecWitness`, `declaration:Prog.ExecWitness`
- Review: `proof-infrastructure` on `2026-08-20`

## `devm-projection-bridge`

- Status: `active`
- Triggers: `goal-shape:devm-update-projection`
- Preferred path: Rewrite with the matching Jaune update-first projection lemma, named `Devm.<update>_<projection>`, for the column in the goal. Never bridge a concrete effect tower or compiled artifact through `withOutput`, `setMach`, `setMeta`, `setWorld`, or another `with*` update using bare `change`, `show`, `rfl`, or `exact`.
- Boundary: A succeeding concrete `getStor` walk can expose the same projection mechanism after the effect tower has already been built. Cure 4 routed that case through the shared `Devm.withRefundCounter_getStor` and `Devm.addLog_getStor` semantic cuts plus a private cold-store boundary, moving `LidoCircuitBreakerDeploymentTrace` from 62.173 to 17.050 seconds. Reuse the earliest matching semantic projection cut; do not reorder `Meta` fields. This does not reopen `successor-projection-normalization`: that measured refutation attacked `setMach` chains in an owner dominated by unrelated kernel checks. Resource ceilings neither detect nor bound this kernel-side class. The matcher needs an explicit `Devm` update head in the target; when a local definition hides the chain, unfold only that binding and invoke `blanc_suggest` again.
- Owner module: [Blanc/LidoCircuitBreakerDeploymentMessage.lean](../Blanc/LidoCircuitBreakerDeploymentMessage.lean)
- Canonical example: [Blanc/LidoCircuitBreakerDeploymentMessage.lean](../Blanc/LidoCircuitBreakerDeploymentMessage.lean) — `officialConstructorPost_refundCounter`
- Registered symbols: `declaration:LidoCircuitBreaker.officialConstructorPost_refundCounter`
- Review: `proof-infrastructure` on `2026-08-25`

## `bytesize-composition`

- Status: `active`
- Triggers: `goal-shape:compileshape-bytesize`
- Preferred path: Prove one small `decide +kernel` fact per leaf, then derive internal `compileShape.byteSize` facts arithmetically through `dispatchNode_size`-style composition. `dispatchCae9_size` is the canonical example: with its children available, its composition closes in 0.004 s.
- Boundary: The measured law is approximately 2.6 ms per compiled byte of the addressed object; byte-range width predicts nothing because `byteAtByShape` is lazy. Cure 2 applied the existing composition route in `Weth10Deploy`: named size facts replaced repeated closed decisions and moved its owner row from 43.283 to 29.463 s. The narrower `Weth10DeployDomainSlices` packet first had to add its missing child facts and then regressed from 16.628 to 17.734 s, so it was reverted; reopen that family only with a broader child-fact or representation change whose owner row wins. `weth10MainEmit_drop_3950` costs approximately 0.011 s and should remain unchanged.
- Owner module: [Blanc/Weth10Deploy.lean](../Blanc/Weth10Deploy.lean)
- Canonical example: [Blanc/Weth10Deploy.lean](../Blanc/Weth10Deploy.lean) — `dispatchCae9_size`
- Registered symbols: `declaration:Weth10.dispatchCae9_size`
- Review: `proof-infrastructure` on `2026-08-25`

## `successor-projection-normalization`

- Status: `partial`
- Triggers: `goal-shape:successor-projection`
- Preferred path: Use an existing named, oriented, one-layer projection lemma when one already serves the goal; otherwise keep the explicit local normalization.
- Boundary: Do not replace deep state towers with transparent abbreviations or broad unfolding; `RegistrySubstrate` records why that diverges. On the heartbeatAfterCount/Expiry/Interval tower, adding six one-layer projection lemmas and six retrofits regressed module elaboration from 40.075 s to 41.944 s. Wave 3 then found `LidoCircuitBreakerAccess` dominated by 27–28 s kernel checks, not its secondary setMach chains. Wave 4 attributed the Registry tail to `directPauseControl_gas` (defeq/whnf plus kernel checking) and `directPauseControl_run` (kernel checking); all later declarations stayed below 2 s and none of the module's 212 `Devm.setMach_setMach` citations occurs after that obstacle. This does not reopen S3, S1, S2, or a module split.
- Owner module: [Blanc/Forward.lean](../Blanc/Forward.lean)
- Canonical example: [Blanc/Forward.lean](../Blanc/Forward.lean) — `Devm.getStorVal_setMach`
- Registered symbols: `declaration:Devm.getStorVal_setMach`
- Review: `proof-infrastructure` on `2026-08-21`

## `runcompiled-family-compression`

- Status: `partial`
- Triggers: `goal-shape:runcompiled-family-compression`
- Preferred path: When expensive bodies repeat the same post-kernel walk, freeze a committed-row decision rule, factor the body-from-kernel boundary, and preserve the old statements as instantiations. If a one-shot `func_run` needs a local resource ceiling, promote its exact tactic-produced residual states to named theorem boundaries, reducing the chunks as far as needed; compare against the original declarations' limits before rejecting the factorization. Profile the generic, chunks, and instances, run the bare elaboration gate, withhold the generic in an isolated falsifier, and reject any split that materially regresses its owner row or adds a proof-resource ceiling.
- Boundary: G1: deleting 687 exact proof-copy lines moved `PauseWorldRunKit` 23.536 to 23.273 s (-1.1%) and raised `RegistrySubstrate` 17.513 to 26.909 s, so exact source duplication alone is not a timing signal. G2 correction: the earlier rejection was not like-for-like because the original registration bodies already carried `maxRecDepth 16384` and `maxHeartbeats 2400000`. The 24-step generic and a 4+20 same-declaration split failed at default limits, but named two-instruction mask chunks plus named argument, branch, admin, and static-prefix summaries succeeded. Reusing one private body-from-kernel theorem across all four zero-pauser bodies removed eight resource scopes and moved `UnregisterRegistration` 38.482 to 5.318 s (-86.2%); the two-old-last intermediate measured 21.359 s. G3 remains refuted: shared placement for `ReplacementRegistration.oldLastNonzero` made `RegistrySubstrate` 35.288 s (>2x baseline), so cross-module reuse still needs independent ancestor headroom. G4: the Registry tail is sparse and kernel/defeq-owned, not a compression family. G5: `PauseWorldRun` (8.995 s), the WETH accounting pair (25.573 s combined), and the rich/local twin (4.424 s) are maintainability-only; source symmetry does not license a timing retrofit.
- Owner module: [Blanc/LidoCircuitBreakerUnregisterRegistration.lean](../Blanc/LidoCircuitBreakerUnregisterRegistration.lean)
- Canonical example: [Blanc/LidoCircuitBreakerUnregisterRegistration.lean](../Blanc/LidoCircuitBreakerUnregisterRegistration.lean) — `registerPauser_body_foundZeroOldLast_runCompiled`
- Registered symbols: `declaration:Blanc.LidoCircuitBreaker.registerPauser_stageArgs_runCompiled`
- Review: `proof-infrastructure` on `2026-08-21`

## `shared-subject-kernel-decision`

- Status: `active`
- Triggers: `goal-shape:shared-subject-kernel-decision`
- Preferred path: When several kernel-decidable facts inspect the same expensive closed subject, bind that subject once, decide the facts as one tuple or conjunction, and project the results; alternatively prove one normalized equality and derive the views with `congrArg`.
- Boundary: This applies only when normalization of one identical closed subject dominates every fact. It does not license bundling facts about different subjects, and it is not a term-size or definitional-equality cure. In cure 2, six Attainment pins bundled over `runtimePersistentSourceSites officialParams` cost the sum rather than the max and regressed the owner row from 32.134 to 53.652 s; for that family, free-variable aliases and conjunction elaboration defeated the rule. Reopen Attainment only with a shared closed-subject representation that avoids those costs.
- Owner module: [Blanc/LidoCircuitBreakerSites.lean](../Blanc/LidoCircuitBreakerSites.lean)
- Canonical example: [Blanc/LidoCircuitBreakerSites.lean](../Blanc/LidoCircuitBreakerSites.lean) — `runtimeSourceEffectPcs_official`
- Registered symbols: `declaration:Blanc.LidoCircuitBreaker.runtimeSourceEffectPcs_official`
- Review: `proof-infrastructure` on `2026-08-25`

## `selector-separation`

- Status: `active`
- Triggers: `goal-shape:selector-separation`
- Preferred path: Hoist a reviewed literal separation table ahead of repeated consumers and transport its facts directly; the ExecAccounting pilot reduced its module profile from 46.28 s to 17.74 s across 16 retrofits.
- Boundary: Cure 2 completed the module-local retrofit: the remaining 28 name-selector kernel decisions now rewrite through the existing numeral bridges, and the approve straggler uses its hoisted separation certificate. Together those changes moved `Weth10HolderFlowExecAccounting` from 17.056 to 13.067 s at the final checkpoint. This does not establish I3's cross-domain canonical selector list, `Nodup` theorem, extractor, named simp set, or cross-module placement; those are separate designs and no blocking rule may require them. The earlier whitespace-only compaction remains a source-size result with no timing claim. `blanc_suggest` still misses the literal `SelectorWordNoPrimaryFlow` certificate goal, so callers must consult this recipe manually for that shape.
- Owner module: [Blanc/Weth10SelectorFacts.lean](../Blanc/Weth10SelectorFacts.lean)
- Canonical example: [Blanc/Weth10SelectorFacts.lean](../Blanc/Weth10SelectorFacts.lean) — `Weth10.selector_name_ne_approveSelector`
- Registered symbols: `declaration:Weth10.selector_name_ne_approveSelector`
- Advisory anti-patterns: `local-selector-table`
- Review: `proof-infrastructure` on `2026-08-21`

## `fixed-byte-offsets`

- Status: `active`
- Triggers: `goal-shape:fixed-byte-offset`
- Preferred path: Use `Bytes.sliceD_writeAt` for the written window, `Bytes.sliceD_writeAt_before` or `Bytes.sliceD_writeAt_after` for disjoint neighboring windows, and `Bytes.readWord_writeAt_self` or `Bytes.readWord_writeAt_of_disjoint` for word reads. For padded or abstract memory, start from `Mem.Wf` and `Mem.Reads`. Keep compiled-emitter `List.drop` equalities local unless a profile proves that a structural helper moves their kernel cost.
- Boundary: These laws cover byte-array writes and fixed-width word reads. They do not turn arbitrary compiled-emitter `List.drop` identities into a shared API. `LidoCircuitBreakerEnumeration` was dominated by 34–35 s kernel checks unrelated to byte offsets. On `Weth10Deploy`, a two-next/branch helper changed its 41.5–41.7 s proof by only 0.6–1.1%, and a later top-level private tail theorem moved the owner median only from 48.11 to 46.85 s (-2.62%); both pilots were reverted. Reopen that separate emitter route only for a change whose serialized owner median improves by the licensed win rule.
- Owner module: [Blanc/CommonProofs.lean](../Blanc/CommonProofs.lean)
- Canonical example: [Blanc/CommonProofs.lean](../Blanc/CommonProofs.lean) — `Bytes.readWord_writeAt_of_disjoint`
- Registered symbols: `module:Blanc/CommonProofs.lean`, `declaration:Bytes.sliceD_writeAt`, `declaration:Bytes.sliceD_writeAt_before`, `declaration:Bytes.sliceD_writeAt_after`, `declaration:Bytes.readWord_writeAt_self`, `declaration:Bytes.readWord_writeAt_of_disjoint`, `declaration:Mem.Wf`, `declaration:Mem.Reads`
- Review: `proof-infrastructure` on `2026-08-21`

## `frame-root-carrying-execution`

- Status: `active`
- Triggers: `goal-shape:frame-root-carrying`
- Preferred path: Use `rootedRunCompiledTo` to carry a predicate through a compiled walk, discharge childless instructions with `ninstAllChildRoots_of_not_exec` or `NonExecInstruction`, establish spawning children with `ninstAllChildRoots_of_exec_spawn`, and finish a whole program with `Prog.exec_of_rootedRunCompiledTo`.
- Boundary: This API preserves predicates over raw entered-frame roots. It does not apply settlement/commit filtering; use `ExecutionSettlement` and `ExecutionOccurrence` for retained or committed histories.
- Owner module: [Blanc/RootedExecution.lean](../Blanc/RootedExecution.lean)
- Canonical example: [Blanc/RootedExecution.lean](../Blanc/RootedExecution.lean) — `Prog.exec_of_rootedRunCompiledTo`
- Registered symbols: `module:Blanc/RootedExecution.lean`, `declaration:rootedRunCompiledTo`, `declaration:ninstAllChildRoots`, `declaration:ninstAllChildRoots_of_not_exec`, `declaration:ninstAllChildRoots_of_exec_spawn`, `declaration:funcExecFree`, `declaration:rootedRunCompiledTo_of_execFree`, `declaration:Prog.exec_of_rootedRunCompiledTo`, `declaration:NonExecInstruction`
- Review: `proof-infrastructure` on `2026-08-29`

## `message-execution-settlement`

- Status: `active`
- Triggers: `goal-shape:message-execution-settlement`
- Preferred path: Use `MessageExecution.processMessage_eq_settle_exec` for the raw-to-settled bridge, then the clean/revert/halt adapters and canonical `settledRevert` or `settledHalt` machines instead of unfolding message settlement at the contract site. For an already-retained `ProcessMessage`, use `processMessage_clean_rawPost` to recover the successful raw post, `processMessage_entry_facts` for the actual entry frame projections, and the separate `processMessage_entry_stack` / `processMessage_entry_memory` empty-entry projections.
- Boundary: The forward bridge requires entry-state identity and disabled precompiles. The retained-frame inversion exposes storage equality rather than whole-state equality because value transfer may change balances. These facts describe ordinary call-message settlement, not CREATE settlement.
- Owner module: [Blanc/MessageExecution.lean](../Blanc/MessageExecution.lean)
- Canonical example: [Blanc/MessageExecution.lean](../Blanc/MessageExecution.lean) — `MessageExecution.processMessage_eq_settle_exec`
- Registered symbols: `module:Blanc/MessageExecution.lean`, `module:Blanc/MessageExecutionInversion.lean`, `declaration:MessageExecution.processMessage_eq_settle_exec`, `declaration:MessageExecution.processMessage_clean_of_exec`, `declaration:MessageExecution.processMessage_revert_of_exec`, `declaration:MessageExecution.processMessage_halt_of_exec`, `declaration:MessageExecution.processMessage_clean_rawPost`, `declaration:MessageExecution.processMessage_entry_facts`, `declaration:MessageExecution.processMessage_entry_stack`, `declaration:MessageExecution.processMessage_entry_memory`, `declaration:MessageExecution.settledRevert`, `declaration:MessageExecution.settledHalt`, `declaration:Msg.initDevm_stack`, `declaration:Msg.initSevm_data`
- Review: `proof-infrastructure` on `2026-08-29`

## `raw-sstore-free-compiled-path`

- Status: `active`
- Triggers: `goal-shape:raw-sstore-free-compiled-path`
- Preferred path: Build `Func.RunCompiledTo.NoRawSstorePath` over the exact selected compiled derivation, supplying childlessness for every reached external instruction. Use `NoRawSstorePath.of_entrySstoreFree_reachableExecFree` when the executable finite-component checkers prove both local SSTORE freedom and reachable exec freedom; otherwise use `NoRawSstorePath.of_execFree` for an execution-free, locally SSTORE-free body, `NoRawSstorePath.of_prepend_nonexec` for an instruction-only prefix, `NoRawSstorePath.of_revWith` for a symbolic constant-error body, or `NoRawSstorePath.of_emptyRevertGuard` for a selected nonzero guard calling an empty-revert auxiliary. When a failing prefix is checker-safe only with a harmless success continuation, certify that source and use `NoRawSstorePath.replaceStopWith_of_error` to reinstate the production continuation that the exact error path never enters. For a warm fixed-width SHA-256 precompile step, preserve the empty child slot with `Ninst.childlessRunCompiled_statcall_sha256_64_warm_ext`; finish with `Prog.exists_exec_noRawSstore`. When an exact `Exec` already exists, use `Exec.noRawSstore_of_exactMain_entrySstoreFree_reachableExecFree` to combine the two executable entry certificates occurrence-first.
- Boundary: This is raw construction-direction chronology, not rollback reasoning. An empty retained-write list or reverted terminal state does not prove the certificate because an earlier raw SSTORE may have executed and then rolled back. Entered child frames require their own evidence; synchronously resolved childless precompiles may use the explicit done-frame constructor.
- Owner module: [Blanc/ForwardNoRawSstore.lean](../Blanc/ForwardNoRawSstore.lean)
- Canonical example: [Blanc/ForwardNoRawSstore.lean](../Blanc/ForwardNoRawSstore.lean) — `Func.RunCompiledTo.NoRawSstorePath.of_execFree`
- Registered symbols: `module:Blanc/ForwardNoRawSstore.lean`, `declaration:Blanc.Ninst.ChildlessRunCompiled`, `declaration:Blanc.Ninst.ChildlessRunCompiled.toRunCompiled`, `declaration:Blanc.Ninst.childlessRunCompiled_exec_doneFrame`, `declaration:Blanc.Ninst.childlessRunCompiled_statcall_doneFrame`, `declaration:Blanc.Ninst.childlessRunCompiled_statcall_sha256_64_warm_ext`, `declaration:Blanc.emptyRevertGuardCost`, `declaration:Blanc.Func.runCompiledTo_emptyRevertGuard`, `declaration:Blanc.Exec.NoRawSstore`, `declaration:Blanc.Func.RunCompiledTo.NoRawSstorePath`, `declaration:Blanc.Func.RunCompiledTo.NoRawSstorePath.of_execFree`, `declaration:Blanc.Func.RunCompiledTo.NoRawSstorePath.of_revWith`, `declaration:Blanc.Func.RunCompiledTo.NoRawSstorePath.of_emptyRevertGuard`, `declaration:Blanc.Func.RunCompiledTo.NoRawSstorePath.of_prepend_nonexec`, `declaration:Blanc.Func.RunCompiledTo.NoRawSstorePath.of_entrySstoreFree_reachableExecFree`, `declaration:Blanc.Func.replaceStopWith`, `declaration:Blanc.Func.RunCompiledTo.NoRawSstorePath.replaceStopWith_of_error`, `declaration:Blanc.Prog.exists_exec_noRawSstore`, `declaration:Blanc.Exec.noRawSstore_of_exactMain_entrySstoreFree_reachableExecFree`, `declaration:Blanc.Exec.NoRawSstore.no_successfulSstoreOccurrence`, `declaration:Blanc.Exec.NoRawSstore.retainedStorageWrites_eq_nil`
- Review: `proof-infrastructure` on `2026-08-30`

## `retained-write-noninterference`

- Status: `active`
- Triggers: `goal-shape:retained-write-noninterference`
- Preferred path: For `Exec.NoRetainedWriteTo`, split first on `Execution.commits out = true`. Close the rollback arm with `Exec.noRetainedWriteTo_of_not_commits`; on a committing exact-main invocation use `Exec.noRetainedWriteTo_of_exactMain_reachableExecFree` when the selected entry and its finite internal-call component pass `Prog.reachableExecFree`. For a dispatcher-selected non-main entry, route an actual `SourceCursor` through `Toward.linearDispatchWith_selectedBody`, discharge same-frame exec absence with `SourceCursor.noExec_of_reachableExecFree`, and finish with `Exec.noRetainedWriteTo_of_no_sameFrame_execAt`. Whole-program source-childlessness and entered-frame owner separation remain the other committing routes.
- Boundary: The noncommitting theorem proves retained-write absence by rollback, not raw instruction absence. `Prog.reachableExecFree` checks both arms and a finite lookup-resolved call-closed source component, but says nothing about unselected entries, child outcomes, commitment, gas, or liveness. The exact-main endpoint applies only to `program.main`; a selected dispatcher body needs the explicit actual-route cursor bridge. Do not infer childlessness merely from a static call flag.
- Owner module: [Blanc/ExecutionNoninterference.lean](../Blanc/ExecutionNoninterference.lean)
- Canonical example: [Blanc/ExecutionNoninterference.lean](../Blanc/ExecutionNoninterference.lean) — `Exec.noRetainedWriteTo_of_not_commits`
- Registered symbols: `module:Blanc/ExecutionNoninterference.lean`, `declaration:Exec.NoRetainedWriteTo`, `declaration:Exec.noRetainedWriteTo_of_not_commits`, `declaration:Exec.noRetainedWriteTo_of_no_execOccurrence`, `declaration:Exec.noRetainedWriteTo_of_sourceSites_no_exec`, `declaration:Exec.noRetainedWriteTo_of_frame_owners_ne`, `module:Blanc/ReachableExecFree.lean`, `declaration:Prog.reachableExecFree`, `declaration:Prog.reachableExecFree_iff`, `declaration:Exec.Deriv.SourceCursor.Toward.linearDispatchWith_selectedBody`, `declaration:Exec.Deriv.SourceCursor.noExec_of_reachableExecFree`, `declaration:Exec.noRetainedWriteTo_of_no_sameFrame_execAt`, `declaration:Exec.noRetainedWriteTo_of_exactMain_reachableExecFree`
- Review: `proof-infrastructure` on `2026-08-30`

## `devm-common-update-laws`

- Status: `active`
- Triggers: `goal-shape:devm-common-update-law`
- Preferred path: Before proving a record projection by `rfl`, search the public `Devm` laws in `CommonProofs`: memory writes, accessed-storage/setMach cancellation, storage read-after-write, and the reusable RETURN/SSTORE post projection cuts are named there. Jaune also supplies update-first projection laws such as `Devm.memWrite_gasLeft` and `Devm.setMach_accessedStorageKeys`.
- Boundary: Use the smallest abstract-base law that matches the goal. Do not unfold a concrete effect tower merely because these laws themselves are definitionally simple.
- Owner module: [Blanc/CommonProofs.lean](../Blanc/CommonProofs.lean)
- Canonical example: [Blanc/CommonProofs.lean](../Blanc/CommonProofs.lean) — `Devm.addAccessedStorageKey_setMach_setMach`
- Registered symbols: `module:Blanc/CommonProofs.lean`, `declaration:Devm.memWrite_memory`, `declaration:Devm.memWrite_stack`, `declaration:Devm.addAccessedStorageKey_setMach_setMach`, `declaration:Devm.getStorVal_setStorVal_self`, `declaration:Devm.retPost_getStorVal`, `declaration:Devm.sstoreBase_state`
- Review: `proof-infrastructure` on `2026-08-29`

## `compiled-terminal-at-zero`

- Status: `active`
- Triggers: `goal-shape:terminal-return-revert`
- Preferred path: For an offset-zero 32-byte RETURN or empty REVERT, use `Func.runCompiledTo_ret_word_at_zero` or `Func.runCompiledTo_rev_empty_at_zero`; use the more general `Func.runCompiledTo_ret_word` and `Func.runCompiledTo_rev` only when the offset, size, stack tail, or payload differs.
- Boundary: These are construction lemmas for two common terminal shapes, not inversion theorems and not a replacement for the general terminal APIs.
- Owner module: [Blanc/ExecutionTerminal.lean](../Blanc/ExecutionTerminal.lean)
- Canonical example: [Blanc/ExecutionTerminal.lean](../Blanc/ExecutionTerminal.lean) — `Func.runCompiledTo_ret_word_at_zero`
- Registered symbols: `module:Blanc/ExecutionTerminal.lean`, `declaration:Func.runCompiledTo_ret_word_at_zero`, `declaration:Func.runCompiledTo_rev_empty_at_zero`
- Review: `proof-infrastructure` on `2026-08-29`

## `full-length-slice`

- Status: `active`
- Triggers: `goal-shape:full-length-slice`
- Preferred path: When a padded `sliceD` begins at zero and its requested width is the source length, rewrite with `Bytes.sliceD_zero_length` instead of reproving the take/drop normalization locally.
- Boundary: The theorem needs exact equality between source length and requested width. It does not characterize nonzero offsets or shorter/longer windows.
- Owner module: [Blanc/CommonProofs.lean](../Blanc/CommonProofs.lean)
- Canonical example: [Blanc/CommonProofs.lean](../Blanc/CommonProofs.lean) — `Bytes.sliceD_zero_length`
- Registered symbols: `module:Blanc/CommonProofs.lean`, `declaration:Bytes.sliceD_zero_length`
- Review: `proof-infrastructure` on `2026-08-29`

## `retained-wrapper-trace`

- Status: `active`
- Triggers: `goal-shape:retained-wrapper-trace`
- Preferred path: Choose the carrier at the wrapper boundary you actually have, then use its matching `exists_*Trace` theorem to retain Jaune's deterministic recursive witness. Start with `RetainedXlot` for a filled execution slot; use `MessageCallTrace`, `TransactionTrace`, `AppliedBodyTrace`, or the configured block/history carriers instead of reconstructing a trace from only the terminal state.
- Boundary: These carriers remember execution and wrapper structure but assign no contract-specific meaning to effects. Use the `Execution*Effects` modules for `ContractSpec` transport, `ExecutionPath` for stable call-tree locations, and the `Execution*StateTrace` modules for ordered world-state replay.
- Owner module: [Blanc/ExecutionTrace.lean](../Blanc/ExecutionTrace.lean)
- Canonical example: [Blanc/ExecutionTrace.lean](../Blanc/ExecutionTrace.lean) — `ExecutionTrace.exists_messageCallTrace`
- Registered symbols: `module:Blanc/ExecutionTrace.lean`, `module:Blanc/ExecutionHistory.lean`, `declaration:ExecutionTrace.RetainedXlot`, `declaration:ExecutionTrace.exists_retainedXlot_of_filled`, `declaration:ExecutionTrace.ProcessMessageTrace`, `declaration:ExecutionTrace.exists_processMessageTrace`, `declaration:ExecutionTrace.ProcessCreateMessageTrace`, `declaration:ExecutionTrace.exists_processCreateMessageTrace`, `declaration:ExecutionTrace.MessageCallTrace`, `declaration:ExecutionTrace.exists_messageCallTrace`, `declaration:ExecutionTrace.TransactionTrace`, `declaration:ExecutionTrace.exists_transactionTrace`, `declaration:ExecutionTrace.ApplyTransactionsTrace`, `declaration:ExecutionTrace.exists_applyTransactionsTrace`, `declaration:ExecutionTrace.SystemMessageTrace`, `declaration:ExecutionTrace.exists_systemMessageTrace`, `declaration:ExecutionTrace.RequestsTrace`, `declaration:ExecutionTrace.exists_requestsTrace`, `declaration:ExecutionTrace.AppliedBodyTrace`, `declaration:ExecutionTrace.exists_appliedBodyTrace`, `declaration:ExecutionTrace.ConfiguredBlockTrace`, `declaration:ExecutionTrace.exists_configuredBlockTrace_of_transition`, `declaration:ExecutionTrace.ConfiguredHistoryTrace`, `declaration:ExecutionTrace.exists_configuredHistoryTrace_of_reachUsing`
- Review: `proof-infrastructure` on `2026-08-30`

## `retained-state-replay`

- Status: `active`
- Triggers: `goal-head:StateReplay`
- Preferred path: Build the chronology at the narrowest retained layer and finish with its `stateReplay` theorem. Use `Exec.committedStateReplay` for a recursive execution, then the message, transaction, body, block, or history chronology module to retain wrapper boundaries in their exact execution order. Compose or relabel an existing replay with `StateReplay.append`, `StateReplay.mapOrigin`, and `StateTransition.mapOrigin`.
- Boundary: A `StateReplay` proves endpoint continuity and preserves exact provenance; it does not classify a transition as a contract deposit, withdrawal, or attack step. Apply that interpretation only in the contract-owned layer above the generic chronology.
- Owner module: [Blanc/ExecutionStateTrace.lean](../Blanc/ExecutionStateTrace.lean)
- Canonical example: [Blanc/ExecutionStateTrace.lean](../Blanc/ExecutionStateTrace.lean) — `Exec.committedStateReplay`
- Registered symbols: `module:Blanc/ExecutionStateTrace.lean`, `module:Blanc/ExecutionMessageStateTrace.lean`, `module:Blanc/ExecutionTransactionStateTrace.lean`, `module:Blanc/ExecutionBodyStateTrace.lean`, `module:Blanc/ExecutionHistoryStateTrace.lean`, `declaration:StateTransition`, `declaration:StateReplay`, `declaration:StateReplay.append`, `declaration:StateTransition.mapOrigin`, `declaration:StateReplay.mapOrigin`, `declaration:Exec.committedStateReplay`, `declaration:ExecutionTrace.MessageCallTrace.stateReplay`, `declaration:ExecutionTrace.TransactionStateChronology.stateReplay`, `declaration:ExecutionTrace.AppliedBodyStateChronology.stateReplay`, `declaration:ExecutionTrace.ConfiguredHistoryStateChronology.stateReplay`
- Review: `proof-infrastructure` on `2026-08-30`

## `constant-error-guard`

- Status: `active`
- Triggers: `goal-shape:constant-error-guard`
- Preferred path: Use `Func.runCompiledTo_errorGuard` when a nonzero branch flag tail-calls an auxiliary equal to `Func.revWith reason`. Supply the auxiliary lookup, exact entry-state memory image and alignment, payload bounds, gas expressed through `errorGuardCost`, and stack room; the theorem returns the complete ABI `Error(string)` payload with exact final memory, stack, and gas. When an existential carrier exposes a different state with the same memory size, transport that exact cost with `errorGuardCost_congr_memory_size`.
- Boundary: This proves the branch-and-internal-call walk only. It does not select a contract route, establish which flag is nonzero, authenticate a contract-specific reason/slot table, or turn the local revert into a public endpoint theorem. Keep `errorGuardCost` indexed by the actual entry state, or transport it only across a proved memory-size equality, so memory expansion is not silently weakened.
- Owner module: [Blanc/RevertPayload.lean](../Blanc/RevertPayload.lean)
- Canonical example: [Blanc/RevertPayload.lean](../Blanc/RevertPayload.lean) — `Func.runCompiledTo_errorGuard`
- Registered symbols: `module:Blanc/RevertPayload.lean`, `declaration:Blanc.errorBodyCost`, `declaration:Blanc.errorCallCost`, `declaration:Blanc.errorGuardCost`, `declaration:Blanc.errorGuardCost_congr_memory_size`, `declaration:Blanc.Func.runCompiledTo_revWith`, `declaration:Blanc.Func.runCompiledTo_errorGuard`
- Review: `proof-infrastructure` on `2026-08-30`

## `one-word-source-return`

- Status: `active`
- Triggers: `goal-head:ReturnsWord`
- Preferred path: For the source fragment `mstoreAt 0 +++ returnMemoryRange 0 32`, use `of_storeReturnWord` when a `Mem.Wf`/`Mem.Reads` image is already available, or `returnsWord_of_storeReturn` when no memory side condition is in context. Both prove `ReturnsWord` from the known stack head and preserve code.
- Boundary: This is the source-level one-word ABI observation. For a compiled terminal walk use `Func.runCompiledTo_ret_word_at_zero`; for other offsets, sizes, or payloads use the general return APIs.
- Owner module: [Blanc/Ladder.lean](../Blanc/Ladder.lean)
- Canonical example: [Blanc/Ladder.lean](../Blanc/Ladder.lean) — `returnsWord_of_storeReturn`
- Registered symbols: `module:Blanc/Ladder.lean`, `declaration:ReturnsWord`, `declaration:of_storeReturnWord`, `declaration:returnsWord_of_storeReturn`
- Review: `proof-infrastructure` on `2026-08-30`
