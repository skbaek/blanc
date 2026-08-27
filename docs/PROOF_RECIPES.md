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
- Preferred path: Use `line_prefix` or `generalize_line_prefix`, with `show_pref` for concrete prefix goals.
- Boundary: `line_prefix` supports a finite instruction set and refuses instructions without a registered case.
- Owner module: [Blanc/Tactics.lean](../Blanc/Tactics.lean)
- Canonical example: [Blanc/Weth10HolderFlowCompiled.lean](../Blanc/Weth10HolderFlowCompiled.lean) — `recognized_of_run_dispatchWith`
- Registered symbols: `tactic:line_prefix`, `tactic:generalize_line_prefix`, `tactic:show_pref`
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
- Triggers: `goal-head:Func.Inv`
- Preferred path: Use `func_inv` to assemble the function invariant from registered line and terminal invariants.
- Boundary: It deliberately refuses `Func.call`, whose callee is arbitrary under `Func.Inv`; fix the context or factor through the entry.
- Owner module: [Blanc/Tactics.lean](../Blanc/Tactics.lean)
- Canonical example: [Blanc/Solvent.lean](../Blanc/Solvent.lean) — `approve_preserves_bal`
- Registered symbols: `tactic:func_inv`, `declaration:Func.Inv`
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

- Status: `partial`
- Triggers: `goal-shape:fixed-byte-offset`
- Preferred path: Use the existing `Mem.Wf` and `Mem.Reads` APIs; I8 proposes the missing `writeAt`/`sliceD` extension. Keep compiled-emitter `List.drop` equalities local unless a profile proves that a structural helper moves their kernel cost.
- Boundary: The current memory layer is live, but no gate may demand the proposed extension before it lands. `LidoCircuitBreakerEnumeration` was dominated by 34–35 s kernel checks unrelated to byte offsets. On `Weth10Deploy`, `blanc_suggest` correctly missed the emitter-drop goal, and a two-next/branch helper changed its 41.5–41.7 s proof by only 0.6–1.1% while the same 41.25 s kernel check remained. A later pilot promoted the whole local parameterized tail proof to a top-level private theorem: the owner median moved only from 48.11 to 46.85 s (-2.62%) and the same dominant 46.568 s kernel check remained. Both pilots were exactly reverted, and their profiler-independent owner medians remain the verdicts. Reopen only for a change whose serialized owner median improves by the licensed win rule; persistence of the trailing kernel row is not a mechanism criterion.
- Owner module: [Blanc/CommonCore.lean](../Blanc/CommonCore.lean)
- Canonical example: [Blanc/Weth10HolderFlowCompiled.lean](../Blanc/Weth10HolderFlowCompiled.lean) — `exists_acceptedValueCallTrace_same_slot`
- Registered symbols: `declaration:Mem.Wf`, `declaration:Mem.Reads`
- Review: `proof-infrastructure` on `2026-08-21`
