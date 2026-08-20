<!-- GENERATED FILE — do not edit by hand. -->
<!-- Regenerate with: python3 scripts/generate-proof-recipes.py --write -->

# Blanc proof recipes

Generated from scripts/proof-recipes.toml; do not edit by hand.

Consult these recipes before beginning a manual multi-step walk or inversion.
A suggestion is guidance, not a proof that its recipe applies at a particular goal.

## `runcompiled-construction`

- Status: `active`
- Triggers: `goal-head:Func.RunCompiled`, `goal-head:Func.RunCompiledTo`, `goal-head:Func.ExecTo`, `goal-head:Func.ExecWitness`
- Preferred path: Use `func_run` and its registered opcode arms. For residual-cost attribution, opt in with the default-off `Blanc.Forward.discharge` trace before changing a fallback.
- Boundary: This constructs a compiled walk; it does not invert an existing run, replace an already completed continuation with a summary, or synthesize a parallel path certificate such as `DirectPausePath`. The PauseWalk pilot attributed its dominant cost to failed defeq/whnf work in heterogeneous value fallbacks; the residual inventory supports only the homogeneous gas class (83/83 tactic 0, 0.754 s total) as the next bounded specialization candidate.
- Owner module: [Blanc/Forward.lean](../Blanc/Forward.lean)
- Canonical example: [Blanc/Weth10Redeemable.lean](../Blanc/Weth10Redeemable.lean) — `withdrawTo_progExecSat`
- Registered symbols: `tactic:func_run`, `declaration:Func.RunCompiled`, `declaration:Func.RunCompiledTo`, `declaration:Func.ExecTo`, `declaration:Func.ExecWitness`
- Review: `proof-infrastructure` on `2026-08-21`

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
- Boundary: This is destructive context cleanup: it removes the state and all local facts that depend on it. The continuation-summary pilot found this trigger to be a false positive after a continuation was already complete; direct reuse of the existing generic summary added two source lines and no measurable elaboration win.
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

## `successor-projection-normalization`

- Status: `partial`
- Triggers: `goal-shape:successor-projection`
- Preferred path: Use an existing named, oriented, one-layer projection lemma when one already serves the goal; otherwise keep the explicit local normalization.
- Boundary: Do not replace deep state towers with transparent abbreviations or broad unfolding; `RegistrySubstrate` records why that diverges. On the heartbeatAfterCount/Expiry/Interval tower, adding six one-layer projection lemmas and six retrofits regressed module elaboration from 40.075 s to 41.944 s, so that shape does not justify a common normalizer.
- Owner module: [Blanc/Forward.lean](../Blanc/Forward.lean)
- Canonical example: [Blanc/Forward.lean](../Blanc/Forward.lean) — `Devm.getStorVal_setMach`
- Registered symbols: `declaration:Devm.getStorVal_setMach`
- Review: `proof-infrastructure` on `2026-08-21`

## `selector-separation`

- Status: `partial`
- Triggers: `goal-shape:selector-separation`
- Preferred path: Hoist a reviewed literal separation table ahead of repeated consumers and transport its facts directly; the ExecAccounting pilot reduced its module profile from 46.28 s to 17.74 s across 16 retrofits.
- Boundary: The local table win does not establish I3's cross-domain canonical selector list, `Nodup` theorem, extractor, or named simp set; those remain unproved and no blocking rule may require them.
- Owner module: [Blanc/Weth10SelectorFacts.lean](../Blanc/Weth10SelectorFacts.lean)
- Canonical example: [Blanc/Weth10SelectorFacts.lean](../Blanc/Weth10SelectorFacts.lean) — `Weth10.selector_name_ne_approveSelector`
- Registered symbols: `declaration:Weth10.selector_name_ne_approveSelector`
- Advisory anti-patterns: `local-selector-table`
- Review: `proof-infrastructure` on `2026-08-21`

## `fixed-byte-offsets`

- Status: `partial`
- Triggers: `goal-shape:fixed-byte-offset`
- Preferred path: Use the existing `Mem.Wf` and `Mem.Reads` APIs; I8 proposes the missing `writeAt`/`sliceD` extension.
- Boundary: The current memory layer is live, but no gate may demand the proposed extension before it lands.
- Owner module: [Blanc/CommonCore.lean](../Blanc/CommonCore.lean)
- Canonical example: [Blanc/Weth10HolderFlowCompiled.lean](../Blanc/Weth10HolderFlowCompiled.lean) — `exists_acceptedValueCallTrace_same_slot`
- Registered symbols: `declaration:Mem.Wf`, `declaration:Mem.Reads`
- Review: `proof-infrastructure` on `2026-08-20`
