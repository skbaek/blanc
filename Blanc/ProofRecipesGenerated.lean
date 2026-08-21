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
  boundary : String
  deriving Repr, Inhabited

/-- Recipes generated from `scripts/proof-recipes.toml`, in registry order. -/
def recipes : List Recipe := [
  {
    id := "runcompiled-construction"
    status := "active"
    triggers := ["goal-head:Func.RunCompiled", "goal-head:Func.RunCompiledTo", "goal-head:Func.ExecTo", "goal-head:Func.ExecWitness"]
    preferredPath := "Use `func_run` and its registered opcode arms. For residual-cost attribution, opt in with the default-off `Blanc.Forward.discharge` trace and aggregate it with `scripts/read-discharge-trace.py` before changing a fallback."
    boundary := "This constructs a compiled walk; it does not invert an existing run, replace an already completed continuation with a summary, synthesize a parallel path certificate such as `DirectPausePath`, or optimize route data before the proof begins. A three-module inventory found the gas class heterogeneous (1,180 tactic / 90 residual) and every expensive value class heterogeneous, so no shared discharge fold is licensed. `LidoCircuitBreakerAttainment` instead measured repeated underconstrained `SourceStep` constructors and its one-path typed-helper pilot reduced 10.321 s to 5.971 s; that result does not license other route retrofits. Wave 4 found that exact proof-copy deletion moved `PauseWorldRunKit` only -1.1%, while a body-from-kernel summary moved `UnregisterRegistration` 38.482 to 21.610 s but required a new recursion ceiling and was reverted. Moving the same helper into `RegistrySubstrate` made that row 35.288 s and the gate red, so the cross-module extension is also closed."
  },
  {
    id := "line-run-split"
    status := "active"
    triggers := ["implication-premise:Line.Run"]
    preferredPath := "Use `line_execute` or `line_execute_with`; revert a named run premise first when needed."
    boundary := "The tactic performs one split and does not automatically transport an arbitrary set of observations."
  },
  {
    id := "func-run-prefix-split"
    status := "active"
    triggers := ["implication-premise:Func.Run"]
    preferredPath := "Use `func_execute n` or `func_execute_with line` to expose a known prefix."
    boundary := "This targets the older implication-shaped `Func.Run`; it is not `RunCompiled` construction and does not invert an arbitrary named derivation without first reverting it."
  },
  {
    id := "stack-prefix-transport"
    status := "active"
    triggers := ["goal-shape:stack-prefix-line-run"]
    preferredPath := "Use `line_prefix` or `generalize_line_prefix`, with `show_pref` for concrete prefix goals."
    boundary := "`line_prefix` supports a finite instruction set and refuses instructions without a registered case."
  },
  {
    id := "state-context-cleanup"
    status := "active"
    triggers := ["context-shape:intermediate-devm"]
    preferredPath := "Use `clear_state hState` after transporting every fact that must survive."
    boundary := "This is destructive context cleanup: it removes the state and all local facts that depend on it. The continuation-summary pilot found this trigger to be a false positive after a continuation was already complete; direct reuse of the existing generic summary added two source lines and no measurable elaboration win. Wave 4 supplied a second eligible false positive in the exact-helper reuse experiment: the goal was discharged by an existing `RunCompiled` summary, so clearing state would only destroy usable hypotheses. The trigger deliberately remains the bare more-than-two-`Devm` heuristic because summary availability is semantic, not recoverable from the context count; narrowing by goal head would introduce false negatives in real construction goals. Treat the trigger as a prompt to check for a completed summary first, never as an automatic cleanup command."
  },
  {
    id := "line-observation-invariance"
    status := "active"
    triggers := ["goal-head:Line.Inv", "goal-head:Ninst.Inv", "goal-head:Rinst.Inv"]
    preferredPath := "Use `line_inv` through the registered `Ninst.Hinv` and `Rinst.Hinv` instances."
    boundary := "A missing contract-neutral instance belongs in the lowest common upstream layer; contract-specific semantic facts do not."
  },
  {
    id := "function-observation-invariance"
    status := "active"
    triggers := ["goal-head:Func.Inv"]
    preferredPath := "Use `func_inv` to assemble the function invariant from registered line and terminal invariants."
    boundary := "It deliberately refuses `Func.call`, whose callee is arbitrary under `Func.Inv`; fix the context or factor through the entry."
  },
  {
    id := "call-boundary-outcomes"
    status := "active"
    triggers := ["goal-head:Func.ExecSat", "goal-head:Prog.ExecSat", "goal-head:Func.ExecWitness"]
    preferredPath := "Use the `ForwardCall` module and the live `ExecSat`/`ExecWitness` layer to cross calls or package multiple outcomes."
    boundary := "Do not duplicate the settlement/determinism tail, and do not infer deadness from qualified-name grep alone."
  },
  {
    id := "successor-projection-normalization"
    status := "partial"
    triggers := ["goal-shape:successor-projection"]
    preferredPath := "Use an existing named, oriented, one-layer projection lemma when one already serves the goal; otherwise keep the explicit local normalization."
    boundary := "Do not replace deep state towers with transparent abbreviations or broad unfolding; `RegistrySubstrate` records why that diverges. On the heartbeatAfterCount/Expiry/Interval tower, adding six one-layer projection lemmas and six retrofits regressed module elaboration from 40.075 s to 41.944 s. Wave 3 then found `LidoCircuitBreakerAccess` dominated by 27–28 s kernel checks, not its secondary setMach chains. Wave 4 attributed the Registry tail to `directPauseControl_gas` (defeq/whnf plus kernel checking) and `directPauseControl_run` (kernel checking); all later declarations stayed below 2 s and none of the module's 212 `Devm.setMach_setMach` citations occurs after that obstacle. This does not reopen S3, S1, S2, or a module split."
  },
  {
    id := "runcompiled-family-compression"
    status := "partial"
    triggers := ["goal-shape:runcompiled-family-compression"]
    preferredPath := "When expensive bodies repeat the same post-kernel walk, freeze a committed-row decision rule, factor the body-from-kernel boundary, and preserve the old statements as instantiations. If a one-shot `func_run` needs a local resource ceiling, promote its exact tactic-produced residual states to named theorem boundaries, reducing the chunks as far as needed; compare against the original declarations' limits before rejecting the factorization. Profile the generic, chunks, and instances, run the bare elaboration gate, withhold the generic in an isolated falsifier, and reject any split that materially regresses its owner row or adds a proof-resource ceiling."
    boundary := "G1: deleting 687 exact proof-copy lines moved `PauseWorldRunKit` 23.536 to 23.273 s (-1.1%) and raised `RegistrySubstrate` 17.513 to 26.909 s, so exact source duplication alone is not a timing signal. G2 correction: the earlier rejection was not like-for-like because the original registration bodies already carried `maxRecDepth 16384` and `maxHeartbeats 2400000`. The 24-step generic and a 4+20 same-declaration split failed at default limits, but named two-instruction mask chunks plus named argument, branch, admin, and static-prefix summaries succeeded. Reusing one private body-from-kernel theorem across all four zero-pauser bodies removed eight resource scopes and moved `UnregisterRegistration` 38.482 to 5.318 s (-86.2%); the two-old-last intermediate measured 21.359 s. G3 remains refuted: shared placement for `ReplacementRegistration.oldLastNonzero` made `RegistrySubstrate` 35.288 s (>2x baseline), so cross-module reuse still needs independent ancestor headroom. G4: the Registry tail is sparse and kernel/defeq-owned, not a compression family. G5: `PauseWorldRun` (8.995 s), the WETH accounting pair (25.573 s combined), and the rich/local twin (4.424 s) are maintainability-only; source symmetry does not license a timing retrofit."
  },
  {
    id := "selector-separation"
    status := "partial"
    triggers := ["goal-shape:selector-separation"]
    preferredPath := "Hoist a reviewed literal separation table ahead of repeated consumers and transport its facts directly; the ExecAccounting pilot reduced its module profile from 46.28 s to 17.74 s across 16 retrofits."
    boundary := "The local table win does not establish I3's cross-domain canonical selector list, `Nodup` theorem, extractor, or named simp set; those remain unproved and no blocking rule may require them. Its 30-line module-size growth is the measured deliverable and remains assigned to the later WETH accounting family-compression/module-split goal; wave 3 refreshes the stale 65.650 s elaboration baseline through the gate's deliberate rebase procedure."
  },
  {
    id := "fixed-byte-offsets"
    status := "partial"
    triggers := ["goal-shape:fixed-byte-offset"]
    preferredPath := "Use the existing `Mem.Wf` and `Mem.Reads` APIs; I8 proposes the missing `writeAt`/`sliceD` extension. Keep compiled-emitter `List.drop` equalities local unless a profile proves that a structural helper moves their kernel cost."
    boundary := "The current memory layer is live, but no gate may demand the proposed extension before it lands. `LidoCircuitBreakerEnumeration` was dominated by 34–35 s kernel checks unrelated to byte offsets. On `Weth10Deploy`, `blanc_suggest` correctly missed the emitter-drop goal, and a two-next/branch helper changed its 41.5–41.7 s proof by only 0.6–1.1% while the same 41.25 s kernel check remained; the pilot was reverted and does not broaden this trigger."
  },
]

end Blanc.ProofRecipes
