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
    boundary := "This constructs a compiled walk; it does not invert an existing run, replace an already completed continuation with a summary, synthesize a parallel path certificate such as `DirectPausePath`, or optimize route data before the proof begins. A three-module inventory found the gas class heterogeneous (1,180 tactic / 90 residual) and every expensive value class heterogeneous, so no shared discharge fold is licensed. `LidoCircuitBreakerAttainment` instead measured repeated underconstrained `SourceStep` constructors and its one-path typed-helper pilot reduced 10.321 s to 5.971 s; that result does not license other route retrofits. The Registry profile stopped at a deterministic `rfl`/`whnf` timeout before it could license S3, while both measured registration heads were kernel-checking costs reserved for family compression."
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
    boundary := "This is destructive context cleanup: it removes the state and all local facts that depend on it. The continuation-summary pilot found this trigger to be a false positive after a continuation was already complete; direct reuse of the existing generic summary added two source lines and no measurable elaboration win. Wave 3 touched no new eligible intermediate-`Devm` goal, so one false positive is insufficient evidence for a narrower predicate that would not introduce false negatives; the trigger deliberately remains a bare heuristic."
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
    boundary := "Do not replace deep state towers with transparent abbreviations or broad unfolding; `RegistrySubstrate` records why that diverges. On the heartbeatAfterCount/Expiry/Interval tower, adding six one-layer projection lemmas and six retrofits regressed module elaboration from 40.075 s to 41.944 s. Wave 3 then found `LidoCircuitBreakerAccess` dominated by 27–28 s kernel checks, not its secondary setMach chains, and the Registry profile could not pass its independent `rfl`/`whnf` timeout; neither result reopens S3."
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
