import Blanc.ExecutionHistoryInSystemEnvironment
import Blanc.ExecutionHistoryInAppend
import Blanc.ExecutionHistoryInSystemOpenings

/-! Actual schedule intervals and opening-code producers for historical seams.
Fork indices here compare selections of the same validated schedule; they do not
replace rule facts inside execution. No installed code is required before Cancun. -/

namespace Blanc.ExecutionTrace

open Jaune

/-- Pre-Cancun blocks have no opening installation obligations. -/
theorem ConfiguredHistoryTraceIn.systemCodeAtOpenings_of_preCancun
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTraceIn HistFork cfg checkpoint future)
    (forks : trace.ForksSatisfy PreCancun) : trace.SystemCodeAtOpenings := by
  induction trace with
  | refl => trivial
  | step prior block ih =>
      exact ⟨ih forks.1, SystemCodeInstalledAt.of_preCancun _ block.forkIn forks.2⟩

/-- Opening installation producers compose along the same retained append. -/
theorem ConfiguredHistoryTraceIn.SystemCodeAtOpenings_append
    {F : Fork → Prop} {cfg : ChainConfig} {a b c : BlockChain}
    (left : ConfiguredHistoryTraceIn F cfg a b) (right : ConfiguredHistoryTraceIn F cfg b c) :
    (left.append right).SystemCodeAtOpenings ↔
      left.SystemCodeAtOpenings ∧ right.SystemCodeAtOpenings := by
  induction right with
  | refl => simp only [ConfiguredHistoryTraceIn.append, SystemCodeAtOpenings, and_true]
  | step prior block ih =>
      simp only [ConfiguredHistoryTraceIn.append, SystemCodeAtOpenings, ih, and_assoc]

/-- Fork properties split across the same retained append. -/
theorem ConfiguredHistoryTraceIn.ForksSatisfy_append
    {F : Fork → Prop} {cfg : ChainConfig} {a b c : BlockChain} (G : Fork → Prop)
    (left : ConfiguredHistoryTraceIn F cfg a b) (right : ConfiguredHistoryTraceIn F cfg b c) :
    (left.append right).ForksSatisfy G ↔ left.ForksSatisfy G ∧ right.ForksSatisfy G := by
  induction right with
  | refl => simp only [ConfiguredHistoryTraceIn.append, ForksSatisfy, and_true]
  | step prior block ih =>
      simp only [ConfiguredHistoryTraceIn.append, ForksSatisfy, ih, and_assoc]

/-- A pre-Prague spine needs no authority exclusion: the gated form holds outright. -/
theorem ConfiguredHistoryTraceIn.pragueNoAuthorityAt_of_prePrague
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (forks : trace.ForksSatisfy PrePrague) (a : Adr) : trace.PragueNoAuthorityAt a := by
  induction trace with
  | refl => trivial
  | step prior block ih => exact ⟨ih forks.1, fun notPre => (notPre forks.2).elim⟩

end Blanc.ExecutionTrace
