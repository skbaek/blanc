import Blanc.ConcreteRun
import Blanc.ExecutionKeptFrames

/-!
Continuing prefixes do not add retained frames. This relates the original
`ConcreteRun.Exec.ofStepN` derivation to the kept frames of its supplied tail.
-/

namespace Blanc.ConcreteRun

open Jaune

/-- Extending an actual execution by a continuing prefix keeps exactly the
frames kept by that execution, at any observed address and on any outcome. -/
theorem Exec.keptAt_ofStepN (a : Adr) (n : Nat) {evm evm' : Evm} {out : Execution}
    (h : stepN n evm = some evm') (run : Jaune.Exec evm'.pc evm'.sta evm'.dyna out) :
    Blanc.Exec.keptAt a (Exec.ofStepN n h run) = Blanc.Exec.keptAt a run := by
  induction n generalizing evm with
  | zero =>
      simp only [stepN, Option.some.injEq] at h
      subst evm'
      rfl
  | succ n ih =>
      cases hs : Evm.step evm with
      | cont pc devm =>
          have tail : stepN n ⟨pc, evm.sta, devm⟩ = some evm' := by
            simpa only [stepN, hs] using h
          have same := Blanc.Exec.unique (Exec.ofStepN (n + 1) h run)
            (Jaune.Exec.cont hs (Exec.ofStepN n tail run))
          rw [same, Blanc.Exec.keptAt]
          exact ih tail
      | halt result => simp only [stepN, hs, reduceCtorEq] at h
      | spawn frame resume pc => simp only [stepN, hs, reduceCtorEq] at h

end Blanc.ConcreteRun
