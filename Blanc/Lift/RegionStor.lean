import Blanc.Lift.ReachFirstExec

/-!
# A protected account's storage across a whole run of a store-free region

`SFunc.RunP.stor_of_preIn`: a big-step run (to its halt or its return) of a region tree
(`SFunc.preIn`, the store-free code before an external instruction, `Blanc/Lift/ReachFirstExec.lean`)
keeps a protected account's storage, provided every external step the run takes keeps it.  The
region's own instructions are state-silent, a region external instruction is followed by silent
code only, silent callees keep the world, and a halt keeps a protected account's storage.  The
big-step companion of `Reach.firstExec`, for runs that may halt without reaching an external
instruction.  Contract-neutral.
-/

namespace Blanc.Lift

open Jaune

variable {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List SFunc} {sevm : Sevm}

/-- **Storage across a region run.** -/
theorem SFunc.RunP.stor_of_preIn (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    {ex : Xinst → Bool} {Pre S : List Nat} (hPre : PreSet fs ex Pre S = true)
    (hS : SilentSet fs S = true) {ca : Adr}
    (hX : ∀ {d : Devm} {x : Xinst} {d' : Devm}, P sevm d (.exec x) d' →
      State.Protected d.state ca → d'.state.getStor ca = d.state.getStor ca) :
    ∀ {d : Devm} {f : SFunc} {o : Outcome}, SFunc.RunP P fs sevm d f o →
      f.preIn ex Pre S = true → State.Protected d.state ca →
      (Outcome.devm o).state.getStor ca = d.state.getStor ca := by
  have silent : ∀ {d : Devm} {f : SFunc} {o : Outcome}, SFunc.RunP P fs sevm d f o →
      f.silentIn S = true → (Outcome.devm o).state = d.state := fun run hf => by
    simp only [SFunc.silentIn, Bool.and_eq_true] at hf
    exact SFunc.RunP.state_of_silent hP hS hf.1 hf.2 run
  intro d f o run
  induction run with
  | zero t pop _ ih =>
      intro hf hp
      simp only [SFunc.preIn, Bool.and_eq_true] at hf
      rw [ih hf.1 (pop.state ▸ hp), pop.state]
  | succ t w _ pop _ ih =>
      intro hf hp
      simp only [SFunc.preIn, Bool.and_eq_true] at hf
      rw [ih hf.2 (pop.state ▸ hp), pop.state]
  | toZero t pop _ ih =>
      intro hf hp
      simp only [SFunc.preIn, Bool.and_eq_true] at hf
      rw [ih hf.2 (pop.state ▸ hp), pop.state]
  | toSucc t w _ hk pop _ ih =>
      intro hf hp
      simp only [SFunc.preIn, Bool.and_eq_true, decide_eq_true_eq] at hf
      rw [ih (PreSet.lookup hPre hf.1 hk) (pop.state ▸ hp), pop.state]
  | last h =>
      intro _ hp
      exact Linst.getStor_eq h ca hp
  | @next d₀ d₁ n f' o' step _ ih =>
      intro hf hp
      cases n with
      | exec x =>
          simp only [SFunc.preIn, Bool.and_eq_true] at hf
          rename_i rest
          rw [silent rest hf.2, hX step hp]
      | _ =>
          simp only [SFunc.preIn, Bool.and_eq_true] at hf
          have e := state_of_stateSilent hP hf.1 step
          rw [ih hf.2 (e ▸ hp), e]
  | dest burn _ ih =>
      intro hf hp
      simp only [SFunc.preIn] at hf
      rw [ih hf (burn.state ▸ hp), burn.state]
  | jump t hk pop _ ih =>
      intro hf hp
      simp only [SFunc.preIn, decide_eq_true_eq] at hf
      rw [ih (PreSet.lookup hPre hf hk) (pop.state ▸ hp), pop.state]
  | ret t pop =>
      intro _ _
      exact congrArg (State.getStor · ca) pop.state.symm
  | callHalt t hk pop callee ih =>
      intro hf hp
      simp only [SFunc.preIn, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hf
      rcases hf with ⟨hkS, -⟩ | ⟨hkP, -⟩
      · rw [silent callee (SilentSet.lookup hS hkS hk), pop.state]
      · rw [ih (PreSet.lookup hPre hkP hk) (pop.state ▸ hp), pop.state]
  | @callRet d0 d1 d2 k f' g o' t hk pop callee rest ih₁ ih₂ =>
      intro hf hp
      simp only [SFunc.preIn, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hf
      rcases hf with ⟨hkS, hf'⟩ | ⟨hkP, hf'⟩
      · have e : d2.state = d1.state := silent callee (SilentSet.lookup hS hkS hk)
        rw [ih₂ hf' (by rw [e, ← pop.state]; exact hp), e, pop.state]
      · have h1 : d2.state.getStor ca = d1.state.getStor ca :=
          ih₁ (PreSet.lookup hPre hkP hk) (pop.state ▸ hp)
        rw [silent rest hf', h1, pop.state]
  | pcAt step _ _ ih =>
      intro hf hp
      simp only [SFunc.preIn] at hf
      have e := state_of_stateSilent hP rfl step
      rw [ih hf (e ▸ hp), e]

end Blanc.Lift
