import Blanc.Lift.Witness
import Blanc.Lift.ExactWalkCallChild

/-! Symbolic observations at an already checked witness halt and original
ordinary-CALL resume. No certificate interpreter is evaluated here. -/

namespace Blanc.Lift.Witness

open Jaune Blanc.Lift

/-- A successful RETURN preserves both accessed sets as well as the world. -/
private theorem return_accKeep {sevm : Sevm} {devm d : Devm}
    (h : Linst.run sevm devm .return_ = .ok d) : AccKeep devm d := by
  simp only [Linst.run] at h
  obtain ⟨⟨i, d1⟩, h1, e1⟩ := Except.bind_eq_ok h
  obtain ⟨⟨n, d2⟩, h2, e2⟩ := Except.bind_eq_ok e1
  obtain ⟨d3, h3, h4⟩ := Except.bind_eq_ok e2
  cases h4
  exact (accKeep_popToNat h1).trans ((accKeep_popToNat h2).trans ((accKeep_chargeGas h3).trans ((accKeep_memRead d3 i n).trans ⟨rfl, rfl, rfl⟩)))

/-- A witness halt preserves the producing configuration's accessed sets.
The configuration is already identified by the existing soundness theorem. -/
private theorem wstep_halted_accKeep {fs : List SFunc} {sevm : Sevm} {c c' : Cfg} {d : Devm}
    (h : wstep fs sevm c = .done (.halted d) c') : AccKeep c'.devm d := by
  rcases c with ⟨devm, f, K, keys, adrs, stor, acs⟩
  cases f with
  | ret =>
      simp only [wstep] at h
      split at h
      · split at h
        · split at h <;> cases h
        · cases h
      · cases h
  | last l =>
      cases l <;> simp only [wstep] at h
      · split at h
        · rename_i post hd
          cases h
          simp only [Linst.run, Except.ok.injEq] at hd
          rw [hd]
          exact ⟨rfl, rfl, rfl⟩
        · cases h
      · split at h
        · rename_i post hd
          cases h
          exact return_accKeep hd
        · cases h
      · split at h
        · rename_i post hd
          simp only [Linst.run] at hd
          obtain ⟨_, _, e1⟩ := Except.bind_eq_ok hd
          obtain ⟨_, _, e2⟩ := Except.bind_eq_ok e1
          obtain ⟨_, _, e3⟩ := Except.bind_eq_ok e2
          cases e3
        · cases h
      · cases h
  | next n g =>
      simp only [wstep] at h
      split at h <;> (try split at h) <;> (try split at h) <;> cases h
  | dest g => simp only [wstep] at h; split at h <;> cases h
  | jump k => simp only [wstep] at h; split at h <;> (try split at h) <;> cases h
  | branch f g => simp only [wstep] at h; split at h <;> (try split at h) <;> cases h
  | branchTo f k =>
      simp only [wstep] at h; split at h <;> (try split at h) <;> (try split at h) <;>
        (try split at h) <;> cases h
  | callNext k f => simp only [wstep] at h; split at h <;> (try split at h) <;> cases h
  | pcAt p g => simp only [wstep] at h; split at h <;> cases h
  | undefined => simp only [wstep, reduceCtorEq] at h

/-- Reuse a checked witness halt to observe the output's actual warm sets and
world, instead of evaluating the concrete witness a second time. -/
theorem wrun_halted_accKeep {fs : List SFunc} {sevm : Sevm} :
    ∀ {n : Nat} {c c' : Cfg} {d : Devm},
      wrun fs sevm n c = .done (.halted d) c' → AccKeep c'.devm d
  | 0, c, c', d, h => by simp only [wrun, reduceCtorEq] at h
  | n + 1, c, c', d, h => by
      simp only [wrun] at h
      split at h
      · exact wrun_halted_accKeep h
      · exact wstep_halted_accKeep h

/-- Resume from an actual suspended parent's access shadows and an already
checked child shadow. Parent storage/account shadows are not reused. -/
theorem agree_callChildPost {parent post : Devm} {child : Cfg}
    {parentKeys : List (Adr × B256)} {parentAdrs : List Adr} {oi os : Nat}
    (keys : ∀ k, k ∈ parent.accessedStorageKeys ↔ k ∈ parentKeys)
    (adrs : ∀ a, a ∈ parent.accessedAddresses ↔ a ∈ parentAdrs)
    (agrees : Agree child) (halted : AccKeep child.devm post) (output : post.output = []) :
    Agree ⟨callChildPost parent post oi os, .undefined, [],
      parentKeys ++ child.keys, parentAdrs ++ child.adrs, child.stor, child.acs⟩ := by
  have union {α : Type} [BEq α] [Hashable α] [LawfulBEq α] [LawfulHashable α]
      (m₁ m₂ : Std.HashSet α) (x : α) : x ∈ m₁.union m₂ ↔ x ∈ m₁ ∨ x ∈ m₂ := by
    simpa only [Std.HashSet.mem_iff_contains, Union.union, Std.HashSet.instUnion] using
      (Std.HashSet.mem_union_iff (m₁ := m₁) (m₂ := m₂) (k := x))
  have cf := callChildPost_facts parent post oi os output
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro k
    rw [cf.2.2.2.2.2.2.2.2.2.2.2.2.1, union,
      halted.2.1, keys k, agrees.1 k]
    exact List.mem_append.symm
  · intro a
    rw [cf.2.2.2.2.2.2.2.2.2.2.2.1, union,
      halted.1, adrs a, agrees.2.1 a]
    exact List.mem_append.symm
  · intro a k
    rw [cf.2.2.2.1, halted.2.2]
    exact agrees.2.2.1 a k
  · intro a
    rw [cf.2.2.2.1, halted.2.2]
    exact agrees.2.2.2 a

end Blanc.Lift.Witness
