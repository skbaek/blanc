import Blanc.Lift.Usdc.ModernBurnStores
import Blanc.Lift.WalkCutKit

/-! The older modern burn helpers preserve storage while checking subtraction. -/
namespace Blanc.Lift.Usdc.OldBurnNonIncCallees

open Jaune Blanc Blanc.Lift

def inner : ModernVersion → SFunc
  | .v2 => ImplV2.t_4be2_c88
  | .v2_1 => ImplV2_1.t_4576_c86
  | .v2_2 => .ret

def entry : ModernVersion → SFunc
  | .v2 => ImplV2.t_4123_c78
  | .v2_1 => ImplV2_1.t_3d4c_c76
  | .v2_2 => .ret

/-- The messaged subtraction's returning arm preserves its base and memory. -/
theorem inner_ret {version : ModernVersion} (old : version ≠ .v2_2)
    {sevm : Sevm} {b : Devm} {message amount value tag : B256} {S : List B256}
    {M : Mem} {G : Nat} {D : Devm}
    (run : SFunc.Run version.cert.prog sevm
      (St b (message :: amount :: value :: tag :: S) M G) (inner version) (.returned D)) :
    amount.toNat ≤ value.toNat ∧ ∃ G', D = St b ((value - amount) :: S) M G' := by
  cases version with
  | v2_2 => exact (old rfl).elim
  | v2 | v2_1 =>
    have h := run.cut
    simp only [inner] at h
    first | unfold ImplV2.t_4be2_c88 at h | unfold ImplV2_1.t_4576_c86 at h
    obtain ⟨_, h⟩ := ric_dest h
    iterate 7
      obtain ⟨_, step, h⟩ := ric_next h
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
    ibranch h safe
    · first
      | exact (SFunc.RunP.false_of_noExit
          (show NoExitSet ImplV2.cert.prog [5, 93] = true from by decide +kernel)
          (by decide +kernel) (by decide +kernel) h.uncut).elim
      | exact (SFunc.RunP.false_of_noExit
          (show NoExitSet ImplV2_1.cert.prog [6, 91] = true from by decide +kernel)
          (by decide +kernel) (by decide +kernel) h.uncut).elim
    first | unfold ImplV2.t_4c8b_c88 at h | unfold ImplV2_1.t_461f_c86 at h
    obtain ⟨_, h⟩ := ric_dest h
    iterate 6
      obtain ⟨_, step, h⟩ := ric_next h
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
    obtain ⟨_, same⟩ := ric_ret h
    exact ⟨le_of_gt_check safe, _, Outcome.returned.inj (Seg.done.inj same)⟩

/-- The outer helper changes scratch memory but preserves the exact storage base. -/
theorem sub_ret {version : ModernVersion} (old : version ≠ .v2_2)
    {sevm : Sevm} {b : Devm} {amount value tag : B256} {S : List B256}
    {M : Mem} {G : Nat} {D : Devm}
    (run : SFunc.Run version.cert.prog sevm
      (St b (amount :: value :: tag :: S) M G) (entry version) (.returned D)) :
    amount.toNat ≤ value.toNat ∧ ∃ M' G', D = St b ((value - amount) :: S) M' G' := by
  cases version with
  | v2_2 => exact (old rfl).elim
  | v2 | v2_1 =>
    have h := run.cut
    simp only [entry] at h
    first | unfold ImplV2.t_4123_c78 at h | unfold ImplV2_1.t_3d4c_c76 at h
    obtain ⟨_, h⟩ := ric_dest h
    iterate 22
      obtain ⟨_, step, h⟩ := ric_next h
      obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
    first
    | obtain ⟨_, D', callee, h⟩ := ric_callRet
        (show NoHaltSet ImplV2.cert.prog [5, 78, 88, 93] = true from by decide +kernel)
        (by decide) (show ImplV2.cert.prog[88]? = some ImplV2.t_4be2_c88 from rfl) h
      obtain ⟨safe, _, rfl⟩ := inner_ret (version := .v2) (by decide) callee
      unfold ImplV2.t_4165_c78 at h
      obtain ⟨_, h⟩ := ric_dest h
      iterate 5
        obtain ⟨_, step, h⟩ := ric_next h
        obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      obtain ⟨_, same⟩ := ric_ret h
      exact ⟨safe, _, _, Outcome.returned.inj (Seg.done.inj same)⟩
    | obtain ⟨_, D', callee, h⟩ := ric_callRet
        (show NoHaltSet ImplV2_1.cert.prog [6, 76, 86, 91] = true from by decide +kernel)
        (by decide) (show ImplV2_1.cert.prog[86]? = some ImplV2_1.t_4576_c86 from rfl) h
      obtain ⟨safe, _, rfl⟩ := inner_ret (version := .v2_1) (by decide) callee
      unfold ImplV2_1.t_3d8e_c76 at h
      obtain ⟨_, h⟩ := ric_dest h
      iterate 5
        obtain ⟨_, step, h⟩ := ric_next h
        obtain ⟨_, rfl⟩ := ri_stepX_nonstorage (by decide) (by decide) step rfl
      obtain ⟨_, same⟩ := ric_ret h
      exact ⟨safe, _, _, Outcome.returned.inj (Seg.done.inj same)⟩

end Blanc.Lift.Usdc.OldBurnNonIncCallees
