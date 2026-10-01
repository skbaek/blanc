import Blanc.Lift.InvWalkWorld

/-! Invert the actual PUSH4/PUSH2 comparison segments in a lifted dispatcher. -/
namespace Blanc.Lift
open Jaune

theorem ric_cmp_gt {fs : List SFunc} {sevm : Sevm} {b : Devm}
    {S : List B256} {M : Mem} {G : Nat} {C : List Nat} {r : Seg}
    {sel : B256} {c0 c1 c2 c3 d0 d1 : UInt8} {l1 l2}
    {f g : SFunc}
    (run : SFunc.RunCut fs sevm C (St b (sel :: S) M G)
      (.next (.reg (.dup 0)) (.next (.push [c0, c1, c2, c3] l1)
      (.next (.reg .gt) (.next (.push [d0, d1] l2) (.branch f g))))) r) :
    ∃ G', SFunc.RunCut fs sevm C (St b (sel :: S) M G')
      (if B256.gtCheck (Bytes.toB256 [c0, c1, c2, c3]) sel = 0 then f else g) r := by
  obtain ⟨d, hd, h⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_gt hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  rcases ric_branch h with ⟨zero, G', h⟩ | ⟨nonzero, G', h⟩
  · rw [ite_eq_left zero]
    exact ⟨G', h⟩
  · rw [ite_eq_right nonzero]
    exact ⟨G', h⟩

theorem ric_cmp_eq {fs : List SFunc} {sevm : Sevm} {b : Devm}
    {S : List B256} {M : Mem} {G : Nat} {C : List Nat} {r : Seg}
    {sel : B256} {c0 c1 c2 c3 d0 d1 : UInt8} {l1 l2}
    {f g : SFunc} {j : Nat}
    (notCut : j ∉ C) (lookup : fs[j]? = some g)
    (run : SFunc.RunCut fs sevm C (St b (sel :: S) M G)
      (.next (.reg (.dup 0)) (.next (.push [c0, c1, c2, c3] l1)
      (.next (.reg .eq) (.next (.push [d0, d1] l2) (.branchTo f j))))) r) :
    ∃ G', SFunc.RunCut fs sevm C (St b (sel :: S) M G')
      (if B256.eqCheck (Bytes.toB256 [c0, c1, c2, c3]) sel = 0 then f else g) r := by
  obtain ⟨d, hd, h⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_eq hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  rcases ric_branchTo notCut lookup h with ⟨zero, G', h⟩ | ⟨nonzero, G', h⟩
  · rw [ite_eq_left zero]
    exact ⟨G', h⟩
  · rw [ite_eq_right nonzero]
    exact ⟨G', h⟩

end Blanc.Lift
