import Blanc.Lift.InvWalkWorld
import Blanc.Lift.InvWalkProvenance

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

/-- Invert the actual greater-than comparison while retaining its instruction
relation and the original cut set and final segment. -/
theorem ric_cmp_gtP {P : Sevm → Devm → Ninst → Devm → Prop}
    {fs : List SFunc} {sevm : Sevm} {b : Devm}
    {S : List B256} {M : Mem} {G : Nat} {C : List Nat} {r : Seg}
    {sel : B256} {c0 c1 c2 c3 d0 d1 : UInt8} {l1 l2} {f g : SFunc}
    (step_sound : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    (run : SFunc.RunCutP P fs sevm C (St b (sel :: S) M G)
      (.next (.reg (.dup 0)) (.next (.push [c0, c1, c2, c3] l1)
      (.next (.reg .gt) (.next (.push [d0, d1] l2) (.branch f g))))) r) :
    ∃ G', SFunc.RunCutP P fs sevm C (St b (sel :: S) M G')
      (if B256.gtCheck (Bytes.toB256 [c0, c1, c2, c3]) sel = 0 then f else g) r := by
  obtain ⟨d, hd, h⟩ := ric_nextP run
  obtain ⟨_, rfl⟩ := ri_dup rfl (step_sound hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, rfl⟩ := ri_push (step_sound hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, rfl⟩ := ri_gt (step_sound hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, rfl⟩ := ri_push (step_sound hd)
  rcases ric_branchP h with ⟨zero, G', h⟩ | ⟨nonzero, G', h⟩
  · rw [ite_eq_left zero]
    exact ⟨G', h⟩
  · rw [ite_eq_right nonzero]
    exact ⟨G', h⟩

/-- The equality comparison retains provenance on either actual branch. The
selected entry is resolved by the same lookup and is outside the same cut set. -/
theorem ric_cmp_eqP {P : Sevm → Devm → Ninst → Devm → Prop}
    {fs : List SFunc} {sevm : Sevm} {b : Devm}
    {S : List B256} {M : Mem} {G : Nat} {C : List Nat} {r : Seg}
    {sel : B256} {c0 c1 c2 c3 d0 d1 : UInt8} {l1 l2} {f g : SFunc} {j : Nat}
    (step_sound : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    (notCut : j ∉ C) (lookup : fs[j]? = some g)
    (run : SFunc.RunCutP P fs sevm C (St b (sel :: S) M G)
      (.next (.reg (.dup 0)) (.next (.push [c0, c1, c2, c3] l1)
      (.next (.reg .eq) (.next (.push [d0, d1] l2) (.branchTo f j))))) r) :
    ∃ G', SFunc.RunCutP P fs sevm C (St b (sel :: S) M G')
      (if B256.eqCheck (Bytes.toB256 [c0, c1, c2, c3]) sel = 0 then f else g) r := by
  obtain ⟨d, hd, h⟩ := ric_nextP run
  obtain ⟨_, rfl⟩ := ri_dup rfl (step_sound hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, rfl⟩ := ri_push (step_sound hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, rfl⟩ := ri_eq (step_sound hd)
  obtain ⟨d, hd, h⟩ := ric_nextP h
  obtain ⟨_, rfl⟩ := ri_push (step_sound hd)
  cases h with
  | toZero d0 h k =>
      obtain ⟨-, hw, e⟩ := St.of_pop2 h
      rw [ite_eq_left hw]
      exact ⟨_, e ▸ k⟩
  | toSuccCut _ _ _ hk' _ => exact absurd hk' notCut
  | toSucc d0 w0 hw _ hk' h k =>
      rw [lookup] at hk'
      cases hk'
      obtain ⟨-, hw', e⟩ := St.of_pop2 h
      rw [ite_eq_right (hw' ▸ hw)]
      exact ⟨_, e ▸ k⟩


end Blanc.Lift
