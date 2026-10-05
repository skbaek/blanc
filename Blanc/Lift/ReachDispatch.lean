import Blanc.Lift.ReachWalk
import Blanc.Lift.InvWalkDispatch

/-! Comparison projections for a stateful reach to an actual external instruction.
The original instruction relation, target configuration and continuation stack
are preserved across both branches of a literal PUSH4/PUSH2 comparison. -/
namespace Blanc.Lift
open Jaune

theorem rr_cmp_gt {P : Sevm → Devm → Ninst → Devm → Prop}
    {fs : List SFunc} {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem}
    {G : Nat} {K : List SFunc} {T : Conf} {sel : B256}
    {c0 c1 c2 c3 d0 d1 : UInt8} {l1 l2} {f g : SFunc}
    (step_sound : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    (run : Reach P fs sevm ⟨St b (sel :: S) M G,
      .next (.reg (.dup 0)) (.next (.push [c0, c1, c2, c3] l1)
      (.next (.reg .gt) (.next (.push [d0, d1] l2) (.branch f g)))), K⟩ T)
    (target : AtExec T) :
    ∃ G', Reach P fs sevm ⟨St b (sel :: S) M G',
      if B256.gtCheck (Bytes.toB256 [c0, c1, c2, c3]) sel = 0 then f else g, K⟩ T := by
  obtain ⟨d, hd, h⟩ := rr_next run target
  obtain ⟨_, rfl⟩ := ri_dup rfl (step_sound hd)
  obtain ⟨d, hd, h⟩ := rr_next h target
  obtain ⟨_, rfl⟩ := ri_push (step_sound hd)
  obtain ⟨d, hd, h⟩ := rr_next h target
  obtain ⟨_, rfl⟩ := ri_gt (step_sound hd)
  obtain ⟨d, hd, h⟩ := rr_next h target
  obtain ⟨_, rfl⟩ := ri_push (step_sound hd)
  rcases rr_branch h target with ⟨zero, G', h⟩ | ⟨nonzero, G', h⟩
  · rw [ite_eq_left zero]
    exact ⟨G', h⟩
  · rw [ite_eq_right nonzero]
    exact ⟨G', h⟩

theorem rr_cmp_eq {P : Sevm → Devm → Ninst → Devm → Prop}
    {fs : List SFunc} {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem}
    {G : Nat} {K : List SFunc} {T : Conf} {sel : B256}
    {c0 c1 c2 c3 d0 d1 : UInt8} {l1 l2} {f g : SFunc} {j : Nat}
    (step_sound : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    (lookup : fs[j]? = some g)
    (run : Reach P fs sevm ⟨St b (sel :: S) M G,
      .next (.reg (.dup 0)) (.next (.push [c0, c1, c2, c3] l1)
      (.next (.reg .eq) (.next (.push [d0, d1] l2) (.branchTo f j)))), K⟩ T)
    (target : AtExec T) :
    ∃ G', Reach P fs sevm ⟨St b (sel :: S) M G',
      if B256.eqCheck (Bytes.toB256 [c0, c1, c2, c3]) sel = 0 then f else g, K⟩ T := by
  obtain ⟨d, hd, h⟩ := rr_next run target
  obtain ⟨_, rfl⟩ := ri_dup rfl (step_sound hd)
  obtain ⟨d, hd, h⟩ := rr_next h target
  obtain ⟨_, rfl⟩ := ri_push (step_sound hd)
  obtain ⟨d, hd, h⟩ := rr_next h target
  obtain ⟨_, rfl⟩ := ri_eq (step_sound hd)
  obtain ⟨d, hd, h⟩ := rr_next h target
  obtain ⟨_, rfl⟩ := ri_push (step_sound hd)
  rcases Reach.branchTo h target with ⟨t, d, pop, h⟩ | ⟨t, w, g', d, nonzero, entry, pop, h⟩
  · obtain ⟨_, zero, eq⟩ := St.of_pop2 pop
    rw [ite_eq_left zero]
    exact ⟨_, eq ▸ h⟩
  · rw [lookup] at entry
    cases entry
    obtain ⟨_, word, eq⟩ := St.of_pop2 pop
    rw [ite_eq_right (word ▸ nonzero)]
    exact ⟨_, eq ▸ h⟩

end Blanc.Lift
