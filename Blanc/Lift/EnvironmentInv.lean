import Blanc.Lift.InvWalk

/-! # Environment pushes inverted over a symbolic walk state -/

namespace Blanc.Lift

open Jaune

theorem ri_number {sevm : Sevm} {b d : Devm} {S : List B256} {M : Mem} {G : Nat}
    (h : Ninst.Run sevm (St b S M G) (.reg .number) d) :
    ∃ G', d = St b (sevm.benvStat.number.toB256 :: S) M G' := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  have hp := Devm.pushBurn_of_pushItem run
  have hs : d.stack = sevm.benvStat.number.toB256 :: S := by
    have := hp.stack
    simpa only [Stack.Push, Split, St.stack, List.cons_append, List.nil_append] using this
  have e := St.of_stackRel hp
  rw [hs] at e
  exact ⟨_, e⟩

theorem ri_timestamp {sevm : Sevm} {b d : Devm} {S : List B256} {M : Mem} {G : Nat}
    (h : Ninst.Run sevm (St b S M G) (.reg .timestamp) d) :
    ∃ G', d = St b (sevm.benvStat.time :: S) M G' := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  have hp := Devm.pushBurn_of_pushItem run
  have hs : d.stack = sevm.benvStat.time :: S := by
    have := hp.stack
    simpa only [Stack.Push, Split, St.stack, List.cons_append, List.nil_append] using this
  have e := St.of_stackRel hp
  rw [hs] at e
  exact ⟨_, e⟩

end Blanc.Lift
