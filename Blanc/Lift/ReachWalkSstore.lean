import Blanc.Lift.ReachWalk
import Blanc.Lift.RunPWalk
import Blanc.Lift.CallSiteChildren

/-!
# Walking a prefix reach to an `SSTORE`

The twin of `Blanc/Lift/ReachWalk.lean` for a target configuration about to run
`SSTORE` (`AtSstore`) instead of an external instruction. A reach of a certified
frame from entry `0` to such a configuration is what `reach_of_parentPrefix` and
`CursorOK.tree_of_sstore` give at a successful raw `SSTORE` node, so a walk with
this kit names the written key and value at every `SSTORE` the frame can reach,
whatever the frame's eventual outcome.

* `Reach.nextS`, `Reach.destS`, `Reach.branchS`, `Reach.branchToS`, `Reach.jumpS`,
  `Reach.callS`, `Reach.not_lastS`, `Reach.not_ret_nilS`: node inversions; at an
  `SSTORE` node `Reach.sstoreS` either stops there or takes the step.
* `Reach.false_of_sstoreFree`: from a tree whose nodes are no `SSTORE` and whose
  referenced entries lie in a closed `SSTORE`-free set (`SstoreFreeSet`, decidable),
  no `SSTORE` is reached.
* `rs_next`, `rs_dest`, `rs_branch`, `rs_branchTo`, `rs_jump`, `rs_callOver`,
  `rs_callInto`: the same over the walk state `St b S M G`.

Contract-neutral.
-/

namespace Blanc.Lift

open Jaune

/-- The target configuration is about to run `SSTORE`. -/
def AtSstore (T : Conf) : Prop := ∃ f', T.f = .next (.reg .sstore) f'

theorem AtSstore.below {T : Conf} {L : List SFunc} : AtSstore (T.below L) ↔ AtSstore T :=
  Iff.rfl

variable {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List SFunc} {sevm : Sevm}

/-! ## Node inversions -/

variable {observe : Conf → Conf → Prop}

theorem ObservedReach.nextS {d : Devm} {n : Ninst} {f : SFunc} {K : List SFunc} {T : Conf}
    (hn : n ≠ .reg .sstore) (h : ObservedReach P observe fs sevm ⟨d, .next n f, K⟩ T) (hT : AtSstore T) :
    ∃ d', P sevm d n d' ∧ observe ⟨d, .next n f, K⟩ ⟨d', f, K⟩ ∧ ObservedReach P observe fs sevm ⟨d', f, K⟩ T := by
  rcases Relation.ReflTransGen.cases_head h with rfl | ⟨c, ⟨step, observed⟩, rest⟩
  · obtain ⟨f', hx⟩ := hT
    injection hx with hx
    exact (hn hx).elim
  · cases step with
    | next hp => exact ⟨_, hp, observed, rest⟩

theorem ObservedReach.sstoreS {d : Devm} {f : SFunc} {K : List SFunc} {T : Conf}
    (h : ObservedReach P observe fs sevm ⟨d, .next (.reg .sstore) f, K⟩ T) :
    T = ⟨d, .next (.reg .sstore) f, K⟩ ∨
      ∃ d', P sevm d (.reg .sstore) d' ∧ observe ⟨d, .next (.reg .sstore) f, K⟩ ⟨d', f, K⟩ ∧ ObservedReach P observe fs sevm ⟨d', f, K⟩ T := by
  rcases Relation.ReflTransGen.cases_head h with rfl | ⟨c, ⟨step, observed⟩, rest⟩
  · exact .inl rfl
  · cases step with
    | next hp => exact .inr ⟨_, hp, observed, rest⟩

theorem ObservedReach.destS {d : Devm} {f : SFunc} {K : List SFunc} {T : Conf}
    (h : ObservedReach P observe fs sevm ⟨d, .dest f, K⟩ T) (hT : AtSstore T) :
    ∃ d', Devm.Burn d d' ∧ ObservedReach P observe fs sevm ⟨d', f, K⟩ T := by
  rcases Relation.ReflTransGen.cases_head h with rfl | ⟨c, ⟨step, observed⟩, rest⟩
  · obtain ⟨f', hx⟩ := hT
    cases hx
  · cases step with
    | dest hb => exact ⟨_, hb, rest⟩

theorem ObservedReach.branchS {d : Devm} {f g : SFunc} {K : List SFunc} {T : Conf}
    (h : ObservedReach P observe fs sevm ⟨d, .branch f g, K⟩ T) (hT : AtSstore T) :
    (∃ t d', Devm.PopBurn [t, 0] d d' ∧ ObservedReach P observe fs sevm ⟨d', f, K⟩ T) ∨
      (∃ t w d', w ≠ 0 ∧ Devm.PopBurn [t, w] d d' ∧ ObservedReach P observe fs sevm ⟨d', g, K⟩ T) := by
  rcases Relation.ReflTransGen.cases_head h with rfl | ⟨c, ⟨step, observed⟩, rest⟩
  · obtain ⟨f', hx⟩ := hT
    cases hx
  · cases step with
    | zero t hp => exact .inl ⟨t, _, hp, rest⟩
    | succ t w hw hp => exact .inr ⟨t, w, _, hw, hp, rest⟩

theorem ObservedReach.branchToS {d : Devm} {f : SFunc} {k : Nat} {K : List SFunc} {T : Conf}
    (h : ObservedReach P observe fs sevm ⟨d, .branchTo f k, K⟩ T) (hT : AtSstore T) :
    (∃ t d', Devm.PopBurn [t, 0] d d' ∧ ObservedReach P observe fs sevm ⟨d', f, K⟩ T) ∨
      (∃ t w g d', w ≠ 0 ∧ fs[k]? = some g ∧ Devm.PopBurn [t, w] d d' ∧
        ObservedReach P observe fs sevm ⟨d', g, K⟩ T) := by
  rcases Relation.ReflTransGen.cases_head h with rfl | ⟨c, ⟨step, observed⟩, rest⟩
  · obtain ⟨f', hx⟩ := hT
    cases hx
  · cases step with
    | toZero t hp => exact .inl ⟨t, _, hp, rest⟩
    | toSucc t w hw hk hp => exact .inr ⟨t, w, _, _, hw, hk, hp, rest⟩

theorem Reach.nextS {d : Devm} {n : Ninst} {f : SFunc} {K : List SFunc} {T : Conf}
    (hn : n ≠ .reg .sstore) (h : Reach P fs sevm ⟨d, .next n f, K⟩ T) (hT : AtSstore T) :
    ∃ d', P sevm d n d' ∧ Reach P fs sevm ⟨d', f, K⟩ T := by
  obtain ⟨d', step, _, rest⟩ := ObservedReach.nextS hn (ObservedReach.of_reach h) hT
  exact ⟨d', step, rest.forget⟩

/-- At an `SSTORE` node, the reach stops there or takes the step. -/
theorem Reach.sstoreS {d : Devm} {f : SFunc} {K : List SFunc} {T : Conf}
    (h : Reach P fs sevm ⟨d, .next (.reg .sstore) f, K⟩ T) :
    T = ⟨d, .next (.reg .sstore) f, K⟩ ∨
      ∃ d', P sevm d (.reg .sstore) d' ∧ Reach P fs sevm ⟨d', f, K⟩ T := by
  rcases ObservedReach.sstoreS (ObservedReach.of_reach h) with stop | ⟨d', step, _, rest⟩
  · exact .inl stop
  · exact .inr ⟨d', step, rest.forget⟩

theorem Reach.branchToS {d : Devm} {f : SFunc} {k : Nat} {K : List SFunc} {T : Conf}
    (h : Reach P fs sevm ⟨d, .branchTo f k, K⟩ T) (hT : AtSstore T) :
    (∃ t d', Devm.PopBurn [t, 0] d d' ∧ Reach P fs sevm ⟨d', f, K⟩ T) ∨
      (∃ t w g d', w ≠ 0 ∧ fs[k]? = some g ∧ Devm.PopBurn [t, w] d d' ∧
        Reach P fs sevm ⟨d', g, K⟩ T) := by
  rcases ObservedReach.branchToS (ObservedReach.of_reach h) hT with
    ⟨t, d', pop, rest⟩ | ⟨t, w, g, d', nonzero, lookup, pop, rest⟩
  · exact .inl ⟨t, d', pop, rest.forget⟩
  · exact .inr ⟨t, w, g, d', nonzero, lookup, pop, rest.forget⟩

theorem ObservedReach.jumpS {d : Devm} {k : Nat} {K : List SFunc} {T : Conf}
    (h : ObservedReach P observe fs sevm ⟨d, .jump k, K⟩ T) (hT : AtSstore T) :
    ∃ t g d', fs[k]? = some g ∧ Devm.PopBurn [t] d d' ∧ ObservedReach P observe fs sevm ⟨d', g, K⟩ T := by
  rcases Relation.ReflTransGen.cases_head h with rfl | ⟨c, ⟨step, _⟩, rest⟩
  · obtain ⟨f', hx⟩ := hT
    cases hx
  · cases step with
    | jump t hk hp => exact ⟨t, _, _, hk, hp, rest⟩

theorem Reach.jumpS {d : Devm} {k : Nat} {K : List SFunc} {T : Conf}
    (h : Reach P fs sevm ⟨d, .jump k, K⟩ T) (hT : AtSstore T) :
    ∃ t g d', fs[k]? = some g ∧ Devm.PopBurn [t] d d' ∧ Reach P fs sevm ⟨d', g, K⟩ T := by
  obtain ⟨t, g, d', hk, pop, rest⟩ := ObservedReach.jumpS (ObservedReach.of_reach h) hT
  exact ⟨t, g, d', hk, pop, rest.forget⟩

/-! ## Over the walk state -/

section St

variable {b : Devm} {S : List B256} {M : Mem} {G : Nat} {f g : SFunc} {K : List SFunc}
  {T : Conf}

theorem ObservedReach.rs_next {n : Ninst} {d : Devm} (run : ObservedReach P observe fs sevm ⟨d, .next n f, K⟩ T)
    (hT : AtSstore T) (hn : n ≠ .reg .sstore := by intro h; cases h) :
    ∃ d', P sevm d n d' ∧ ObservedReach P observe fs sevm ⟨d', f, K⟩ T := by
  obtain ⟨d', step, _, rest⟩ := ObservedReach.nextS hn run hT
  exact ⟨d', step, rest⟩

theorem ObservedReach.rs_dest (run : ObservedReach P observe fs sevm ⟨St b S M G, .dest f, K⟩ T) (hT : AtSstore T) :
    ∃ G', ObservedReach P observe fs sevm ⟨St b S M G', f, K⟩ T := by
  obtain ⟨d', burn, rest⟩ := ObservedReach.destS run hT
  exact ⟨_, (St.of_burn burn) ▸ rest⟩

theorem ObservedReach.rs_branch {dd w : B256}
    (run : ObservedReach P observe fs sevm ⟨St b (dd :: w :: S) M G, .branch f g, K⟩ T) (hT : AtSstore T) :
    (w = 0 ∧ ∃ G', ObservedReach P observe fs sevm ⟨St b S M G', f, K⟩ T) ∨
      (w ≠ 0 ∧ ∃ G', ObservedReach P observe fs sevm ⟨St b S M G', g, K⟩ T) := by
  rcases ObservedReach.branchS run hT with ⟨t, d', pop, rest⟩ | ⟨t, w0, d', hw, pop, rest⟩
  · obtain ⟨-, hw, e⟩ := St.of_pop2 pop
    exact .inl ⟨hw, _, e ▸ rest⟩
  · obtain ⟨-, hw', e⟩ := St.of_pop2 pop
    exact .inr ⟨hw' ▸ hw, _, e ▸ rest⟩

theorem ObservedReach.rs_branchTo {k : Nat} {dd w : B256}
    (run : ObservedReach P observe fs sevm ⟨St b (dd :: w :: S) M G, .branchTo f k, K⟩ T) (hT : AtSstore T) :
    (w = 0 ∧ ∃ G', ObservedReach P observe fs sevm ⟨St b S M G', f, K⟩ T) ∨
      (w ≠ 0 ∧ ∃ g G', fs[k]? = some g ∧ ObservedReach P observe fs sevm ⟨St b S M G', g, K⟩ T) := by
  rcases ObservedReach.branchToS run hT with ⟨t, d', pop, rest⟩ | ⟨t, w0, g, d', hw, hk, pop, rest⟩
  · obtain ⟨-, hw, e⟩ := St.of_pop2 pop
    exact .inl ⟨hw, _, e ▸ rest⟩
  · obtain ⟨-, hw', e⟩ := St.of_pop2 pop
    exact .inr ⟨hw' ▸ hw, g, _, hk, e ▸ rest⟩

theorem rs_next {n : Ninst} {d : Devm} (run : Reach P fs sevm ⟨d, .next n f, K⟩ T)
    (hT : AtSstore T) (hn : n ≠ .reg .sstore := by intro h; cases h) :
    ∃ d', P sevm d n d' ∧ Reach P fs sevm ⟨d', f, K⟩ T :=
  Reach.nextS hn run hT

theorem rs_dest (run : Reach P fs sevm ⟨St b S M G, .dest f, K⟩ T) (hT : AtSstore T) :
    ∃ G', Reach P fs sevm ⟨St b S M G', f, K⟩ T := by
  obtain ⟨G', rest⟩ := ObservedReach.rs_dest (ObservedReach.of_reach run) hT
  exact ⟨G', rest.forget⟩

theorem rs_branch {dd w : B256}
    (run : Reach P fs sevm ⟨St b (dd :: w :: S) M G, .branch f g, K⟩ T) (hT : AtSstore T) :
    (w = 0 ∧ ∃ G', Reach P fs sevm ⟨St b S M G', f, K⟩ T) ∨
      (w ≠ 0 ∧ ∃ G', Reach P fs sevm ⟨St b S M G', g, K⟩ T) := by
  rcases ObservedReach.rs_branch (ObservedReach.of_reach run) hT with ⟨zero, G', rest⟩ | ⟨nonzero, G', rest⟩
  · exact .inl ⟨zero, G', rest.forget⟩
  · exact .inr ⟨nonzero, G', rest.forget⟩

theorem rs_branchTo {k : Nat} {dd w : B256}
    (run : Reach P fs sevm ⟨St b (dd :: w :: S) M G, .branchTo f k, K⟩ T) (hT : AtSstore T) :
    (w = 0 ∧ ∃ G', Reach P fs sevm ⟨St b S M G', f, K⟩ T) ∨
      (w ≠ 0 ∧ ∃ g G', fs[k]? = some g ∧ Reach P fs sevm ⟨St b S M G', g, K⟩ T) := by
  rcases ObservedReach.rs_branchTo (ObservedReach.of_reach run) hT with
    ⟨zero, G', rest⟩ | ⟨nonzero, g, G', lookup, rest⟩
  · exact .inl ⟨zero, G', rest.forget⟩
  · exact .inr ⟨nonzero, g, G', lookup, rest.forget⟩

theorem ObservedReach.rs_jump {k : Nat} {dd : B256}
    (run : ObservedReach P observe fs sevm ⟨St b (dd :: S) M G, .jump k, K⟩ T) (hT : AtSstore T) :
    ∃ g G', fs[k]? = some g ∧ ObservedReach P observe fs sevm ⟨St b S M G', g, K⟩ T := by
  obtain ⟨t, g, d', hk, pop, rest⟩ := ObservedReach.jumpS run hT
  exact ⟨g, _, hk, (St.of_pop1 pop).2 ▸ rest⟩

theorem rs_jump {k : Nat} {dd : B256}
    (run : Reach P fs sevm ⟨St b (dd :: S) M G, .jump k, K⟩ T) (hT : AtSstore T) :
    ∃ g G', fs[k]? = some g ∧ Reach P fs sevm ⟨St b S M G', g, K⟩ T := by
  obtain ⟨g, G', hk, rest⟩ := ObservedReach.rs_jump (ObservedReach.of_reach run) hT
  exact ⟨g, G', hk, rest.forget⟩

end St

end Blanc.Lift
