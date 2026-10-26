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

/-- A tree with no `SSTORE` node, all of whose entry references lie in `E`. -/
def SFunc.sstoreFreeIn (E : List Nat) (f : SFunc) : Bool :=
  f.nodesSatisfy (fun n _ => n != .reg .sstore) && f.refs.all (· ∈ E)

/-- `E` is closed and `SSTORE`-free: each member's tree is `sstoreFreeIn E`. -/
def SstoreFreeSet (fs : List SFunc) (E : List Nat) : Bool :=
  E.all fun k => match fs[k]? with
    | some g => g.sstoreFreeIn E
    | none => false

variable {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List SFunc} {sevm : Sevm}

theorem SstoreFreeSet.lookup {E : List Nat} (hE : SstoreFreeSet fs E = true) {k : Nat}
    {g : SFunc} (hk : k ∈ E) (hg : fs[k]? = some g) : g.sstoreFreeIn E = true := by
  have h := (List.all_eq_true.mp hE) k hk
  rw [hg] at h
  exact h

private theorem sstoreFree_step {E : List Nat} (hE : SstoreFreeSet fs E = true) {a b : Conf}
    (step : ConfStep P fs sevm a b) (ha : a.f.sstoreFreeIn E = true)
    (hK : ∀ s ∈ a.K, s.sstoreFreeIn E = true) :
    b.f.sstoreFreeIn E = true ∧ ∀ s ∈ b.K, s.sstoreFreeIn E = true := by
  cases step with
  | @next d d' n f K _ =>
      refine ⟨?_, hK⟩
      simp only [SFunc.sstoreFreeIn, SFunc.nodesSatisfy, SFunc.refs, Bool.and_eq_true] at ha ⊢
      exact ⟨ha.1.2, ha.2⟩
  | dest _ =>
      refine ⟨?_, hK⟩
      simpa only [SFunc.sstoreFreeIn, SFunc.nodesSatisfy, SFunc.refs] using ha
  | zero _ _ =>
      refine ⟨?_, hK⟩
      simp only [SFunc.sstoreFreeIn, SFunc.nodesSatisfy, SFunc.refs, List.all_append,
        Bool.and_eq_true] at ha ⊢
      exact ⟨ha.1.1, ha.2.1⟩
  | succ _ _ _ _ =>
      refine ⟨?_, hK⟩
      simp only [SFunc.sstoreFreeIn, SFunc.nodesSatisfy, SFunc.refs, List.all_append,
        Bool.and_eq_true] at ha ⊢
      exact ⟨ha.1.2, ha.2.2⟩
  | toZero _ _ =>
      refine ⟨?_, hK⟩
      simp only [SFunc.sstoreFreeIn, SFunc.nodesSatisfy, SFunc.refs, List.all_cons,
        Bool.and_eq_true] at ha ⊢
      exact ⟨ha.1, ha.2.2⟩
  | @toSucc d d' f g k K _ _ _ hk _ =>
      refine ⟨SstoreFreeSet.lookup hE ?_ hk, hK⟩
      simp only [SFunc.sstoreFreeIn, SFunc.refs, List.all_cons, Bool.and_eq_true,
        decide_eq_true_eq] at ha
      exact ha.2.1
  | @jump d d' g k K _ hk _ =>
      refine ⟨SstoreFreeSet.lookup hE ?_ hk, hK⟩
      simp only [SFunc.sstoreFreeIn, SFunc.refs, List.all_cons, List.all_nil, Bool.and_true,
        Bool.and_eq_true, decide_eq_true_eq] at ha
      exact ha.2
  | @call d d' f g k K _ hk _ =>
      simp only [SFunc.sstoreFreeIn, SFunc.nodesSatisfy, SFunc.refs, List.all_cons,
        Bool.and_eq_true, decide_eq_true_eq] at ha
      refine ⟨SstoreFreeSet.lookup hE ha.2.1 hk, fun s hs => ?_⟩
      rcases List.mem_cons.mp hs with rfl | hs
      · simp only [SFunc.sstoreFreeIn, Bool.and_eq_true]
        exact ⟨ha.1, ha.2.2⟩
      · exact hK s hs
  | ret _ _ => exact ⟨hK _ List.mem_cons_self, fun s hs => hK s (List.mem_cons_of_mem _ hs)⟩
  | pcAt _ _ =>
      refine ⟨?_, hK⟩
      simpa only [SFunc.sstoreFreeIn, SFunc.nodesSatisfy, SFunc.refs] using ha

/-- **No `SSTORE` in an `SSTORE`-free region.** -/
theorem Reach.false_of_sstoreFree {E : List Nat} (hE : SstoreFreeSet fs E = true) {d : Devm}
    {f : SFunc} {K : List SFunc} {T : Conf}
    (h : Reach P fs sevm ⟨d, f, K⟩ T) (hT : AtSstore T) (hf : f.sstoreFreeIn E = true)
    (hK : ∀ s ∈ K, s.sstoreFreeIn E = true) : False := by
  suffices ∀ {a : Conf}, Reach P fs sevm a T → a.f.sstoreFreeIn E = true →
      (∀ s ∈ a.K, s.sstoreFreeIn E = true) → False from this h hf hK
  intro a h ha hK
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
      obtain ⟨f', hx⟩ := hT
      rw [hx] at ha
      simp only [SFunc.sstoreFreeIn, SFunc.nodesSatisfy, bne_self_eq_false, Bool.false_and,
        Bool.false_eq_true] at ha
  | head step _ ih =>
      obtain ⟨hb, hbK⟩ := sstoreFree_step hE step ha hK
      exact ih hb hbK

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

theorem Reach.destS {d : Devm} {f : SFunc} {K : List SFunc} {T : Conf}
    (h : Reach P fs sevm ⟨d, .dest f, K⟩ T) (hT : AtSstore T) :
    ∃ d', Devm.Burn d d' ∧ Reach P fs sevm ⟨d', f, K⟩ T := by
  obtain ⟨d', burn, rest⟩ := ObservedReach.destS (ObservedReach.of_reach h) hT
  exact ⟨d', burn, rest.forget⟩

theorem Reach.branchS {d : Devm} {f g : SFunc} {K : List SFunc} {T : Conf}
    (h : Reach P fs sevm ⟨d, .branch f g, K⟩ T) (hT : AtSstore T) :
    (∃ t d', Devm.PopBurn [t, 0] d d' ∧ Reach P fs sevm ⟨d', f, K⟩ T) ∨
      (∃ t w d', w ≠ 0 ∧ Devm.PopBurn [t, w] d d' ∧ Reach P fs sevm ⟨d', g, K⟩ T) := by
  rcases ObservedReach.branchS (ObservedReach.of_reach h) hT with
    ⟨t, d', pop, rest⟩ | ⟨t, w, d', nonzero, pop, rest⟩
  · exact .inl ⟨t, d', pop, rest.forget⟩
  · exact .inr ⟨t, w, d', nonzero, pop, rest.forget⟩

theorem Reach.branchToS {d : Devm} {f : SFunc} {k : Nat} {K : List SFunc} {T : Conf}
    (h : Reach P fs sevm ⟨d, .branchTo f k, K⟩ T) (hT : AtSstore T) :
    (∃ t d', Devm.PopBurn [t, 0] d d' ∧ Reach P fs sevm ⟨d', f, K⟩ T) ∨
      (∃ t w g d', w ≠ 0 ∧ fs[k]? = some g ∧ Devm.PopBurn [t, w] d d' ∧
        Reach P fs sevm ⟨d', g, K⟩ T) := by
  rcases ObservedReach.branchToS (ObservedReach.of_reach h) hT with
    ⟨t, d', pop, rest⟩ | ⟨t, w, g, d', nonzero, lookup, pop, rest⟩
  · exact .inl ⟨t, d', pop, rest.forget⟩
  · exact .inr ⟨t, w, g, d', nonzero, lookup, pop, rest.forget⟩

theorem Reach.jumpS {d : Devm} {k : Nat} {K : List SFunc} {T : Conf}
    (h : Reach P fs sevm ⟨d, .jump k, K⟩ T) (hT : AtSstore T) :
    ∃ t g d', fs[k]? = some g ∧ Devm.PopBurn [t] d d' ∧ Reach P fs sevm ⟨d', g, K⟩ T := by
  rcases Relation.ReflTransGen.cases_head h with rfl | ⟨c, step, rest⟩
  · obtain ⟨f', hx⟩ := hT
    cases hx
  · cases step with
    | jump t hk hp => exact ⟨t, _, _, hk, hp, rest⟩

theorem Reach.callS {d : Devm} {k : Nat} {f : SFunc} {K : List SFunc} {T : Conf}
    (h : Reach P fs sevm ⟨d, .callNext k f, K⟩ T) (hT : AtSstore T) :
    ∃ t g d', fs[k]? = some g ∧ Devm.PopBurn [t] d d' ∧
      ((∃ T', Reach P fs sevm ⟨d', g, []⟩ T' ∧ T = T'.below (f :: K)) ∨
        ∃ d'', SFunc.RunP P fs sevm d' g (.returned d'') ∧ Reach P fs sevm ⟨d'', f, K⟩ T) := by
  rcases Relation.ReflTransGen.cases_head h with rfl | ⟨c, step, rest⟩
  · obtain ⟨f', hx⟩ := hT
    cases hx
  · cases step with
    | call t hk hp =>
        exact ⟨t, _, _, hk, hp, Reach.split (S := []) rest rfl⟩

theorem Reach.not_lastS {d : Devm} {l : Linst} {K : List SFunc} {T : Conf}
    (h : Reach P fs sevm ⟨d, .last l, K⟩ T) (hT : AtSstore T) : False := by
  rcases Relation.ReflTransGen.cases_head h with rfl | ⟨c, step, rest⟩
  · obtain ⟨f', hx⟩ := hT
    cases hx
  · cases step

theorem Reach.not_ret_nilS {d : Devm} {T : Conf}
    (h : Reach P fs sevm ⟨d, .ret, []⟩ T) (hT : AtSstore T) : False := by
  rcases Relation.ReflTransGen.cases_head h with rfl | ⟨c, step, rest⟩
  · obtain ⟨f', hx⟩ := hT
    cases hx
  · cases step

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

theorem rs_jump {k : Nat} {dd : B256}
    (run : Reach P fs sevm ⟨St b (dd :: S) M G, .jump k, K⟩ T) (hT : AtSstore T) :
    ∃ g G', fs[k]? = some g ∧ Reach P fs sevm ⟨St b S M G', g, K⟩ T := by
  obtain ⟨t, g, d', hk, pop, rest⟩ := Reach.jumpS run hT
  exact ⟨g, _, hk, (St.of_pop1 pop).2 ▸ rest⟩

/-- A `callNext` whose callee is `SSTORE`-free: the callee returns before the target. -/
theorem rs_callOver {E : List Nat} (hE : SstoreFreeSet fs E = true) {k : Nat} {dd : B256}
    (hk : fs[k]? = some g) (hkE : k ∈ E)
    (run : Reach P fs sevm ⟨St b (dd :: S) M G, .callNext k f, K⟩ T) (hT : AtSstore T) :
    ∃ G' D, SFunc.RunP P fs sevm (St b S M G') g (.returned D) ∧
      Reach P fs sevm ⟨D, f, K⟩ T := by
  obtain ⟨t, g', d', hk', pop, inside | ⟨D, callee, rest⟩⟩ := Reach.callS run hT
  · rw [hk] at hk'
    cases hk'
    obtain ⟨T', r', rfl⟩ := inside
    exact (Reach.false_of_sstoreFree hE r' hT (SstoreFreeSet.lookup hE hkE hk)
      (by simp only [List.not_mem_nil, IsEmpty.forall_iff, implies_true])).elim
  · rw [hk] at hk'
    cases hk'
    obtain ⟨-, e⟩ := St.of_pop1 pop
    exact ⟨_, D, e ▸ callee, rest⟩

/-- A `callNext` whose continuation (with the pending ones) is `SSTORE`-free: the
target lies inside the callee, reached from an empty stack. -/
theorem rs_callInto {E : List Nat} (hE : SstoreFreeSet fs E = true) {k : Nat} {dd : B256}
    (hk : fs[k]? = some g) (hf : f.sstoreFreeIn E = true)
    (hK : ∀ s ∈ K, s.sstoreFreeIn E = true)
    (run : Reach P fs sevm ⟨St b (dd :: S) M G, .callNext k f, K⟩ T) (hT : AtSstore T) :
    ∃ G' T', Reach P fs sevm ⟨St b S M G', g, []⟩ T' ∧ T = T'.below (f :: K) := by
  obtain ⟨t, g', d', hk', pop, ⟨T', r', hT'⟩ | ⟨D, _, rest⟩⟩ := Reach.callS run hT
  · rw [hk] at hk'
    cases hk'
    obtain ⟨-, e⟩ := St.of_pop1 pop
    exact ⟨_, T', e ▸ r', hT'⟩
  · exact (Reach.false_of_sstoreFree hE rest hT hf hK).elim

end St

end Blanc.Lift
