import Blanc.Lift.ReachWalk
import Blanc.Lift.Silent
import Blanc.Lift.ShuffleSkip
import Blanc.Lift.FrameSkip

/-!
# Reach forms of the route-C skips

The node clause of `ImplStepLaw` is a statement about the machine at an external-instruction node
of a frame's own chain; `reach_of_parentPrefix` (`Blanc/Lift/Cursor.lean`) places that node at a
`Reach` of the certificate.  When the world at the node depends on a store before it (`_permit`'s
nonce bump), the reach is walked up to that store.  This module gives the two route-C skips in reach
form:

* `rr_shuffle`: a checked shuffle segment (`Blanc/Lift/ShuffleSkip.lean`) on a reach to an external
  instruction: the reach passes through the segment's target, with the same world and the carried
  stack;
* `rr_call_silent`: a silent, exec-free internal call on such a reach returns, with the same world
  and the declared number of words over the stack below the callee's frame.

Nothing here mentions a contract.  (Hoist candidates, next to `ShuffleSkip` and `FrameSkip`.)
-/

namespace Blanc.Lift

open Jaune

variable {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List SFunc} {sevm : Sevm}

/-! ## Shuffle segments on a reach -/

section ReachShuffle

open AbstractStackSafety

variable {es : List Entry} {Fw : List Nat} {tgt : SFunc} {pB : Nat} {X R : List B256} {T : Conf}
  {K : List SFunc}

/-- What a checked result promises for a reach to an external instruction from `d0`. -/
def ShReachR (fs : List SFunc) (sevm : Sevm) (P : Sevm → Devm → Ninst → Devm → Prop)
    (X R : List B256) (d0 : Devm) (tgt : SFunc) (K : List SFunc) (T : Conf) :
    Option (List SVal) → Prop
  | none => False
  | some π => ∃ d, d.state = d0.state ∧ ∃ Y, d.stack = Y ++ R ∧ Carried X π Y ∧
      Reach P fs sevm ⟨d, tgt, K⟩ T

theorem ShReachR.mono {d0 : Devm} {o o' : Option (List SVal)}
    (h : ShReachR fs sevm P X R d0 tgt K T o) (hle : ShLe o o') :
    ShReachR fs sevm P X R d0 tgt K T o' := by
  match o, o', h, hle with
  | some _, some _, ⟨d, hs, Y, hst, hY, run⟩, hle => exact ⟨d, hs, Y, hst, hY.mono hle, run⟩

theorem ShReachR.state {d0 d1 : Devm} {o : Option (List SVal)}
    (h : ShReachR fs sevm P X R d1 tgt K T o) (hs : d1.state = d0.state) :
    ShReachR fs sevm P X R d0 tgt K T o := by
  match o, h with
  | some _, ⟨d, hd, rest⟩ => exact ⟨d, hd.trans hs, rest⟩

theorem shNinst_not_exec {n : Ninst} {a a' : List SVal} (h : shNinst n a = some a') :
    ∀ x, n ≠ .exec x := by
  rintro x rfl
  simp only [shNinst, Ninst.stateSilent, Bool.false_and, Bool.false_eq_true, ↓reduceIte,
    reduceCtorEq] at h

/-- **Soundness of the shuffle checker on a reach** to an external instruction: the reach passes
through the target. -/
theorem rshuffle_sound (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
    (fork : CoveredFork sevm.benvStat.fork) (hT : AtExec T) :
    ∀ (fuel pc : Nat) (a : List SVal) (f : SFunc) (o : Option (List SVal)) (d : Devm)
      (Y : List B256), shuffle fs es Fw tgt pB fuel pc a f = some o →
      Reach P fs sevm ⟨d, f, K⟩ T → d.stack = Y ++ R → Carried X a Y →
      ShReachR fs sevm P X R d tgt K T o := by
  intro fuel
  induction fuel with
  | zero => intro pc a f o d Y h; simp only [shuffle, reduceCtorEq] at h
  | succ fuel ih =>
    intro pc a f o d Y h run hst hY
    simp only [shuffle] at h
    split at h
    · split at h
      · rename_i hsame
        simp only [Option.some.injEq] at h
        subst h
        rw [SFunc.eq_of_same hsame] at run
        exact ⟨d, rfl, Y, hst, hY, run⟩
      · cases h
    · cases f with
      | next n g =>
        simp only at h
        obtain ⟨a', hn, h'⟩ := Option.bind_eq_some_iff.mp h
        obtain ⟨d', hrun, rest⟩ := Reach.next (shNinst_not_exec hn) run hT
        obtain ⟨hs, Y', hst', hY'⟩ := shNinst_run fork hn hst hY (hP hrun)
        exact (ih _ _ _ _ _ _ h' rest hst' hY').state hs
      | dest g =>
        simp only at h
        obtain ⟨d', burn, rest⟩ := Reach.dest run hT
        exact (ih _ _ _ _ _ _ h rest (by rw [← burn.stack, hst]) hY).state burn.state.symm
      | branch g g' =>
        rcases a with _ | ⟨t, _ | ⟨v, a⟩⟩
        · simp only [reduceCtorEq] at h
        · simp only [reduceCtorEq] at h
        · simp only at h
          rcases hY with _ | ⟨_, hY1⟩
          rcases hY1 with _ | ⟨hv, hY'⟩
          rename_i y0 Y0 y1 Y'
          rcases Reach.branch run hT with ⟨dd, d', pop, rest⟩ | ⟨dd, w, d', hw, pop, rest⟩
          · have hp := popBurn_two_stack pop
            rw [hst] at hp
            simp only [List.cons_append, List.cons.injEq] at hp
            obtain ⟨_, rfl, hp⟩ := hp
            obtain ⟨o0, h0, hle⟩ := shBranch_zero h hv
            exact ((ih _ _ _ _ _ _ h0 rest hp.symm hY').mono hle).state pop.state.symm
          · have hp := popBurn_two_stack pop
            rw [hst] at hp
            simp only [List.cons_append, List.cons.injEq] at hp
            obtain ⟨_, rfl, hp⟩ := hp
            obtain ⟨o1, h1, hle⟩ := shBranch_succ h hv hw
            exact ((ih _ _ _ _ _ _ h1 rest hp.symm hY').mono hle).state pop.state.symm
      | branchTo g k =>
        rcases a with _ | ⟨t, _ | ⟨v, a⟩⟩
        · simp only [reduceCtorEq] at h
        · simp only [reduceCtorEq] at h
        · simp only at h
          rcases hY with _ | ⟨_, hY1⟩
          rcases hY1 with _ | ⟨hv, hY'⟩
          rename_i y0 Y0 y1 Y'
          cases hk : fs[k]? with
          | none => simp only [hk, reduceCtorEq] at h
          | some g' =>
            cases he : es[k]? with
            | none => simp only [hk, he, reduceCtorEq] at h
            | some e =>
              simp only [hk, he] at h
              split at h
              · rcases Reach.branchTo run hT with ⟨dd, d', pop, rest⟩ |
                  ⟨dd, w, g'', d', hw, hk', pop, rest⟩
                · have hp := popBurn_two_stack pop
                  rw [hst] at hp
                  simp only [List.cons_append, List.cons.injEq] at hp
                  obtain ⟨_, rfl, hp⟩ := hp
                  obtain ⟨o0, h0, hle⟩ := shBranch_zero h hv
                  exact ((ih _ _ _ _ _ _ h0 rest hp.symm hY').mono hle).state pop.state.symm
                · rw [hk] at hk'
                  cases hk'
                  have hp := popBurn_two_stack pop
                  rw [hst] at hp
                  simp only [List.cons_append, List.cons.injEq] at hp
                  obtain ⟨_, rfl, hp⟩ := hp
                  obtain ⟨o1, h1, hle⟩ := shBranch_succ h hv hw
                  exact ((ih _ _ _ _ _ _ h1 rest hp.symm hY').mono hle).state pop.state.symm
              · cases h
      | jump k =>
        rcases a with _ | ⟨t, a⟩
        · simp only [reduceCtorEq] at h
        · simp only at h
          rcases hY with _ | ⟨_, hY'⟩
          rename_i y0 Y'
          cases hk : fs[k]? with
          | none => simp only [hk, reduceCtorEq] at h
          | some g' =>
            cases he : es[k]? with
            | none => simp only [hk, he, reduceCtorEq] at h
            | some e =>
              simp only [hk, he] at h
              split at h
              · obtain ⟨dd, g'', d', hk', pop, rest⟩ := Reach.jump run hT
                rw [hk] at hk'
                cases hk'
                have hp := popBurn_one_stack pop
                rw [hst] at hp
                simp only [List.cons_append, List.cons.injEq] at hp
                exact (ih _ _ _ _ _ _ h rest hp.2.symm hY').state pop.state.symm
              · cases h
      | last l => exact (Reach.not_last run hT).elim
      | undefined =>
        rcases Relation.ReflTransGen.cases_head run with rfl | ⟨c, step, -⟩
        · obtain ⟨x, f', hx⟩ := hT
          cases hx
        · cases step
      | callNext _ _ => simp only [reduceCtorEq] at h
      | ret => simp only [reduceCtorEq] at h
      | pcAt _ _ => simp only [reduceCtorEq] at h

/-- **The shuffle skip on a reach** to an external instruction. -/
theorem rr_shuffle (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d') {f : SFunc}
    {pA fuel n : Nat} {π : List SVal} (fork : CoveredFork sevm.benvStat.fork) (hT : AtExec T)
    (hchk : shuffle fs es Fw tgt pB fuel pA (argFrame n) f = some (some π))
    (hX : X.length = n) {b : Devm} {M : Mem} {G : Nat}
    (run : Reach P fs sevm ⟨St b (X ++ R) M G, f, K⟩ T) :
    ∃ b' Y M' G', b'.state = b.state ∧ Carried X π Y ∧
      Reach P fs sevm ⟨St b' (Y ++ R) M' G', tgt, K⟩ T := by
  subst hX
  obtain ⟨d, hs, Y, hst, hY, run'⟩ :=
    rshuffle_sound hP fork hT _ _ _ _ _ _ _ hchk run rfl (carried_argFrame X)
  refine ⟨d, Y, d.memory, d.gasLeft, hs, hY, ?_⟩
  rw [← St.self hst rfl]
  exact run'

end ReachShuffle

/-- **Crossing a silent, exec-free internal call on a reach** to an external instruction: the
callee returns, and the reach continues from a state with the caller's world state and the stack
`Y ++ S.drop e.frame.length`, `Y.length = e.rets`. -/
theorem rr_call_silent (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d') {code : ByteArray}
    {c : Cert} (hc : Cert.check code c = true) (fork : CoveredFork sevm.benvStat.fork)
    {Sk E : List Nat} (hS : SilentSet c.prog Sk = true) (hE : ExecFreeSet c.prog E = true)
    {k : Nat} (hkS : k ∈ Sk) (hkE : k ∈ E) {e : Entry} {g : SFunc} (he : c.entries[k]? = some e)
    (hg : c.prog[k]? = some g) {b : Devm} {S : List B256} {M : Mem} {G : Nat} {dd ρ : B256}
    {f : SFunc} {K : List SFunc} {T : Conf}
    (hframe : FrameMatches ρ e.frame (S.take e.frame.length)) (hT : AtExec T)
    (run : Reach P c.prog sevm ⟨St b (dd :: S) M G, .callNext k f, K⟩ T) :
    ∃ b' Y M' G', b'.state = b.state ∧ Y.length = e.rets ∧
      Reach P c.prog sevm ⟨St b' (Y ++ S.drop e.frame.length) M' G', f, K⟩ T := by
  obtain ⟨G', D, callee, rest⟩ := rr_callOver hE hg hkE run hT
  have hgS : g.silent = true ∧ g.refs.all (· ∈ Sk) = true := by
    have h := (List.all_eq_true.mp hS) k hkS
    rw [hg] at h
    simpa only [Bool.and_eq_true] using h
  have hstate := SFunc.RunP.state_of_silent hP hS hgS.1 hgS.2 callee
  obtain ⟨Y, hY, hlen⟩ := callee.entry_stack_below hP hc fork he hg
    (List.take_append_drop _ _).symm hframe
  rw [St.stack] at hY
  refine ⟨D, Y, D.memory, D.gasLeft, hstate, hlen, ?_⟩
  rw [← St.self hY rfl]
  exact rest

end Blanc.Lift
