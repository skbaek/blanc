import Blanc.Lift.ReachWalk
import Blanc.Lift.InvWalkWorld

/-!
# Node inversions of big-step runs under an arbitrary step relation

The certificate-driven walk kit for a big-step run `SFunc.RunP P fs sevm d f o` over the walk
state `St b S M G`, for any instruction relation `P` (a `pause` body runs under `StepIn R`, a proxy
under the relation its frame theorem carries): every step is the inversion of the checked tree's
node, never an unfolding of the bytes.  The cut-run forms (`ric_*`, `Blanc/Lift/InvWalkWorld.lean`,
`InvWalkStep.lean`) and the prefix-reach forms (`rr_*`, `Blanc/Lift/ReachWalk.lean`) are the same
kit for the other two run shapes.

* The big-step node inversions `rpw_next`, `rpw_dest`, `rpw_branch`, `rpw_branchTo`, `rpw_jump`,
  `rpw_call` (callee returns or halts), `rpw_callOver` (a callee in a `NoHaltSet` returns),
  `rpw_callRet` (a returning run's callee returns), `rpw_ret`, `rpw_revert`;
* `SFunc.haltsOnly` with `SFunc.RunP.not_returned_of_haltsOnly`: a tree with no `.ret` and no
  reference has no returning run;
* the prefix-reach gotos `rr_branchTo`, `rr_jump`, the instruction inversions `ri_address`,
  `ri_dup_any` (a `DUP` of an unnamed word) and `St.self'` (every machine is its own walk state).

Nothing here mentions a contract.
-/

namespace Blanc.Lift

open Jaune Blanc

variable {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List SFunc} {sevm : Sevm} {b : Devm}
  {S : List B256} {M : Mem} {G : Nat} {f g : SFunc} {o : Outcome} {K : List SFunc} {T : Conf}

/-! ## Walk states and instruction inversions -/

/-- Every machine is its own walk state. -/
theorem St.self' (d : Devm) : d = St d d.stack d.memory d.gasLeft := St.self rfl rfl

/-- `ADDRESS`, inverted. -/
theorem ri_address {d : Devm}
    (h : Ninst.Run sevm (St b S M G) (.reg .address) d) :
    ∃ G', d = St b (sevm.currentTarget.toB256 :: S) M G' := by
  have hp := of_run_address h
  have hs : d.stack = sevm.currentTarget.toB256 :: S := by
    have := hp.stack
    simpa only [Stack.Push, Split, St.stack, List.cons_append, List.nil_append] using this
  have e := St.of_stackRel hp
  rw [hs] at e
  exact ⟨_, e⟩

/-- `DUP n` over a stack whose `n`-th word is not named. -/
theorem ri_dup_any {n : Fin 16} {d : Devm}
    (h : Ninst.Run sevm (St b S M G) (.reg (.dup n)) d) :
    ∃ w, S[n.val]? = some w ∧ ∃ G', d = St b (w :: S) M G' := by
  obtain ⟨x, hx, -⟩ := of_run_dup h
  simp only [St.stack] at hx
  exact ⟨x, hx, ri_dup hx h⟩

/-! ## Prefix-reach gotos -/

theorem rr_branchTo {k : Nat} {dd w : B256}
    (run : Reach P fs sevm ⟨St b (dd :: w :: S) M G, .branchTo f k, K⟩ T) (hT : AtExec T) :
    (w = 0 ∧ ∃ G', Reach P fs sevm ⟨St b S M G', f, K⟩ T) ∨
      (w ≠ 0 ∧ ∃ g G', fs[k]? = some g ∧ Reach P fs sevm ⟨St b S M G', g, K⟩ T) := by
  rcases Reach.branchTo run hT with ⟨t, d', pop, rest⟩ | ⟨t, w0, g, d', hw, hk, pop, rest⟩
  · obtain ⟨-, hw, e⟩ := St.of_pop2 pop
    exact .inl ⟨hw, _, e ▸ rest⟩
  · obtain ⟨-, hw', e⟩ := St.of_pop2 pop
    exact .inr ⟨hw' ▸ hw, g, _, hk, e ▸ rest⟩

/-! ## Big-step node inversions -/

theorem rpw_next {n : Ninst} {d : Devm} (run : SFunc.RunP P fs sevm d (.next n f) o) :
    ∃ d', P sevm d n d' ∧ SFunc.RunP P fs sevm d' f o := by
  cases run with
  | next h k => exact ⟨_, h, k⟩

theorem rpw_dest (run : SFunc.RunP P fs sevm (St b S M G) (.dest f) o) :
    ∃ G', SFunc.RunP P fs sevm (St b S M G') f o := by
  cases run with
  | dest h k => exact ⟨_, (St.of_burn h) ▸ k⟩

theorem rpw_branch {dd w : B256}
    (run : SFunc.RunP P fs sevm (St b (dd :: w :: S) M G) (.branch f g) o) :
    (w = 0 ∧ ∃ G', SFunc.RunP P fs sevm (St b S M G') f o) ∨
      (w ≠ 0 ∧ ∃ G', SFunc.RunP P fs sevm (St b S M G') g o) := by
  cases run with
  | zero d0 h k =>
      obtain ⟨-, hw, e⟩ := St.of_pop2 h
      exact .inl ⟨hw, _, e ▸ k⟩
  | succ d0 w0 hw h k =>
      obtain ⟨-, hw', e⟩ := St.of_pop2 h
      exact .inr ⟨hw' ▸ hw, _, e ▸ k⟩

theorem rpw_ret {dd : B256} {D : Devm}
    (run : SFunc.RunP P fs sevm (St b (dd :: S) M G) .ret (.returned D)) :
    ∃ G', D = St b S M G' := by
  cases run with
  | ret d0 h => exact ⟨_, (St.of_pop1 h).2⟩

/-! ## Trees with no returning run -/

/-- No returning run of a halting tree: no `.ret` and no reference. -/
def SFunc.haltsOnly : SFunc → Bool
  | .next _ f => f.haltsOnly
  | .dest f => f.haltsOnly
  | .branch f g => f.haltsOnly && g.haltsOnly
  | .last _ => true
  | .undefined => true
  | _ => false

theorem SFunc.RunP.not_returned_of_haltsOnly {d D : Devm}
    (run : SFunc.RunP P fs sevm d f (.returned D)) (h : f.haltsOnly = true) : False := by
  generalize ho : Outcome.returned D = o at run
  induction run with
  | zero _ _ _ ih => simp only [SFunc.haltsOnly, Bool.and_eq_true] at h; exact ih h.1 ho
  | succ _ _ _ _ _ ih => simp only [SFunc.haltsOnly, Bool.and_eq_true] at h; exact ih h.2 ho
  | next _ _ ih => exact ih h ho
  | dest _ _ ih => exact ih h ho
  | last _ => cases ho
  | _ => simp only [SFunc.haltsOnly, Bool.false_eq_true] at h

end Blanc.Lift
