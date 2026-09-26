import Blanc.Lift.ExactWalk
import Blanc.CommonProofs
import Blanc.Lift.Loop
import Blanc.CompiledWalkInversion

/-!
# Inverting successful synthetic runs, one tree node at a time

The converse of `ExactWalk.lean`: from a successful `SFunc.Run` (the safety relation `exec_lift`
produces) of a node at a state `St b S M G`, the successor state is again an `St` over the same
base `b` (for every step that does not touch the world), with the stack the step computes and
some gas.  Each lemma pairs with its `rx_*` counterpart; together they make an inversion walk as
mechanical as a liveness walk.

Nothing here mentions a contract.
-/

namespace Blanc.Lift

open Jaune

/-- A relation that keeps every field except stack and gas keeps the `St` form. -/
theorem St.of_stackRel {R1 : List B256 → List B256 → Prop} {R3 : Nat → Nat → Prop}
    {b d : Devm} {S : List B256} {M : Mem} {G : Nat}
    (h : Devm.Rel {Devm.Rels.eq with stack := R1, gasLeft := R3} (St b S M G) d) :
    d = St b d.stack M d.gasLeft := by
  obtain ⟨_, hmem, _, hlogs, hrc, hout, hdel, hrd, herr, haddr, hkeys, hstate, hcre, htr, hsg,
    hacc, hsto⟩ := h
  rcases d with ⟨⟨s, m, g, sg⟩, ⟨l, rc, o, del, rd, e, ad, ks, cr, ar, sr⟩, ⟨st, tr⟩⟩
  rcases b with ⟨⟨s0, m0, g0, sg0⟩, ⟨l0, rc0, o0, del0, rd0, e0, ad0, ks0, cr0, ar0, sr0⟩,
    ⟨st0, tr0⟩⟩
  simp only [St, Devm.setMach, Devm.memory, Devm.logs, Devm.refundCounter, Devm.output,
    Devm.accountsToDelete, Devm.returnData, Devm.error, Devm.accessedAddresses,
    Devm.accessedStorageKeys, Devm.state, Devm.createdAccounts, Devm.transientStorage,
    Devm.stateGas, Devm.Rels.eq] at *
  subst hmem hlogs hrc hout hdel hrd herr haddr hkeys hstate hcre htr hsg hacc hsto
  rfl

section Steps

variable {fs : List SFunc} {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}

/-- `PUSH`, inverted. -/
theorem ri_push {xs : Bytes} {le : xs.length ≤ 32} {d : Devm}
    (h : Ninst.Run sevm (St b S M G) (.push xs le) d) :
    ∃ G', d = St b (xs.toB256 :: S) M G' := by
  have hp := of_run_push h
  have hs : d.stack = xs.toB256 :: S := by
    have := hp.stack
    simpa [Stack.Push, Split] using this
  have e := St.of_stackRel hp
  rw [hs] at e
  exact ⟨_, e⟩

theorem St.of_diff {v : B256 → B256 → B256} {x y : B256} {d : Devm}
    (hd : ∃ x' y', Devm.DiffBurn [x', y'] [v x' y'] (St b (x :: y :: S) M G) d) :
    ∃ G', d = St b (v x y :: S) M G' := by
  obtain ⟨x', y', hd'⟩ := hd
  obtain ⟨s1, hpop, hpush⟩ := hd'.stack
  simp only [Stack.Pop, Stack.Push, Split, St.stack] at hpop hpush
  simp only [List.cons_append, List.nil_append, List.cons.injEq] at hpop
  obtain ⟨rfl, rfl, rfl⟩ := hpop
  have e := St.of_stackRel hd'
  rw [hpush] at e
  exact ⟨_, e⟩

theorem St.of_diff1 {v : B256 → B256} {x : B256} {d : Devm}
    (hd : ∃ x', Devm.DiffBurn [x'] [v x'] (St b (x :: S) M G) d) :
    ∃ G', d = St b (v x :: S) M G' := by
  obtain ⟨x', hd'⟩ := hd
  obtain ⟨s1, hpop, hpush⟩ := hd'.stack
  simp only [Stack.Pop, Stack.Push, Split, St.stack] at hpop hpush
  simp only [List.cons_append, List.nil_append, List.cons.injEq] at hpop
  obtain ⟨rfl, rfl⟩ := hpop
  have e := St.of_stackRel hd'
  rw [hpush] at e
  exact ⟨_, e⟩

/-- A binary `Rinst` built on `applyBinary`, inverted. -/
theorem ri_and {x y : B256} {d : Devm}
    (h : Ninst.Run sevm (St b (x :: y :: S) M G) (.reg .and) d) :
    ∃ G', d = St b ((x &&& y) :: S) M G' := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact St.of_diff (v := (· &&& ·)) (Devm.diffBurn_of_applyBinary run)

theorem ri_add {x y : B256} {d : Devm}
    (h : Ninst.Run sevm (St b (x :: y :: S) M G) (.reg .add) d) :
    ∃ G', d = St b ((x + y) :: S) M G' := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact St.of_diff (v := (· + ·)) (Devm.diffBurn_of_applyBinary run)

theorem ri_eq {x y : B256} {d : Devm}
    (h : Ninst.Run sevm (St b (x :: y :: S) M G) (.reg .eq) d) :
    ∃ G', d = St b (B256.eqCheck x y :: S) M G' := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact St.of_diff (v := B256.eqCheck) (Devm.diffBurn_of_applyBinary run)

theorem ri_lt {x y : B256} {d : Devm}
    (h : Ninst.Run sevm (St b (x :: y :: S) M G) (.reg .lt) d) :
    ∃ G', d = St b (B256.ltCheck x y :: S) M G' := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact St.of_diff (v := B256.ltCheck) (Devm.diffBurn_of_applyBinary run)

theorem ri_iszero {x : B256} {d : Devm}
    (h : Ninst.Run sevm (St b (x :: S) M G) (.reg .iszero) d) :
    ∃ G', d = St b (B256.eqCheck x 0 :: S) M G' := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact St.of_diff1 (v := (B256.eqCheck · 0)) (Devm.diffBurn_of_applyUnary run)

/-- `POP`, inverted. -/
theorem ri_pop {x : B256} {d : Devm}
    (h : Ninst.Run sevm (St b (x :: S) M G) (.reg .pop) d) :
    ∃ G', d = St b S M G' := by
  obtain ⟨x', hp⟩ := of_run_pop h
  have hs := hp.stack
  simp only [Stack.Pop, Split, St.stack, List.cons_append, List.nil_append,
    List.cons.injEq] at hs
  have e := St.of_stackRel hp
  rw [← hs.2] at e
  exact ⟨_, e⟩

/-- `DUP n`, inverted. -/
theorem ri_dup {n : Fin 16} {w : B256} {d : Devm} (hget : S[n.val]? = some w)
    (h : Ninst.Run sevm (St b S M G) (.reg (.dup n)) d) :
    ∃ G', d = St b (w :: S) M G' := by
  obtain ⟨x, hx, hp⟩ := of_run_dup h
  simp only [St.stack, hget, Option.some.injEq] at hx
  subst hx
  have hs : d.stack = w :: S := by simpa [Stack.Push, Split] using hp.stack
  have e := St.of_stackRel hp
  rw [hs] at e
  exact ⟨_, e⟩

/-- `SWAP n`, inverted. -/
theorem ri_swap {n : Fin 16} {S' : List B256} {d : Devm} (hsw : Jaune.List.swap S n.val = some S')
    (h : Ninst.Run sevm (St b S M G) (.reg (.swap n)) d) :
    ∃ G', d = St b S' M G' := by
  have hs := of_run_swap h
  simp only [St.stack, hsw, Option.some.injEq] at hs
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨s₁, h1, h2⟩
  have hb := Devm.burn_of_chargeGas h1
  split at h2
  · cases h2
  · injection h2 with eq
    subst eq
    have e := St.of_stackRel hb
    rename_i stk _
    refine ⟨s₁.gasLeft, ?_⟩
    have hs' : S' = stk := by rw [hs]; rfl
    subst hs'
    rw [e]
    rfl

end Steps

/-! ## Control nodes of cut runs -/

section Control

variable {fs : List SFunc} {sevm : Sevm} {C : List Nat} {b : Devm} {S : List B256} {M : Mem}
  {G : Nat} {f g : SFunc} {r : Seg}

theorem St.of_burn {d : Devm} (h : Devm.Burn (St b S M G) d) : d = St b S M d.gasLeft := by
  have e := St.of_stackRel (R1 := Eq) (R3 := (· ≥ ·)) h
  rw [show d.stack = S from h.stack.symm] at e
  exact e

theorem St.of_pop1 {dd d0 : B256} {d : Devm} (h : Devm.PopBurn [d0] (St b (dd :: S) M G) d) :
    dd = d0 ∧ d = St b S M d.gasLeft := by
  have hs := h.stack
  simp only [Stack.Pop, Split, St.stack, List.cons_append, List.nil_append,
    List.cons.injEq] at hs
  have e := St.of_stackRel h
  rw [← hs.2] at e
  exact ⟨hs.1, e⟩

theorem St.of_pop2 {dd w d0 w0 : B256} {d : Devm}
    (h : Devm.PopBurn [d0, w0] (St b (dd :: w :: S) M G) d) :
    dd = d0 ∧ w = w0 ∧ d = St b S M d.gasLeft := by
  have hs := h.stack
  simp only [Stack.Pop, Split, St.stack, List.cons_append, List.nil_append,
    List.cons.injEq] at hs
  have e := St.of_stackRel h
  rw [← hs.2.2] at e
  exact ⟨hs.1, hs.2.1, e⟩

theorem ric_next {n : Ninst} {devm : Devm}
    (run : SFunc.RunCut fs sevm C devm (.next n f) r) :
    ∃ d, Ninst.Run sevm devm n d ∧ SFunc.RunCut fs sevm C d f r := by
  cases run with
  | next h k => exact ⟨_, h, k⟩

theorem ric_dest (run : SFunc.RunCut fs sevm C (St b S M G) (.dest f) r) :
    ∃ G', SFunc.RunCut fs sevm C (St b S M G') f r := by
  cases run with
  | dest h k => exact ⟨_, (St.of_burn h) ▸ k⟩

theorem ric_branch {dd w : B256}
    (run : SFunc.RunCut fs sevm C (St b (dd :: w :: S) M G) (.branch f g) r) :
    (w = 0 ∧ ∃ G', SFunc.RunCut fs sevm C (St b S M G') f r) ∨
      (w ≠ 0 ∧ ∃ G', SFunc.RunCut fs sevm C (St b S M G') g r) := by
  cases run with
  | zero d0 h k =>
      obtain ⟨-, hw, e⟩ := St.of_pop2 h
      exact .inl ⟨hw, _, e ▸ k⟩
  | succ d0 w0 hw h k =>
      obtain ⟨-, hw', e⟩ := St.of_pop2 h
      exact .inr ⟨hw' ▸ hw, _, e ▸ k⟩

theorem ric_jumpCut {k : Nat} {dd : B256} (hk : k ∈ C)
    (run : SFunc.RunCut fs sevm C (St b (dd :: S) M G) (.jump k) r) :
    ∃ G', r = .at k (St b S M G') := by
  cases run with
  | jumpCut d0 _ h =>
      exact ⟨_, congrArg _ (St.of_pop1 h).2⟩
  | jump _ hkC _ _ _ => exact absurd hk hkC

theorem ric_jump {k : Nat} {dd : B256} (hkC : k ∉ C) (hk : fs[k]? = some g)
    (run : SFunc.RunCut fs sevm C (St b (dd :: S) M G) (.jump k) r) :
    ∃ G', SFunc.RunCut fs sevm C (St b S M G') g r := by
  cases run with
  | jumpCut _ hk' _ => exact absurd hk' hkC
  | jump d0 _ hk' h k =>
      rw [hk] at hk'
      cases hk'
      exact ⟨_, (St.of_pop1 h).2 ▸ k⟩

theorem ric_ret {dd : B256}
    (run : SFunc.RunCut fs sevm C (St b (dd :: S) M G) .ret r) :
    ∃ G', r = .done (.returned (St b S M G')) := by
  cases run with
  | ret d0 h =>
      exact ⟨_, congrArg (fun x => Seg.done (Outcome.returned x)) (St.of_pop1 h).2⟩

theorem ric_undefined {devm : Devm} (run : SFunc.RunCut fs sevm C devm .undefined r) : False := by
  cases run

theorem ric_revert {devm : Devm} (run : SFunc.RunCut fs sevm C devm (.last .revert) r) : False := by
  cases run with
  | last h => exact Linst.not_run_revert_ok h

end Control

/-! ## World-touching steps (frozen) -/

section World

/-- A burn only moves gas: the successor is the predecessor with its gas replaced. -/
theorem Devm.eq_setGas_of_burn {a c : Devm} (h : Devm.Burn a c) :
    c = a.setMach ⟨a.stack, a.memory, c.gasLeft, a.stateGas⟩ := by
  obtain ⟨hs, hmem, _, hlogs, hrc, hout, hdel, hrd, herr, haddr, hkeys, hstate, hcre, htr, hsg,
    hacc, hsto⟩ := h
  rcases c with ⟨⟨s, m, g, sg⟩, ⟨l, rc, o, del, rd, e, ad, ks, cr, ar, sr⟩, ⟨st, tr⟩⟩
  rcases a with ⟨⟨s0, m0, g0, sg0⟩, ⟨l0, rc0, o0, del0, rd0, e0, ad0, ks0, cr0, ar0, sr0⟩,
    ⟨st0, tr0⟩⟩
  simp only [Devm.stack, Devm.memory, Devm.logs, Devm.refundCounter, Devm.output,
    Devm.accountsToDelete, Devm.returnData, Devm.error, Devm.accessedAddresses,
    Devm.accessedStorageKeys, Devm.state, Devm.createdAccounts, Devm.transientStorage,
    Devm.stateGas, Devm.Rels.eq] at *
  subst hs hmem hlogs hrc hout hdel hrd herr haddr hkeys hstate hcre htr hsg hacc hsto
  rfl

variable {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}

-- SEGMENT: riSstore
/-- `SSTORE`, inverted: the successor is the selected `afterSstore` over the base.

Proof sketch.  Unfold `Rinst.run .sstore` as `of_run_sstore` does (covered fork:
`rules.stateGas = none`); the two pops, the access-set insertion (if cold), the refund update
and `setStorVal` are exactly `afterSstore`'s pieces (`ForwardCall.lean`), and the charge and
sentry only move gas.  Compare the pieces field by field (`Devm.ext`, `Meta.ext`). -/
theorem ri_sstore {k v : B256} {d : Devm} (hfork : CoveredFork sevm.benvStat.fork)
    (h : Ninst.Run sevm (St b (k :: v :: S) M G) (.reg .sstore) d) :
    ∃ G', d = St (afterSstore sevm b k v) S M G' := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore, hfork.rules_stateGas_none,
    Devm.balReadStorage_of_bal_none (CoveredFork.rules_bal_none hfork),
    Devm.balReadAccount_of_bal_none (CoveredFork.rules_bal_none hfork)] at run
  rw [show (St b (k :: v :: S) M G).pop = .ok (k, St b (v :: S) M G) from rfl] at run
  simp only [Except.bind_ok] at run
  rw [show (St b (v :: S) M G).pop = .ok (v, St b S M G) from rfl] at run
  simp only [Except.bind_ok] at run
  rcases Except.bind_eq_ok run with ⟨_, -, run₃⟩
  rcases Except.bind_eq_ok run₃ with ⟨s₅, h7, run₇⟩
  rcases Except.bind_eq_ok run₇ with ⟨_, -, h9⟩
  cases h9
  have e5 := Devm.eq_setGas_of_burn (Devm.burn_of_chargeGas h7)
  refine ⟨s₅.gasLeft, ?_⟩
  rw [e5]
  unfold afterSstore
  by_cases hw : (⟨sevm.currentTarget, k⟩ : Adr × B256) ∈ b.accessedStorageKeys
  · simp only [St.accessedStorageKeys, hw, not_true_eq_false, ite_false, ite_true]
    rfl
  · simp only [St.accessedStorageKeys, hw, not_false_eq_true, ite_false, ite_true]
    rfl

end World

end Blanc.Lift
