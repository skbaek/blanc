import Blanc.Lift.InvWalkOps

/-!
# Inverting successful synthetic runs: failing arms, calls, gotos and world steps

Companions to `InvWalk.lean`:

* `SFunc.noOk`, a decidable test for trees built only of straight-line steps and branches over
  `REVERT`/`undefined` terminals, with `SFunc.RunCutP.false_of_noOk` and
  `SFunc.RunP.false_of_noOk`: such a tree has no successful run at all, so every `REVERT` arm
  of an inversion walk closes by `(by decide)`;
* `ric_branchTo`/`ric_branchToCut` for conditional gotos, and `ric_call`/`ri_call` for internal
  calls (`callNext`), the converses of `rx_branchTo_*` and `rx_callRet`;
* the world steps `ri_sload` (successor over `afterSload`) and `ri_log1` (the entry appended by
  `addLog`), the converses of `rx_sload_sel` and `Ninst.runCompiled_log_of`.

Nothing here mentions a contract.
-/

namespace Blanc.Lift

open Jaune

/-! ## Trees with no successful run -/

/-- Straight-line steps and branches over failing terminals only: no jump, call, return or
successful halt is reachable. -/
def SFunc.noOk : SFunc → Bool
  | .next _ f => f.noOk
  | .dest f => f.noOk
  | .branch f g => f.noOk && g.noOk
  | .last .revert => true
  | .undefined => true
  | _ => false

/-- A tree with `noOk` has no cut run (successful or stopped at a cut entry). -/
theorem SFunc.RunCutP.false_of_noOk {P : Sevm → Devm → Ninst → Devm → Prop}
    {fs : List SFunc} {sevm : Sevm} {C : List Nat} {devm : Devm} {f : SFunc} {r : Seg}
    (run : SFunc.RunCutP P fs sevm C devm f r) (h : f.noOk = true) : False := by
  induction run with
  | zero _ _ _ ih => simp only [SFunc.noOk, Bool.and_eq_true] at h; exact ih h.1
  | succ _ _ _ _ _ ih => simp only [SFunc.noOk, Bool.and_eq_true] at h; exact ih h.2
  | last hl =>
      rename_i l
      cases l <;> simp only [SFunc.noOk, reduceCtorEq] at h
      exact Linst.not_run_revert_ok hl
  | next _ _ ih => exact ih h
  | dest _ _ ih => exact ih h
  | _ => simp [SFunc.noOk] at h

/-- A tree with `noOk` has no run. -/
theorem SFunc.RunP.false_of_noOk {P : Sevm → Devm → Ninst → Devm → Prop}
    {fs : List SFunc} {sevm : Sevm} {devm : Devm} {f : SFunc} {o : Outcome}
    (run : SFunc.RunP P fs sevm devm f o) (h : f.noOk = true) : False :=
  (SFunc.runP_iff_runCutP_nil.mp run).false_of_noOk h

/-! ## Gotos and calls of cut runs -/

section Control

variable {fs : List SFunc} {sevm : Sevm} {C : List Nat} {b : Devm} {S : List B256} {M : Mem}
  {G : Nat} {f g : SFunc} {r : Seg}

/-- A conditional goto to an entry outside the cut list. -/
theorem ric_branchTo {k : Nat} {dd w : B256} (hkC : k ∉ C) (hk : fs[k]? = some g)
    (run : SFunc.RunCut fs sevm C (St b (dd :: w :: S) M G) (.branchTo f k) r) :
    (w = 0 ∧ ∃ G', SFunc.RunCut fs sevm C (St b S M G') f r) ∨
      (w ≠ 0 ∧ ∃ G', SFunc.RunCut fs sevm C (St b S M G') g r) := by
  cases run with
  | toZero d0 h k =>
      obtain ⟨-, hw, e⟩ := St.of_pop2 h
      exact .inl ⟨hw, _, e ▸ k⟩
  | toSuccCut _ _ _ hk' _ => exact absurd hk' hkC
  | toSucc d0 w0 hw _ hk' h k =>
      rw [hk] at hk'
      cases hk'
      obtain ⟨-, hw', e⟩ := St.of_pop2 h
      exact .inr ⟨hw' ▸ hw, _, e ▸ k⟩

/-- A conditional goto to a cut entry: taken, the run stops there. -/
theorem ric_branchToCut {k : Nat} {dd w : B256} (hk : k ∈ C)
    (run : SFunc.RunCut fs sevm C (St b (dd :: w :: S) M G) (.branchTo f k) r) :
    (w = 0 ∧ ∃ G', SFunc.RunCut fs sevm C (St b S M G') f r) ∨
      (w ≠ 0 ∧ ∃ G', r = .at k (St b S M G')) := by
  cases run with
  | toZero d0 h k =>
      obtain ⟨-, hw, e⟩ := St.of_pop2 h
      exact .inl ⟨hw, _, e ▸ k⟩
  | toSuccCut d0 w0 hw _ h =>
      obtain ⟨-, hw', e⟩ := St.of_pop2 h
      exact .inr ⟨hw' ▸ hw, _, congrArg _ e⟩
  | toSucc _ _ _ hkC _ _ _ => exact absurd hk hkC

/-- An internal call (`JUMP` into entry `k` with a return tag below): the callee runs from the
state with the destination popped, and either returns into the continuation or halts the
frame. -/
theorem ric_call {k : Nat} {dd : B256} (hk : fs[k]? = some g)
    (run : SFunc.RunCut fs sevm C (St b (dd :: S) M G) (.callNext k f) r) :
    ∃ G', (∃ D, SFunc.Run fs sevm (St b S M G') g (.returned D) ∧ SFunc.RunCut fs sevm C D f r) ∨
      (∃ D, SFunc.Run fs sevm (St b S M G') g (.halted D) ∧ r = .done (.halted D)) := by
  cases run with
  | callHalt d0 hk' h hr =>
      rw [hk] at hk'
      cases hk'
      exact ⟨_, .inr ⟨_, (St.of_pop1 h).2 ▸ hr, rfl⟩⟩
  | callRet d0 hk' h hr k =>
      rw [hk] at hk'
      cases hk'
      exact ⟨_, .inl ⟨_, (St.of_pop1 h).2 ▸ hr, k⟩⟩

/-- `ric_call` when the continuation cannot halt through the callee: the callee returns. -/
theorem ric_callRet {k : Nat} {dd : B256} (hk : fs[k]? = some g)
    (hnh : ∀ D, r ≠ .done (.halted D))
    (run : SFunc.RunCut fs sevm C (St b (dd :: S) M G) (.callNext k f) r) :
    ∃ G' D, SFunc.Run fs sevm (St b S M G') g (.returned D) ∧ SFunc.RunCut fs sevm C D f r := by
  obtain ⟨G', ⟨D, h1, h2⟩ | ⟨D, -, hr⟩⟩ := ric_call hk run
  · exact ⟨G', D, h1, h2⟩
  · exact absurd hr (hnh D)

end Control

/-! ## Uncut runs

The segment statements are over `SFunc.Run`; `SFunc.Run.cut` moves one to the cut form with
nothing cut, where every `ric_*` lemma applies with `C = []`, and `SFunc.RunCut.uncut` moves
back. -/

theorem SFunc.Run.cut {fs : List SFunc} {sevm : Sevm} {devm : Devm} {f : SFunc} {o : Outcome}
    (run : SFunc.Run fs sevm devm f o) : SFunc.RunCut fs sevm [] devm f (.done o) :=
  SFunc.runP_iff_runCutP_nil.mp run

theorem SFunc.RunCut.uncut {fs : List SFunc} {sevm : Sevm} {devm : Devm} {f : SFunc}
    {o : Outcome} (run : SFunc.RunCut fs sevm [] devm f (.done o)) : SFunc.Run fs sevm devm f o :=
  SFunc.runP_iff_runCutP_nil.mpr run

/-! ## World steps -/

section World

variable {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}

theorem Devm.eq_of_push_ok {x : B256} {d d' : Devm} (h : d.push x = .ok d') :
    d' = d.setMach {d.mach with stack := x :: d.stack} := by
  rw [Devm.push_def] at h
  unfold Except.assert at h
  split at h
  · cases h; rfl
  · cases h

/-- `SLOAD`, inverted: the successor is over the selected `afterSload` base, with the stored
value pushed. -/
theorem ri_sload {k : B256} {d : Devm} (hfork : CoveredFork sevm.benvStat.fork)
    (h : Ninst.Run sevm (St b (k :: S) M G) (.reg .sload) d) :
    ∃ G', d = St (afterSload sevm b k) (b.getStorVal sevm.currentTarget k :: S) M G' := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore,
    Devm.balReadStorage_of_bal_none (CoveredFork.rules_bal_none hfork)] at run
  rw [show (St b (k :: S) M G).pop = .ok (k, St b S M G) from rfl] at run
  simp only [Except.bind_ok] at run
  by_cases hw : (⟨sevm.currentTarget, k⟩ : Adr × B256) ∈ b.accessedStorageKeys
  · simp only [St.accessedStorageKeys, hw, ite_true] at run
    rcases Except.bind_eq_ok run with ⟨s1, h1, h2⟩
    have e2 := Devm.eq_of_push_ok h2
    subst e2
    have e1 := Devm.eq_setGas_of_burn (Devm.burn_of_chargeGas h1)
    rw [e1]
    refine ⟨s1.gasLeft, ?_⟩
    simp only [afterSload, hw, ite_true]
    rfl
  · simp only [St.accessedStorageKeys, hw, ite_false] at run
    rcases Except.bind_eq_ok run with ⟨s1, h1, h2⟩
    have e2 := Devm.eq_of_push_ok h2
    subst e2
    have e1 := Devm.eq_setGas_of_burn (Devm.burn_of_chargeGas h1)
    rw [e1]
    refine ⟨s1.gasLeft, ?_⟩
    simp only [afterSload, hw, ite_false]
    rfl

/-- `LOG1`, inverted: the successor's base carries the entry `rx_log1` appends, over the bytes
the window reads; memory is the window read's image. -/
theorem ri_log1 {i sz t : B256} {d : Devm}
    (h : Ninst.Run sevm (St b (i :: sz :: t :: S) M G) (.reg (.log 1)) d) :
    ∃ G', d = St (b.addLog ⟨sevm.currentTarget, [t], (M.read i.toNat sz.toNat).1⟩) S
      (M.read i.toNat sz.toNat).2 G' := by
  rcases of_run_reg h with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  rw [show (St b (i :: sz :: t :: S) M G).popToNat = .ok (i.toNat, St b (sz :: t :: S) M G)
    from rfl] at run
  simp only [Except.bind_ok] at run
  rw [show (St b (sz :: t :: S) M G).popToNat = .ok (sz.toNat, St b (t :: S) M G)
    from rfl] at run
  simp only [Except.bind_ok] at run
  rw [show (St b (t :: S) M G).popN ((1 : Fin 5) : Nat) = .ok ([t], St b S M G) from rfl] at run
  simp only [Except.bind_ok] at run
  rcases Except.bind_eq_ok run with ⟨s1, h1, h2⟩
  rcases Except.bind_eq_ok h2 with ⟨_, -, h3⟩
  cases h3
  have e1 := Devm.eq_setGas_of_burn (Devm.burn_of_chargeGas h1)
  refine ⟨s1.gasLeft, ?_⟩
  rw [e1]
  rfl

end World

end Blanc.Lift
