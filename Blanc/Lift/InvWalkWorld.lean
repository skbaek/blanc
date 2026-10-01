import Blanc.Lift.InvWalkOps

/-!
# Inverting successful synthetic runs: failing arms, calls, gotos and world steps

Companions to `InvWalk.lean`:

* `SFunc.noOk`, a decidable test for trees built only of straight-line steps and branches over
  `REVERT`/`undefined` terminals, with `SFunc.RunCutP.false_of_noOk`
  (a plain run is the cut run with nothing cut): such a tree has no successful run at all, so every `REVERT` arm
  of an inversion walk closes by `(by decide)`;
* `SFunc.noHalt` and the closed entry sets `NoHaltSet`, with `SFunc.RunP.not_halted` and
  `SFunc.RunP.not_halted_entry`: trees whose only terminals are `REVERT`, returns and
  `undefined` never halt;
* `ric_branchTo`/`ric_branchToCut` for conditional gotos, and `ric_call`/`ri_call` for internal
  calls (`callNext`), the converses of `rx_branchTo_*` and `rx_callRet`;
* the world steps `ri_sload` (successor over `afterSload`) and `ri_log1` (the entry appended by
  `addLog`), the converses of `rx_sload_sel` and `rx_log1`.

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
  | _ => simp only [noOk, Bool.false_eq_true] at h

/-! ## Trees that cannot halt -/

/-- Trees with no halting terminal: only `.revert`, `.ret`, `.undefined`. -/
def SFunc.noHalt : SFunc → Bool
  | .branch f g => f.noHalt && g.noHalt
  | .branchTo f _ => f.noHalt
  | .last l => l == .revert
  | .next _ f => f.noHalt
  | .dest f => f.noHalt
  | .jump _ => true
  | .callNext _ f => f.noHalt
  | .ret => true
  | .pcAt _ f => f.noHalt
  | .undefined => true

/-- `S` is closed under the entries referenced by its members, and none of them halts. -/
def NoHaltSet (fs : List SFunc) (S : List Nat) : Bool :=
  S.all fun k => match fs[k]? with
    | some g => g.noHalt && g.refs.all (· ∈ S)
    | none => false

/-- A run of a tree in a `NoHaltSet` cannot halt. -/
theorem SFunc.RunP.not_halted {P : Sevm → Devm → Ninst → Devm → Prop}
    {fs : List SFunc} {S : List Nat} (hS : NoHaltSet fs S = true)
    {sevm : Sevm} {devm : Devm} {f : SFunc} {D : Devm} {o : Outcome}
    (hf : f.noHalt = true) (hrefs : f.refs.all (· ∈ S) = true)
    (run : SFunc.RunP P fs sevm devm f o) (ho : o = .halted D) : False := by
  have closed : ∀ {k g}, k ∈ S → fs[k]? = some g →
      g.noHalt = true ∧ g.refs.all (· ∈ S) = true := by
    intro k g hk hget
    have h := (List.all_eq_true.mp hS) k hk
    rw [hget] at h
    simpa only [List.all_eq_true, decide_eq_true_eq, Bool.and_eq_true] using h
  induction run with
  | zero d pop run ih =>
      simp only [SFunc.noHalt, Bool.and_eq_true] at hf
      simp only [SFunc.refs, List.all_append, Bool.and_eq_true] at hrefs
      exact ih hf.1 hrefs.1 ho
  | succ d w hnz pop run ih =>
      simp only [SFunc.noHalt, Bool.and_eq_true] at hf
      simp only [SFunc.refs, List.all_append, Bool.and_eq_true] at hrefs
      exact ih hf.2 hrefs.2 ho
  | toZero d pop run ih =>
      simp only [SFunc.refs, List.all_cons, Bool.and_eq_true] at hrefs
      exact ih hf hrefs.2 ho
  | toSucc d w hnz lookup pop run ih =>
      simp only [SFunc.refs, List.all_cons, Bool.and_eq_true] at hrefs
      have ht := closed (of_decide_eq_true hrefs.1) lookup
      exact ih ht.1 ht.2 ho
  | last hrun =>
      cases ho
      rename_i l
      simp only [SFunc.noHalt] at hf
      have : l = .revert := by
        revert hf
        cases l <;> decide
      subst this
      exact Linst.not_run_revert_ok hrun
  | next hrun run ih =>
      simp only [SFunc.noHalt] at hf
      exact ih hf hrefs ho
  | dest burn run ih =>
      exact ih hf hrefs ho
  | jump d lookup pop run ih =>
      simp only [SFunc.refs, List.all_cons, Bool.and_eq_true] at hrefs
      have ht := closed (of_decide_eq_true hrefs.1) lookup
      exact ih ht.1 ht.2 ho
  | ret => cases ho
  | callHalt d lookup pop run ih =>
      simp only [SFunc.refs, List.all_cons, Bool.and_eq_true] at hrefs
      have ht := closed (of_decide_eq_true hrefs.1) lookup
      cases ho
      exact ih ht.1 ht.2 rfl
  | callRet d lookup pop run tail ihRun ihTail =>
      simp only [SFunc.refs, List.all_cons, Bool.and_eq_true] at hrefs
      simp only [SFunc.noHalt] at hf
      exact ihTail hf hrefs.2 ho
  | pcAt _ _ run ih =>
      simp only [SFunc.noHalt] at hf
      simp only [SFunc.refs] at hrefs
      exact ih hf hrefs ho

/-- A run of an entry in a `NoHaltSet` cannot halt. -/
theorem SFunc.RunP.not_halted_entry {P : Sevm → Devm → Ninst → Devm → Prop}
    {fs : List SFunc} {S : List Nat} (hS : NoHaltSet fs S = true)
    {k : Nat} (hkS : k ∈ S) {g : SFunc} (hk : fs[k]? = some g)
    {sevm : Sevm} {devm : Devm} {D : Devm} {o : Outcome}
    (run : SFunc.RunP P fs sevm devm g o) (ho : o = .halted D) : False := by
  have closed : ∀ {k g}, k ∈ S → fs[k]? = some g →
      g.noHalt = true ∧ g.refs.all (· ∈ S) = true := by
    intro k g hk hget
    have h := (List.all_eq_true.mp hS) k hk
    rw [hget] at h
    simpa only [List.all_eq_true, decide_eq_true_eq, Bool.and_eq_true] using h
  have ht := closed hkS hk
  exact SFunc.RunP.not_halted hS ht.1 ht.2 run ho

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
