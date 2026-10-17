import Blanc.Lift.Usdc.ProxyReach
import Blanc.Lift.Usdc.LibSpawns

/-!
# The successful runs of the proxy certificate (C2b)

`proxy_halt`: a run of the proxy certificate from entry `0` that halts runs `_delegate`'s
`DELEGATECALL` (`DelegateStep`), or its caller is the admin word and either the dispatcher selected
`upgradeTo`/`upgradeToAndCall`/`changeAdmin` or the frame's storage maps are unchanged (the admin's
`implementation()`/`admin()` getters).  Big-step inversion of the checked trees (`rpw_*`, `ri_*`);
the getter bodies are crossed by their specs, and quiet regions by `SFunc.RunP.getStor_of_quiet`.
-/

namespace Blanc.Lift

open Jaune Blanc

section Kit

variable {P : Sevm → Devm → Ninst → Devm → Prop} {fs : List SFunc} {sevm : Sevm} {b : Devm}
  {S : List B256} {M : Mem} {G : Nat} {f g : SFunc} {o : Outcome}

theorem rpw_branchTo {k : Nat} {dd w : B256}
    (run : SFunc.RunP P fs sevm (St b (dd :: w :: S) M G) (.branchTo f k) o) :
    (w = 0 ∧ ∃ G', SFunc.RunP P fs sevm (St b S M G') f o) ∨
      (w ≠ 0 ∧ ∃ g G', fs[k]? = some g ∧ SFunc.RunP P fs sevm (St b S M G') g o) := by
  cases run with
  | toZero d0 h k =>
      obtain ⟨-, hw, e⟩ := St.of_pop2 h
      exact .inl ⟨hw, _, e ▸ k⟩
  | toSucc d0 w0 hw hk h k =>
      obtain ⟨-, hw', e⟩ := St.of_pop2 h
      exact .inr ⟨hw' ▸ hw, _, _, hk, e ▸ k⟩

theorem rpw_jump {k : Nat} {dd : B256}
    (run : SFunc.RunP P fs sevm (St b (dd :: S) M G) (.jump k) o) :
    ∃ g G', fs[k]? = some g ∧ SFunc.RunP P fs sevm (St b S M G') g o := by
  cases run with
  | jump d0 hk h k => exact ⟨_, _, hk, (St.of_pop1 h).2 ▸ k⟩

theorem rpw_call {k : Nat} {dd : B256} (hk : fs[k]? = some g)
    (run : SFunc.RunP P fs sevm (St b (dd :: S) M G) (.callNext k f) o) :
    ∃ G', (∃ D, SFunc.RunP P fs sevm (St b S M G') g (.returned D) ∧
        SFunc.RunP P fs sevm D f o) ∨
      (∃ D, SFunc.RunP P fs sevm (St b S M G') g (.halted D) ∧ o = .halted D) := by
  cases run with
  | callHalt d0 hk' h hr =>
      rw [hk] at hk'
      cases hk'
      exact ⟨_, .inr ⟨_, (St.of_pop1 h).2 ▸ hr, rfl⟩⟩
  | callRet d0 hk' h hr k =>
      rw [hk] at hk'
      cases hk'
      exact ⟨_, .inl ⟨_, (St.of_pop1 h).2 ▸ hr, k⟩⟩

/-- A call to a callee that cannot halt: it returns, then the continuation runs. -/
theorem rpw_callOver {S' : List Nat} (hS : NoHaltSet fs S' = true) {k : Nat} {dd : B256}
    (hk : fs[k]? = some g) (hkS : k ∈ S')
    (run : SFunc.RunP P fs sevm (St b (dd :: S) M G) (.callNext k f) o) :
    ∃ G' D, SFunc.RunP P fs sevm (St b S M G') g (.returned D) ∧ SFunc.RunP P fs sevm D f o := by
  obtain ⟨G', ⟨D, callee, rest⟩ | ⟨D, callee, -⟩⟩ := rpw_call hk run
  · exact ⟨G', D, callee, rest⟩
  · exact (SFunc.RunP.not_halted_entry hS hkS hk callee rfl).elim

theorem rpw_revert {d : Devm} (run : SFunc.RunP P fs sevm d (.last .revert) o) : False := by
  cases run with
  | last h => exact Linst.not_run_revert_ok h

end Kit

end Blanc.Lift

namespace Blanc.Lift.Usdc.Proxy

open Jaune Blanc Blanc.Lift

/-- A run of the certificate passes `_delegate`'s `DELEGATECALL`. -/
def DelegateStep (P : Sevm → Devm → Ninst → Devm → Prop) (sevm : Sevm) : Prop :=
  ∃ d d1, P sevm d (.exec .delegatecall) d1

theorem getters_noHalt : NoHaltSet prog getterEntries = true := by decide
theorem ent3_admin_noHalt : NoHaltSet prog [14, 15] = true := by decide
theorem ent3_admin_quiet : QuietSet prog [14, 15] = true := by decide
theorem ent5_admin_quiet : QuietSet prog [8, 20] = true := by decide
theorem empty_quiet : QuietSet prog [] = true := by decide

theorem getStor_St (b : Devm) (S : List B256) (M : Mem) (G : Nat) :
    Devm.getStor (St b S M G) = Devm.getStor b := rfl

section Halt

variable {P : Sevm → Devm → Ninst → Devm → Prop} (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
  {sevm : Sevm} {S : List B256} {M : Mem} {G : Nat} {o : Outcome}

include hP

/-- A `_fallback()` copy never returns. -/
theorem fb_not_returned (hfork : CoveredFork sevm.benvStat.fork) {b : Devm} {d : Nat} {D : Devm}
    (hd : prog[d]? = some t_0682_c23)
    (run : SFunc.RunP P prog sevm (St b S M G) (fbTree d) (.returned D)) : False := by
  unfold fbTree at run
  obtain ⟨_, run⟩ := rpw_dest run
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, D1, callee, run⟩ := rpw_callOver getters_noHalt (k := 22) rfl (by decide) run
  obtain ⟨-, _, rfl⟩ := willFallback_ret hP hfork callee
  obtain ⟨_, run⟩ := rpw_dest run
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, D2, callee, run⟩ := rpw_callOver getters_noHalt (k := 14) rfl (by decide) run
  obtain ⟨_, rfl⟩ := impl_ret hP hfork callee
  obtain ⟨_, run⟩ := rpw_dest run
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨g, _, hg, run⟩ := rpw_jump run
  rw [hd] at hg
  cases hg
  exact SFunc.RunP.not_returned_of_haltsOnly run (by decide)

/-- A halting `_fallback()` copy runs `_delegate`'s `DELEGATECALL`. -/
theorem fb_halted (hfork : CoveredFork sevm.benvStat.fork) {b : Devm} {d : Nat} {D : Devm}
    (hd : prog[d]? = some t_0682_c23)
    (run : SFunc.RunP P prog sevm (St b S M G) (fbTree d) (.halted D)) : DelegateStep P sevm := by
  unfold fbTree at run
  obtain ⟨_, run⟩ := rpw_dest run
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, D1, callee, run⟩ := rpw_callOver getters_noHalt (k := 22) rfl (by decide) run
  obtain ⟨-, _, rfl⟩ := willFallback_ret hP hfork callee
  obtain ⟨_, run⟩ := rpw_dest run
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, D2, callee, run⟩ := rpw_callOver getters_noHalt (k := 14) rfl (by decide) run
  obtain ⟨_, rfl⟩ := impl_ret hP hfork callee
  obtain ⟨_, run⟩ := rpw_dest run
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨g, _, hg, run⟩ := rpw_jump run
  rw [hd] at hg
  cases hg
  unfold t_0682_c23 at run
  obtain ⟨_, run⟩ := rpw_dest run
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_calldatasize (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_calldatacopy (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_calldatasize (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, _, rfl⟩ := ri_gas (hP s)
  obtain ⟨d1, s, -⟩ := rpw_next run
  exact ⟨_, d1, s⟩

theorem ent1_run (hfork : CoveredFork sevm.benvStat.fork) {b : Devm}
    (run : SFunc.RunP P prog sevm (St b S M G) t_0213_c1 o) :
    sevm.caller = (b.getStorVal sevm.currentTarget adminSlot).toAdr ∨
      ∃ (b₁ : Devm) (S₁ : List B256) (M₁ : Mem) (G₁ : Nat), b₁.state = b.state ∧
        SFunc.RunP P prog sevm (St b₁ S₁ M₁ G₁) (fbTree 26) o := by
  unfold t_0213_c1 at run
  obtain ⟨_, run⟩ := rpw_dest run
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, D, callee, run⟩ := rpw_callOver getters_noHalt (k := 8) rfl (by decide) run
  obtain ⟨_, rfl⟩ := admin_ret hP hfork callee
  unfold t_021b_c1 at run
  obtain ⟨_, run⟩ := rpw_dest run
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_and (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_caller (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_and (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_eq (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_iszero (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  rcases rpw_branch run with ⟨hz, _, run⟩ | ⟨-, _, run⟩
  · exact .inl ((masked_eq_iff _ _).mp (eqCheck_ne_zero (iszero_eq_zero hz)))
  unfold t_025c_c1 at run
  obtain ⟨_, run⟩ := rpw_dest run
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨g, _, hg, run⟩ := rpw_jump run
  obtain rfl : g = fbTree 26 := Option.some.inj (hg.symm.trans rfl)
  exact .inr ⟨_, _, _, _, NodeWalk.afterSload_state _ _ _, run⟩

theorem ent2_run (hfork : CoveredFork sevm.benvStat.fork) {b : Devm}
    (run : SFunc.RunP P prog sevm (St b S M G) t_0268_c2 o) :
    sevm.caller = (b.getStorVal sevm.currentTarget adminSlot).toAdr ∨
      ∃ (b₁ : Devm) (S₁ : List B256) (M₁ : Mem) (G₁ : Nat), b₁.state = b.state ∧
        SFunc.RunP P prog sevm (St b₁ S₁ M₁ G₁) (fbTree 27) o := by
  unfold t_0268_c2 at run
  obtain ⟨_, run⟩ := rpw_dest run
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, D, callee, run⟩ := rpw_callOver getters_noHalt (k := 8) rfl (by decide) run
  obtain ⟨_, rfl⟩ := admin_ret hP hfork callee
  unfold t_0270_c2 at run
  obtain ⟨_, run⟩ := rpw_dest run
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_and (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_caller (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_and (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_eq (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_iszero (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  rcases rpw_branch run with ⟨hz, _, run⟩ | ⟨-, _, run⟩
  · exact .inl ((masked_eq_iff _ _).mp (eqCheck_ne_zero (iszero_eq_zero hz)))
  unfold t_02fa_c2 at run
  obtain ⟨_, run⟩ := rpw_dest run
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨g, _, hg, run⟩ := rpw_jump run
  obtain rfl : g = fbTree 27 := Option.some.inj (hg.symm.trans rfl)
  exact .inr ⟨_, _, _, _, NodeWalk.afterSload_state _ _ _, run⟩

theorem ent3_run (hfork : CoveredFork sevm.benvStat.fork) {b : Devm}
    (run : SFunc.RunP P prog sevm (St b S M G) t_0308_c3 o) :
    (sevm.caller = (b.getStorVal sevm.currentTarget adminSlot).toAdr ∧
      Devm.getStor (Outcome.devm o) = Devm.getStor b) ∨
      ∃ (b₁ : Devm) (S₁ : List B256) (M₁ : Mem) (G₁ : Nat), b₁.state = b.state ∧
        SFunc.RunP P prog sevm (St b₁ S₁ M₁ G₁) (fbTree 28) o := by
  unfold t_0308_c3 at run
  obtain ⟨_, run⟩ := rpw_dest run
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, D, callee, run⟩ := rpw_callOver getters_noHalt (k := 8) rfl (by decide) run
  obtain ⟨_, rfl⟩ := admin_ret hP hfork callee
  unfold t_0312_c3 at run
  obtain ⟨_, run⟩ := rpw_dest run
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_and (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_caller (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_and (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_eq (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_iszero (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  rcases rpw_branch run with ⟨hz, _, run⟩ | ⟨-, _, run⟩
  · refine .inl ⟨(masked_eq_iff _ _).mp (eqCheck_ne_zero (iszero_eq_zero hz)), ?_⟩
    rw [SFunc.RunP.getStor_of_quiet hP ent3_admin_quiet hfork (by decide) (by decide) run, getStor_St]
    funext a
    exact afterSload_getStor _ _ _ _
  unfold t_0354_c3 at run
  obtain ⟨_, run⟩ := rpw_dest run
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨g, _, hg, run⟩ := rpw_jump run
  obtain rfl : g = fbTree 28 := Option.some.inj (hg.symm.trans rfl)
  exact .inr ⟨_, _, _, _, NodeWalk.afterSload_state _ _ _, run⟩

theorem ent4_run (hfork : CoveredFork sevm.benvStat.fork) {b : Devm}
    (run : SFunc.RunP P prog sevm (St b S M G) t_0360_c4 o) :
    sevm.caller = (b.getStorVal sevm.currentTarget adminSlot).toAdr ∨
      ∃ (b₁ : Devm) (S₁ : List B256) (M₁ : Mem) (G₁ : Nat), b₁.state = b.state ∧
        SFunc.RunP P prog sevm (St b₁ S₁ M₁ G₁) (fbTree 29) o := by
  unfold t_0360_c4 at run
  obtain ⟨_, run⟩ := rpw_dest run
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, D, callee, run⟩ := rpw_callOver getters_noHalt (k := 8) rfl (by decide) run
  obtain ⟨_, rfl⟩ := admin_ret hP hfork callee
  unfold t_0368_c4 at run
  obtain ⟨_, run⟩ := rpw_dest run
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_and (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_caller (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_and (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_eq (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_iszero (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  rcases rpw_branch run with ⟨hz, _, run⟩ | ⟨-, _, run⟩
  · exact .inl ((masked_eq_iff _ _).mp (eqCheck_ne_zero (iszero_eq_zero hz)))
  unfold t_0512_c4 at run
  obtain ⟨_, run⟩ := rpw_dest run
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨g, _, hg, run⟩ := rpw_jump run
  obtain rfl : g = fbTree 29 := Option.some.inj (hg.symm.trans rfl)
  exact .inr ⟨_, _, _, _, NodeWalk.afterSload_state _ _ _, run⟩

theorem ent5_run (hfork : CoveredFork sevm.benvStat.fork) {b : Devm}
    (run : SFunc.RunP P prog sevm (St b S M G) t_051e_c5 o) :
    (sevm.caller = (b.getStorVal sevm.currentTarget adminSlot).toAdr ∧
      Devm.getStor (Outcome.devm o) = Devm.getStor b) ∨
      ∃ (b₁ : Devm) (S₁ : List B256) (M₁ : Mem) (G₁ : Nat), b₁.state = b.state ∧
        SFunc.RunP P prog sevm (St b₁ S₁ M₁ G₁) (fbTree 30) o := by
  unfold t_051e_c5 at run
  obtain ⟨_, run⟩ := rpw_dest run
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, D, callee, run⟩ := rpw_callOver getters_noHalt (k := 8) rfl (by decide) run
  obtain ⟨_, rfl⟩ := admin_ret hP hfork callee
  unfold t_0528_c5 at run
  obtain ⟨_, run⟩ := rpw_dest run
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_and (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_caller (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_and (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_eq (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_iszero (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  rcases rpw_branch run with ⟨hz, _, run⟩ | ⟨-, _, run⟩
  · refine .inl ⟨(masked_eq_iff _ _).mp (eqCheck_ne_zero (iszero_eq_zero hz)), ?_⟩
    rw [SFunc.RunP.getStor_of_quiet hP ent5_admin_quiet hfork (by decide) (by decide) run, getStor_St]
    funext a
    exact afterSload_getStor _ _ _ _
  unfold t_056a_c5 at run
  obtain ⟨_, run⟩ := rpw_dest run
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨g, _, hg, run⟩ := rpw_jump run
  obtain rfl : g = fbTree 30 := Option.some.inj (hg.symm.trans rfl)
  exact .inr ⟨_, _, _, _, NodeWalk.afterSload_state _ _ _, run⟩

theorem sel33_halt (hfork : CoveredFork sevm.benvStat.fork) {b : Devm} {x : B256} {post : Devm}
    (run : SFunc.RunP P prog sevm (St b (x :: S) M G) t_0077_c33 (.halted post)) :
    DelegateStep P sevm ∨ sevm.caller = (b.getStorVal sevm.currentTarget adminSlot).toAdr := by
  unfold t_0077_c33 at run
  obtain ⟨_, run⟩ := rpw_dest run
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_callvalue (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_iszero (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  rcases rpw_branch run with ⟨-, _, run⟩ | ⟨-, _, run⟩
  ·
    unfold t_007f_c33 at run
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
    exact (rpw_revert run).elim
  unfold t_0083_c33 at run
  obtain ⟨_, run⟩ := rpw_dest run
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_pop (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_calldatasize (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_sub (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_add (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_calldataload (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_and (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_add (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_swap (n := 2) rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_swap (n := 1) rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_pop (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_pop (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_pop (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, ⟨D, callee, cont⟩ | ⟨D, callee, hpost⟩⟩ := rpw_call (k := 1) rfl run
  · rcases ent1_run hP hfork callee with h | ⟨_, _, _, _, -, fb⟩
    · exact .inr h
    · exact (fb_not_returned hP hfork rfl fb).elim
  · rcases ent1_run hP hfork callee with h | ⟨_, _, _, _, -, fb⟩
    · exact .inr h
    · exact .inl (fb_halted hP hfork rfl fb)

theorem sel34_halt (hfork : CoveredFork sevm.benvStat.fork) {b : Devm} {x : B256} {post : Devm}
    (run : SFunc.RunP P prog sevm (St b (x :: S) M G) t_00ba_c34 (.halted post)) :
    DelegateStep P sevm ∨ sevm.caller = (b.getStorVal sevm.currentTarget adminSlot).toAdr := by
  unfold t_00ba_c34 at run
  obtain ⟨_, run⟩ := rpw_dest run
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_calldatasize (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_sub (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_add (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_calldataload (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_and (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_add (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_swap (n := 2) rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_swap (n := 1) rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_calldataload (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_add (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_add (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_calldataload (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_add (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_swap (n := 1) rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_swap (n := 1) rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_swap (n := 2) rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_swap (n := 3) rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_swap (n := 1) rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_swap (n := 2) rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_swap (n := 3) rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_pop (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_pop (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_pop (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, ⟨D, callee, cont⟩ | ⟨D, callee, hpost⟩⟩ := rpw_call (k := 2) rfl run
  · rcases ent2_run hP hfork callee with h | ⟨_, _, _, _, -, fb⟩
    · exact .inr h
    · exact (fb_not_returned hP hfork rfl fb).elim
  · rcases ent2_run hP hfork callee with h | ⟨_, _, _, _, -, fb⟩
    · exact .inr h
    · exact .inl (fb_halted hP hfork rfl fb)

theorem sel35_halt (hfork : CoveredFork sevm.benvStat.fork) {b : Devm} {x : B256} {post : Devm}
    (run : SFunc.RunP P prog sevm (St b (x :: S) M G) t_0108_c35 (.halted post)) :
    DelegateStep P sevm ∨ (sevm.caller = (b.getStorVal sevm.currentTarget adminSlot).toAdr ∧
      Devm.getStor post = Devm.getStor b) := by
  unfold t_0108_c35 at run
  obtain ⟨_, run⟩ := rpw_dest run
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_callvalue (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_iszero (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  rcases rpw_branch run with ⟨-, _, run⟩ | ⟨-, _, run⟩
  ·
    unfold t_0110_c35 at run
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
    exact (rpw_revert run).elim
  unfold t_0114_c35 at run
  obtain ⟨_, run⟩ := rpw_dest run
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_pop (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, ⟨D, callee, cont⟩ | ⟨D, callee, hpost⟩⟩ := rpw_call (k := 3) rfl run
  · rcases ent3_run hP hfork callee with ⟨h, hs⟩ | ⟨_, _, _, _, -, fb⟩
    · refine .inr ⟨h, ?_⟩
      exact (SFunc.RunP.getStor_of_quiet hP empty_quiet hfork (by decide) (by decide) cont).trans hs
    · exact (fb_not_returned hP hfork rfl fb).elim
  · rcases ent3_run hP hfork callee with ⟨h, hs⟩ | ⟨_, _, _, _, -, fb⟩
    · cases hpost
      exact .inr ⟨h, hs⟩
    · exact .inl (fb_halted hP hfork rfl fb)

theorem sel36_halt (hfork : CoveredFork sevm.benvStat.fork) {b : Devm} {x : B256} {post : Devm}
    (run : SFunc.RunP P prog sevm (St b (x :: S) M G) t_015f_c36 (.halted post)) :
    DelegateStep P sevm ∨ sevm.caller = (b.getStorVal sevm.currentTarget adminSlot).toAdr := by
  unfold t_015f_c36 at run
  obtain ⟨_, run⟩ := rpw_dest run
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_callvalue (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_iszero (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  rcases rpw_branch run with ⟨-, _, run⟩ | ⟨-, _, run⟩
  ·
    unfold t_0167_c36 at run
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
    exact (rpw_revert run).elim
  unfold t_016b_c36 at run
  obtain ⟨_, run⟩ := rpw_dest run
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_pop (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_calldatasize (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_sub (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_add (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_calldataload (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_and (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_add (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_swap (n := 2) rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_swap (n := 1) rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_pop (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_pop (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_pop (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, ⟨D, callee, cont⟩ | ⟨D, callee, hpost⟩⟩ := rpw_call (k := 4) rfl run
  · rcases ent4_run hP hfork callee with h | ⟨_, _, _, _, -, fb⟩
    · exact .inr h
    · exact (fb_not_returned hP hfork rfl fb).elim
  · rcases ent4_run hP hfork callee with h | ⟨_, _, _, _, -, fb⟩
    · exact .inr h
    · exact .inl (fb_halted hP hfork rfl fb)

theorem sel37_halt (hfork : CoveredFork sevm.benvStat.fork) {b : Devm} {x : B256} {post : Devm}
    (run : SFunc.RunP P prog sevm (St b (x :: S) M G) t_01a2_c37 (.halted post)) :
    DelegateStep P sevm ∨ (sevm.caller = (b.getStorVal sevm.currentTarget adminSlot).toAdr ∧
      Devm.getStor post = Devm.getStor b) := by
  unfold t_01a2_c37 at run
  obtain ⟨_, run⟩ := rpw_dest run
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_callvalue (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_iszero (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  rcases rpw_branch run with ⟨-, _, run⟩ | ⟨-, _, run⟩
  ·
    unfold t_01aa_c37 at run
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
    exact (rpw_revert run).elim
  unfold t_01ae_c37 at run
  obtain ⟨_, run⟩ := rpw_dest run
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_pop (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, ⟨D, callee, cont⟩ | ⟨D, callee, hpost⟩⟩ := rpw_call (k := 5) rfl run
  · rcases ent5_run hP hfork callee with ⟨h, hs⟩ | ⟨_, _, _, _, -, fb⟩
    · refine .inr ⟨h, ?_⟩
      exact (SFunc.RunP.getStor_of_quiet hP empty_quiet hfork (by decide) (by decide) cont).trans hs
    · exact (fb_not_returned hP hfork rfl fb).elim
  · rcases ent5_run hP hfork callee with ⟨h, hs⟩ | ⟨_, _, _, _, -, fb⟩
    · cases hpost
      exact .inr ⟨h, hs⟩
    · exact .inl (fb_halted hP hfork rfl fb)

/-- **The successful runs of the proxy certificate.** -/
theorem proxy_halt (hfork : CoveredFork sevm.benvStat.fork) {b : Devm} {post : Devm}
    (run : SFunc.RunP P prog sevm (St b S M G) t_0000_c0 (.halted post)) :
    DelegateStep P sevm ∨
      (sevm.caller = (b.getStorVal sevm.currentTarget adminSlot).toAdr ∧
        (dispatchWord sevm = Bytes.toB256 [0x36, 0x59, 0xcf, 0xe6] ∨
          dispatchWord sevm = Bytes.toB256 [0x4f, 0x1e, 0xf2, 0x86] ∨
          dispatchWord sevm = Bytes.toB256 [0x8f, 0x28, 0x39, 0x70] ∨
          Devm.getStor post = Devm.getStor b)) := by
  unfold t_0000_c0 at run
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_mstore (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_calldatasize (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_lt (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  rcases rpw_branch run with ⟨-, _, run⟩ | ⟨-, _, run⟩
  ·
    unfold t_000d_c0 at run
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_calldataload (hP s)
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (hP s)
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_div (hP s)
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_and (hP s)
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_eq (hP s)
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
    rcases rpw_branchTo run with ⟨-, _, run⟩ | ⟨h, g, _, hg, run⟩
    swap
    · obtain rfl : g = t_0077_c33 := Option.some.inj (hg.symm.trans rfl)
      exact (sel33_halt hP hfork run).imp id fun ha => ⟨ha, .inl (eqCheck_ne_zero h).symm⟩
    unfold t_0041_c0 at run
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_eq (hP s)
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
    rcases rpw_branchTo run with ⟨-, _, run⟩ | ⟨h, g, _, hg, run⟩
    swap
    · obtain rfl : g = t_00ba_c34 := Option.some.inj (hg.symm.trans rfl)
      exact (sel34_halt hP hfork run).imp id fun ha => ⟨ha, .inr (.inl (eqCheck_ne_zero h).symm)⟩
    unfold t_004c_c0 at run
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_eq (hP s)
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
    rcases rpw_branchTo run with ⟨-, _, run⟩ | ⟨-, g, _, hg, run⟩
    swap
    · obtain rfl : g = t_0108_c35 := Option.some.inj (hg.symm.trans rfl)
      exact (sel35_halt hP hfork run).imp id fun ha => ⟨ha.1, .inr (.inr (.inr ha.2))⟩
    unfold t_0057_c0 at run
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_eq (hP s)
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
    rcases rpw_branchTo run with ⟨-, _, run⟩ | ⟨h, g, _, hg, run⟩
    swap
    · obtain rfl : g = t_015f_c36 := Option.some.inj (hg.symm.trans rfl)
      exact (sel36_halt hP hfork run).imp id fun ha =>
        ⟨ha, .inr (.inr (.inl (eqCheck_ne_zero h).symm))⟩
    unfold t_0062_c0 at run
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_eq (hP s)
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
    rcases rpw_branchTo run with ⟨-, _, run⟩ | ⟨-, g, _, hg, run⟩
    swap
    · obtain rfl : g = t_01a2_c37 := Option.some.inj (hg.symm.trans rfl)
      exact (sel37_halt hP hfork run).imp id fun ha => ⟨ha.1, .inr (.inr (.inr ha.2))⟩
    unfold t_006d_c0 at run
    obtain ⟨_, run⟩ := rpw_dest run
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
    obtain ⟨g, _, hg, run⟩ := rpw_jump run
    obtain rfl : g = fbTree 23 := Option.some.inj (hg.symm.trans rfl)
    exact .inl (fb_halted hP hfork rfl run)
  unfold t_006d_c0_1 at run
  obtain ⟨_, run⟩ := rpw_dest run
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨g, _, hg, run⟩ := rpw_jump run
  obtain rfl : g = fbTree 24 := Option.some.inj (hg.symm.trans rfl)
  exact .inl (fb_halted hP hfork rfl run)

end Halt

end Blanc.Lift.Usdc.Proxy
