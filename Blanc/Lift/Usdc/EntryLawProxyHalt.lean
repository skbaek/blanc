import Blanc.Lift.Usdc.ProxyReachH
import Blanc.Lift.Usdc.ProxyHalt
import Blanc.Lift.InvWalkLegacy

/-!
# The successful runs of the proxy certificate on historical forks

`proxy_haltH`: `proxy_halt` under `rules.bal = none` in place of `CoveredFork`, inverting `SLOAD` under the
actual access schedule (`ri_sloadH`, `afterSloadH`). A run of the certificate from entry `0` that halts
passes `_delegate`'s `DELEGATECALL` (`DelegateStep`), or its caller is the admin word. The covered-fork
walk's other clause, what the admin's getters keep, has no use here. Near-copy of `ProxyHalt`, as `ProxyReachH`
is of `ProxyReach`.
-/

namespace Blanc.Lift.Usdc.Proxy

open Jaune Blanc Blanc.Lift

/-- The proxy's five admin selectors: `upgradeTo`, `upgradeToAndCall`, `implementation`, `changeAdmin`, `admin`. -/
def adminSelectors : List B256 := [0x3659cfe6, 0x4f1ef286, 0x5c60da1b, 0x8f283970, 0xf851a440]

/-- The dispatcher's comparison that hits an admin selector names it. -/
theorem admin_of_hit {sevm : Sevm} {c : B256}
    (hit : B256.eqCheck c (Bytes.toB256 [255, 255, 255, 255] &&&
      Sevm.dataWord sevm (Bytes.toB256 [0]) /
        Bytes.toB256 [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]) ≠ 0)
    (hc : c ∈ adminSelectors) :
    Blanc.Sevm.selector sevm ∈ adminSelectors := by
  rw [legacy_selector_word] at hit
  rw [← B256.eq_of_eqCheck_ne_zero hit]
  exact hc

section Halt

variable {P : Sevm → Devm → Ninst → Devm → Prop} (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
  {sevm : Sevm} {S : List B256} {M : Mem} {G : Nat} {o : Outcome}

include hP

/-- A `_fallback()` copy never returns. -/
theorem fb_not_returnedH (bal : sevm.benvStat.rules.bal = none) {b : Devm} {d : Nat} {D : Devm}
    (hd : prog[d]? = some t_0682_c23)
    (run : SFunc.RunP P prog sevm (St b S M G) (fbTree d) (.returned D)) : False := by
  unfold fbTree at run
  obtain ⟨_, run⟩ := rpw_dest run
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, D1, callee, run⟩ := rpw_callOver getters_noHalt (k := 22) rfl (by decide) run
  obtain ⟨-, _, rfl⟩ := willFallback_retH hP bal callee
  obtain ⟨_, run⟩ := rpw_dest run
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, D2, callee, run⟩ := rpw_callOver getters_noHalt (k := 14) rfl (by decide) run
  obtain ⟨_, rfl⟩ := impl_retH hP bal callee
  obtain ⟨_, run⟩ := rpw_dest run
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨g, _, hg, run⟩ := rpw_jump run
  rw [hd] at hg
  cases hg
  exact SFunc.RunP.not_returned_of_haltsOnly run (by decide)

/-- A halting `_fallback()` copy runs `_delegate`'s `DELEGATECALL`. -/
theorem fb_haltedH (bal : sevm.benvStat.rules.bal = none) {b : Devm} {d : Nat} {D : Devm}
    (hd : prog[d]? = some t_0682_c23)
    (run : SFunc.RunP P prog sevm (St b S M G) (fbTree d) (.halted D)) :
    DelegateStep P sevm b D := by
  unfold fbTree at run
  obtain ⟨_, run⟩ := rpw_dest run
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, D1, callee, run⟩ := rpw_callOver getters_noHalt (k := 22) rfl (by decide) run
  obtain ⟨notAdmin, _, rfl⟩ := willFallback_retH hP bal callee
  obtain ⟨_, run⟩ := rpw_dest run
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, D2, callee, run⟩ := rpw_callOver getters_noHalt (k := 14) rfl (by decide) run
  obtain ⟨_, rfl⟩ := impl_retH hP bal callee
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
  obtain ⟨d1, s, tail⟩ := rpw_next run
  rw [getStorVal_afterSloadH] at s
  exact ⟨notAdmin, _, _, _, _, _, d1, by rw [afterSloadH_state, afterSloadH_state],
    s, tail⟩

theorem ent1_runH (bal : sevm.benvStat.rules.bal = none) {b : Devm}
    (run : SFunc.RunP P prog sevm (St b S M G) t_0213_c1 o) :
    sevm.caller = (b.getStorVal sevm.currentTarget adminSlot).toAdr ∨
      ∃ (b₁ : Devm) (S₁ : List B256) (M₁ : Mem) (G₁ : Nat), b₁.state = b.state ∧
        SFunc.RunP P prog sevm (St b₁ S₁ M₁ G₁) (fbTree 26) o := by
  unfold t_0213_c1 at run
  obtain ⟨_, run⟩ := rpw_dest run
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, D, callee, run⟩ := rpw_callOver getters_noHalt (k := 8) rfl (by decide) run
  obtain ⟨_, rfl⟩ := admin_retH hP bal callee
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
  · exact .inl ((masked_eq_iff _ _).mp (B256.eq_of_eqCheck_ne_zero (iszero_eq_zero hz)))
  unfold t_025c_c1 at run
  obtain ⟨_, run⟩ := rpw_dest run
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨g, _, hg, run⟩ := rpw_jump run
  obtain rfl : g = fbTree 26 := Option.some.inj (hg.symm.trans rfl)
  exact .inr ⟨_, _, _, _, afterSloadH_state _ _ _, run⟩

theorem ent2_runH (bal : sevm.benvStat.rules.bal = none) {b : Devm}
    (run : SFunc.RunP P prog sevm (St b S M G) t_0268_c2 o) :
    sevm.caller = (b.getStorVal sevm.currentTarget adminSlot).toAdr ∨
      ∃ (b₁ : Devm) (S₁ : List B256) (M₁ : Mem) (G₁ : Nat), b₁.state = b.state ∧
        SFunc.RunP P prog sevm (St b₁ S₁ M₁ G₁) (fbTree 27) o := by
  unfold t_0268_c2 at run
  obtain ⟨_, run⟩ := rpw_dest run
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, D, callee, run⟩ := rpw_callOver getters_noHalt (k := 8) rfl (by decide) run
  obtain ⟨_, rfl⟩ := admin_retH hP bal callee
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
  · exact .inl ((masked_eq_iff _ _).mp (B256.eq_of_eqCheck_ne_zero (iszero_eq_zero hz)))
  unfold t_02fa_c2 at run
  obtain ⟨_, run⟩ := rpw_dest run
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨g, _, hg, run⟩ := rpw_jump run
  obtain rfl : g = fbTree 27 := Option.some.inj (hg.symm.trans rfl)
  exact .inr ⟨_, _, _, _, afterSloadH_state _ _ _, run⟩

theorem ent3_runH (bal : sevm.benvStat.rules.bal = none) {b : Devm}
    (run : SFunc.RunP P prog sevm (St b S M G) t_0308_c3 o) :
    sevm.caller = (b.getStorVal sevm.currentTarget adminSlot).toAdr ∨
      ∃ (b₁ : Devm) (S₁ : List B256) (M₁ : Mem) (G₁ : Nat), b₁.state = b.state ∧
        SFunc.RunP P prog sevm (St b₁ S₁ M₁ G₁) (fbTree 28) o := by
  unfold t_0308_c3 at run
  obtain ⟨_, run⟩ := rpw_dest run
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, D, callee, run⟩ := rpw_callOver getters_noHalt (k := 8) rfl (by decide) run
  obtain ⟨_, rfl⟩ := admin_retH hP bal callee
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
  · exact .inl ((masked_eq_iff _ _).mp (B256.eq_of_eqCheck_ne_zero (iszero_eq_zero hz)))
  unfold t_0354_c3 at run
  obtain ⟨_, run⟩ := rpw_dest run
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨g, _, hg, run⟩ := rpw_jump run
  obtain rfl : g = fbTree 28 := Option.some.inj (hg.symm.trans rfl)
  exact .inr ⟨_, _, _, _, afterSloadH_state _ _ _, run⟩

theorem ent4_runH (bal : sevm.benvStat.rules.bal = none) {b : Devm}
    (run : SFunc.RunP P prog sevm (St b S M G) t_0360_c4 o) :
    sevm.caller = (b.getStorVal sevm.currentTarget adminSlot).toAdr ∨
      ∃ (b₁ : Devm) (S₁ : List B256) (M₁ : Mem) (G₁ : Nat), b₁.state = b.state ∧
        SFunc.RunP P prog sevm (St b₁ S₁ M₁ G₁) (fbTree 29) o := by
  unfold t_0360_c4 at run
  obtain ⟨_, run⟩ := rpw_dest run
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, D, callee, run⟩ := rpw_callOver getters_noHalt (k := 8) rfl (by decide) run
  obtain ⟨_, rfl⟩ := admin_retH hP bal callee
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
  · exact .inl ((masked_eq_iff _ _).mp (B256.eq_of_eqCheck_ne_zero (iszero_eq_zero hz)))
  unfold t_0512_c4 at run
  obtain ⟨_, run⟩ := rpw_dest run
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨g, _, hg, run⟩ := rpw_jump run
  obtain rfl : g = fbTree 29 := Option.some.inj (hg.symm.trans rfl)
  exact .inr ⟨_, _, _, _, afterSloadH_state _ _ _, run⟩

theorem ent5_runH (bal : sevm.benvStat.rules.bal = none) {b : Devm}
    (run : SFunc.RunP P prog sevm (St b S M G) t_051e_c5 o) :
    sevm.caller = (b.getStorVal sevm.currentTarget adminSlot).toAdr ∨
      ∃ (b₁ : Devm) (S₁ : List B256) (M₁ : Mem) (G₁ : Nat), b₁.state = b.state ∧
        SFunc.RunP P prog sevm (St b₁ S₁ M₁ G₁) (fbTree 30) o := by
  unfold t_051e_c5 at run
  obtain ⟨_, run⟩ := rpw_dest run
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, D, callee, run⟩ := rpw_callOver getters_noHalt (k := 8) rfl (by decide) run
  obtain ⟨_, rfl⟩ := admin_retH hP bal callee
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
  · exact .inl ((masked_eq_iff _ _).mp (B256.eq_of_eqCheck_ne_zero (iszero_eq_zero hz)))
  unfold t_056a_c5 at run
  obtain ⟨_, run⟩ := rpw_dest run
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨g, _, hg, run⟩ := rpw_jump run
  obtain rfl : g = fbTree 30 := Option.some.inj (hg.symm.trans rfl)
  exact .inr ⟨_, _, _, _, afterSloadH_state _ _ _, run⟩

theorem sel33_haltH (bal : sevm.benvStat.rules.bal = none) {b : Devm} {x : B256} {post : Devm}
    (run : SFunc.RunP P prog sevm (St b (x :: S) M G) t_0077_c33 (.halted post)) :
    DelegateStep P sevm b post ∨ sevm.caller = (b.getStorVal sevm.currentTarget adminSlot).toAdr := by
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
  · rcases ent1_runH hP bal callee with h | ⟨_, _, _, _, -, fb⟩
    · exact .inr h
    · exact (fb_not_returnedH hP bal rfl fb).elim
  · cases hpost
    rcases ent1_runH hP bal callee with h | ⟨_, _, _, _, hb, fb⟩
    · exact .inr h
    · exact .inl ((fb_haltedH hP bal rfl fb).of_state hb)


theorem sel34_haltH (bal : sevm.benvStat.rules.bal = none) {b : Devm} {x : B256} {post : Devm}
    (run : SFunc.RunP P prog sevm (St b (x :: S) M G) t_00ba_c34 (.halted post)) :
    DelegateStep P sevm b post ∨ sevm.caller = (b.getStorVal sevm.currentTarget adminSlot).toAdr := by
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
  · rcases ent2_runH hP bal callee with h | ⟨_, _, _, _, -, fb⟩
    · exact .inr h
    · exact (fb_not_returnedH hP bal rfl fb).elim
  · cases hpost
    rcases ent2_runH hP bal callee with h | ⟨_, _, _, _, hb, fb⟩
    · exact .inr h
    · exact .inl ((fb_haltedH hP bal rfl fb).of_state hb)


theorem sel35_haltH (bal : sevm.benvStat.rules.bal = none) {b : Devm} {x : B256} {post : Devm}
    (run : SFunc.RunP P prog sevm (St b (x :: S) M G) t_0108_c35 (.halted post)) :
    DelegateStep P sevm b post ∨ sevm.caller = (b.getStorVal sevm.currentTarget adminSlot).toAdr := by
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
  · rcases ent3_runH hP bal callee with h | ⟨_, _, _, _, -, fb⟩
    · exact .inr h
    · exact (fb_not_returnedH hP bal rfl fb).elim
  · cases hpost
    rcases ent3_runH hP bal callee with h | ⟨_, _, _, _, hb, fb⟩
    · exact .inr h
    · exact .inl ((fb_haltedH hP bal rfl fb).of_state hb)


theorem sel36_haltH (bal : sevm.benvStat.rules.bal = none) {b : Devm} {x : B256} {post : Devm}
    (run : SFunc.RunP P prog sevm (St b (x :: S) M G) t_015f_c36 (.halted post)) :
    DelegateStep P sevm b post ∨ sevm.caller = (b.getStorVal sevm.currentTarget adminSlot).toAdr := by
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
  · rcases ent4_runH hP bal callee with h | ⟨_, _, _, _, -, fb⟩
    · exact .inr h
    · exact (fb_not_returnedH hP bal rfl fb).elim
  · cases hpost
    rcases ent4_runH hP bal callee with h | ⟨_, _, _, _, hb, fb⟩
    · exact .inr h
    · exact .inl ((fb_haltedH hP bal rfl fb).of_state hb)


theorem sel37_haltH (bal : sevm.benvStat.rules.bal = none) {b : Devm} {x : B256} {post : Devm}
    (run : SFunc.RunP P prog sevm (St b (x :: S) M G) t_01a2_c37 (.halted post)) :
    DelegateStep P sevm b post ∨ sevm.caller = (b.getStorVal sevm.currentTarget adminSlot).toAdr := by
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
  · rcases ent5_runH hP bal callee with h | ⟨_, _, _, _, -, fb⟩
    · exact .inr h
    · exact (fb_not_returnedH hP bal rfl fb).elim
  · cases hpost
    rcases ent5_runH hP bal callee with h | ⟨_, _, _, _, hb, fb⟩
    · exact .inr h
    · exact .inl ((fb_haltedH hP bal rfl fb).of_state hb)


/-- **The successful runs of the proxy certificate, by selector**: only the five admin selectors have an arm for the
admin word; any other selector reaches the fallback, which reverts for the admin. -/
theorem proxy_haltH_sel (bal : sevm.benvStat.rules.bal = none) {b : Devm} {post : Devm}
    (run : SFunc.RunP P prog sevm (St b S M G) t_0000_c0 (.halted post)) :
    DelegateStep P sevm b post ∨ (sevm.caller = (b.getStorVal sevm.currentTarget adminSlot).toAdr ∧
      Blanc.Sevm.selector sevm ∈ adminSelectors) := by
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
      exact (sel33_haltH hP bal run).imp_right fun c => ⟨c, admin_of_hit h (by decide)⟩
    unfold t_0041_c0 at run
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_eq (hP s)
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
    rcases rpw_branchTo run with ⟨-, _, run⟩ | ⟨h, g, _, hg, run⟩
    swap
    · obtain rfl : g = t_00ba_c34 := Option.some.inj (hg.symm.trans rfl)
      exact (sel34_haltH hP bal run).imp_right fun c => ⟨c, admin_of_hit h (by decide)⟩
    unfold t_004c_c0 at run
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_eq (hP s)
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
    rcases rpw_branchTo run with ⟨-, _, run⟩ | ⟨h, g, _, hg, run⟩
    swap
    · obtain rfl : g = t_0108_c35 := Option.some.inj (hg.symm.trans rfl)
      exact (sel35_haltH hP bal run).imp_right fun c => ⟨c, admin_of_hit h (by decide)⟩
    unfold t_0057_c0 at run
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_eq (hP s)
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
    rcases rpw_branchTo run with ⟨-, _, run⟩ | ⟨h, g, _, hg, run⟩
    swap
    · obtain rfl : g = t_015f_c36 := Option.some.inj (hg.symm.trans rfl)
      exact (sel36_haltH hP bal run).imp_right fun c => ⟨c, admin_of_hit h (by decide)⟩
    unfold t_0062_c0 at run
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_eq (hP s)
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
    rcases rpw_branchTo run with ⟨-, _, run⟩ | ⟨h, g, _, hg, run⟩
    swap
    · obtain rfl : g = t_01a2_c37 := Option.some.inj (hg.symm.trans rfl)
      exact (sel37_haltH hP bal run).imp_right fun c => ⟨c, admin_of_hit h (by decide)⟩
    unfold t_006d_c0 at run
    obtain ⟨_, run⟩ := rpw_dest run
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
    obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
    obtain ⟨g, _, hg, run⟩ := rpw_jump run
    obtain rfl : g = fbTree 23 := Option.some.inj (hg.symm.trans rfl)
    exact .inl (fb_haltedH hP bal rfl run)
  unfold t_006d_c0_1 at run
  obtain ⟨_, run⟩ := rpw_dest run
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨g, _, hg, run⟩ := rpw_jump run
  obtain rfl : g = fbTree 24 := Option.some.inj (hg.symm.trans rfl)
  exact .inl (fb_haltedH hP bal rfl run)

/-- **The successful runs of the proxy certificate.** -/
theorem proxy_haltH (bal : sevm.benvStat.rules.bal = none) {b : Devm} {post : Devm}
    (run : SFunc.RunP P prog sevm (St b S M G) t_0000_c0 (.halted post)) :
    DelegateStep P sevm b post ∨ sevm.caller = (b.getStorVal sevm.currentTarget adminSlot).toAdr :=
  (proxy_haltH_sel hP bal run).imp_right (·.1)

end Halt

end Blanc.Lift.Usdc.Proxy
