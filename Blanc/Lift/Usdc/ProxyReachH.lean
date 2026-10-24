import Blanc.Lift.Usdc.ProxyForward
import Blanc.Lift.HistAccessWalk

/-!
# The proxy walk on historical forks

`proxy_reach` (`ProxyReach.lean`) and its getter and fallback walks
(`ProxyWalk.lean`) take `CoveredFork` only to invert `SLOAD` (`ri_sload`).  This
module restates the walk under `rules.bal = none` alone, inverting `SLOAD` under
the actual access schedule (`ri_sloadH`, successor `afterSloadH`), so it applies
to the proxy frames of a historical (In) history: `proxy_reachH`, and the node
form `proxy_nodeH` from a pc-0 proxy frame without state gas.  The statements
are those of the covered-fork walk with `afterSloadH` for `afterSload`;
`DelegateConf` and `SelfCallConf` are unchanged.
-/

namespace Blanc.Lift.Usdc.Proxy

open Jaune Blanc Blanc.Lift

theorem afterSloadH_state (sevm : Sevm) (b : Devm) (k : B256) :
    (afterSloadH sevm b k).state = b.state := by
  unfold afterSloadH; split
  · exact NodeWalk.afterSload_state sevm b k
  · rfl

section GettersH

variable {P : Sevm → Devm → Ninst → Devm → Prop} (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
  {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat}

include hP

/-- `_admin()`: the admin word, after one storage read. -/
theorem admin_retH (bal : sevm.benvStat.rules.bal = none) {r : B256} {D : Devm}
    (run : SFunc.RunP P prog sevm (St b (r :: S) M G) t_06a8_c8 (.returned D)) :
    ∃ G', D = St (afterSloadH sevm b adminSlot)
      (b.getStorVal sevm.currentTarget adminSlot :: S) M G' := by
  unfold t_06a8_c8 at run
  obtain ⟨_, run⟩ := rpw_dest run
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_mul (hP s)
  rw [adminSlot_word] at run
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_pop (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_sloadH bal (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_swap (n := 1) rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_pop (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_pop (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (hP s)
  exact rpw_ret run

/-- `_implementation()`: the implementation word, after one storage read. -/
theorem impl_retH (bal : sevm.benvStat.rules.bal = none) {r : B256} {D : Devm}
    (run : SFunc.RunP P prog sevm (St b (r :: S) M G) t_0651_c14 (.returned D)) :
    ∃ G', D = St (afterSloadH sevm b implSlot)
      (b.getStorVal sevm.currentTarget implSlot :: S) M G' := by
  unfold t_0651_c14 at run
  obtain ⟨_, run⟩ := rpw_dest run
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_mul (hP s)
  rw [implSlot_word] at run
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_pop (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_sloadH bal (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_swap (n := 1) rfl (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_pop (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_pop (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (hP s)
  exact rpw_ret run

/-- `_willFallback()` returns only for a caller other than the admin word. -/
theorem willFallback_retH (bal : sevm.benvStat.rules.bal = none) {r : B256} {D : Devm}
    (run : SFunc.RunP P prog sevm (St b (r :: S) M G) t_0576_c22 (.returned D)) :
    sevm.caller ≠ (b.getStorVal sevm.currentTarget adminSlot).toAdr ∧
      ∃ G', D = St (afterSloadH sevm b adminSlot) S M G' := by
  unfold t_0576_c22 at run
  obtain ⟨_, run⟩ := rpw_dest run
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, D1, callee, run⟩ := rpw_callRet (k := 8) rfl run
  obtain ⟨_, rfl⟩ := admin_retH hP bal callee
  unfold t_057e_c22 at run
  obtain ⟨_, run⟩ := rpw_dest run
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_and (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_caller (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_and (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_eq (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_iszero (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_iszero (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_iszero (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  rcases rpw_branch run with ⟨-, _, run⟩ | ⟨hc, _, run⟩
  · exact (SFunc.RunP.not_returned_of_haltsOnly run (by decide)).elim
  refine ⟨fun h => ne_of_eqCheck_eq_zero (iszero_ne (iszero_eq_zero (iszero_ne hc))) ((masked_eq_iff _ _).mpr h), ?_⟩
  unfold t_0647_c22 at run
  obtain ⟨_, run⟩ := rpw_dest run
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rpw_next run; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, D2, callee, run⟩ := rpw_callRet (k := 31) rfl run
  unfold t_0777_c31 at callee
  obtain ⟨_, callee⟩ := rpw_dest callee
  obtain ⟨_, rfl⟩ := rpw_ret callee
  unfold t_064f_c22 at run
  obtain ⟨_, run⟩ := rpw_dest run
  exact rpw_ret run

end GettersH

section FallbackH

variable {P : Sevm → Devm → Ninst → Devm → Prop} (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
  {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}

include hP

/-- **The fallback reaches only its `DELEGATECALL`.**  A prefix reach from a `_fallback()` copy to
an external instruction passes `_willFallback()` (so the caller is not the admin word) and stops at
the `DELEGATECALL` of `_delegate`, whose operands are the remaining gas, the implementation word,
and the input window `[0, calldatasize)` that `CALLDATACOPY` has just filled with the calldata. -/
theorem fallback_reachH (bal : sevm.benvStat.rules.bal = none) {d : Nat}
    (hd : prog[d]? = some t_0682_c23)
    (run : Reach P prog sevm ⟨St b S M G, fbTree d, K⟩ T) (hT : AtExec T) :
    sevm.caller ≠ (b.getStorVal sevm.currentTarget adminSlot).toAdr ∧
      ∃ (g : B256) (rest : SFunc) (G' : Nat), T = ⟨St (afterSloadH sevm (afterSloadH sevm b adminSlot) implSlot)
        (g :: b.getStorVal sevm.currentTarget implSlot :: 0 :: sevm.data.length.toB256 :: 0 :: 0 ::
          b.getStorVal sevm.currentTarget implSlot :: Bytes.toB256 [0x02, 0x11] :: S)
        (M.write 0 (sevm.data.sliceD 0 sevm.data.length.toB256.toNat 0)) G',
        .next (.exec .delegatecall) rest, K⟩ := by
  unfold fbTree at run
  obtain ⟨_, run⟩ := rr_dest run hT
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, D, callee, run⟩ := rr_callOver getters_execFree (k := 22) rfl (by decide) run hT
  obtain ⟨notAdmin, _, rfl⟩ := willFallback_retH hP bal callee
  refine ⟨notAdmin, ?_⟩
  obtain ⟨_, run⟩ := rr_dest run hT
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, D, callee, run⟩ := rr_callOver getters_execFree (k := 14) rfl (by decide) run hT
  obtain ⟨_, rfl⟩ := impl_retH hP bal callee
  obtain ⟨_, run⟩ := rr_dest run hT
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨g, _, hg, run⟩ := rr_jump run hT
  rw [hd] at hg
  cases hg
  unfold t_0682_c23 at run
  obtain ⟨_, run⟩ := rr_dest run hT
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_calldatasize (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_calldatacopy (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_calldatasize (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨w, _, rfl⟩ := ri_gas (hP s)
  rcases Reach.exec run with rfl | ⟨_, -, run⟩
  · exact ⟨w, _, _, by rw [getStorVal_afterSloadH]; rfl⟩
  · obtain ⟨_, -, run⟩ := Reach.next (fun _ h => by cases h) run hT
    obtain ⟨_, -, run⟩ := Reach.next (fun _ h => by cases h) run hT
    obtain ⟨_, -, run⟩ := Reach.next (fun _ h => by cases h) run hT
    obtain ⟨_, -, run⟩ := Reach.next (fun _ h => by cases h) run hT
    obtain ⟨_, -, run⟩ := Reach.next (fun _ h => by cases h) run hT
    obtain ⟨_, -, run⟩ := Reach.next (fun _ h => by cases h) run hT
    obtain ⟨_, -, run⟩ := Reach.next (fun _ h => by cases h) run hT
    obtain ⟨_, -, run⟩ := Reach.next (fun _ h => by cases h) run hT
    obtain ⟨_, -, run⟩ := Reach.next (fun _ h => by cases h) run hT
    rcases Reach.branch run hT with ⟨_, _, -, run⟩ | ⟨_, _, _, -, -, run⟩
    · unfold t_069f_c23 at run
      obtain ⟨_, -, run⟩ := Reach.next (fun _ h => by cases h) run hT
      obtain ⟨_, -, run⟩ := Reach.next (fun _ h => by cases h) run hT
      exact (Reach.not_last run hT).elim
    · unfold t_06a3_c23 at run
      obtain ⟨_, -, run⟩ := Reach.dest run hT
      obtain ⟨_, -, run⟩ := Reach.next (fun _ h => by cases h) run hT
      obtain ⟨_, -, run⟩ := Reach.next (fun _ h => by cases h) run hT
      exact (Reach.not_last run hT).elim

end FallbackH

section ReachH

variable {P : Sevm → Devm → Ninst → Devm → Prop} (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
  {sevm : Sevm} {S : List B256} {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}

include hP

theorem fallback_delegateH (bal : sevm.benvStat.rules.bal = none) {b b₁ : Devm}
    (hb : b₁.state = b.state) {d : Nat} (hd : prog[d]? = some t_0682_c23)
    (run : Reach P prog sevm ⟨St b₁ S M G, fbTree d, K⟩ T) (hT : AtExec T) :
    DelegateConf sevm b T := by
  obtain ⟨na, g, rest, G', rfl⟩ := fallback_reachH hP bal hd run hT
  rw [getStorVal_of_state hb] at na
  refine ⟨na, afterSloadH sevm (afterSloadH sevm b₁ adminSlot) implSlot, g,
    b.getStorVal sevm.currentTarget implSlot :: Bytes.toB256 [0x02, 0x11] :: S, M, G', rest, ?_, rfl, ?_⟩
  · rw [afterSloadH_state, afterSloadH_state, hb]
  · show St _ _ _ _ = St _ _ _ _
    rw [getStorVal_of_state hb]

/-- `upgradeTo` (entry 33, wrapper of entry 1): its admin side makes no external call. -/
theorem sel33_reachH (bal : sevm.benvStat.rules.bal = none) {b : Devm} {x : B256}
    (run : Reach P prog sevm ⟨St b (x :: S) M G, t_0077_c33, []⟩ T) (hT : AtExec T) :
    DelegateConf sevm b T := by
  unfold t_0077_c33 at run
  obtain ⟨_, run⟩ := rr_dest run hT
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_callvalue (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_iszero (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  rcases rr_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  ·
    unfold t_007f_c33 at run
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
    exact (Reach.not_last run hT).elim
  unfold t_0083_c33 at run
  obtain ⟨_, run⟩ := rr_dest run hT
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_pop (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_calldatasize (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_sub (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_add (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_calldataload (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_and (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_add (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_swap (n := 2) rfl (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_swap (n := 1) rfl (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_pop (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_pop (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_pop (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, T', inner, rfl⟩ := rr_callInto empty_execFree (k := 1) rfl (by decide)
    (fun _ h => by cases h) run hT
  replace run := inner
  replace hT : AtExec T' := AtExec.below.mp hT
  refine DelegateConf.below ?_
  unfold t_0213_c1 at run
  obtain ⟨_, run⟩ := rr_dest run hT
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, D, callee, run⟩ := rr_callOver getters_execFree (k := 8) rfl (by decide) run hT
  obtain ⟨_, rfl⟩ := admin_retH hP bal callee
  unfold t_021b_c1 at run
  obtain ⟨_, run⟩ := rr_dest run hT
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_and (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_caller (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_and (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_eq (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_iszero (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  rcases rr_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_execFree ent1_admin_execFree run hT (by decide)
      (fun _ h => by cases h)).elim
  unfold t_025c_c1 at run
  obtain ⟨_, run⟩ := rr_dest run hT
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨g, _, hg, run⟩ := rr_jump run hT
  obtain rfl : g = fbTree 26 := Option.some.inj (hg.symm.trans rfl)
  exact fallback_delegateH hP bal (afterSloadH_state _ _ _) rfl run hT


/-- `upgradeToAndCall` (entry 34, wrapper of entry 2): for the admin, the `CALL` to the proxy. -/
theorem sel34_reachH (bal : sevm.benvStat.rules.bal = none) {b : Devm} {x : B256}
    (run : Reach P prog sevm ⟨St b (x :: S) M G, t_00ba_c34, []⟩ T) (hT : AtExec T) :
    DelegateConf sevm b T ∨ SelfCallConf sevm b T := by
  unfold t_00ba_c34 at run
  obtain ⟨_, run⟩ := rr_dest run hT
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_calldatasize (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_sub (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_add (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_calldataload (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_and (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_add (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_swap (n := 2) rfl (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_swap (n := 1) rfl (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_calldataload (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_add (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_add (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_calldataload (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_add (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_swap (n := 1) rfl (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_swap (n := 1) rfl (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_swap (n := 2) rfl (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_swap (n := 3) rfl (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_swap (n := 1) rfl (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_swap (n := 2) rfl (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_swap (n := 3) rfl (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_pop (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_pop (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_pop (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, T', inner, rfl⟩ := rr_callInto empty_execFree (k := 2) rfl (by decide)
    (fun _ h => by cases h) run hT
  replace run := inner
  replace hT : AtExec T' := AtExec.below.mp hT
  refine (Or.imp DelegateConf.below SelfCallConf.below) ?_
  unfold t_0268_c2 at run
  obtain ⟨_, run⟩ := rr_dest run hT
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, D, callee, run⟩ := rr_callOver getters_execFree (k := 8) rfl (by decide) run hT
  obtain ⟨_, rfl⟩ := admin_retH hP bal callee
  unfold t_0270_c2 at run
  obtain ⟨_, run⟩ := rr_dest run hT
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_and (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_caller (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_and (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_eq (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_iszero (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  rcases rr_branch run hT with ⟨hz, _, run⟩ | ⟨-, _, run⟩
  · have hadm : sevm.caller = (b.getStorVal sevm.currentTarget adminSlot).toAdr :=
      (masked_eq_iff _ _).mp (eqCheck_ne_zero (iszero_eq_zero hz))
    right
    unfold t_02a4_c2 at run
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
    obtain ⟨_, D, -, run⟩ := rr_callOver upgrade_execFree (k := 9) rfl (by decide) run hT
    rw [St.self' D] at run
    unfold t_02ac_c2 at run
    obtain ⟨_, run⟩ := rr_dest run hT
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_address (hP s)
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_and (hP s)
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_callvalue (hP s)
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, _, _, rfl⟩ := ri_dup_any (hP s)
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, _, _, rfl⟩ := ri_dup_any (hP s)
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_mload (hP s)
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_calldatacopy (hP s)
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_add (hP s)
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_swap (n := 1) rfl (hP s)
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_pop (hP s)
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_pop (hP s)
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_swap (n := 2) rfl (hP s)
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_pop (hP s)
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_pop (hP s)
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_pop (hP s)
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_mload (hP s)
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_sub (hP s)
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨w, _, rfl⟩ := ri_gas (hP s)
    rcases Reach.exec run with rfl | ⟨_, -, run⟩
    · exact ⟨hadm, ⟨_, rfl⟩, w, _, by rw [St.stack, ff20_caller]⟩
    · exact (Reach.false_of_execFree ent2_tail_execFree run hT (by decide)
        (fun _ h => by cases h)).elim
  · left
    unfold t_02fa_c2 at run
    obtain ⟨_, run⟩ := rr_dest run hT
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
    obtain ⟨g, _, hg, run⟩ := rr_jump run hT
    obtain rfl : g = fbTree 27 := Option.some.inj (hg.symm.trans rfl)
    exact fallback_delegateH hP bal (afterSloadH_state _ _ _) rfl run hT

/-- `implementation()` (entry 35, wrapper of entry 3): its admin side makes no external call. -/
theorem sel35_reachH (bal : sevm.benvStat.rules.bal = none) {b : Devm} {x : B256}
    (run : Reach P prog sevm ⟨St b (x :: S) M G, t_0108_c35, []⟩ T) (hT : AtExec T) :
    DelegateConf sevm b T := by
  unfold t_0108_c35 at run
  obtain ⟨_, run⟩ := rr_dest run hT
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_callvalue (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_iszero (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  rcases rr_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  ·
    unfold t_0110_c35 at run
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
    exact (Reach.not_last run hT).elim
  unfold t_0114_c35 at run
  obtain ⟨_, run⟩ := rr_dest run hT
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_pop (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, T', inner, rfl⟩ := rr_callInto empty_execFree (k := 3) rfl (by decide)
    (fun _ h => by cases h) run hT
  replace run := inner
  replace hT : AtExec T' := AtExec.below.mp hT
  refine DelegateConf.below ?_
  unfold t_0308_c3 at run
  obtain ⟨_, run⟩ := rr_dest run hT
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, D, callee, run⟩ := rr_callOver getters_execFree (k := 8) rfl (by decide) run hT
  obtain ⟨_, rfl⟩ := admin_retH hP bal callee
  unfold t_0312_c3 at run
  obtain ⟨_, run⟩ := rr_dest run hT
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_and (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_caller (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_and (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_eq (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_iszero (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  rcases rr_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_execFree ent3_admin_execFree run hT (by decide)
      (fun _ h => by cases h)).elim
  unfold t_0354_c3 at run
  obtain ⟨_, run⟩ := rr_dest run hT
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨g, _, hg, run⟩ := rr_jump run hT
  obtain rfl : g = fbTree 28 := Option.some.inj (hg.symm.trans rfl)
  exact fallback_delegateH hP bal (afterSloadH_state _ _ _) rfl run hT

/-- `changeAdmin` (entry 36, wrapper of entry 4): its admin side makes no external call. -/
theorem sel36_reachH (bal : sevm.benvStat.rules.bal = none) {b : Devm} {x : B256}
    (run : Reach P prog sevm ⟨St b (x :: S) M G, t_015f_c36, []⟩ T) (hT : AtExec T) :
    DelegateConf sevm b T := by
  unfold t_015f_c36 at run
  obtain ⟨_, run⟩ := rr_dest run hT
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_callvalue (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_iszero (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  rcases rr_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  ·
    unfold t_0167_c36 at run
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
    exact (Reach.not_last run hT).elim
  unfold t_016b_c36 at run
  obtain ⟨_, run⟩ := rr_dest run hT
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_pop (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_calldatasize (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_sub (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_add (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_calldataload (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_and (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_add (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_swap (n := 2) rfl (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_swap (n := 1) rfl (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_pop (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_pop (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_pop (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, T', inner, rfl⟩ := rr_callInto empty_execFree (k := 4) rfl (by decide)
    (fun _ h => by cases h) run hT
  replace run := inner
  replace hT : AtExec T' := AtExec.below.mp hT
  refine DelegateConf.below ?_
  unfold t_0360_c4 at run
  obtain ⟨_, run⟩ := rr_dest run hT
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, D, callee, run⟩ := rr_callOver getters_execFree (k := 8) rfl (by decide) run hT
  obtain ⟨_, rfl⟩ := admin_retH hP bal callee
  unfold t_0368_c4 at run
  obtain ⟨_, run⟩ := rr_dest run hT
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_and (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_caller (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_and (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_eq (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_iszero (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  rcases rr_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_execFree ent4_admin_execFree run hT (by decide)
      (fun _ h => by cases h)).elim
  unfold t_0512_c4 at run
  obtain ⟨_, run⟩ := rr_dest run hT
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨g, _, hg, run⟩ := rr_jump run hT
  obtain rfl : g = fbTree 29 := Option.some.inj (hg.symm.trans rfl)
  exact fallback_delegateH hP bal (afterSloadH_state _ _ _) rfl run hT

/-- `admin()` (entry 37, wrapper of entry 5): its admin side makes no external call. -/
theorem sel37_reachH (bal : sevm.benvStat.rules.bal = none) {b : Devm} {x : B256}
    (run : Reach P prog sevm ⟨St b (x :: S) M G, t_01a2_c37, []⟩ T) (hT : AtExec T) :
    DelegateConf sevm b T := by
  unfold t_01a2_c37 at run
  obtain ⟨_, run⟩ := rr_dest run hT
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_callvalue (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_iszero (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  rcases rr_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  ·
    unfold t_01aa_c37 at run
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
    exact (Reach.not_last run hT).elim
  unfold t_01ae_c37 at run
  obtain ⟨_, run⟩ := rr_dest run hT
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_pop (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, T', inner, rfl⟩ := rr_callInto empty_execFree (k := 5) rfl (by decide)
    (fun _ h => by cases h) run hT
  replace run := inner
  replace hT : AtExec T' := AtExec.below.mp hT
  refine DelegateConf.below ?_
  unfold t_051e_c5 at run
  obtain ⟨_, run⟩ := rr_dest run hT
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, D, callee, run⟩ := rr_callOver getters_execFree (k := 8) rfl (by decide) run hT
  obtain ⟨_, rfl⟩ := admin_retH hP bal callee
  unfold t_0528_c5 at run
  obtain ⟨_, run⟩ := rr_dest run hT
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_and (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_caller (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_and (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_eq (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_iszero (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  rcases rr_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  · exact (Reach.false_of_execFree ent5_admin_execFree run hT (by decide)
      (fun _ h => by cases h)).elim
  unfold t_056a_c5 at run
  obtain ⟨_, run⟩ := rr_dest run hT
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨g, _, hg, run⟩ := rr_jump run hT
  obtain rfl : g = fbTree 30 := Option.some.inj (hg.symm.trans rfl)
  exact fallback_delegateH hP bal (afterSloadH_state _ _ _) rfl run hT

/-- **Every external instruction a proxy frame reaches.** -/
theorem proxy_reachH (bal : sevm.benvStat.rules.bal = none) {b : Devm}
    (run : Reach P prog sevm ⟨St b S M G, t_0000_c0, []⟩ T) (hT : AtExec T) :
    DelegateConf sevm b T ∨
      (SelfCallConf sevm b T ∧ dispatchWord sevm = Bytes.toB256 [0x4f, 0x1e, 0xf2, 0x86]) := by
  unfold t_0000_c0 at run
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_mstore (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_calldatasize (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_lt (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  rcases rr_branch run hT with ⟨-, _, run⟩ | ⟨-, _, run⟩
  ·
    unfold t_000d_c0 at run
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_calldataload (hP s)
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (hP s)
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_div (hP s)
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_and (hP s)
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_eq (hP s)
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
    rcases rr_branchTo run hT with ⟨-, _, run⟩ | ⟨-, g, _, hg, run⟩
    swap
    · obtain rfl : g = t_0077_c33 := Option.some.inj (hg.symm.trans rfl)
      exact .inl (sel33_reachH hP bal run hT)
    unfold t_0041_c0 at run
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_eq (hP s)
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
    rcases rr_branchTo run hT with ⟨-, _, run⟩ | ⟨h, g, _, hg, run⟩
    swap
    · obtain rfl : g = t_00ba_c34 := Option.some.inj (hg.symm.trans rfl)
      exact (sel34_reachH hP bal run hT).imp id fun hc => ⟨hc, (eqCheck_ne_zero h).symm⟩
    unfold t_004c_c0 at run
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_eq (hP s)
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
    rcases rr_branchTo run hT with ⟨-, _, run⟩ | ⟨-, g, _, hg, run⟩
    swap
    · obtain rfl : g = t_0108_c35 := Option.some.inj (hg.symm.trans rfl)
      exact .inl (sel35_reachH hP bal run hT)
    unfold t_0057_c0 at run
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_eq (hP s)
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
    rcases rr_branchTo run hT with ⟨-, _, run⟩ | ⟨-, g, _, hg, run⟩
    swap
    · obtain rfl : g = t_015f_c36 := Option.some.inj (hg.symm.trans rfl)
      exact .inl (sel36_reachH hP bal run hT)
    unfold t_0062_c0 at run
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_eq (hP s)
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
    rcases rr_branchTo run hT with ⟨-, _, run⟩ | ⟨-, g, _, hg, run⟩
    swap
    · obtain rfl : g = t_01a2_c37 := Option.some.inj (hg.symm.trans rfl)
      exact .inl (sel37_reachH hP bal run hT)
    unfold t_006d_c0 at run
    obtain ⟨_, run⟩ := rr_dest run hT
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
    obtain ⟨g, _, hg, run⟩ := rr_jump run hT
    obtain rfl : g = fbTree 23 := Option.some.inj (hg.symm.trans rfl)
    exact .inl (fallback_delegateH hP bal rfl rfl run hT)
  unfold t_006d_c0_1 at run
  obtain ⟨_, run⟩ := rr_dest run hT
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨g, _, hg, run⟩ := rr_jump run hT
  obtain rfl : g = fbTree 24 := Option.some.inj (hg.symm.trans rfl)
  exact .inl (fallback_delegateH hP bal rfl rfl run hT)

end ReachH

/-- **The external instructions of a proxy frame on a historical fork.**  `proxy_node` under
`rules.stateGas = none` and `rules.bal = none` in place of `CoveredFork`. -/
theorem proxy_nodeH {sevm : Sevm} {pre : Devm} {out : Execution} (run : Exec 0 sevm pre out)
    (codeEq : sevm.code = Proxy.code) (hsg : sevm.benvStat.rules.stateGas = none)
    (bal : sevm.benvStat.rules.bal = none) {N : Exec.Deriv}
    (chain : Exec.Deriv.ParentPrefix ⟨0, sevm, pre, out, run⟩ N) {x : Xinst}
    (hat : Ninst.At N.sevm.code N.pc (.exec x)) :
    ∃ (f : SFunc) (K : List SFunc), (x = .delegatecall ∧ DelegateConf sevm pre ⟨N.devm, .next (.exec x) f, K⟩) ∨
      (x = .call ∧ SelfCallConf sevm pre ⟨N.devm, .next (.exec x) f, K⟩ ∧
        dispatchWord sevm = Bytes.toB256 [0x4f, 0x1e, 0xf2, 0x86]) := by
  obtain ⟨κ, reach, ok⟩ := reach_of_parentPrefix_noStateGas cert_check
    (R := ⟨0, sevm, pre, out, run⟩) rfl codeEq hsg chain
  obtain ⟨g, hf, -⟩ := ok.tree_of_exec hat
  have hT : AtExec (κ.conf N.devm) := ⟨x, g, hf⟩
  change Reach _ _ _ ⟨pre, t_0000_c0, []⟩ _ at reach
  rw [show (⟨pre, t_0000_c0, []⟩ : Conf) =
      ⟨St pre pre.stack pre.memory pre.gasLeft, t_0000_c0, []⟩ by rw [← St.self' pre]] at reach
  rw [show κ.conf N.devm = ⟨N.devm, .next (.exec x) g, κ.K.map Cont.f⟩ by
    show (⟨N.devm, κ.f, κ.K.map Cont.f⟩ : Conf) = _
    rw [hf]] at reach hT
  refine ⟨g, κ.K.map Cont.f, ?_⟩
  rcases proxy_reachH (fun h => StepIn.toRun h) bal reach hT with hd | ⟨hs, hw⟩
  · refine .inl ⟨?_, hd⟩
    obtain ⟨-, _, _, _, _, _, _, -, hf', -⟩ := hd
    simp only [SFunc.next.injEq, Ninst.exec.injEq] at hf'
    exact hf'.1
  · refine .inr ⟨?_, hs, hw⟩
    obtain ⟨-, ⟨_, hf'⟩, -⟩ := hs
    simp only [SFunc.next.injEq, Ninst.exec.injEq] at hf'
    exact hf'.1

end Blanc.Lift.Usdc.Proxy
