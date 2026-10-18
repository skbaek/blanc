import Blanc.Lift.Usdc.ProxyWalk

/-!
# Every external instruction a proxy frame reaches (C2b)

`proxy_reach`: a prefix reach of the proxy certificate from entry `0` to an external instruction
stops either at `_delegate`'s `DELEGATECALL`, for a caller other than the admin word
(`DelegateConf`: operands the implementation word and the calldata window), or, for the admin
caller under the `upgradeToAndCall` selector, at its `CALL` to the proxy itself (`SelfCallConf`).
The walk follows the checked trees: the dispatcher, the five `ifAdmin` wrappers (their admin
sides are exec-free regions, except `upgradeToAndCall`'s), and the seven `_fallback()` copies
(`fallback_reach`).
-/

namespace Blanc.Lift.Usdc.Proxy

open Jaune Blanc Blanc.Lift

/-- At `_delegate`'s `DELEGATECALL`, for a caller other than the admin word of `b`. -/
def DelegateConf (sevm : Sevm) (b : Devm) (T : Conf) : Prop :=
  sevm.caller ≠ (b.getStorVal sevm.currentTarget adminSlot).toAdr ∧
    ∃ (b' : Devm) (g : B256) (S : List B256) (M : Mem) (G : Nat) (rest : SFunc),
      b'.state = b.state ∧ T.f = .next (.exec .delegatecall) rest ∧
      T.d = St b' (g :: b.getStorVal sevm.currentTarget implSlot :: 0 :: sevm.data.length.toB256 ::
        0 :: 0 :: S) (M.write 0 (sevm.data.sliceD 0 sevm.data.length.toB256.toNat 0)) G

/-- At `upgradeToAndCall`'s `CALL` to the proxy itself, for the admin caller of `b`. -/
def SelfCallConf (sevm : Sevm) (b : Devm) (T : Conf) : Prop :=
  sevm.caller = (b.getStorVal sevm.currentTarget adminSlot).toAdr ∧
    (∃ rest, T.f = .next (.exec .call) rest) ∧
    ∃ (g : B256) (S : List B256), T.d.stack = g :: sevm.currentTarget.toB256 :: S

/-- The word the dispatcher compares with the selectors. -/
def dispatchWord (sevm : Sevm) : B256 :=
  Bytes.toB256 [0xff, 0xff, 0xff, 0xff] &&& (Sevm.dataWord sevm (Bytes.toB256 [0x00]) /
    Bytes.toB256 [0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00,
      0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00])

theorem getStorVal_of_state {b b' : Devm} (h : b'.state = b.state) (a : Adr) (k : B256) :
    b'.getStorVal a k = b.getStorVal a k := by
  simp only [Devm.getStorVal, Devm.getAcct, h]

theorem ent1_admin_execFree : ExecFreeSet prog [9, 10, 25, 32] = true := by decide
theorem ent3_admin_execFree : ExecFreeSet prog [14, 15] = true := by decide
theorem ent4_admin_execFree : ExecFreeSet prog [8, 17, 18] = true := by decide
theorem ent5_admin_execFree : ExecFreeSet prog [8, 20] = true := by decide
theorem upgrade_execFree : ExecFreeSet prog [9, 25, 32] = true := by decide
theorem ent2_tail_execFree : ExecFreeSet prog [12] = true := by decide
theorem empty_execFree : ExecFreeSet prog [] = true := by decide

theorem DelegateConf.below {sevm : Sevm} {b : Devm} {T : Conf} {L : List SFunc}
    (h : DelegateConf sevm b T) : DelegateConf sevm b (T.below L) := h

theorem SelfCallConf.below {sevm : Sevm} {b : Devm} {T : Conf} {L : List SFunc}
    (h : SelfCallConf sevm b T) : SelfCallConf sevm b (T.below L) := h

section Reach

variable {P : Sevm → Devm → Ninst → Devm → Prop} (hP : ∀ {s d n d'}, P s d n d' → Ninst.Run s d n d')
  {sevm : Sevm} {S : List B256} {M : Mem} {G : Nat} {K : List SFunc} {T : Conf}

include hP

theorem fallback_delegate (hfork : CoveredFork sevm.benvStat.fork) {b b₁ : Devm}
    (hb : b₁.state = b.state) {d : Nat} (hd : prog[d]? = some t_0682_c23)
    (run : Reach P prog sevm ⟨St b₁ S M G, fbTree d, K⟩ T) (hT : AtExec T) :
    DelegateConf sevm b T := by
  obtain ⟨na, g, rest, G', rfl⟩ := fallback_reach hP hfork hd run hT
  rw [getStorVal_of_state hb] at na
  refine ⟨na, afterSload sevm (afterSload sevm b₁ adminSlot) implSlot, g,
    b.getStorVal sevm.currentTarget implSlot :: Bytes.toB256 [0x02, 0x11] :: S, M, G', rest, ?_, rfl, ?_⟩
  · rw [NodeWalk.afterSload_state, NodeWalk.afterSload_state, hb]
  · show St _ _ _ _ = St _ _ _ _
    rw [getStorVal_of_state hb]

/-- `upgradeTo` (entry 33, wrapper of entry 1): its admin side makes no external call. -/
theorem sel33_reach (hfork : CoveredFork sevm.benvStat.fork) {b : Devm} {x : B256}
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
  obtain ⟨_, rfl⟩ := admin_ret hP hfork callee
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
  exact fallback_delegate hP hfork (NodeWalk.afterSload_state _ _ _) rfl run hT


/-- `upgradeToAndCall` (entry 34, wrapper of entry 2): for the admin, the `CALL` to the proxy. -/
theorem sel34_reach (hfork : CoveredFork sevm.benvStat.fork) {b : Devm} {x : B256}
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
  obtain ⟨_, rfl⟩ := admin_ret hP hfork callee
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
    exact fallback_delegate hP hfork (NodeWalk.afterSload_state _ _ _) rfl run hT

/-- `implementation()` (entry 35, wrapper of entry 3): its admin side makes no external call. -/
theorem sel35_reach (hfork : CoveredFork sevm.benvStat.fork) {b : Devm} {x : B256}
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
  obtain ⟨_, rfl⟩ := admin_ret hP hfork callee
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
  exact fallback_delegate hP hfork (NodeWalk.afterSload_state _ _ _) rfl run hT

/-- `changeAdmin` (entry 36, wrapper of entry 4): its admin side makes no external call. -/
theorem sel36_reach (hfork : CoveredFork sevm.benvStat.fork) {b : Devm} {x : B256}
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
  obtain ⟨_, rfl⟩ := admin_ret hP hfork callee
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
  exact fallback_delegate hP hfork (NodeWalk.afterSload_state _ _ _) rfl run hT

/-- `admin()` (entry 37, wrapper of entry 5): its admin side makes no external call. -/
theorem sel37_reach (hfork : CoveredFork sevm.benvStat.fork) {b : Devm} {x : B256}
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
  obtain ⟨_, rfl⟩ := admin_ret hP hfork callee
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
  exact fallback_delegate hP hfork (NodeWalk.afterSload_state _ _ _) rfl run hT

/-- **Every external instruction a proxy frame reaches.** -/
theorem proxy_reach (hfork : CoveredFork sevm.benvStat.fork) {b : Devm}
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
      exact .inl (sel33_reach hP hfork run hT)
    unfold t_0041_c0 at run
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_eq (hP s)
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
    rcases rr_branchTo run hT with ⟨-, _, run⟩ | ⟨h, g, _, hg, run⟩
    swap
    · obtain rfl : g = t_00ba_c34 := Option.some.inj (hg.symm.trans rfl)
      exact (sel34_reach hP hfork run hT).imp id fun hc => ⟨hc, (eqCheck_ne_zero h).symm⟩
    unfold t_004c_c0 at run
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_eq (hP s)
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
    rcases rr_branchTo run hT with ⟨-, _, run⟩ | ⟨-, g, _, hg, run⟩
    swap
    · obtain rfl : g = t_0108_c35 := Option.some.inj (hg.symm.trans rfl)
      exact .inl (sel35_reach hP hfork run hT)
    unfold t_0057_c0 at run
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_eq (hP s)
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
    rcases rr_branchTo run hT with ⟨-, _, run⟩ | ⟨-, g, _, hg, run⟩
    swap
    · obtain rfl : g = t_015f_c36 := Option.some.inj (hg.symm.trans rfl)
      exact .inl (sel36_reach hP hfork run hT)
    unfold t_0062_c0 at run
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_dup rfl (hP s)
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_eq (hP s)
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
    rcases rr_branchTo run hT with ⟨-, _, run⟩ | ⟨-, g, _, hg, run⟩
    swap
    · obtain rfl : g = t_01a2_c37 := Option.some.inj (hg.symm.trans rfl)
      exact .inl (sel37_reach hP hfork run hT)
    unfold t_006d_c0 at run
    obtain ⟨_, run⟩ := rr_dest run hT
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
    obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
    obtain ⟨g, _, hg, run⟩ := rr_jump run hT
    obtain rfl : g = fbTree 23 := Option.some.inj (hg.symm.trans rfl)
    exact .inl (fallback_delegate hP hfork rfl rfl run hT)
  unfold t_006d_c0_1 at run
  obtain ⟨_, run⟩ := rr_dest run hT
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨_, s, run⟩ := rr_next run hT; obtain ⟨_, rfl⟩ := ri_push (hP s)
  obtain ⟨g, _, hg, run⟩ := rr_jump run hT
  obtain rfl : g = fbTree 24 := Option.some.inj (hg.symm.trans rfl)
  exact .inl (fallback_delegate hP hfork rfl rfl run hT)

end Reach

end Blanc.Lift.Usdc.Proxy
