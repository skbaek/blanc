import Blanc.Lift.UniswapV2Pair.GetterMemory
import Blanc.Lift.UniswapV2Pair.Execution
import Blanc.Lift.UniswapV2Pair.Jumps
import Blanc.Lift.UniswapV2Pair.Check
import Blanc.CommonCore
import Blanc.Lift.ExactWalkSolc

/-! Exact execution of the deployed Pair's getter paths. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

theorem totalSupply_callee_exact {fs : List SFunc} {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G c : Nat} {ρ : B256}
    (fork : CoveredFork sevm.benvStat.fork) (cost : c = sloadCost sevm b 0)
    (room : R.length ≤ 1021) :
    SFunc.RunExact fs sevm (St b (ρ :: R) M (G + c + 15)) t_0e18_c53
      (.returned (St (afterSload sevm b 0)
        (b.getStorVal sevm.currentTarget 0 :: ρ :: R) M G)) := by
  unfold t_0e18_c53
  refine rx_dest ?_
  refine rx_push (w := 0) rfl (by simp only [List.length_cons]; omega) ?_
  have gas : G + c + 11 = (G + 11) + c := by omega
  rw [gas]
  refine rx_sload_selC fork cost (by simp only [List.length_cons]; omega) ?_
  refine rx_dup2 (by simp only [List.length_cons]; omega) ?_
  exact rx_ret

theorem totalSupply_callee_inv {fs : List SFunc} {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G : Nat} {ρ : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.Run fs sevm (St b (ρ :: R) M G) t_0e18_c53 o) :
    ∃ G', o = .returned (St (afterSload sevm b 0)
      (b.getStorVal sevm.currentTarget 0 :: ρ :: R) M G') := by
  have h := run.cut
  unfold t_0e18_c53 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_sload fork hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup (w := ρ) rfl hd
  obtain ⟨g, hg⟩ := ric_ret h
  exact ⟨g, Seg.done.inj hg⟩

/-- The literal word return charges only its actual memory expansion. -/
theorem getterWord_tail_ptr_exact {fs : List SFunc} {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G n : Nat} {v : B256}
    (mem : PtrMem 128 n M) (room : R.length ≤ 1019) :
    SFunc.RunExact fs sevm (St b (v :: R) M (G + 43 + (calculateMemoryGasCost (memExtSize n 128 32) - calculateMemoryGasCost n))) t_039b_c98
      (.halted (getterWordPost b R M v G)) := by
  let expansion := calculateMemoryGasCost (memExtSize n 128 32) - calculateMemoryGasCost n
  have outmem := mem.write 128 v (Or.inr (by decide : 96 ≤ 128))
  have fit : 128 + 32 ≤ memExtSize n 128 32 := by
    change 32 * 5 ≤ 32 * max (ceilDiv n 32) 5
    exact Nat.mul_le_mul_left _ (Nat.le_max_right _ _)
  change SFunc.RunExact fs sevm (St b (v :: R) M (G + 43 + expansion)) t_039b_c98 _
  rw [show G + 43 + expansion = (G + expansion) + 43 from by omega]
  unfold t_039b_c98
  refine rx_dest ?_
  refine rx_push (w := 64) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup1 (by simp only [List.length_cons]; omega) ?_
  refine rx_mload (c := 3) ?_ mem.word (mem.read_self (i := 64) (sz := 32) mem.ge)
    (by simp only [List.length_cons]; omega) ?_
  · rw [St.extCost_eq mem.size]
    rw [memExtSize_of_le mem.n32 mem.ge, Nat.sub_self]; rfl
  refine rx_swap2 ?_
  refine rx_dup3 (by simp only [List.length_cons]; omega) ?_
  rw [show (G + expansion) + 27 = (G + 24) + (3 + expansion) from by omega]
  refine rx_mstore (c := 3 + expansion) ?_ rfl ?_
  · rw [St.extCost_eq mem.size]
    rfl
  refine rx_mload (c := 3) ?_ outmem.word (outmem.read_self (i := 64) (sz := 32) outmem.ge)
    (by simp only [List.length_cons]; omega) ?_
  · simp only [show (128 : B256).toNat = 128 from rfl]
    rw [St.extCost_eq outmem.size]
    rw [memExtSize_of_le outmem.n32 outmem.ge, Nat.sub_self]; rfl
  refine rx_swap1 ?_
  refine rx_dup2 (by simp only [List.length_cons]; omega) ?_
  refine rx_swap1 ?_
  refine rx_sub' (v := 0) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := 32) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_add' (v := 32) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_swap1 ?_
  exact rx_return_any rfl (by
    simp only [show (128 : B256).toNat = 128 from rfl, show (32 : B256).toNat = 32 from rfl]
    rw [St.extCost_eq outmem.size]
    rw [memExtSize_of_le outmem.n32 fit, Nat.sub_self])

theorem getterWord_tail_exact {fs : List SFunc} {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G : Nat} {v : B256}
    (mem : PtrMem 128 96 M) (room : R.length ≤ 1019) :
    SFunc.RunExact fs sevm (St b (v :: R) M (G + 49)) t_039b_c98
      (.halted (getterWordPost b R M v G)) := by
  have charge : (43 : Nat) +
      (calculateMemoryGasCost (memExtSize 96 128 32) - calculateMemoryGasCost 96) = 49 := by decide
  simpa only [Nat.add_assoc, charge] using getterWord_tail_ptr_exact mem room

/-- The return word is independent of the incoming allocated high-water mark. -/
theorem getterWord_tail_ptr_inv {fs : List SFunc} {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G n : Nat} {v : B256} {o : Outcome}
    (mem : PtrMem 128 n M)
    (run : SFunc.Run fs sevm (St b (v :: R) M G) t_039b_c98 o) :
    ∃ d, o = .halted d ∧ d.output = v.toBytes ∧
      (∀ a, Devm.getStor d a = Devm.getStor b a) ∧ d.logs = b.logs := by
  have outmem := mem.write 128 v (Or.inr (by decide : 96 ≤ 128))
  have h := run.cut
  unfold t_039b_c98 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_mload hd
  simp only [show Bytes.toB256 [0x40] = (64 : B256) from rfl,
    show (64 : B256).toNat = 64 from rfl,
    mem.read_self (i := 64) (sz := 32) mem.ge, show Bytes.toB256 (M.read 64 32).1 = (128 : B256) from mem.word] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_mstore hd
  simp only [show (128 : B256).toNat = 128 from rfl] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_mload hd
  simp only [show (64 : B256).toNat = 64 from rfl,
    outmem.read_self (i := 64) (sz := 32) outmem.ge, show Bytes.toB256 ((M.write 128 v.toBytes).read 64 32).1 = (128 : B256) from outmem.word] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_sub hd
  simp only [show (128 : B256) - 128 = 0 from by decide] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_add hd
  simp only [show Bytes.toB256 [0x20] = (32 : B256) from rfl,
    show (32 : B256) + 0 = 32 from by decide] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  cases h with
  | last hr =>
    obtain ⟨hout, hstor, hlogs⟩ := ri_return hr
    refine ⟨_, rfl, ?_, hstor, hlogs⟩
    rw [hout]
    exact Mem.read_write_word_of_wf mem.wf 128 v

theorem getterWord_tail_inv {fs : List SFunc} {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G : Nat} {v : B256} {o : Outcome}
    (mem : PtrMem 128 96 M)
    (run : SFunc.Run fs sevm (St b (v :: R) M G) t_039b_c98 o) :
    ∃ d, o = .halted d ∧ d.output = v.toBytes ∧
      (∀ a, Devm.getStor d a = Devm.getStor b a) ∧ d.logs = b.logs := by
  exact getterWord_tail_ptr_inv mem run

theorem totalSupply_entry_exact {sevm : Sevm} {b : Devm}
    {M : Mem} {G c : Nat} {sel : B256}
    (fork : CoveredFork sevm.benvStat.fork) (cost : c = sloadCost sevm b 0)
    (mem : PtrMem 128 96 M) :
    SFunc.RunExact cert.prog sevm (St b [sel] M (G + c + 79)) t_0393_c98
      (.halted (getterWordPost (afterSload sevm b 0) [0x039b, sel] M
        (b.getStorVal sevm.currentTarget 0) G)) := by
  unfold t_0393_c98
  refine rx_dest ?_
  refine rx_push (w := 0x039b) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_push (w := 0x0e18) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  have gas : G + c + 72 = ((G + 49) + c + 15) + 8 := by omega
  rw [gas]
  refine rx_callRet (g := t_0e18_c53) (by rfl)
    (totalSupply_callee_exact fork cost (by simp only [List.length_cons, List.length_nil]; decide)) ?_
  exact getterWord_tail_exact mem (by simp only [List.length_cons, List.length_nil]; decide)

theorem totalSupply_entry_inv {sevm : Sevm} {b : Devm}
    {M : Mem} {G : Nat} {sel : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 96 M)
    (run : SFunc.Run cert.prog sevm (St b [sel] M G) t_0393_c98 o) :
    ∃ d, o = .halted d ∧ d.output = (b.getStorVal sevm.currentTarget 0).toBytes ∧
      (∀ a, Devm.getStor d a = Devm.getStor b a) ∧ d.logs = b.logs := by
  have h := run.cut
  unfold t_0393_c98 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨_, h⟩ := ric_call (g := t_0e18_c53) (by rfl) h
  rcases h with ⟨d, hc, h⟩ | ⟨d, hc, _⟩
  · obtain ⟨_, eq⟩ := totalSupply_callee_inv fork hc
    cases eq
    obtain ⟨d, ho, hout, hs, hl⟩ := getterWord_tail_inv mem h.uncut
    exact ⟨d, ho, hout, fun a => (hs a).trans (afterSload_getStor _ _ _ _), hl.trans (afterSload_logs _ _ _)⟩
  · obtain ⟨_, eq⟩ := totalSupply_callee_inv fork hc
    cases eq


/-- The guard compares the wrapped CALLDATASIZE word; trailing bytes are unrestricted. -/
theorem totalSupply_dispatch_exact {sevm : Sevm} {b : Devm} {G : Nat} {o : Outcome}
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = 0x18160ddd)
    (body : SFunc.RunExact cert.prog sevm
      (St b [0x18160ddd] getterInitMemory G) t_0393_c98 o) :
    SFunc.RunExact cert.prog sevm (St b [] Mem.empty (G + 209)) t_0000_c0 o := by
  unfold t_0000_c0
  refine rx_push (w := 128) rfl (by decide) ?_
  refine rx_push (w := 64) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_mstore (c := 12) ?_ rfl ?_
  · rw [St.extCost_eq (n := 0) rfl]
    decide
  refine rx_callvalue (by decide) ?_
  rw [value]
  refine rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_iszero (v := 1) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_push (w := 16) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_branch_succ (by decide) ?_
  unfold t_0010_c0
  refine rx_dest ?_
  refine rx_pop ?_
  refine rx_push (w := 4) rfl (by decide) ?_
  refine rx_calldatasize (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_lt (v := 0) (ltCheck_zero_of_le size) (by decide) ?_
  refine rx_push (w := 0x01b9) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_branch_zero ?_
  unfold t_001a_c0
  refine rx_push (w := 0) rfl (by decide) ?_
  refine rx_calldataload (by decide) ?_
  refine rx_push (w := 224) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_shr (v := 0x18160ddd) selector (by decide) ?_
  refine rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_push (w := 0x6a627842) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_gt (v := 1) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_push (w := 0x00f9) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_branch_succ (by decide) ?_
  unfold t_00f9_c0
  refine rx_dest ?_
  refine rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_push (w := 0x23b872dd) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_gt (v := 1) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_push (w := 0x0166) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_branch_succ (by decide) ?_
  unfold t_0166_c0
  refine rx_dest ?_
  refine rx_dup1 (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_push (w := 0x095ea7b3) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_gt (v := 0) (by decide) (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_push (w := 0x0197) rfl (by simp only [List.length_cons, List.length_nil]; decide) ?_
  refine rx_branch_zero ?_
  unfold t_0172_c0
  refine cmp_miss (by decide) ?_
  unfold t_017d_c0
  refine cmp_miss (by decide) ?_
  unfold t_0188_c0
  exact cmp_hit (tgt := t_0393_c98) rfl (by rfl) body

/-- Pc-zero exact liveness; selected SLOAD charge includes warm/cold metadata. -/
theorem totalSupply_pc0_exact {sevm : Sevm} {b : Devm} {G c : Nat}
    (fork : CoveredFork sevm.benvStat.fork)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = 0x18160ddd) (cost : c = sloadCost sevm b 0) :
    SProg.RunExact cert.prog sevm (St b [] Mem.empty (G + c + 288))
      (getterWordPost (afterSload sevm b 0) [0x039b, 0x18160ddd]
        getterInitMemory (b.getStorVal sevm.currentTarget 0) G) := by
  refine ⟨t_0000_c0, rfl, ?_⟩
  exact totalSupply_dispatch_exact value size selector
    (totalSupply_entry_exact fork cost getterInitMemory_ptr)

/-- Exact liveness on the certified deployed bytes, on every covered fork and both static settings. -/
theorem totalSupply_bytecode_exact {sevm : Sevm} {b : Devm} {G c : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = 0x18160ddd) (cost : c = sloadCost sevm b 0) :
    Nonempty (Exec 0 sevm (St b [] Mem.empty (G + c + 288))
      (.ok (getterWordPost (afterSload sevm b 0) [0x039b, 0x18160ddd]
        getterInitMemory (b.getStorVal sevm.currentTarget 0) G))) :=
  lift_exact cert_check jumps_ok codeEq fork
    (totalSupply_pc0_exact fork value size selector cost)


theorem getter_zeroRevert_impossible {fs : List SFunc} {sevm : Sevm}
    {C : List Nat} {d : Devm} {r : Seg}
    (run : SFunc.RunCut fs sevm C d t_000c_c0 r) : False := by
  unfold t_000c_c0 at run
  obtain ⟨_, _, h⟩ := ric_next run
  obtain ⟨_, _, h⟩ := ric_next h
  exact ric_revert h

/-- Successful entry establishes actual nonpayability and the wrapped size guard. -/
theorem getter_guards_inv {fs : List SFunc} {sevm : Sevm} {b : Devm}
    {G : Nat} {o : Outcome}
    (run : SFunc.Run fs sevm (St b [] Mem.empty G) t_0000_c0 o) :
    sevm.value = 0 ∧ (4 : B256) ≤ sevm.data.length.toB256 ∧
      ∃ G', SFunc.Run fs sevm (St b [] getterInitMemory G') t_001a_c0 o := by
  have h := run.cut
  unfold t_0000_c0 at h
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_mstore hd
  simp only [show Bytes.toB256 [0x40] = (64 : B256) from rfl,
    show (64 : B256).toNat = 64 from rfl,
    show Bytes.toB256 [0x80] = (128 : B256) from rfl] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_callvalue hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_iszero hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  rcases ric_branch h with ⟨_, _, bad⟩ | ⟨nonzero, _, h⟩
  · exact (getter_zeroRevert_impossible bad).elim
  · have value : sevm.value = 0 := by
      by_contra ne
      have zero : B256.eqCheck sevm.value 0 = 0 := by
        simp only [B256.eqCheck, ne, ite_false]
      exact nonzero zero
    rw [value] at h
    unfold t_0010_c0 at h
    obtain ⟨_, h⟩ := ric_dest h
    obtain ⟨d, hd, h⟩ := ric_next h
    obtain ⟨_, rfl⟩ := ri_pop hd
    obtain ⟨d, hd, h⟩ := ric_next h
    obtain ⟨_, rfl⟩ := ri_push hd
    obtain ⟨d, hd, h⟩ := ric_next h
    obtain ⟨_, rfl⟩ := ri_calldatasize hd
    obtain ⟨d, hd, h⟩ := ric_next h
    obtain ⟨_, hd⟩ := ri_lt hd
    simp only [show Bytes.toB256 [0x04] = (4 : B256) from rfl] at hd
    subst d
    obtain ⟨d, hd, h⟩ := ric_next h
    obtain ⟨_, rfl⟩ := ri_push hd
    rcases ric_branch h with ⟨zero, g, h⟩ | ⟨_, _, bad⟩
    · have size : (4 : B256) ≤ sevm.data.length.toB256 := by
        by_contra ne
        have lt : sevm.data.length.toB256 < (4 : B256) := lt_of_not_ge ne
        have one : B256.ltCheck sevm.data.length.toB256 4 = 1 := by
          simp only [B256.ltCheck, lt, ite_true]
        rw [one] at zero
        exact (by decide : (1 : B256) ≠ 0) zero
      exact ⟨value, size, g, h.uncut⟩
    · unfold t_01b9_c0 at bad
      obtain ⟨_, bad⟩ := ric_dest bad
      exact (getter_zeroRevert_impossible bad).elim


theorem totalSupply_selector_inv {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat} {o : Outcome}
    (selector : Blanc.Sevm.selector sevm = 0x18160ddd)
    (run : SFunc.Run cert.prog sevm (St b [] M G) t_001a_c0 o) :
    ∃ G', SFunc.Run cert.prog sevm (St b [0x18160ddd] M G') t_0393_c98 o := by
  have h := run.cut
  unfold t_001a_c0 at h
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_calldataload hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_shr hd
  simp only [show Bytes.toB256 [0x00] = (0 : B256) from rfl,
    show Bytes.toB256 [0xe0] = (224 : B256) from rfl,
    show (224 : B256).toNat = 224 from rfl,
    show Sevm.dataWord sevm 0 >>> 224 = (0x18160ddd : B256) from selector] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_gt hd
  simp only [show B256.gtCheck (Bytes.toB256 [0x6a, 0x62, 0x78, 0x42]) (0x18160ddd : B256) = (1 : B256) from by decide] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨_, _, h⟩ := (ric_branch h).resolve_left
    (by rintro ⟨bad, _, _⟩; exact (by decide : (1 : B256) ≠ 0) bad)
  unfold t_00f9_c0 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_gt hd
  simp only [show B256.gtCheck (Bytes.toB256 [0x23, 0xb8, 0x72, 0xdd]) (0x18160ddd : B256) = (1 : B256) from by decide] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨_, _, h⟩ := (ric_branch h).resolve_left
    (by rintro ⟨bad, _, _⟩; exact (by decide : (1 : B256) ≠ 0) bad)
  unfold t_0166_c0 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_gt hd
  simp only [show B256.gtCheck (Bytes.toB256 [0x09, 0x5e, 0xa7, 0xb3]) (0x18160ddd : B256) = (0 : B256) from by decide] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨_, _, h⟩ := (ric_branch h).resolve_right
    (by rintro ⟨bad, _, _⟩; exact bad rfl)
  unfold t_0172_c0 at h
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_eq hd
  simp only [show B256.eqCheck (Bytes.toB256 [0x09, 0x5e, 0xa7, 0xb3]) (0x18160ddd : B256) = (0 : B256) from by decide] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨_, _, h⟩ := (ric_branchTo (g := t_0315_c96) (by intro h; cases h) (by rfl) h).resolve_right
    (by rintro ⟨bad, _, _⟩; exact bad rfl)
  unfold t_017d_c0 at h
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_eq hd
  simp only [show B256.eqCheck (Bytes.toB256 [0x0d, 0xfe, 0x16, 0x81]) (0x18160ddd : B256) = (0 : B256) from by decide] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨_, _, h⟩ := (ric_branchTo (g := t_0362_c97) (by intro h; cases h) (by rfl) h).resolve_right
    (by rintro ⟨bad, _, _⟩; exact bad rfl)
  unfold t_0188_c0 at h
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_eq hd
  simp only [show B256.eqCheck (Bytes.toB256 [0x18, 0x16, 0x0d, 0xdd]) (0x18160ddd : B256) = (1 : B256) from by decide] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨_, _, h⟩ := (ric_branchTo (g := t_0393_c98) (by intro h; cases h) (by rfl) h).resolve_left
    (by rintro ⟨bad, _, _⟩; exact (by decide : (1 : B256) ≠ 0) bad)
  exact ⟨_, h.uncut⟩


theorem totalSupply_pc0_inv {sevm : Sevm} {b post : Devm} {G : Nat}
    (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x18160ddd)
    (run : SProg.Run cert.prog sevm (St b [] Mem.empty G) post) :
    sevm.value = 0 ∧ (4 : B256) ≤ sevm.data.length.toB256 ∧
      post.output = (b.getStorVal sevm.currentTarget 0).toBytes ∧
      (∀ a, Devm.getStor post a = Devm.getStor b a) ∧ post.logs = b.logs := by
  obtain ⟨f, entry, run⟩ := run
  rw [show cert.prog[0]? = some t_0000_c0 from rfl] at entry
  cases entry
  obtain ⟨value, size, _, run⟩ := getter_guards_inv run
  obtain ⟨_, run⟩ := totalSupply_selector_inv selector run
  obtain ⟨d, eq, out, stor, logs⟩ :=
    totalSupply_entry_inv fork getterInitMemory_ptr run
  cases eq
  exact ⟨value, size, out, stor, logs⟩

/-- Universal successful pc-zero refinement to the source getter, independent of gas and staticness. -/
theorem totalSupply_bytecode_refines {sevm : Sevm} {b post : Devm} {G : Nat} {st : State}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x18160ddd)
    (supply : st.totalSupply = b.getStorVal sevm.currentTarget 0)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    sevm.value = 0 ∧ (4 : B256) ≤ sevm.data.length.toB256 ∧
      some post.output = getterResult st .totalSupply ∧
      (∀ a, Devm.getStor post a = Devm.getStor b a) ∧ post.logs = b.logs := by
  obtain ⟨value, size, out, stor, logs⟩ :=
    totalSupply_pc0_inv fork selector (lift_sound cert_check codeEq fork run)
  refine ⟨value, size, ?_, stor, logs⟩
  simp only [getterResult, encodeWords, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, supply, out]

/-- Source-result liveness with closed opcode overhead 288 and the actual selected SLOAD charge. -/
theorem totalSupply_bytecode_live {sevm : Sevm} {b : Devm} {G c : Nat} {st : State}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (value : sevm.value = 0) (size : (4 : B256) ≤ sevm.data.length.toB256)
    (selector : Blanc.Sevm.selector sevm = 0x18160ddd) (cost : c = sloadCost sevm b 0)
    (supply : st.totalSupply = b.getStorVal sevm.currentTarget 0) :
    ∃ post, Nonempty (Exec 0 sevm (St b [] Mem.empty (G + c + 288)) (.ok post)) ∧
      post.gasLeft = G ∧ some post.output = getterResult st .totalSupply ∧
      (∀ a, Devm.getStor post a = Devm.getStor b a) ∧ post.logs = b.logs := by
  refine ⟨_, totalSupply_bytecode_exact codeEq fork value size selector cost, ?_⟩
  obtain ⟨out, stor, logs, gas⟩ :=
    getterWordPost_facts (b := afterSload sevm b 0) (R := [0x039b, 0x18160ddd])
      (G := G) (v := b.getStorVal sevm.currentTarget 0) getterInitMemory_ptr.wf
  refine ⟨gas, ?_, fun a => (stor a).trans (afterSload_getStor _ _ _ _),
    logs.trans (afterSload_logs _ _ _)⟩
  simp only [getterResult, encodeWords, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, supply, out]

end Blanc.Lift.UniswapV2Pair
