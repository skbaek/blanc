import Blanc.Lift.UniswapV2Pair.GetterMemory
import Blanc.Lift.InvWalkWorld
import Blanc.Lift.MapSlot
import Blanc.Lift.UniswapV2Pair.Cert

/-! Ordered scratch images and the actual common writer boolean return tail. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

def approveOwnerMemory (M : Mem) (owner : B256) : Mem :=
  (M.write 0 owner.toBytes).write 32 (2 : B256).toBytes

def approveScratch (M : Mem) (owner spender : B256) : Mem :=
  ((approveOwnerMemory M owner).write 0 spender.toBytes).write 32 (mapSlot owner 2).toBytes

def transferScratch (M : Mem) (owner : B256) : Mem :=
  (M.write 0 owner.toBytes).write 32 (1 : B256).toBytes

theorem approveOwnerMemory_ptr {M : Mem} (mem : PtrMem 128 96 M) (owner : B256) :
    PtrMem 128 96 (approveOwnerMemory M owner) := by
  have a := mem.write 0 owner (Or.inl (by decide))
  rw [show memExtSize 96 0 32 = 96 from by decide] at a
  have b := a.write 32 2 (Or.inl (by decide))
  rw [show memExtSize 96 32 32 = 96 from by decide] at b
  exact b

theorem approveScratch_ptr {M : Mem} (mem : PtrMem 128 96 M) (owner spender : B256) :
    PtrMem 128 96 (approveScratch M owner spender) := by
  have a := (approveOwnerMemory_ptr mem owner).write 0 spender (Or.inl (by decide))
  rw [show memExtSize 96 0 32 = 96 from by decide] at a
  have b := a.write 32 (mapSlot owner 2) (Or.inl (by decide))
  rw [show memExtSize 96 32 32 = 96 from by decide] at b
  exact b

theorem transferScratch_ptr {M : Mem} (mem : PtrMem 128 96 M) (owner : B256) :
    PtrMem 128 96 (transferScratch M owner) := by
  have a := mem.write 0 owner (Or.inl (by decide))
  rw [show memExtSize 96 0 32 = 96 from by decide] at a
  have b := a.write 32 1 (Or.inl (by decide))
  rw [show memExtSize 96 32 32 = 96 from by decide] at b
  exact b

/-- The three public boolean writer continuations share precisely this literal tree. -/
theorem writerBool_transfer_tail : t_034e_c85 = t_034e_c96 := rfl

theorem writerBool_transferFrom_tail : t_034e_c93 = t_034e_c96 := rfl

/-- The event has already allocated 160 bytes; the bool store does not expand memory. -/
theorem writerBool_tail_exact {fs : List SFunc} {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G : Nat} (mem : PtrMem 128 160 M)
    (room : R.length ≤ 1019) :
    SFunc.RunExact fs sevm (St b (1 :: R) M (G + 49)) t_034e_c96
      (.halted (getterWordPost b R M 1 G)) := by
  have outmem := mem.write 128 1 (Or.inr (by decide))
  rw [show memExtSize 160 128 32 = 160 from by decide] at outmem
  unfold t_034e_c96
  refine rx_dest ?_
  refine rx_push (w := 64) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup1 (by simp only [List.length_cons]; omega) ?_
  refine rx_mload (c := 3) ?_ mem.word (mem.read_self (by decide))
    (by simp only [List.length_cons]; omega) ?_
  · rw [St.extCost_eq mem.size]; decide
  refine rx_swap2 ?_
  refine rx_iszero (v := 0) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_iszero (v := 1) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_dup3 (by simp only [List.length_cons]; omega) ?_
  refine rx_mstore (c := 3) ?_ rfl ?_
  · rw [St.extCost_eq mem.size]; decide
  refine rx_mload (c := 3) ?_ outmem.word (outmem.read_self (by decide))
    (by simp only [List.length_cons]; omega) ?_
  · simp only [show (128 : B256).toNat = 128 from rfl]
    rw [St.extCost_eq outmem.size]; decide
  refine rx_swap1 ?_
  refine rx_dup2 (by simp only [List.length_cons]; omega) ?_
  refine rx_swap1 ?_
  refine rx_sub' (v := 0) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := 32) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_add' (v := 32) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_swap1 ?_
  exact rx_return_any rfl (by
    simp only [show (128 : B256).toNat = 128 from rfl]
    rw [St.extCost_eq outmem.size]; decide)


/-- Inversion retains the complete final state, including memory and all storage metadata. -/
theorem writerBool_tail_inv {fs : List SFunc} {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G : Nat} {o : Outcome} (mem : PtrMem 128 160 M)
    (run : SFunc.Run fs sevm (St b (1 :: R) M G) t_034e_c96 o) :
    ∃ G', o = .halted (getterWordPost b R M 1 G') := by
  have outmem := mem.write 128 1 (Or.inr (by decide))
  rw [show memExtSize 160 128 32 = 160 from by decide] at outmem
  have h := run.cut
  unfold t_034e_c96 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_mload hd
  simp only [show Bytes.toB256 [0x40] = (64 : B256) from rfl,
    show (64 : B256).toNat = 64 from rfl,
    mem.read_self (by decide : 64 + 32 ≤ 160),
    show Bytes.toB256 (M.read 64 32).1 = (128 : B256) from mem.word] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_val (w := 0) (by decide) (ri_iszero hd)
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_val (w := 1) (by decide) (ri_iszero hd)
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_mstore hd
  simp only [show (128 : B256).toNat = 128 from rfl] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_mload hd
  simp only [show (64 : B256).toNat = 64 from rfl,
    outmem.read_self (by decide : 64 + 32 ≤ 160),
    show Bytes.toB256 ((M.write 128 (1 : B256).toBytes).read 64 32).1 = (128 : B256)
      from outmem.word] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_val (w := 0) (by decide) (ri_sub hd)
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_val (w := 32) (by decide) (ri_add hd)
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨G', rfl⟩ := ri_swap rfl hd
  cases h with
  | last hr =>
    have hext : (St b (128 :: 32 :: R) (M.write 128 (1 : B256).toBytes) G').extCost
        [⟨(128 : B256).toNat, (32 : B256).toNat⟩] = 0 := by
      rw [St.extCost_eq outmem.size]; decide
    have hreturn : Linst.run sevm (St b (128 :: 32 :: R) (M.write 128 (1 : B256).toBytes) G')
        .return_ = .ok (getterWordPost b R M 1 G') := by
      exact Linst.run_return_eq_ok rfl (by rw [hext]; exact Nat.zero_le _)
        (by rw [hext, Nat.sub_zero]; rfl)
    change Linst.run sevm (St b (128 :: 32 :: R) (M.write 128 (1 : B256).toBytes) G')
      .return_ = .ok _ at hr
    rw [hreturn] at hr
    cases hr
    exact ⟨G', rfl⟩

end Blanc.Lift.UniswapV2Pair
