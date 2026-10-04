import Blanc.Lift.UniswapV2Pair.WriterMemory
import Blanc.Lift.UniswapV2Pair.WriterArithmetic
import Blanc.Lift.ExactWalkSolc
import Blanc.Lift.WalkSteps

/-! The literal internal approval writer, retaining storage metadata and exact event memory. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

def approvalTopic : B256 :=
  0x8c5be1e5ebec7d5bd14f71427d1e84f3dd0314c0f7b2291e5b200ac8c7c3b925

def approveCoreBase (sevm : Sevm) (b : Devm) (owner spender : Adr) (v : B256) : Devm :=
  (afterSstore sevm b (mapSlot spender.toB256 (mapSlot owner.toB256 2)) v).addLog
    ⟨sevm.currentTarget, [approvalTopic, owner.toB256, spender.toB256], v.toBytes⟩

def approveCorePost (sevm : Sevm) (b : Devm) (R : List B256) (M : Mem)
    (owner spender : Adr) (v : B256) (G : Nat) : Devm :=
  St (approveCoreBase sevm b owner spender v) R
    ((approveScratch M owner.toB256 spender.toB256).write 128 v.toBytes) G

/-- The same post image with the event word at an arbitrary free pointer. -/
def approveCorePostAt (sevm : Sevm) (b : Devm) (R : List B256) (M : Mem) (p : B256)
    (owner spender : Adr) (v : B256) (G : Nat) : Devm :=
  St (approveCoreBase sevm b owner spender v) R
    ((approveScratch M owner.toB256 spender.toB256).write p.toNat v.toBytes) G

theorem approveOwnerMemory_ptr_at {p : B256} {n : Nat} {M : Mem} (mem : PtrMem p n M)
    (owner : B256) : PtrMem p n (approveOwnerMemory M owner) := by
  have a := mem.write 0 owner (Or.inl (by decide))
  rw [memExtSize_of_le mem.n32 (by have := mem.ge; omega)] at a
  have b := a.write 32 2 (Or.inl (by decide))
  rw [memExtSize_of_le mem.n32 (by have := mem.ge; omega)] at b
  exact b

theorem approveScratch_ptr_at {p : B256} {n : Nat} {M : Mem} (mem : PtrMem p n M)
    (owner spender : B256) : PtrMem p n (approveScratch M owner spender) := by
  have a := (approveOwnerMemory_ptr_at mem owner).write 0 spender (Or.inl (by decide))
  rw [memExtSize_of_le mem.n32 (by have := mem.ge; omega)] at a
  have b := a.write 32 (mapSlot owner 2) (Or.inl (by decide))
  rw [memExtSize_of_le mem.n32 (by have := mem.ge; omega)] at b
  exact b

/-- Pointer-parametric literal core: `e` is the actual expansion charge of the
event-word store at the free pointer, the only store that can expand memory. -/
theorem approve64_exact_at {fs : List SFunc} {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G c e n : Nat} {p : B256} {owner spender : Adr} {v ρ : B256}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem p n M) (high : 96 ≤ p.toNat)
    (ext : calculateMemoryGasCost (memExtSize n p.toNat 32) - calculateMemoryGasCost n = e)
    (cost : c = sstoreCost sevm b (mapSlot spender.toB256 (mapSlot owner.toB256 2)) v)
    (sentry : gCallStipend < G + c + 1818 + e) (nonstatic : sevm.isStatic = false)
    (room : R.length ≤ 1012) :
    SFunc.RunExact fs sevm (St b (v :: spender.toB256 :: owner.toB256 :: ρ :: R)
      M (G + e + c + 1993)) t_259c_c64
      (.returned (approveCorePostAt sevm b R M p owner spender v G)) := by
  have ge := mem.ge
  have m0 := mem.write 0 owner.toB256 (Or.inl (by decide))
  rw [memExtSize_of_le mem.n32 (by omega)] at m0
  have m1 := approveOwnerMemory_ptr_at mem owner.toB256
  have m2 := m1.write 0 spender.toB256 (Or.inl (by decide))
  rw [memExtSize_of_le mem.n32 (by omega)] at m2
  have m3 := approveScratch_ptr_at mem owner.toB256 spender.toB256
  have m4 := m3.write p.toNat v (Or.inr high)
  have fitP : p.toNat + 32 ≤ memExtSize n p.toNat 32 := by
    by_cases fits : p.toNat + 32 ≤ n
    · rw [memExtSize_of_le mem.n32 fits]; exact fits
    · rw [memExtSize_eq_ceil32_of_le (by decide) (by omega)]; exact Nat.le_ceil32 _
  have n4 := memExtSize_mod_32 (i := p.toNat) (sz := 32) mem.n32
  have big4 := memExtSize_ge n p.toNat 32
  have s1 : ((M.write 0 owner.toB256.toBytes).write 32 (2 : B256).toBytes).size = n := m1.size
  have s2 : (((M.write 0 owner.toB256.toBytes).write 32 (2 : B256).toBytes).write 0
      spender.toB256.toBytes).size = n := m2.size
  have s3 : ((((M.write 0 owner.toB256.toBytes).write 32 (2 : B256).toBytes).write 0
      spender.toB256.toBytes).write 32 (mapSlot owner.toB256 2).toBytes).size = n := m3.size
  have s4 : (((((M.write 0 owner.toB256.toBytes).write 32 (2 : B256).toBytes).write 0
      spender.toB256.toBytes).write 32 (mapSlot owner.toB256 2).toBytes).write p.toNat
      v.toBytes).size = memExtSize n p.toNat 32 := m4.size
  unfold t_259c_c64
  refine rx_dest ?_
  refine rx_push rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup1 (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 4) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_and (v := owner.toB256) (by rw [B256.and_comm]; exact ff20_and_adr owner)
    (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := 0) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup2 (by simp only [List.length_cons]; omega) ?_
  refine rx_dup2 (by simp only [List.length_cons]; omega) ?_
  refine rx_mstore (c := 3) ?_ rfl ?_
  · rw [St.extCost_eq mem.size, memExtSize_of_le mem.n32 (Nat.le_trans (by decide) ge),
      Nat.sub_self]; decide
  refine rx_push (w := 2) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := 32) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_swap1 ?_
  refine rx_dup2 (by simp only [List.length_cons]; omega) ?_
  refine rx_mstore (c := 3) ?_ rfl ?_
  · simp only [show (0 : B256).toNat = 0 from rfl]
    rw [St.extCost_eq m0.size, memExtSize_of_le mem.n32 (Nat.le_trans (by decide) ge),
      Nat.sub_self]; decide
  refine rx_push (w := 64) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup1 (by simp only [List.length_cons]; omega) ?_
  refine rx_dup4 (by simp only [List.length_cons]; omega) ?_
  simp only [show (32 : B256).toNat = 32 from rfl, show (0 : B256).toNat = 0 from rfl]
  have gas1 : G + e + c + 1944 = (G + e + c + 1902) + 42 := by omega
  rw [gas1]
  refine rx_keccak (v := mapSlot owner.toB256 2) (c := 42) ?_ ?_
    (m1.read_self (Nat.le_trans (by decide) ge)) (by simp only [List.length_cons]; omega) ?_
  · rw [St.extCost_eq s1, memExtSize_of_le mem.n32 (Nat.le_trans (by decide) ge),
      Nat.sub_self]; decide
  · exact congrArg Bytes.keccak (Mem.read_two_word_writes_at_raw M 0 owner.toB256 2)
  refine rx_swap (n := 4) rfl ?_
  dsimp only [List.set]
  refine rx_dup (n := 7) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_and (v := spender.toB256) (by rw [B256.and_comm]; exact ff20_and_adr spender)
    (by simp only [List.length_cons]; omega) ?_
  refine rx_dup1 (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 4) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_mstore (c := 3) ?_ rfl ?_
  · rw [St.extCost_eq s1, memExtSize_of_le mem.n32 (Nat.le_trans (by decide) ge),
      Nat.sub_self]; decide
  refine rx_swap (n := 4) rfl ?_
  dsimp only [List.set]
  refine rx_dup3 (by simp only [List.length_cons]; omega) ?_
  refine rx_mstore (c := 3) ?_ rfl ?_
  · simp only [show (0 : B256).toNat = 0 from rfl]
    rw [St.extCost_eq s2, memExtSize_of_le mem.n32 (Nat.le_trans (by decide) ge),
      Nat.sub_self]; decide
  refine rx_swap2 ?_
  refine rx_dup3 (by simp only [List.length_cons]; omega) ?_
  refine rx_swap1 ?_
  simp only [show (32 : B256).toNat = 32 from rfl, show (0 : B256).toNat = 0 from rfl]
  have gas2 : G + e + c + 1866 = (G + e + c + 1824) + 42 := by omega
  rw [gas2]
  refine rx_keccak (v := mapSlot spender.toB256 (mapSlot owner.toB256 2)) (c := 42) ?_ ?_
    (m3.read_self (Nat.le_trans (by decide) ge)) (by simp only [List.length_cons]; omega) ?_
  · rw [St.extCost_eq s3, memExtSize_of_le mem.n32 (Nat.le_trans (by decide) ge),
      Nat.sub_self]; decide
  · exact congrArg Bytes.keccak
      (Mem.read_two_word_writes_at_raw (approveOwnerMemory M owner.toB256) 0 spender.toB256
        (mapSlot owner.toB256 2))
  refine rx_dup (n := 5) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_swap1 ?_
  have gas3 : G + e + c + 1818 = (G + e + 1818) + c := by omega
  rw [gas3]
  refine rx_sstoreC fork cost (by omega) nonstatic ?_
  refine rx_dup2 (by simp only [List.length_cons]; omega) ?_
  refine rx_mload (c := 3) ?_ m3.word (m3.read_self (Nat.le_trans (by decide) ge))
    (by simp only [List.length_cons]; omega) ?_
  · rw [St.extCost_eq s3, memExtSize_of_le mem.n32 (Nat.le_trans (by decide) ge),
      Nat.sub_self]; decide
  refine rx_dup (n := 5) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup2 (by simp only [List.length_cons]; omega) ?_
  have gas4 : G + e + 1806 = (G + 1803) + (3 + e) := by omega
  rw [gas4]
  refine rx_mstore (c := 3 + e) ?_ rfl ?_
  · rw [St.extCost_eq s3, ext]; rfl
  refine rx_swap2 ?_
  refine rx_mload (c := 3) ?_ m4.word
    (m4.read_self (Nat.le_trans (Nat.le_trans (by decide) ge) big4))
    (by simp only [List.length_cons]; omega) ?_
  · rw [St.extCost_eq s4, memExtSize_of_le n4 (Nat.le_trans (Nat.le_trans (by decide) ge) big4),
      Nat.sub_self]; decide
  refine rx_push (w := approvalTopic) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_swap3 ?_
  refine rx_dup2 (by simp only [List.length_cons]; omega) ?_
  refine rx_swap1 ?_
  refine rx_sub' (v := 0) (B256.sub_self p) (by simp only [List.length_cons]; omega) ?_
  refine rx_swap1 ?_
  refine rx_swap2 ?_
  refine rx_add' (v := 32) (by decide) (by simp only [List.length_cons]; omega) ?_
  refine rx_swap1 ?_
  have gas5 : G + 1770 = (G + 14) + 1756 := by omega
  rw [gas5]
  refine rx_log3 (data := v.toBytes) nonstatic ?_ ?_
    (m4.read_self (by simp only [show (32 : B256).toNat = 32 from rfl]; exact fitP)) ?_
  · rw [St.extCost_eq s4, memExtSize_of_le n4 (by simp only [show (32 : B256).toNat = 32 from rfl]; omega),
      Nat.sub_self]; decide
  · exact Mem.read_write_word_of_wf m3.wf p.toNat v
  refine rx_pop ?_
  refine rx_pop ?_
  refine rx_pop ?_
  exact rx_ret

/-- The store sentry is on its actual incoming gas, before the selected charge. -/
theorem approve64_exact {fs : List SFunc} {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G c : Nat} {owner spender : Adr} {v ρ : B256}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 96 M)
    (cost : c = sstoreCost sevm b (mapSlot spender.toB256 (mapSlot owner.toB256 2)) v)
    (sentry : gCallStipend < G + c + 1824) (nonstatic : sevm.isStatic = false)
    (room : R.length ≤ 1012) :
    SFunc.RunExact fs sevm (St b (v :: spender.toB256 :: owner.toB256 :: ρ :: R)
      M (G + c + 1999)) t_259c_c64
      (.returned (approveCorePost sevm b R M owner spender v G)) := by
  have hp : (128 : B256).toNat = 128 := rfl
  have post : approveCorePost sevm b R M owner spender v G =
      approveCorePostAt sevm b R M 128 owner spender v G := by
    unfold approveCorePost approveCorePostAt
    rw [hp]
  rw [post, show G + c + 1999 = G + 6 + c + 1993 by omega]
  exact approve64_exact_at fork mem (by rw [hp]; decide) (by rw [hp]; decide) cost (by omega)
    nonstatic room

/-- Any completed run of the actual core at an arbitrary free pointer returns
its full store, event and memory image. -/
theorem approve64_inv_at {fs : List SFunc} {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G n : Nat} {p : B256} {owner spender : Adr} {v ρ : B256}
    {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem p n M) (high : 96 ≤ p.toNat)
    (run : SFunc.Run fs sevm (St b (v :: spender.toB256 :: owner.toB256 :: ρ :: R) M G)
      t_259c_c64 o) :
    sevm.isStatic = false ∧
      ∃ G', o = .returned (approveCorePostAt sevm b R M p owner spender v G') := by
  have ge := mem.ge
  have m1 := approveOwnerMemory_ptr_at mem owner.toB256
  have m3 := approveScratch_ptr_at mem owner.toB256 spender.toB256
  have m4 := m3.write p.toNat v (Or.inr high)
  have fitP : p.toNat + 32 ≤ memExtSize n p.toNat 32 := by
    by_cases fits : p.toNat + 32 ≤ n
    · rw [memExtSize_of_le mem.n32 fits]; exact fits
    · rw [memExtSize_eq_ceil32_of_le (by decide) (by omega)]; exact Nat.le_ceil32 _
  have big4 := memExtSize_ge n p.toNat 32
  dsimp only [approveScratch, approveOwnerMemory] at m1 m3 m4
  have read2 := Mem.read_two_word_writes_at_raw (approveOwnerMemory M owner.toB256) 0
    spender.toB256 (mapSlot owner.toB256 2)
  dsimp only [approveOwnerMemory] at read2
  have ptr3 := m3.word
  have ptr4 := m4.word
  dsimp only [memWord] at ptr3 ptr4
  have h := run.cut
  unfold t_259c_c64 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_val (w := owner.toB256)
    (by rw [B256.and_comm]; exact ff20_and_adr owner) (ri_and hd)
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_mstore hd
  simp only [show (Bytes.toB256 [0]).toNat = 0 from rfl] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_mstore hd
  simp only [show (Bytes.toB256 [0x20]).toNat = 32 from rfl] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_keccak hd
  simp only [show Bytes.toB256 [2] = (2 : B256) from rfl,
    show (Bytes.toB256 [0]).toNat = 0 from rfl,
    show (Bytes.toB256 [0x40]).toNat = 64 from rfl,
    m1.read_self (by omega : 0 + 64 ≤ n),
    Mem.read_two_word_writes_at_raw M 0 owner.toB256 2] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  dsimp only [List.set] at h
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_val (w := spender.toB256)
    (by rw [B256.and_comm]; exact ff20_and_adr spender) (ri_and hd)
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_mstore hd
  simp only [show (Bytes.toB256 [0]).toNat = 0 from rfl] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  dsimp only [List.set] at h
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_mstore hd
  simp only [show (Bytes.toB256 [0x20]).toNat = 32 from rfl] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_keccak hd
  change d = St b (((approveScratch M owner.toB256 spender.toB256).read 0 64).1.keccak :: _)
    ((approveScratch M owner.toB256 spender.toB256).read 0 64).2 _ at hd
  dsimp only [approveScratch, approveOwnerMemory] at hd
  rw [m3.read_self (by omega : 0 + 64 ≤ n), read2] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  have nonstatic := ri_sstore_nonstatic fork hd
  obtain ⟨_, rfl⟩ := ri_sstore fork hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_mload hd
  simp only [show (Bytes.toB256 [0x40]).toNat = 64 from rfl,
    m3.read_self (by omega : 64 + 32 ≤ n), ptr3] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_mstore hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_mload hd
  simp only [show (Bytes.toB256 [0x40]).toNat = 64 from rfl,
    m4.read_self (by omega : 64 + 32 ≤ memExtSize n p.toNat 32), ptr4] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_val (w := 0) (B256.sub_self p) (ri_sub hd)
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_val (w := 32) (by decide) (ri_add hd)
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, hd⟩ := ri_log3 hd
  simp only [show (32 : B256).toNat = 32 from rfl,
    m4.read_self fitP, Mem.read_write_word_of_wf m3.wf p.toNat v] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_pop hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_pop hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_pop hd
  obtain ⟨G', hg⟩ := ric_ret h
  exact ⟨nonstatic, G', Seg.done.inj hg⟩

/-- Any completed run of the actual core returns its full store, event and memory image. -/
theorem approve64_inv {fs : List SFunc} {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G : Nat} {owner spender : Adr} {v ρ : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 96 M)
    (run : SFunc.Run fs sevm (St b (v :: spender.toB256 :: owner.toB256 :: ρ :: R) M G)
      t_259c_c64 o) :
    sevm.isStatic = false ∧ ∃ G', o = .returned (approveCorePost sevm b R M owner spender v G') := by
  have hp : (128 : B256).toNat = 128 := rfl
  obtain ⟨nonstatic, G', eq⟩ := approve64_inv_at fork mem (by rw [hp]; decide) run
  refine ⟨nonstatic, G', ?_⟩
  rw [eq]
  unfold approveCorePost approveCorePostAt
  rw [hp]


def approve51Post (sevm : Sevm) (b : Devm) (R : List B256) (M : Mem)
    (spender : Adr) (v : B256) (G : Nat) : Devm :=
  St (approveCoreBase sevm b sevm.caller spender v) (1 :: R)
    ((approveScratch M sevm.caller.toB256 spender.toB256).write 128 v.toBytes) G

/-- The real public implementation calls core64 with CALLER, then returns true. -/
theorem approve51_exact {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G c : Nat} {spender : Adr} {v ρ : B256}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 96 M)
    (cost : c = sstoreCost sevm b (mapSlot spender.toB256 (mapSlot sevm.caller.toB256 2)) v)
    (sentry : gCallStipend < G + c + 1849) (nonstatic : sevm.isStatic = false)
    (room : R.length ≤ 1008) :
    SFunc.RunExact cert.prog sevm (St b (v :: spender.toB256 :: ρ :: R) M (G + c + 2050))
      t_0de5_c51 (.returned (approve51Post sevm b R M spender v G)) := by
  unfold t_0de5_c51
  refine rx_dest ?_
  refine rx_push (w := 0) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := 0x0df2) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_caller (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 4) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_dup (n := 4) rfl (by simp only [List.length_cons]; omega) ?_
  refine rx_push (w := 0x259c) rfl (by simp only [List.length_cons]; omega) ?_
  have gas : G + c + 2032 = ((G + 25) + c + 1999) + 8 := by omega
  rw [gas]
  refine rx_callRet (g := t_259c_c64) (by rfl)
    (approve64_exact fork mem cost (by omega) nonstatic
      (by simp only [List.length_cons]; omega)) ?_
  unfold t_0df2_c51
  refine rx_dest ?_
  refine rx_pop ?_
  refine rx_push (w := 1) rfl (by simp only [List.length_cons]; omega) ?_
  exact checked_return_exact

theorem approve51_inv {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} {spender : Adr} {v ρ : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem 128 96 M)
    (run : SFunc.Run cert.prog sevm (St b (v :: spender.toB256 :: ρ :: R) M G) t_0de5_c51 o) :
    sevm.isStatic = false ∧ ∃ G', o = .returned (approve51Post sevm b R M spender v G') := by
  have h := run.cut
  unfold t_0de5_c51 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_caller hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h
  obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨_, h⟩ := ric_call (g := t_259c_c64) (by rfl) h
  rcases h with ⟨d, hc, h⟩ | ⟨d, hc, _⟩
  · obtain ⟨nonstatic, _, eq⟩ := approve64_inv fork mem hc
    cases eq
    unfold t_0df2_c51 at h
    obtain ⟨_, h⟩ := ric_dest h
    obtain ⟨d, hd, h⟩ := ric_next h
    obtain ⟨_, rfl⟩ := ri_pop hd
    obtain ⟨d, hd, h⟩ := ric_next h
    obtain ⟨_, rfl⟩ := ri_push hd
    obtain ⟨G', eq⟩ := checked_return_inv h.uncut
    exact ⟨nonstatic, G', eq⟩
  · obtain ⟨_, _, eq⟩ := approve64_inv fork mem hc
    cases eq

end Blanc.Lift.UniswapV2Pair
