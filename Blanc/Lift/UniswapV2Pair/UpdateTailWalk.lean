import Blanc.Lift.UniswapV2Pair.UpdateArithmetic
import Blanc.Lift.ExactWalkSolc
import Blanc.Lift.ExactWalkMemory
import Blanc.Lift.WalkSteps
import Blanc.Lift.InvWalkWorld
import Blanc.Lift.InvWalkOps

/-! The sole packed reserve SSTORE and the actual Sync log/return suffix. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- Literal suffix immediately after SSTORE2552 in the certified update routine. -/
def updateSyncTree : SFunc := (.next (.push [0x40] (by decide))
  (.next (.reg (.dup 0))
  (.next (.reg .mload)
  (.next (.reg (.dup 4))
  (.next (.reg (.dup 4))
  (.next (.reg .and)
  (.next (.reg (.dup 1))
  (.next (.reg .mstore)
  (.next (.reg (.swap 1))
  (.next (.reg (.swap 0))
  (.next (.reg (.swap 3))
  (.next (.reg .div)
  (.next (.reg (.swap 0))
  (.next (.reg (.swap 1))
  (.next (.reg .and)
  (.next (.push [0x20] (by decide))
  (.next (.reg (.dup 2))
  (.next (.reg .add)
  (.next (.reg .mstore)
  (.next (.reg (.dup 1))
  (.next (.reg .mload)
  (.next (.push [0x1c, 0x41, 0x1e, 0x9a, 0x96, 0xe0, 0x71, 0x24, 0x1c, 0x2f, 0x21, 0xf7, 0x72, 0x6b, 0x17, 0xae, 0x89, 0xe3, 0xca, 0xb4, 0xc7, 0x8b, 0xe5, 0x0e, 0x06, 0x2b, 0x03, 0xa9, 0xff, 0xfb, 0xba, 0xd1] (by decide))
  (.next (.reg (.swap 2))
  (.next (.reg (.swap 1))
  (.next (.reg (.dup 1))
  (.next (.reg (.swap 0))
  (.next (.reg .sub)
  (.next (.reg (.swap 0))
  (.next (.reg (.swap 1))
  (.next (.reg .add)
  (.next (.reg (.swap 0))
  (.next (.reg (.log 1))
  (.next (.reg .pop)
  (.next (.reg .pop)
  (.next (.reg .pop)
  (.next (.reg .pop)
  (.next (.reg .pop)
  (.next (.reg .pop) .ret))))))))))))))))))))))))))))))))))))))

/-- Actual metadata after the single packed slot8 store. -/
def updatePackedPost (sevm : Sevm) (b : Devm) (balance0 balance1 timestamp : B256) : Devm :=
  afterSstore sevm (afterSload sevm b 8) 8
    (updatePackedWord (b.getStorVal sevm.currentTarget 8) balance0 balance1 timestamp)


/-- The actual three masks/ORs perform one slot8 store, with selected primitive
charges and the individual SSTORE sentry preserved. -/
theorem update_packed_store_exact {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G loadCost storeCost : Nat} {dt ts r0 r1 b0 b1 tag : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (static : sevm.isStatic = false)
    (loadCharge : loadCost = sloadCost sevm b 8)
    (storeCharge : storeCost = sstoreCost sevm (afterSload sevm b 8) 8
      (updatePackedWord (b.getStorVal sevm.currentTarget 8) b0 b1 ts))
    (sentry : gCallStipend < G + storeCost) (room : R.length ≤ 1010)
    (body : SFunc.RunExact cert.prog sevm
      (St (updatePackedPost sevm b b0 b1 ts)
        (reserveDiv112 :: reserveMask112 ::
          updatePackedWord (b.getStorVal sevm.currentTarget 8) b0 b1 ts ::
          dt :: ts :: r1 :: r0 :: b1 :: b0 :: tag :: R) M G) updateSyncTree o) :
    SFunc.RunExact cert.prog sevm
      (St b (dt :: ts :: r1 :: r0 :: b1 :: b0 :: tag :: R)
        M (G + loadCost + storeCost + 110)) t_2492_c22 o := by
  unfold t_2492_c22
  apply rx_dest
  apply rx_push (w := 8) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup1 (by simp only [List.length_cons]; omega)
  have loadGas : G + loadCost + storeCost + 103 = (G + storeCost + 103) + loadCost := by omega
  rw [loadGas]
  apply rx_sload_selC fork loadCharge (by simp only [List.length_cons]; omega)
  apply rx_push (w := updateKeepHigh144) rfl (by simp only [List.length_cons]; omega)
  apply rx_and rfl (by simp only [List.length_cons]; omega)
  apply rx_push (w := reserveMask112) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup (w := b0) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup (w := reserveMask112) rfl (by simp only [List.length_cons]; omega)
  apply rx_and rfl (by simp only [List.length_cons]; omega)
  apply rx_swap2
  apply rx_swap1
  apply rx_swap2
  apply rx_or rfl (by simp only [List.length_cons]; omega)
  apply rx_push (w := updateKeepTimestampLow112) rfl (by simp only [List.length_cons]; omega)
  apply rx_and rfl (by simp only [List.length_cons]; omega)
  apply rx_push (w := reserveDiv112) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup (w := b1) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup (w := reserveMask112) rfl (by simp only [List.length_cons]; omega)
  apply rx_and rfl (by simp only [List.length_cons]; omega)
  apply rx_dup (w := reserveDiv112) rfl (by simp only [List.length_cons]; omega)
  apply rx_mul rfl (by simp only [List.length_cons]; omega)
  apply rx_swap2
  apply rx_swap1
  apply rx_swap2
  apply rx_or rfl (by simp only [List.length_cons]; omega)
  apply rx_push (w := uqMask224) rfl (by simp only [List.length_cons]; omega)
  apply rx_and rfl (by simp only [List.length_cons]; omega)
  apply rx_push (w := reserveDiv224) rfl (by simp only [List.length_cons]; omega)
  apply rx_push (w := reserveMask32) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup (w := ts) rfl (by simp only [List.length_cons]; omega)
  apply rx_and rfl (by simp only [List.length_cons]; omega)
  apply rx_mul rfl (by simp only [List.length_cons]; omega)
  apply rx_or rfl (by simp only [List.length_cons]; omega)
  apply rx_swap3
  apply rx_dup (w := updatePackedWord (b.getStorVal sevm.currentTarget 8) b0 b1 ts) rfl (by simp only [List.length_cons]; omega)
  apply rx_swap1
  apply rx_sstoreC fork storeCharge sentry static
  exact body

/-- Successful bytecode derives its mutable frame and exact sole packed store. -/
theorem update_packed_store_inv {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G : Nat} {dt ts r0 r1 b0 b1 tag : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.Run cert.prog sevm
      (St b (dt :: ts :: r1 :: r0 :: b1 :: b0 :: tag :: R) M G) t_2492_c22 o) :
    sevm.isStatic = false ∧ ∃ G', SFunc.Run cert.prog sevm
      (St (updatePackedPost sevm b b0 b1 ts)
        (reserveDiv112 :: reserveMask112 ::
          updatePackedWord (b.getStorVal sevm.currentTarget 8) b0 b1 ts ::
          dt :: ts :: r1 :: r0 :: b1 :: b0 :: tag :: R) M G') updateSyncTree o := by
  have h := run.cut
  unfold t_2492_c22 at h
  obtain ⟨_, h⟩ := ric_dest h
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_sload fork hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_and hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_and hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_or hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  clear * - h fork
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_and hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_and hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_mul hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_or hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  clear * - h fork
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_and hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_and hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_mul hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_or hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  clear * - h fork
  obtain ⟨d, hd, h⟩ := ric_next h
  have nonstatic := ri_sstore_nonstatic fork hd
  obtain ⟨g, rfl⟩ := ri_sstore fork hd
  exact ⟨nonstatic, g, h.uncut⟩


def updateSyncTopic : B256 :=
  0x1c411e9a96e071241c2f21f7726b17ae89e3cab4c78be50e062b03a9fffbbad1

def updateSyncMemory (M : Mem) (packed : B256) : Mem :=
  (M.write 128 (reserve0Read packed).toBytes).write 160 (reserve1Read packed).toBytes

/-- Sync's actual memory image at the incoming free-memory pointer. -/
def updateSyncMemoryAt (M : Mem) (p : B256) (packed : B256) : Mem :=
  (M.write p.toNat (reserve0Read packed).toBytes).write
    (p + 32).toNat (reserve1Read packed).toBytes

/-- The actual Sync word stores preserve the incoming pointer and cover the
complete64-byte event window in the resulting allocation. -/
theorem updateSyncMemoryAt_layout {M : Mem} {p packed : B256} {n : Nat}
    (mem : PtrMem p n M) (low : 96 ≤ p.toNat) (high : p.toNat + 64 < 2 ^ 256) :
    PtrMem p (memExtSize (memExtSize n p.toNat 32) (p + 32).toNat 32)
      (updateSyncMemoryAt M p packed) ∧
    p.toNat + 64 ≤ memExtSize (memExtSize n p.toNat 32) (p + 32).toNat 32 := by
  have p32Nat : (p + 32).toNat = p.toNat + 32 := by
    rw [B256.toNat_add_eq_of_nof p 32 (by change p.toNat + 32 < 2 ^ 256; omega)]
    rfl
  have m1 := mem.write p.toNat (reserve0Read packed) (Or.inr low)
  have m2 := m1.write (p + 32).toNat (reserve1Read packed) (Or.inr (by omega))
  refine ⟨m2, ?_⟩
  have h := (Mem.memWord_write_word (M.write p.toNat (reserve0Read packed).toBytes)
    (p + 32).toNat (reserve1Read packed)).2
  rw [m2.size] at h
  omega

def updateSyncPost (sevm : Sevm) (b : Devm) (packed : B256) : Devm :=
  b.addLog ⟨sevm.currentTarget, [updateSyncTopic],
    (reserve0Read packed).toBytes ++ (reserve1Read packed).toBytes⟩

def updateSyncStoreCost0 (n : Nat) : Nat :=
  3 + (calculateMemoryGasCost (memExtSize n 128 32) - calculateMemoryGasCost n)

def updateSyncStoreCost1 (n : Nat) : Nat :=
  3 + (calculateMemoryGasCost (memExtSize (memExtSize n 128 32) 160 32) -
    calculateMemoryGasCost (memExtSize n 128 32))

/-- Actual first event-word store charge at the incoming pointer. -/
def updateSyncStoreCost0At (n : Nat) (p : B256) : Nat :=
  3 + (calculateMemoryGasCost (memExtSize n p.toNat 32) - calculateMemoryGasCost n)

/-- Actual second event-word store charge after the first expansion. -/
def updateSyncStoreCost1At (n : Nat) (p : B256) : Nat :=
  3 + (calculateMemoryGasCost (memExtSize (memExtSize n p.toNat 32) (p + 32).toNat 32) -
    calculateMemoryGasCost (memExtSize n p.toNat 32))

/-- Actual Sync suffix, with symbolic incoming allocation, exact memory image,
emitter/topic/two ABI words and exact gas including both expansion charges. -/
theorem update_sync_event_exact_at {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G n : Nat} {p packed dt ts r0 r1 b0 b1 tag : B256}
    (static : sevm.isStatic = false) (mem : PtrMem p n M)
    (low : 96 ≤ p.toNat) (high : p.toNat + 64 < 2 ^ 256) (room : R.length ≤ 1010) :
    SFunc.RunExact cert.prog sevm
      (St b (reserveDiv112 :: reserveMask112 :: packed :: dt :: ts :: r1 :: r0 :: b1 :: b0 :: tag :: R)
        M (G + updateSyncStoreCost0At n p + updateSyncStoreCost1At n p + 1371)) updateSyncTree
      (.returned (St (updateSyncPost sevm b packed) R (updateSyncMemoryAt M p packed) G)) := by
  have p32Nat : (p + 32).toNat = p.toNat + 32 := by
    rw [B256.toNat_add_eq_of_nof p 32 (by change p.toNat + 32 < 2 ^ 256; omega)]
    rfl
  have m1 := mem.write p.toNat (reserve0Read packed) (Or.inr low)
  have m2 := m1.write (p + 32).toNat (reserve1Read packed) (Or.inr (by omega))
  have covered : p.toNat + 64 ≤
      memExtSize (memExtSize n p.toNat 32) (p + 32).toNat 32 := by
    have h := (Mem.memWord_write_word (M.write p.toNat (reserve0Read packed).toBytes)
      (p + 32).toNat (reserve1Read packed)).2
    rw [m2.size] at h
    omega
  have payload : ((updateSyncMemoryAt M p packed).read p.toNat 64).1 =
      (reserve0Read packed).toBytes ++ (reserve1Read packed).toBytes := by
    unfold updateSyncMemoryAt
    rw [p32Nat]
    exact Mem.read_two_word_writes_at_raw M p.toNat _ _
  unfold updateSyncTree
  apply rx_push (w := 64) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup1 (by simp only [List.length_cons]; omega)
  refine rx_mload (c := 3) ?_ mem.word (mem.read_self (by change 64 + 32 ≤ n; have := mem.ge; omega))
    (by simp only [List.length_cons]; omega) ?_
  · rw [St.extCost_eq mem.size, show (64 : B256).toNat = 64 from rfl, memExtSize_of_le mem.n32 (by have := mem.ge; omega), Nat.sub_self]
    rfl
  apply rx_dup (w := packed) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup (w := reserveMask112) rfl (by simp only [List.length_cons]; omega)
  apply rx_and (v := reserve0Read packed) (B256.and_comm _ _)
    (by simp only [List.length_cons]; omega)
  apply rx_dup2 (by simp only [List.length_cons]; omega)
  have gas0 : G + updateSyncStoreCost0At n p + updateSyncStoreCost1At n p + 1350 =
      (G + updateSyncStoreCost1At n p + 1350) + updateSyncStoreCost0At n p := by omega
  rw [gas0]
  refine rx_mstore (M' := M.write p.toNat (reserve0Read packed).toBytes) (c := updateSyncStoreCost0At n p) ?_ rfl ?_
  · rw [St.extCost_eq mem.size]
    rfl
  apply rx_swap2
  apply rx_swap1
  apply rx_swap4
  apply rx_div rfl (by simp only [List.length_cons]; omega)
  apply rx_swap1
  apply rx_swap2
  apply rx_and (v := reserve1Read packed) (B256.and_comm _ _)
    (by simp only [List.length_cons]; omega)
  apply rx_push (w := 32) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup3 (by simp only [List.length_cons]; omega)
  apply rx_add' (v := p + 32) rfl (by simp only [List.length_cons]; omega)
  have gas1 : G + updateSyncStoreCost1At n p + 1318 = (G + 1318) + updateSyncStoreCost1At n p := by omega
  rw [gas1]
  refine rx_mstore (M' := (M.write p.toNat (reserve0Read packed).toBytes).write (p + 32).toNat (reserve1Read packed).toBytes)
    (c := updateSyncStoreCost1At n p) ?_ rfl ?_
  · rw [St.extCost_eq m1.size]
    rfl
  apply rx_dup2 (by simp only [List.length_cons]; omega)
  refine rx_mload (c := 3) ?_ m2.word (m2.read_self (by change 64 + 32 ≤ memExtSize (memExtSize n p.toNat 32) (p + 32).toNat 32; have := m2.ge; omega))
    (by simp only [List.length_cons]; omega) ?_
  · rw [St.extCost_eq m2.size, show (64 : B256).toNat = 64 from rfl,
      memExtSize_of_le m2.n32 (by have := m2.ge; omega), Nat.sub_self]
    rfl
  apply rx_push (w := updateSyncTopic) rfl (by simp only [List.length_cons]; omega)
  apply rx_swap3
  apply rx_swap2
  apply rx_dup2 (by simp only [List.length_cons]; omega)
  apply rx_swap1
  apply rx_sub' (v := 0) (B256.sub_self p) (by simp only [List.length_cons]; omega)
  apply rx_swap1
  apply rx_swap2
  apply rx_add' (v := 64) (by decide) (by simp only [List.length_cons]; omega)
  apply rx_swap1
  refine rx_log1 (c := 1262) static ?_ payload (m2.read_self covered) ?_
  · rw [St.extCost_eq m2.size, show (64 : B256).toNat = 64 from rfl, memExtSize_of_le m2.n32 covered, Nat.sub_self]
    rfl
  apply rx_pop
  apply rx_pop
  apply rx_pop
  apply rx_pop
  apply rx_pop
  apply rx_pop
  exact rx_ret


/-- Successful actual Sync logging/return yields the exact emitter, topic, data,
whole memory image and caller tail. -/
theorem update_sync_event_inv_at {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G n : Nat} {p packed dt ts r0 r1 b0 b1 tag : B256} {o : Outcome}
    (mem : PtrMem p n M) (low : 96 ≤ p.toNat)
    (high : p.toNat + 64 < 2 ^ 256)
    (run : SFunc.Run cert.prog sevm
      (St b (reserveDiv112 :: reserveMask112 :: packed :: dt :: ts :: r1 :: r0 :: b1 :: b0 :: tag :: R)
        M G) updateSyncTree o) :
    ∃ G', o = .returned (St (updateSyncPost sevm b packed) R (updateSyncMemoryAt M p packed) G') := by
  have p32Nat : (p + 32).toNat = p.toNat + 32 := by
    rw [B256.toNat_add_eq_of_nof p 32 (by change p.toNat + 32 < 2 ^ 256; omega)]
    rfl
  have m1 := mem.write p.toNat (reserve0Read packed) (Or.inr low)
  have m2 := m1.write (p + 32).toNat (reserve1Read packed) (Or.inr (by omega))
  have covered : p.toNat + 64 ≤
      memExtSize (memExtSize n p.toNat 32) (p + 32).toNat 32 := by
    have h := (Mem.memWord_write_word (M.write p.toNat (reserve0Read packed).toBytes)
      (p + 32).toNat (reserve1Read packed)).2
    rw [m2.size] at h
    omega
  simp only [reserve0Read, reserve1Read] at m2
  have h := run.cut
  unfold updateSyncTree at h
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, hd⟩ := ri_mload hd
  simp only [show Bytes.toB256 [0x40] = (64 : B256) from rfl,
    show (64 : B256).toNat = 64 from rfl,
    mem.read_self (i := 64) (sz := 32) (by have := mem.ge; omega),
    show Bytes.toB256 (M.read 64 32).1 = p from mem.word] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, hd⟩ := ri_and hd
  rw [B256.and_comm reserveMask112 packed] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, hd⟩ := ri_mstore hd
  subst d
  clear * - h m2 covered p32Nat
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_div hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, hd⟩ := ri_and hd
  rw [B256.and_comm reserveMask112 (packed / reserveDiv112)] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, hd⟩ := ri_add hd
  simp only [show Bytes.toB256 [0x20] = (32 : B256) from rfl] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, hd⟩ := ri_mstore hd
  subst d
  clear * - h m2 covered p32Nat
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, hd⟩ := ri_mload hd
  simp only [show (64 : B256).toNat = 64 from rfl,
    m2.read_self (i := 64) (sz := 32) (by have := m2.ge; omega),
    show Bytes.toB256 (((M.write p.toNat (packed &&& reserveMask112).toBytes).write (p + 32).toNat
      (packed / reserveDiv112 &&& reserveMask112).toBytes).read 64 32).1 = p from m2.word] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, hd⟩ := ri_sub hd
  simp only [B256.sub_self] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, hd⟩ := ri_add hd
  simp only [show (64 : B256) + 0 = 64 from by decide] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, hd⟩ := ri_log1 hd
  simp only [show (64 : B256).toNat = 64 from rfl, m2.read_self covered] at hd
  simp only [p32Nat, Mem.read_two_word_writes_at_raw] at hd
  rw [← p32Nat] at hd
  subst d
  clear * - h
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_pop hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_pop hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_pop hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_pop hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_pop hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_pop hd
  obtain ⟨g, hg⟩ := ric_ret h
  exact ⟨g, Seg.done.inj hg⟩


end Blanc.Lift.UniswapV2Pair
