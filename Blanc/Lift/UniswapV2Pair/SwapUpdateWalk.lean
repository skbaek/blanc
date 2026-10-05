import Blanc.Lift.UniswapV2Pair.SwapCheckWalk
import Blanc.Lift.UniswapV2Pair.UpdateSource
import Blanc.Lift.WordWindowMemory

/-! The shared `_update` routine called from swap, at a moved free pointer `p`.
`update_inv` fixes the pointer at 128 (the mint/burn/sync callers); only its Sync
log suffix touches memory, so this module re-derives that suffix at `p` and
recomposes the unchanged guard, oracle and packed-store stages. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- The Sync log suffix at pointer `p`: exact emitter, topic and two ABI words,
the caller tail, and a memory that keeps the free pointer. -/
theorem swapSyncEvent_inv {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G n : Nat} {p packed dt ts r0 r1 b0 b1 tag : B256} {o : Outcome}
    (mem : PtrMem p n M) (lower : 128 ≤ p.toNat) (width : p.toNat + 260 < 2 ^ 256)
    (run : SFunc.Run cert.prog sevm
      (St b (reserveDiv112 :: reserveMask112 :: packed :: dt :: ts :: r1 :: r0 :: b1 :: b0 :: tag :: R)
        M G) updateSyncTree o) :
    ∃ n' M' G', PtrMem p n' M' ∧
      o = .returned (St (updateSyncPost sevm b packed) R M' G') := by
  have p32 : (p + Bytes.toB256 [0x20]).toNat = p.toNat + 32 := swapPtr_add (k := 32) (by omega)
  have m1 := mem.write p.toNat (reserveMask112 &&& packed) (Or.inr (by omega))
  have m2 := m1.write (p.toNat + 32) (reserveMask112 &&& (packed / reserveDiv112)) (Or.inr (by omega))
  have covered : p.toNat + 64 ≤ memExtSize (memExtSize n p.toNat 32) (p.toNat + 32) 32 := by
    have h := (Mem.memWord_write_word (M.write p.toNat (reserveMask112 &&& packed).toBytes)
      (p.toNat + 32) (reserveMask112 &&& (packed / reserveDiv112))).2
    rw [m2.size] at h
    omega
  have h := run.cut
  unfold updateSyncTree at h
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, hd⟩ := ri_mload hd
  rw [show (Bytes.toB256 [0x40]).toNat = 64 from rfl,
    mem.read_self (i := 64) (sz := 32) (by have := mem.ge; omega),
    (PtrWord.of_ptrMem mem).2] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_and hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_mstore hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_div hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_and hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_add hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, hd⟩ := ri_mstore hd
  rw [p32] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, hd⟩ := ri_mload hd
  rw [show (Bytes.toB256 [0x40]).toNat = 64 from rfl,
    m2.read_self (i := 64) (sz := 32) (by have := m2.ge; omega),
    (PtrWord.of_ptrMem m2).2] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_push hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_dup rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, hd⟩ := ri_sub hd
  rw [B256.sub_self] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, hd⟩ := ri_add hd
  rw [show (Bytes.toB256 [0x40]) + 0 = 64 from by decide] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_swap rfl hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, hd⟩ := ri_log1 hd
  rw [show (64 : B256).toNat = 64 from rfl, m2.read_self covered,
    Mem.read_two_word_writes_at_raw] at hd
  subst d
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_pop hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_pop hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_pop hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_pop hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_pop hd
  obtain ⟨d, hd, h⟩ := ric_next h; obtain ⟨_, rfl⟩ := ri_pop hd
  obtain ⟨g, hg⟩ := ric_ret h
  refine ⟨_, _, g, m2, ?_⟩
  rw [Seg.done.inj hg, B256.and_comm reserveMask112 packed,
    B256.and_comm reserveMask112 (packed / reserveDiv112)]
  rfl

/-- The shared update routine at pointer `p`: the same guards, oracle, packed
store and exact world as `update_inv`, with a pointer-preserving memory. -/
theorem swapUpdate_inv {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G n : Nat} {p old0 old1 balance0 balance1 tag : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem p n M)
    (lower : 128 ≤ p.toNat) (width : p.toNat + 260 < 2 ^ 256)
    (run : SFunc.Run cert.prog sevm
      (St b (old1 :: old0 :: balance1 :: balance0 :: tag :: R) M G) t_22e0_c60 o) :
    balance0.toNat < 2 ^ 112 ∧ balance1.toNat < 2 ^ 112 ∧ sevm.isStatic = false ∧
      ∃ n' M' G', PtrMem p n' M' ∧
        o = .returned (St (updateWorld sevm b old0 old1 balance0 balance1) R M' G') := by
  obtain ⟨bound0, bound1, _, h⟩ := update_guards_inv run
  obtain ⟨_, h⟩ := update_header_inv fork h
  obtain ⟨_, h⟩ := update_oracle_reserve_inv h
  obtain ⟨_, h⟩ := update_oracle_route_inv h
  rw [update_oracle_flag_source] at h
  clear * - h fork mem lower width bound0 bound1
  by_cases active : updateOracleActive sevm b old0 old1
  · change updateElapsedWord (b.getStorVal sevm.currentTarget 8) sevm.benvStat.time &&& reserveMask32 ≠ 0 ∧
      old0 &&& reserveMask112 ≠ 0 ∧ old1 &&& reserveMask112 ≠ 0 at active
    rw [ite_eq_left active, ite_eq_right (by decide : (1 : B256) ≠ 0)] at h
    obtain ⟨_, _, h⟩ := update_price0_inv h
    obtain ⟨_, _, _, h⟩ := update_accumulator0_inv fork h
    obtain ⟨_, _, h⟩ := update_accumulator1_inv fork h
    obtain ⟨nonstatic, _, h⟩ := update_packed_store_inv fork h
    obtain ⟨n', M', g, ptr, eq⟩ := swapSyncEvent_inv mem lower width h
    refine ⟨bound0, bound1, nonstatic, n', M', g, ptr, ?_⟩
    have oracleEq : updateOracleWorld sevm b old0 old1 =
        updateAccumulatorPost sevm
          (updateAccumulatorPost sevm (afterSload sevm b 8) 9 (updatePriceWord old0 old1)
            (updateElapsedWord (b.getStorVal sevm.currentTarget 8) sevm.benvStat.time))
          10 (updatePriceWord old1 old0)
            (updateElapsedWord (b.getStorVal sevm.currentTarget 8) sevm.benvStat.time) := by
      unfold updateOracleWorld
      exact ite_eq_left active
    change o = .returned (St (updateSyncPost sevm
      (updatePackedPost sevm (updateOracleWorld sevm b old0 old1) balance0 balance1
        (updateTimestampWord sevm.benvStat.time))
      (updatePackedWord ((updateOracleWorld sevm b old0 old1).getStorVal sevm.currentTarget 8)
        balance0 balance1 (updateTimestampWord sevm.benvStat.time))) R M' g)
    rw [oracleEq]
    exact eq
  · change ¬ (updateElapsedWord (b.getStorVal sevm.currentTarget 8) sevm.benvStat.time &&& reserveMask32 ≠ 0 ∧
      old0 &&& reserveMask112 ≠ 0 ∧ old1 &&& reserveMask112 ≠ 0) at active
    simp only [active, ite_false, ite_true] at h
    obtain ⟨nonstatic, _, h⟩ := update_packed_store_inv fork h
    obtain ⟨n', M', g, ptr, eq⟩ := swapSyncEvent_inv mem lower width h
    refine ⟨bound0, bound1, nonstatic, n', M', g, ptr, ?_⟩
    simpa only [updateWorld, updateFinalPackedWord, updateOracleWorld,
      updateOracleActive, active, ite_false] using eq

def swapEventTopic : B256 :=
  0xd78ad95fa46c994b6551d0da85fc275fe613ce37657fb8d5e3d130840159d822

/-- The raw `Swap(sender, amount0In, amount1In, amount0Out, amount1Out, to)` log. -/
def swapEventLog (sevm : Sevm) (in0 in1 a0 a1 toW : B256) : Jaune.Log :=
  ⟨sevm.currentTarget, [swapEventTopic, sevm.caller.toB256, swapTokenWord toW],
    in0.toBytes ++ in1.toBytes ++ a0.toBytes ++ a1.toBytes⟩

/-- `_update`, the `Swap` log, the unlock store and the body's return. -/
theorem swapTail_inv {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G n : Nat}
    {p adj1 adj0 in1 in0 bal1 bal0 r1 r0 len off toW a1 a0 ρ : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem p n M)
    (lower : 128 ≤ p.toNat) (width : p.toNat + 260 < 2 ^ 256)
    (run : SFunc.RunCut cert.prog sevm []
      (St b (adj1 :: adj0 :: in1 :: in0 :: bal1 :: bal0 :: r1 :: r0 :: len :: off :: toW ::
        a1 :: a0 :: ρ :: S) M G) t_0cd6_c8 (.done o)) :
    bal0.toNat < 2 ^ 112 ∧ bal1.toNat < 2 ^ 112 ∧ sevm.isStatic = false ∧ ∃ M' G',
      o = .returned (St (afterSstore sevm ((updateWorld sevm b r0 r1 bal0 bal1).addLog
        (swapEventLog sevm in0 in1 a0 a1 toW)) 12 1) S M' G') := by
  have p32 : (p + Bytes.toB256 [0x20]).toNat = p.toNat + 32 := swapPtr_add (k := 32) (by omega)
  have p64 : (Bytes.toB256 [0x40] + p).toNat = p.toNat + 64 := by
    rw [B256.add_comm]
    exact swapPtr_add (k := 64) (by omega)
  have p96 : (p + Bytes.toB256 [0x60]).toNat = p.toNat + 96 := swapPtr_add (k := 96) (by omega)
  unfold t_0cd6_c8 at run
  obtain ⟨_, run⟩ := ric_dest run
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, ⟨D, callee, run⟩ | ⟨D, callee, _⟩⟩ := ric_call (g := t_22e0_c60) rfl run
  swap
  · obtain ⟨_, _, _, _, _, _, _, returned⟩ := swapUpdate_inv fork mem lower width callee
    cases returned
  obtain ⟨bound0, bound1, nonstatic, n', M', g, ptr, returned⟩ :=
    swapUpdate_inv fork mem lower width callee
  cases returned
  refine ⟨bound0, bound1, nonstatic, ?_⟩
  have m1 := ptr.write p.toNat in0 (Or.inr (by omega))
  have m2 := m1.write (p.toNat + 32) in1 (Or.inr (by omega))
  have m3 := m2.write (p.toNat + 64) a0 (Or.inr (by omega))
  have m4 := m3.write (p.toNat + 96) a1 (Or.inr (by omega))
  have covered : p.toNat + 128 ≤ memExtSize (memExtSize (memExtSize (memExtSize n' p.toNat 32)
      (p.toNat + 32) 32) (p.toNat + 64) 32) (p.toNat + 96) 32 := by
    have h := (Mem.memWord_write_word ((((M'.write p.toNat in0.toBytes).write (p.toNat + 32)
      in1.toBytes).write (p.toNat + 64) a0.toBytes)) (p.toNat + 96) a1).2
    rw [m4.size] at h
    omega
  unfold t_0ce4_c8 at run
  obtain ⟨_, run⟩ := ric_dest run
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨d, hs, run⟩ := ric_next run; obtain ⟨_, hd⟩ := ri_mload hs
  rw [show (Bytes.toB256 [0x40]).toNat = 64 from rfl,
    ptr.read_self (i := 64) (sz := 32) (by have := ptr.ge; omega), (PtrWord.of_ptrMem ptr).2] at hd
  subst d
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_mstore hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_add hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨d, hs, run⟩ := ric_next run; obtain ⟨_, hd⟩ := ri_mstore hs
  rw [p32] at hd
  subst d
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_add hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨d, hs, run⟩ := ric_next run; obtain ⟨_, hd⟩ := ri_mstore hs
  rw [p64] at hd
  subst d
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_add hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨d, hs, run⟩ := ric_next run; obtain ⟨_, hd⟩ := ri_mstore hs
  rw [p96] at hd
  subst d
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨d, hs, run⟩ := ric_next run; obtain ⟨_, hd⟩ := ri_mload hs
  rw [show (Bytes.toB256 [0x40]).toNat = 64 from rfl,
    m4.read_self (i := 64) (sz := 32) (by have := m4.ge; omega), (PtrWord.of_ptrMem m4).2] at hd
  subst d
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_and hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_caller hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_dup rfl hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨d, hs, run⟩ := ric_next run; obtain ⟨_, hd⟩ := ri_sub hs
  rw [B256.sub_self] at hd
  subst d
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨d, hs, run⟩ := ric_next run; obtain ⟨_, hd⟩ := ri_add hs
  rw [show (Bytes.toB256 [0x80]) + 0 = 128 from by decide] at hd
  subst d
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_swap rfl hs
  obtain ⟨d, hs, run⟩ := ric_next run; obtain ⟨_, hd⟩ := ri_log3 hs
  rw [show (128 : B256).toNat = 128 from rfl, m4.read_self covered,
    Mem.read_four_word_writes ptr.wf] at hd
  subst d
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_push hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_sstore fork hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop hs
  obtain ⟨_, hs, run⟩ := ric_next run; obtain ⟨_, rfl⟩ := ri_pop hs
  obtain ⟨g', hg⟩ := ric_ret run
  exact ⟨_, g', Seg.done.inj hg⟩

end Blanc.Lift.UniswapV2Pair
