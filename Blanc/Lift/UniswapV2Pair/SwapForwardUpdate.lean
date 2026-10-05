import Blanc.Lift.UniswapV2Pair.SwapUpdateWalk

/-! Forward (gas-exact) `_update` at the swap's moved free pointer `p`. The shared
`update_exact` fixes the pointer at 128; only its Sync log suffix touches memory, so this
module builds that suffix at `p` (`swapSyncEvent_exact`, the forward dual of
`swapSyncEvent_inv`) and recomposes the unchanged guard, header, oracle and packed-store
stages (`swapUpdate_exact`, the forward dual of `swapUpdate_inv`). -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- The Sync payload staged at `p`: both reserve words of the packed slot. -/
def swapSyncMemory (M : Mem) (p packed : B256) : Mem :=
  (M.write p.toNat (reserve0Read packed).toBytes).write (p.toNat + 32) (reserve1Read packed).toBytes

/-- Expansion charge of the first Sync payload store at `p`. -/
def swapSyncCost0 (n : Nat) (p : B256) : Nat :=
  3 + (calculateMemoryGasCost (memExtSize n p.toNat 32) - calculateMemoryGasCost n)

/-- Expansion charge of the second Sync payload store at `p + 32`. -/
def swapSyncCost1 (n : Nat) (p : B256) : Nat :=
  3 + (calculateMemoryGasCost (memExtSize (memExtSize n p.toNat 32) (p.toNat + 32) 32) -
    calculateMemoryGasCost (memExtSize n p.toNat 32))

/-- Exact Sync suffix gas at pointer `p`, both expansion charges included. -/
def swapSyncGas (n : Nat) (p : B256) : Nat := swapSyncCost0 n p + swapSyncCost1 n p + 1371

/-- The allocation after the Sync payload. -/
def swapSyncSize (n : Nat) (p : B256) : Nat :=
  memExtSize (memExtSize n p.toNat 32) (p.toNat + 32) 32

theorem swapSyncMemory_ptr {M : Mem} {n : Nat} {p : B256} (packed : B256)
    (mem : PtrMem p n M) (lower : 128 ≤ p.toNat) :
    PtrMem p (swapSyncSize n p) (swapSyncMemory M p packed) :=
  (mem.write p.toNat (reserve0Read packed) (Or.inr (by omega))).write (p.toNat + 32)
    (reserve1Read packed) (Or.inr (by omega))

/-- **Forward Sync suffix at `p`.** Exact emitter, topic and two ABI words, the caller
tail, the payload memory and the exact charge. -/
theorem swapSyncEvent_exact {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G n : Nat} {p packed dt ts r0 r1 b0 b1 tag : B256}
    (static : sevm.isStatic = false) (mem : PtrMem p n M) (lower : 128 ≤ p.toNat)
    (width : p.toNat + 260 < 2 ^ 256) (room : R.length ≤ 1010) :
    SFunc.RunExact cert.prog sevm
      (St b (reserveDiv112 :: reserveMask112 :: packed :: dt :: ts :: r1 :: r0 :: b1 :: b0 :: tag :: R)
        M (G + swapSyncGas n p)) updateSyncTree
      (.returned (St (updateSyncPost sevm b packed) R (swapSyncMemory M p packed) G)) := by
  have p32 : (p + (32 : B256)).toNat = p.toNat + 32 := swapPtr_add (k := 32) (by omega)
  have m1 := mem.write p.toNat (reserve0Read packed) (Or.inr (by omega))
  have m2 : PtrMem p (swapSyncSize n p) (swapSyncMemory M p packed) :=
    swapSyncMemory_ptr packed mem lower
  have covered : p.toNat + 64 ≤ swapSyncSize n p := by
    have h := (Mem.memWord_write_word (M.write p.toNat (reserve0Read packed).toBytes)
      (p.toNat + 32) (reserve1Read packed)).2
    change (swapSyncMemory M p packed).size ≥ p.toNat + 32 + 32 at h
    rw [m2.size] at h
    omega
  rw [show G + swapSyncGas n p = G + swapSyncCost0 n p + swapSyncCost1 n p + 1371 by
    unfold swapSyncGas; omega]
  unfold updateSyncTree
  apply rx_push (w := 64) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup1 (by simp only [List.length_cons]; omega)
  refine rx_mload (c := 3) ?_ mem.word (mem.read_self (by change 64 + 32 ≤ n; have := mem.ge; omega))
    (by simp only [List.length_cons]; omega) ?_
  · rw [St.extCost_eq mem.size, show (64 : B256).toNat = 64 from rfl,
      memExtSize_of_le mem.n32 (by have := mem.ge; omega), Nat.sub_self]
    rfl
  apply rx_dup (w := packed) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup (w := reserveMask112) rfl (by simp only [List.length_cons]; omega)
  apply rx_and (v := reserve0Read packed) (B256.and_comm _ _)
    (by simp only [List.length_cons]; omega)
  apply rx_dup2 (by simp only [List.length_cons]; omega)
  have gas0 : G + swapSyncCost0 n p + swapSyncCost1 n p + 1350 =
      (G + swapSyncCost1 n p + 1350) + swapSyncCost0 n p := by omega
  rw [gas0]
  refine rx_mstore (M' := M.write p.toNat (reserve0Read packed).toBytes) (c := swapSyncCost0 n p)
    ?_ rfl ?_
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
  apply rx_add (by simp only [List.length_cons]; omega)
  have gas1 : G + swapSyncCost1 n p + 1318 = (G + 1318) + swapSyncCost1 n p := by omega
  rw [gas1]
  refine rx_mstore (M' := swapSyncMemory M p packed) (c := swapSyncCost1 n p) ?_ (by rw [p32]; rfl) ?_
  · rw [St.extCost_eq m1.size, p32]
    rfl
  apply rx_dup2 (by simp only [List.length_cons]; omega)
  refine rx_mload (c := 3) ?_ m2.word
    (m2.read_self (by change 64 + 32 ≤ swapSyncSize n p; have := m2.ge; exact this))
    (by simp only [List.length_cons]; omega) ?_
  · rw [St.extCost_eq m2.size, show (64 : B256).toNat = 64 from rfl,
      memExtSize_of_le m2.n32 (by have := m2.ge; omega), Nat.sub_self]
    rfl
  apply rx_push (w := updateSyncTopic) rfl (by simp only [List.length_cons]; omega)
  apply rx_swap3
  apply rx_swap2
  apply rx_dup2 (by simp only [List.length_cons]; omega)
  apply rx_swap1
  apply rx_sub' (v := 0) (B256.sub_self _) (by simp only [List.length_cons]; omega)
  apply rx_swap1
  apply rx_swap2
  apply rx_add' (v := 64) (by decide) (by simp only [List.length_cons]; omega)
  apply rx_swap1
  refine rx_log1 (c := 1262) static ?_ (Mem.read_two_word_writes_at_raw M p.toNat
    (reserve0Read packed) (reserve1Read packed)) (m2.read_self covered) ?_
  · rw [St.extCost_eq m2.size, show (64 : B256).toNat = 64 from rfl,
      memExtSize_of_le m2.n32 covered, Nat.sub_self]
    rfl
  apply rx_pop
  apply rx_pop
  apply rx_pop
  apply rx_pop
  apply rx_pop
  apply rx_pop
  exact rx_ret

/-- **Forward `_update` at pointer `p`** (dual of `swapUpdate_inv`): the charges name the
executed primitives exactly as in `update_exact`; only the Sync suffix's memory charges and
image are taken at `p`. -/
theorem swapUpdate_exact {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G n headerLoad load9 store9 load10 store10 load8 store8 : Nat}
    {old0 old1 balance0 balance1 tag : B256}
    (fork : CoveredFork sevm.benvStat.fork) {p : B256} (mem : PtrMem p n M)
    (lower : 128 ≤ p.toNat) (width : p.toNat + 260 < 2 ^ 256)
    (static : sevm.isStatic = false) (bound0 : balance0.toNat < 2 ^ 112)
    (bound1 : balance1.toNat < 2 ^ 112) (room : R.length ≤ 1008)
    (headerCharge : headerLoad = sloadCost sevm b 8)
    (packedLoadCharge : load8 = sloadCost sevm (updateOracleWorld sevm b old0 old1) 8)
    (packedStoreCharge : store8 = sstoreCost sevm
      (afterSload sevm (updateOracleWorld sevm b old0 old1) 8) 8
      (updateFinalPackedWord sevm b old0 old1 balance0 balance1))
    (oracleCharges : updateOracleActive sevm b old0 old1 →
      load9 = sloadCost sevm (afterSload sevm b 8) 9 ∧
      store9 = sstoreCost sevm (afterSload sevm (afterSload sevm b 8) 9) 9
        (updateAccumulatorWord ((afterSload sevm b 8).getStorVal sevm.currentTarget 9)
          (updatePriceWord old0 old1)
          (updateElapsedWord (b.getStorVal sevm.currentTarget 8) sevm.benvStat.time)) ∧
      load10 = sloadCost sevm
        (updateAccumulatorPost sevm (afterSload sevm b 8) 9 (updatePriceWord old0 old1)
          (updateElapsedWord (b.getStorVal sevm.currentTarget 8) sevm.benvStat.time)) 10 ∧
      store10 = sstoreCost sevm (afterSload sevm
        (updateAccumulatorPost sevm (afterSload sevm b 8) 9 (updatePriceWord old0 old1)
          (updateElapsedWord (b.getStorVal sevm.currentTarget 8) sevm.benvStat.time)) 10) 10
        (updateAccumulatorWord
          ((updateAccumulatorPost sevm (afterSload sevm b 8) 9 (updatePriceWord old0 old1)
            (updateElapsedWord (b.getStorVal sevm.currentTarget 8) sevm.benvStat.time)).getStorVal
            sevm.currentTarget 10) (updatePriceWord old1 old0)
          (updateElapsedWord (b.getStorVal sevm.currentTarget 8) sevm.benvStat.time)))
    (sentry8 : gCallStipend < G + swapSyncGas n p + store8)
    (sentry10 : updateOracleActive sevm b old0 old1 →
      gCallStipend < G + swapSyncGas n p + load8 + store8 + 110 + store10)
    (sentry9 : updateOracleActive sevm b old0 old1 →
      gCallStipend < G + swapSyncGas n p + load8 + store8 + 110 +
        load10 + store10 + 42 + 149 + store9) :
    SFunc.RunExact cert.prog sevm
      (St b (old1 :: old0 :: balance1 :: balance0 :: tag :: R) M
        (G + swapSyncGas n p + load8 + store8 + 110 +
          (if updateOracleActive sevm b old0 old1 then load9 + store9 + load10 + store10 + 382 else 0) +
          17 + 20 +
          (if updateOraclePrefixWord (b.getStorVal sevm.currentTarget 8) sevm.benvStat.time old0 = 0
            then 0 else 17) + headerLoad + 75 +
          (if updateElapsedWord (b.getStorVal sevm.currentTarget 8) sevm.benvStat.time &&& reserveMask32 = 0
            then 0 else 17) + 60)) t_22e0_c60
      (.returned (St (updateWorld sevm b old0 old1 balance0 balance1) R
        (swapSyncMemory M p (updateFinalPackedWord sevm b old0 old1 balance0 balance1)) G)) := by
  let dt := updateElapsedWord (b.getStorVal sevm.currentTarget 8) sevm.benvStat.time
  let ts := updateTimestampWord sevm.benvStat.time
  let prefixFlag := updateOraclePrefixWord (b.getStorVal sevm.currentTarget 8) sevm.benvStat.time old0
  let flag := updateOracleReserveFlagWord prefixFlag old1
  let tailGas := G + swapSyncGas n p + load8 + store8 + 110
  let oracleGas := if updateOracleActive sevm b old0 old1 then load9 + store9 + load10 + store10 + 382 else 0
  let result := Outcome.returned (St (updateWorld sevm b old0 old1 balance0 balance1) R
    (swapSyncMemory M p (updateFinalPackedWord sevm b old0 old1 balance0 balance1)) G)
  have eventRun : SFunc.RunExact cert.prog sevm
      (St (updatePackedPost sevm (updateOracleWorld sevm b old0 old1) balance0 balance1 ts)
        (reserveDiv112 :: reserveMask112 :: updateFinalPackedWord sevm b old0 old1 balance0 balance1 ::
          dt :: ts :: old1 :: old0 :: balance1 :: balance0 :: tag :: R) M (G + swapSyncGas n p))
      updateSyncTree result := by
    exact swapSyncEvent_exact static mem lower width (by omega)
  have packedRun := update_packed_store_exact fork static packedLoadCharge packedStoreCharge sentry8
    (by omega : R.length ≤ 1010) eventRun
  have packedGas : G + swapSyncGas n p + load8 + store8 + 110 = tailGas := rfl
  change SFunc.RunExact cert.prog sevm
    (St (updateOracleWorld sevm b old0 old1) (dt :: ts :: old1 :: old0 :: balance1 :: balance0 :: tag :: R)
      M ((G + swapSyncGas n p) + load8 + store8 + 110)) t_2492_c22 result at packedRun
  rw [packedGas] at packedRun
  have oracleRun : SFunc.RunExact cert.prog sevm
      (St (afterSload sevm b 8) (dt :: ts :: old1 :: old0 :: balance1 :: balance0 :: tag :: R)
        M (tailGas + oracleGas)) (if flag = 0 then t_2492_c22 else t_23e8_c21) result := by
    have flagSource : flag = if updateOracleActive sevm b old0 old1 then 1 else 0 :=
      update_oracle_flag_source
    by_cases active : updateOracleActive sevm b old0 old1
    · obtain ⟨charge9, write9, charge10, write10⟩ := oracleCharges active
      rw [flagSource, ite_eq_left active, ite_eq_right (by decide : (1 : B256) ≠ 0)]
      have oracleEq : updateOracleWorld sevm b old0 old1 =
          updateAccumulatorPost sevm
            (updateAccumulatorPost sevm (afterSload sevm b 8) 9 (updatePriceWord old0 old1) dt)
            10 (updatePriceWord old1 old0) dt := by
        unfold updateOracleWorld
        exact ite_eq_left active
      rw [oracleEq] at packedRun
      have h10 := update_accumulator1_exact fork static charge10 write10 (sentry10 active)
        (by omega : R.length ≤ 1012) packedRun
      have h9 := update_accumulator0_exact fork static charge9 write9 (sentry9 active)
        active.2.2 room h10
      have h0 := update_price0_exact
        active.2.1 room h9
      have gas : tailGas + oracleGas = tailGas + load10 + store10 + 42 + load9 + store9 + 191 + 149 := by
        dsimp only [oracleGas]
        rw [ite_eq_left active]
        omega
      rw [gas]
      exact h0
    · rw [flagSource, ite_eq_right active, ite_eq_left (rfl : (0 : B256) = 0)]
      have oracleEq : updateOracleWorld sevm b old0 old1 = afterSload sevm b 8 := by
        unfold updateOracleWorld
        exact ite_eq_right active
      dsimp only [oracleGas]
      rw [ite_eq_right active, Nat.add_zero]
      rw [oracleEq] at packedRun
      exact packedRun
  have routeRun := update_oracle_route_exact (by omega : R.length ≤ 1015) oracleRun
  have reserveRun := update_oracle_reserve_exact (by omega : R.length ≤ 1014) routeRun
  have headerRun := update_header_exact fork headerCharge (by omega : R.length ≤ 1014) reserveRun
  have guardsRun := update_guards_exact bound0 bound1 (by omega : R.length ≤ 1016) headerRun
  exact guardsRun


/-- The packed-slot load `_update` performs, in the world its oracle stage left. -/
def swapUpdLoad8 (sevm : Sevm) (b : Devm) (old0 old1 : B256) : Nat :=
  sloadCost sevm (updateOracleWorld sevm b old0 old1) 8

/-- The packed-slot store `_update` performs. -/
def swapUpdStore8 (sevm : Sevm) (b : Devm) (old0 old1 balance0 balance1 : B256) : Nat :=
  sstoreCost sevm (afterSload sevm (updateOracleWorld sevm b old0 old1) 8) 8
    (updateFinalPackedWord sevm b old0 old1 balance0 balance1)

/-- The cumulative-price-0 load (oracle arm). -/
def swapUpdLoad9 (sevm : Sevm) (b : Devm) : Nat := sloadCost sevm (afterSload sevm b 8) 9

/-- The cumulative-price-0 store (oracle arm). -/
def swapUpdStore9 (sevm : Sevm) (b : Devm) (old0 old1 : B256) : Nat :=
  sstoreCost sevm (afterSload sevm (afterSload sevm b 8) 9) 9
    (updateAccumulatorWord ((afterSload sevm b 8).getStorVal sevm.currentTarget 9)
      (updatePriceWord old0 old1)
      (updateElapsedWord (b.getStorVal sevm.currentTarget 8) sevm.benvStat.time))

/-- The world after the first accumulator store (oracle arm). -/
def swapUpdAcc0 (sevm : Sevm) (b : Devm) (old0 old1 : B256) : Devm :=
  updateAccumulatorPost sevm (afterSload sevm b 8) 9 (updatePriceWord old0 old1)
    (updateElapsedWord (b.getStorVal sevm.currentTarget 8) sevm.benvStat.time)

/-- The cumulative-price-1 load (oracle arm). -/
def swapUpdLoad10 (sevm : Sevm) (b : Devm) (old0 old1 : B256) : Nat :=
  sloadCost sevm (swapUpdAcc0 sevm b old0 old1) 10

/-- The cumulative-price-1 store (oracle arm). -/
def swapUpdStore10 (sevm : Sevm) (b : Devm) (old0 old1 : B256) : Nat :=
  sstoreCost sevm (afterSload sevm (swapUpdAcc0 sevm b old0 old1) 10) 10
    (updateAccumulatorWord ((swapUpdAcc0 sevm b old0 old1).getStorVal sevm.currentTarget 10)
      (updatePriceWord old1 old0)
      (updateElapsedWord (b.getStorVal sevm.currentTarget 8) sevm.benvStat.time))

/-- **Closed `_update` charge at pointer `p`**: every term is the executed primitive's
selected cost over the actual world (no existential segment cost). -/
def swapUpdateCharge (sevm : Sevm) (b : Devm) (n : Nat) (p old0 old1 balance0 balance1 : B256) :
    Nat :=
  swapSyncGas n p + swapUpdLoad8 sevm b old0 old1 + swapUpdStore8 sevm b old0 old1 balance0 balance1 +
    110 + (if updateOracleActive sevm b old0 old1 then swapUpdLoad9 sevm b +
      swapUpdStore9 sevm b old0 old1 + swapUpdLoad10 sevm b old0 old1 +
      swapUpdStore10 sevm b old0 old1 + 382 else 0) + 17 + 20 +
    (if updateOraclePrefixWord (b.getStorVal sevm.currentTarget 8) sevm.benvStat.time old0 = 0
      then 0 else 17) + sloadCost sevm b 8 + 75 +
    (if updateElapsedWord (b.getStorVal sevm.currentTarget 8) sevm.benvStat.time &&& reserveMask32 = 0
      then 0 else 17) + 60

/-- The three SSTORE sentries `_update` needs, at the gas left after it returns. -/
structure SwapUpdateSentries (sevm : Sevm) (b : Devm) (n : Nat)
    (p old0 old1 balance0 balance1 : B256) (G : Nat) : Prop where
  s8 : gCallStipend < G + swapSyncGas n p + swapUpdStore8 sevm b old0 old1 balance0 balance1
  s10 : updateOracleActive sevm b old0 old1 →
    gCallStipend < G + swapSyncGas n p + swapUpdLoad8 sevm b old0 old1 +
      swapUpdStore8 sevm b old0 old1 balance0 balance1 + 110 + swapUpdStore10 sevm b old0 old1
  s9 : updateOracleActive sevm b old0 old1 →
    gCallStipend < G + swapSyncGas n p + swapUpdLoad8 sevm b old0 old1 +
      swapUpdStore8 sevm b old0 old1 balance0 balance1 + 110 + swapUpdLoad10 sevm b old0 old1 +
      swapUpdStore10 sevm b old0 old1 + 42 + 149 + swapUpdStore9 sevm b old0 old1

/-- `swapUpdate_exact` with every charge closed (`swapUpdateCharge`). -/
theorem swapUpdate_closed {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G n : Nat} {p old0 old1 balance0 balance1 tag : B256}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem p n M)
    (lower : 128 ≤ p.toNat) (width : p.toNat + 260 < 2 ^ 256)
    (static : sevm.isStatic = false) (bound0 : balance0.toNat < 2 ^ 112)
    (bound1 : balance1.toNat < 2 ^ 112) (room : R.length ≤ 1008)
    (sentries : SwapUpdateSentries sevm b n p old0 old1 balance0 balance1 G) :
    SFunc.RunExact cert.prog sevm
      (St b (old1 :: old0 :: balance1 :: balance0 :: tag :: R) M
        (G + swapUpdateCharge sevm b n p old0 old1 balance0 balance1)) t_22e0_c60
      (.returned (St (updateWorld sevm b old0 old1 balance0 balance1) R
        (swapSyncMemory M p (updateFinalPackedWord sevm b old0 old1 balance0 balance1)) G)) := by
  have run := swapUpdate_exact (load9 := swapUpdLoad9 sevm b)
    (store9 := swapUpdStore9 sevm b old0 old1) (load10 := swapUpdLoad10 sevm b old0 old1)
    (store10 := swapUpdStore10 sevm b old0 old1) (tag := tag) (R := R)
    fork mem lower width static bound0 bound1 room rfl rfl rfl
    (fun _ => ⟨rfl, rfl, rfl, rfl⟩) sentries.s8 sentries.s10 sentries.s9
  convert run using 2
  unfold swapUpdateCharge swapUpdLoad8 swapUpdStore8
  omega


/-- One word store at `i` over an allocation of `m` bytes: base charge plus expansion. -/
def swapStoreCost (m i : Nat) : Nat :=
  3 + (calculateMemoryGasCost (memExtSize m i 32) - calculateMemoryGasCost m)

/-- The `Swap` payload staged at `p`: both inferred inputs and both outputs. -/
def swapEventMemory (M : Mem) (p in0 in1 a0 a1 : B256) : Mem :=
  (((M.write p.toNat in0.toBytes).write (p.toNat + 32) in1.toBytes).write (p.toNat + 64)
    a0.toBytes).write (p.toNat + 96) a1.toBytes

/-- The `Swap` log charge over an allocation `m` at `p` after the unlock store, as executed. -/
def swapEventRunGas (G : Nat) (m : Nat) (p : B256) (unlockCost : Nat) : Nat :=
  G + 26 + unlockCost + 2581 +
    swapStoreCost (memExtSize (memExtSize (memExtSize m p.toNat 32) (p.toNat + 32) 32)
      (p.toNat + 64) 32) (p.toNat + 96) + 15 +
    swapStoreCost (memExtSize (memExtSize m p.toNat 32) (p.toNat + 32) 32) (p.toNat + 64) + 15 +
    swapStoreCost (memExtSize m p.toNat 32) (p.toNat + 32) + 15 +
    swapStoreCost m p.toNat + 16

/-- **Forward `Swap` log and unlock** (`t_0ce4_c8`, the suffix of `swapTail_inv`): the four
payload words staged at `p`, `LOG3` with caller and masked recipient topics, the unlock
store and the body's return. -/
theorem swapEvent_exact {sevm : Sevm} {W : Devm} {S : List B256} {M : Mem} {G n : Nat}
    {p in1 in0 bal1 bal0 r1 r0 len off toW a1 a0 ρ : B256}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem p n M)
    (lower : 128 ≤ p.toNat) (width : p.toNat + 260 < 2 ^ 256)
    (static : sevm.isStatic = false) (room : S.length ≤ 990)
    (unlock : gCallStipend < G + 26 +
      sstoreCost sevm (W.addLog (swapEventLog sevm in0 in1 a0 a1 toW)) 12 1) :
    SFunc.RunExact cert.prog sevm
      (St W (in1 :: in0 :: bal1 :: bal0 :: r1 :: r0 :: len :: off :: toW :: a1 :: a0 :: ρ :: S) M
        (swapEventRunGas G n p
          (sstoreCost sevm (W.addLog (swapEventLog sevm in0 in1 a0 a1 toW)) 12 1))) t_0ce4_c8
      (.returned (St (afterSstore sevm (W.addLog (swapEventLog sevm in0 in1 a0 a1 toW)) 12 1) S
        (swapEventMemory M p in0 in1 a0 a1) G)) := by
  have p32 : (p + (32 : B256)).toNat = p.toNat + 32 := swapPtr_add (k := 32) (by omega)
  have p64 : ((64 : B256) + p).toNat = p.toNat + 64 := by
    rw [B256.add_comm]
    exact swapPtr_add (k := 64) (by omega)
  have p96 : (p + (96 : B256)).toNat = p.toNat + 96 := swapPtr_add (k := 96) (by omega)
  have m1 := mem.write p.toNat in0 (Or.inr (by omega))
  have m2 := m1.write (p.toNat + 32) in1 (Or.inr (by omega))
  have m3 := m2.write (p.toNat + 64) a0 (Or.inr (by omega))
  have m4 := m3.write (p.toNat + 96) a1 (Or.inr (by omega))
  have covered : p.toNat + 128 ≤ memExtSize (memExtSize (memExtSize (memExtSize n p.toNat 32)
      (p.toNat + 32) 32) (p.toNat + 64) 32) (p.toNat + 96) 32 := by
    have h := (Mem.memWord_write_word ((((M.write p.toNat in0.toBytes).write (p.toNat + 32)
      in1.toBytes).write (p.toNat + 64) a0.toBytes)) (p.toNat + 96) a1).2
    rw [m4.size] at h
    omega
  unfold swapEventRunGas t_0ce4_c8
  apply rx_dest
  apply rx_push (w := 64) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup1 (by simp only [List.length_cons]; omega)
  refine rx_mload (c := 3) ?_ mem.word (mem.read_self (by change 64 + 32 ≤ n; have := mem.ge; omega))
    (by simp only [List.length_cons]; omega) ?_
  · rw [St.extCost_eq mem.size, show (64 : B256).toNat = 64 from rfl,
      memExtSize_of_le mem.n32 (by have := mem.ge; omega), Nat.sub_self]
    rfl
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  refine rx_mstore (c := swapStoreCost n p.toNat) ?_ rfl ?_
  · rw [St.extCost_eq mem.size]
    rfl
  apply rx_push (w := 32) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_add (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_swap1
  refine rx_mstore (c := swapStoreCost (memExtSize n p.toNat 32) (p.toNat + 32)) ?_
    (by rw [p32]) ?_
  · rw [St.extCost_eq m1.size, p32]
    rfl
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_add (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_swap1
  refine rx_mstore (c := swapStoreCost (memExtSize (memExtSize n p.toNat 32) (p.toNat + 32) 32)
    (p.toNat + 64)) ?_ (by rw [p64]) ?_
  · rw [St.extCost_eq m2.size, p64]
    rfl
  apply rx_push (w := 96) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_add (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_swap1
  refine rx_mstore (c := swapStoreCost (memExtSize (memExtSize (memExtSize n p.toNat 32)
    (p.toNat + 32) 32) (p.toNat + 64) 32) (p.toNat + 96)) ?_ (by rw [p96]) ?_
  · rw [St.extCost_eq m3.size, p96]
    rfl
  apply rx_swap1
  refine rx_mload (c := 3) ?_ m4.word
    (m4.read_self (i := 64) (sz := 32) (by have := m4.ge; omega))
    (by simp only [List.length_cons]; omega) ?_
  · rw [St.extCost_eq m4.size, show (64 : B256).toNat = 64 from rfl,
      memExtSize_of_le m4.n32 (by have := m4.ge; omega), Nat.sub_self]
    rfl
  apply rx_push (w := 0xffffffffffffffffffffffffffffffffffffffff) rfl
    (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_and (v := swapTokenWord toW) rfl (by simp only [List.length_cons]; omega)
  apply rx_swap2
  apply rx_caller (by simp only [List.length_cons]; omega)
  apply rx_swap2
  apply rx_push (w := swapEventTopic) rfl (by simp only [List.length_cons]; omega)
  apply rx_swap2
  apply rx_dup2 (by simp only [List.length_cons]; omega)
  apply rx_swap1
  apply rx_sub' (v := 0) (B256.sub_self _) (by simp only [List.length_cons]; omega)
  apply rx_push (w := 128) rfl (by simp only [List.length_cons]; omega)
  apply rx_add' (v := 128) (by decide) (by simp only [List.length_cons]; omega)
  apply rx_swap1
  refine rx_log3 (c := 2524) static ?_ (Mem.read_four_word_writes mem.wf p.toNat in0 in1 a0 a1)
    (m4.read_self covered) ?_
  · rw [St.extCost_eq m4.size, show (128 : B256).toNat = 128 from rfl,
      memExtSize_of_le m4.n32 covered, Nat.sub_self]
    rfl
  apply rx_pop
  apply rx_pop
  apply rx_push (w := 1) rfl (by simp only [List.length_cons]; omega)
  apply rx_push (w := 12) rfl (by simp only [List.length_cons]; omega)
  refine rx_sstore fork unlock static ?_
  apply rx_pop
  apply rx_pop
  apply rx_pop
  apply rx_pop
  apply rx_pop
  apply rx_pop
  apply rx_pop
  apply rx_pop
  apply rx_pop
  exact rx_ret

/-- The world the unlock store reads: `_update`'s world with the `Swap` log appended. -/
def swapLoggedWorld (sevm : Sevm) (b : Devm) (r0 r1 bal0 bal1 in0 in1 a0 a1 toW : B256) : Devm :=
  (updateWorld sevm b r0 r1 bal0 bal1).addLog (swapEventLog sevm in0 in1 a0 a1 toW)

/-- The selected cost of the unlock store. -/
def swapUnlockCost (sevm : Sevm) (b : Devm) (r0 r1 bal0 bal1 in0 in1 a0 a1 toW : B256) : Nat :=
  sstoreCost sevm (swapLoggedWorld sevm b r0 r1 bal0 bal1 in0 in1 a0 a1 toW) 12 1

/-- **Forward tail** (dual of `swapTail_inv`): `_update` at `p`, the `Swap` log staged at `p`,
the unlock store and the body's return, with the exact closed charge. -/
theorem swapTail_exact {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G n : Nat}
    {p adj1 adj0 in1 in0 bal1 bal0 r1 r0 len off toW a1 a0 ρ : B256}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem p n M)
    (lower : 128 ≤ p.toNat) (width : p.toNat + 260 < 2 ^ 256)
    (static : sevm.isStatic = false) (bound0 : bal0.toNat < 2 ^ 112)
    (bound1 : bal1.toNat < 2 ^ 112) (room : S.length ≤ 990)
    (sentries : SwapUpdateSentries sevm b n p r0 r1 bal0 bal1
      (swapEventRunGas G (swapSyncSize n p) p
        (swapUnlockCost sevm b r0 r1 bal0 bal1 in0 in1 a0 a1 toW)))
    (unlock : gCallStipend < G + 26 + swapUnlockCost sevm b r0 r1 bal0 bal1 in0 in1 a0 a1 toW) :
    SFunc.RunExact cert.prog sevm
      (St b (adj1 :: adj0 :: in1 :: in0 :: bal1 :: bal0 :: r1 :: r0 :: len :: off :: toW ::
        a1 :: a0 :: ρ :: S) M
        (swapEventRunGas G (swapSyncSize n p) p
          (swapUnlockCost sevm b r0 r1 bal0 bal1 in0 in1 a0 a1 toW) +
          swapUpdateCharge sevm b n p r0 r1 bal0 bal1 + 31)) t_0cd6_c8
      (.returned (St (afterSstore sevm (swapLoggedWorld sevm b r0 r1 bal0 bal1 in0 in1 a0 a1 toW)
        12 1) S
        (swapEventMemory (swapSyncMemory M p (updateFinalPackedWord sevm b r0 r1 bal0 bal1))
          p in0 in1 a0 a1) G)) := by
  unfold t_0cd6_c8
  apply rx_dest
  apply rx_pop
  apply rx_pop
  apply rx_push (w := 0x0ce4) rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_dup rfl (by simp only [List.length_cons]; omega)
  apply rx_push (w := 0x22e0) rfl (by simp only [List.length_cons]; omega)
  refine rx_callRet rfl (swapUpdate_closed fork mem lower width static bound0 bound1
    (by simp only [List.length_cons]; omega) sentries) ?_
  exact swapEvent_exact fork (swapSyncMemory_ptr _ mem lower) lower width static room unlock

end Blanc.Lift.UniswapV2Pair
