import Blanc.Lift.UniswapV2Pair.UpdateWalk

/-! Source correspondence of the actual shared reserve update. Cached reserves
remain separate from the currently stored timestamp and cumulative prices. -/
namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- A bounded cached-reserve price agrees with the source UQ quotient. -/
theorem updatePriceWord_source {den num : B256}
    (denBound : den.toNat < 2 ^ 112) (numBound : num.toNat < 2 ^ 112)
    (nonzero : den ≠ 0) :
    updatePriceWord den num = (num.toNat * 2 ^ 112 / den.toNat).toB256 := by
  have numeratorBound : num.toNat * 2 ^ 112 < 2 ^ 224 := by
    simpa only [show 2 ^ 112 * 2 ^ 112 = 2 ^ 224 from by decide] using
      Nat.mul_lt_mul_of_pos_right numBound (by decide : 0 < 2 ^ 112)
  have encodedBound : (uqEncodeWord num).toNat < 2 ^ 224 := by
    rw [uqEncodeWord_source numBound, B256.toNat_toB256_of_lt
      (lt_trans numeratorBound (by decide : 2 ^ 224 < 2 ^ 256))]
    exact numeratorBound
  unfold updatePriceWord
  rw [show uqMask224 = (2 ^ 224 - 1).toB256 from rfl,
    PackedWord.lowMask_eq_self_of_lt (by decide) encodedBound,
    uqDivWord_source denBound encodedBound nonzero,
    uqEncodeWord_source numBound,
    B256.toNat_toB256_of_lt (lt_trans numeratorBound (by decide : 2 ^ 224 < 2 ^ 256))]

/-- The actual accumulator product is unwrapped; its cumulative addition
retains B256 wrapping exactly as in the source model. -/
theorem updateAccumulatorWord_source {old den num elapsed : B256}
    (denBound : den.toNat < 2 ^ 112) (numBound : num.toNat < 2 ^ 112)
    (nonzero : den ≠ 0) :
    updateAccumulatorWord old (updatePriceWord den num) elapsed =
      old + ((num.toNat * 2 ^ 112 / den.toNat) *
        (elapsed &&& reserveMask32).toNat).toB256 := by
  have numeratorBound : num.toNat * 2 ^ 112 < 2 ^ 224 := by
    simpa only [show 2 ^ 112 * 2 ^ 112 = 2 ^ 224 from by decide] using
      Nat.mul_lt_mul_of_pos_right numBound (by decide : 0 < 2 ^ 112)
  have quotientBound : num.toNat * 2 ^ 112 / den.toNat < 2 ^ 224 :=
    lt_of_le_of_lt (Nat.div_le_self _ _) numeratorBound
  have priceRead : (updatePriceWord den num).toNat = num.toNat * 2 ^ 112 / den.toNat := by
    rw [updatePriceWord_source denBound numBound nonzero,
      B256.toNat_toB256_of_lt (lt_trans quotientBound (by decide : 2 ^ 224 < 2 ^ 256))]
  have priceBound : (updatePriceWord den num).toNat < 2 ^ 224 := by
    rw [priceRead]
    exact quotientBound
  have elapsedBound : (elapsed &&& reserveMask32).toNat < 2 ^ 32 := by
    rw [show reserveMask32 = (2 ^ 32 - 1).toB256 from rfl,
      PackedWord.lowMask_toNat elapsed (k := 32) (by decide)]
    exact Nat.mod_lt _ (Nat.two_pow_pos 32)
  have productBound : (num.toNat * 2 ^ 112 / den.toNat) *
      (elapsed &&& reserveMask32).toNat < 2 ^ 256 := by
    calc
      _ ≤ (num.toNat * 2 ^ 112 / den.toNat) * 2 ^ 32 :=
        Nat.mul_le_mul_left _ (Nat.le_of_lt elapsedBound)
      _ < 2 ^ 224 * 2 ^ 32 := Nat.mul_lt_mul_of_pos_right quotientBound (by decide)
      _ = 2 ^ 256 := by decide
  have productEq : updatePriceWord den num * (elapsed &&& reserveMask32) =
      ((num.toNat * 2 ^ 112 / den.toNat) * (elapsed &&& reserveMask32).toNat).toB256 := by
    apply B256.toNat_inj
    rw [B256.toNat_mul_mod, priceRead, Nat.mod_eq_of_lt productBound,
      B256.toNat_toB256_of_lt productBound]
  unfold updateAccumulatorWord
  rw [show uqMask224 = (2 ^ 224 - 1).toB256 from rfl,
    PackedWord.lowMask_eq_self_of_lt (by decide) priceBound, productEq, B256.add_comm]

theorem updateOracleWorld_slot8H (sevm : Sevm) (b : Devm) (old0 old1 : B256) :
    (updateOracleWorldH sevm b old0 old1).getStorVal sevm.currentTarget 8 =
      b.getStorVal sevm.currentTarget 8 := by
  unfold updateOracleWorldH
  split
  · unfold updateAccumulatorPostH
    rw [getStorVal_afterStoreH, Stor.get_set_ne _ (by decide : (10 : B256) ≠ 8)]
    change (afterSstoreH sevm (afterSloadH sevm (afterSloadH sevm b 8) 9) 9 _).getStorVal
      sevm.currentTarget 8 = _
    rw [getStorVal_afterStoreH, Stor.get_set_ne _ (by decide : (9 : B256) ≠ 8)]
    exact getStorVal_afterSloadH
  · exact getStorVal_afterSloadH

theorem updateWorld_storage_frameH {sevm : Sevm} {b : Devm} {old0 old1 balance0 balance1 : B256}
    {a : Adr} {k : B256}
    (frame : a ≠ sevm.currentTarget ∨ (k ≠ 8 ∧ k ≠ 9 ∧ k ≠ 10)) :
    (updateWorldH sevm b old0 old1 balance0 balance1).getStorVal a k = b.getStorVal a k := by
  unfold updateWorldH updateSyncPost
  change (Devm.getStor (Devm.addLog _ _) a).get k = _
  rw [getStor_addLog]
  by_cases account : a = sevm.currentTarget
  · subst a
    obtain ⟨key8, key9, key10⟩ := frame.resolve_left (not_ne_iff.mpr rfl)
    unfold updatePackedPostH
    rw [getStor_afterStoreH, Stor.get_set_ne _ (Ne.symm key8)]
    change (updateOracleWorldH sevm b old0 old1).getStorVal sevm.currentTarget k = _
    unfold updateOracleWorldH
    split
    · unfold updateAccumulatorPostH
      rw [getStorVal_afterStoreH, Stor.get_set_ne _ (Ne.symm key10)]
      change (afterSstoreH sevm (afterSloadH sevm (afterSloadH sevm b 8) 9) 9 _).getStorVal
        sevm.currentTarget k = _
      rw [getStorVal_afterStoreH, Stor.get_set_ne _ (Ne.symm key9)]
      exact getStorVal_afterSloadH
    · exact getStorVal_afterSloadH
  · unfold updatePackedPostH
    rw [getStor_afterStore_neH account]
    unfold updateOracleWorldH
    split
    · unfold updateAccumulatorPostH
      rw [getStor_afterStore_neH account, getStor_afterStore_neH account, afterSloadH_getStor]
      rfl
    · rw [afterSloadH_getStor]
      rfl

/-- Actual TIMESTAMP truncation agrees with the source uint32 field. -/
theorem updateTimestampWord_source (timestamp : B256) :
    updateTimestampWord timestamp = (UInt32.ofNat (timestamp.toNat % 2 ^ 32)).toB256 := by
  apply B256.toNat_inj
  unfold updateTimestampWord
  rw [B256.and_comm, show reserveMask32 = (2 ^ 32 - 1).toB256 from rfl,
    PackedWord.lowMask_toNat timestamp (k := 32) (by decide)]
  have wordNat (x : UInt32) : x.toB256.toNat = x.toNat := by
    simp only [UInt32.toB256, B256.toNat, B128.toNat, B128.zero_eq,
      UInt64.toNat_zero, Nat.zero_shiftLeft, Nat.zero_or, UInt32.toNat_toUInt64]
  rw [wordNat, UInt32.toNat_ofNat', Nat.mod_mod]

/-- The oracle observes the timestamp in the current slot, independently of
its cached reserve parameters. -/
theorem updateElapsedWord_layout_source {st : State} {sevm : Sevm} {b : Devm}
    (slots : ReserveSlotMatches st sevm b) :
    (updateElapsedWord (b.getStorVal sevm.currentTarget 8) sevm.benvStat.time &&& reserveMask32).toNat =
      (sevm.benvStat.time.toNat % 2 ^ 32 + 2 ^ 32 - st.blockTimestampLast.toNat) % 2 ^ 32 := by
  have lastRead := congrArg B256.toNat slots.2.2
  simp only [UInt32.toB256, B256.toNat, B128.toNat, B128.zero_eq,
    UInt64.toNat_zero, Nat.zero_shiftLeft, Nat.zero_or, UInt32.toNat_toUInt64] at lastRead
  exact updateElapsedWord_source lastRead (UInt32.toNat_lt _)

/-- The actual short-circuit oracle predicate is the source predicate for
bounded cached reserves and the currently stored timestamp. -/
theorem updateOracleActive_source {st : State} {sevm : Sevm} {b : Devm} {old0 old1 : B256}
    (slots : ReserveSlotMatches st sevm b)
    (bound0 : old0.toNat < 2 ^ 112) (bound1 : old1.toNat < 2 ^ 112) :
    updateOracleActive sevm b old0 old1 ↔
      (sevm.benvStat.time.toNat % 2 ^ 32 + 2 ^ 32 - st.blockTimestampLast.toNat) % 2 ^ 32 > 0 ∧
      old0.toNat ≠ 0 ∧ old1.toNat ≠ 0 := by
  have elapsed := updateElapsedWord_layout_source slots
  have reserve0 : old0 &&& reserveMask112 = old0 :=
    PackedWord.lowMask_eq_self_of_lt (k := 112) (by decide) bound0
  have reserve1 : old1 &&& reserveMask112 = old1 :=
    PackedWord.lowMask_eq_self_of_lt (k := 112) (by decide) bound1
  unfold updateOracleActive
  rw [reserve0, reserve1]
  constructor
  · intro active
    refine ⟨Nat.pos_of_ne_zero ?_, ?_, ?_⟩
    · intro zero
      apply active.1
      apply B256.toNat_inj
      rw [elapsed, B256.toNat_zero]
      exact zero
    · intro zero
      apply active.2.1
      apply B256.toNat_inj
      rw [zero, B256.toNat_zero]
    · intro zero
      apply active.2.2
      apply B256.toNat_inj
      rw [zero, B256.toNat_zero]
  · intro active
    refine ⟨?_, ?_, ?_⟩
    · intro zero
      have zeroNat := congrArg B256.toNat zero
      rw [elapsed, B256.toNat_zero] at zeroNat
      omega
    · intro zero
      apply active.2.1
      rw [zero, B256.toNat_zero]
    · intro zero
      apply active.2.2
      rw [zero, B256.toNat_zero]

theorem updateOracleWorld_cumulatives_sourceH {st : State} {sevm : Sevm} {b : Devm}
    {old0 old1 : B256} (slots : ReserveSlotMatches st sevm b)
    (cum0 : b.getStorVal sevm.currentTarget 9 = st.price0CumulativeLast)
    (cum1 : b.getStorVal sevm.currentTarget 10 = st.price1CumulativeLast)
    (bound0 : old0.toNat < 2 ^ 112) (bound1 : old1.toNat < 2 ^ 112) :
    let dt := (sevm.benvStat.time.toNat % 2 ^ 32 + 2 ^ 32 - st.blockTimestampLast.toNat) % 2 ^ 32
    let active := dt > 0 ∧ old0.toNat ≠ 0 ∧ old1.toNat ≠ 0
    (updateOracleWorldH sevm b old0 old1).getStorVal sevm.currentTarget 9 =
      st.price0CumulativeLast + (if active then (old1.toNat * 2 ^ 112 / old0.toNat) * dt else 0).toB256 ∧
    (updateOracleWorldH sevm b old0 old1).getStorVal sevm.currentTarget 10 =
      st.price1CumulativeLast + (if active then (old0.toNat * 2 ^ 112 / old1.toNat) * dt else 0).toB256 := by
  dsimp only
  have elapsed := updateElapsedWord_layout_source slots
  have activeEq := updateOracleActive_source slots bound0 bound1
  by_cases active : updateOracleActive sevm b old0 old1
  · have sourceActive := activeEq.mp active
    have nz0 : old0 ≠ 0 := by
      intro zero
      apply sourceActive.2.1
      rw [zero, B256.toNat_zero]
    have nz1 : old1 ≠ 0 := by
      intro zero
      apply sourceActive.2.2
      rw [zero, B256.toNat_zero]
    unfold updateOracleWorldH
    rw [ite_eq_left active, ite_eq_left sourceActive, ite_eq_left sourceActive]
    constructor
    · unfold updateAccumulatorPostH
      rw [getStorVal_afterStoreH, Stor.get_set_ne _ (by decide : (10 : B256) ≠ 9)]
      change (afterSstoreH sevm (afterSloadH sevm (afterSloadH sevm b 8) 9) 9 _).getStorVal
        sevm.currentTarget 9 = _
      rw [getStorVal_afterStoreH, Stor.get_set_self,
        updateAccumulatorWord_source bound0 bound1 nz0, getStorVal_afterSloadH, cum0, elapsed]
    · unfold updateAccumulatorPostH
      rw [getStorVal_afterStoreH, Stor.get_set_self,
        updateAccumulatorWord_source bound1 bound0 nz1]
      rw [getStorVal_afterStoreH, Stor.get_set_ne _ (by decide : (9 : B256) ≠ 10)]
      change (afterSloadH sevm b 8).getStorVal sevm.currentTarget 10 + _ = _
      rw [getStorVal_afterSloadH, cum1, elapsed]
  · have sourceInactive := (not_congr activeEq).mp active
    unfold updateOracleWorldH
    rw [ite_eq_right active, ite_eq_right sourceInactive, ite_eq_right sourceInactive]
    simp only [getStorVal_afterSloadH, cum0, cum1, show (0 : Nat).toB256 = 0 from rfl,
      B256.add_zero, and_self]

theorem updateWorld_slot8H (sevm : Sevm) (b : Devm) (old0 old1 balance0 balance1 : B256) :
    (updateWorldH sevm b old0 old1 balance0 balance1).getStorVal sevm.currentTarget 8 =
      updateFinalPackedWordH sevm b old0 old1 balance0 balance1 := by
  unfold updateWorldH updateSyncPost
  change (Devm.getStor (Devm.addLog _ _) _).get 8 = _
  rw [getStor_addLog, updatePackedPostH, getStor_afterStoreH, Stor.get_set_self]
  rfl

theorem updateWorld_oracle_slotH {sevm : Sevm} {b : Devm} {old0 old1 balance0 balance1 key : B256}
    (other : key ≠ 8) :
    (updateWorldH sevm b old0 old1 balance0 balance1).getStorVal sevm.currentTarget key =
      (updateOracleWorldH sevm b old0 old1).getStorVal sevm.currentTarget key := by
  unfold updateWorldH updateSyncPost
  change (Devm.getStor (Devm.addLog _ _) _).get key = _
  rw [getStor_addLog, updatePackedPostH, getStor_afterStoreH, Stor.get_set_ne _ (Ne.symm other)]
  rfl

/-- The precise actual log appends the two source balance words. -/
theorem updateWorld_logs {sevm : Sevm} {b : Devm} {old0 old1 balance0 balance1 : B256}
    (bound0 : balance0.toNat < 2 ^ 112) (bound1 : balance1.toNat < 2 ^ 112) :
    (updateWorld sevm b old0 old1 balance0 balance1).logs =
      b.logs ++ [⟨sevm.currentTarget, [updateSyncTopic], encodeWords [balance0, balance1]⟩] := by
  have fields := updatePackedWord_layout
    ((updateOracleWorld sevm b old0 old1).getStorVal sevm.currentTarget 8)
    balance0 balance1 (updateTimestampWord sevm.benvStat.time)
  have field0 : reserve0Read (updateFinalPackedWord sevm b old0 old1 balance0 balance1) = balance0 := by
    rw [updateFinalPackedWord, fields.1]
    exact PackedWord.lowMask_eq_self_of_lt (k := 112) (by decide) bound0
  have field1 : reserve1Read (updateFinalPackedWord sevm b old0 old1 balance0 balance1) = balance1 := by
    rw [updateFinalPackedWord, fields.2.1]
    exact PackedWord.lowMask_eq_self_of_lt (k := 112) (by decide) bound1
  have oracleLogs : (updateOracleWorld sevm b old0 old1).logs = b.logs := by
    unfold updateOracleWorld
    split
    · simp only [updateAccumulatorPost, logs_afterStore, afterSload_logs]
    · exact afterSload_logs _ _ _
  unfold updateWorld updateSyncPost
  rw [logs_addLog, updatePackedPost, logs_afterStore, oracleLogs, field0, field1]
  simp only [encodeWords, List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem updateWorld_logsH {sevm : Sevm} {b : Devm} {old0 old1 balance0 balance1 : B256}
    (bound0 : balance0.toNat < 2 ^ 112) (bound1 : balance1.toNat < 2 ^ 112) :
    (updateWorldH sevm b old0 old1 balance0 balance1).logs =
      b.logs ++ [⟨sevm.currentTarget, [updateSyncTopic], encodeWords [balance0, balance1]⟩] := by
  have fields := updatePackedWord_layout
    ((updateOracleWorldH sevm b old0 old1).getStorVal sevm.currentTarget 8)
    balance0 balance1 (updateTimestampWord sevm.benvStat.time)
  have field0 : reserve0Read (updateFinalPackedWordH sevm b old0 old1 balance0 balance1) = balance0 := by
    rw [updateFinalPackedWordH, fields.1]
    exact PackedWord.lowMask_eq_self_of_lt (k := 112) (by decide) bound0
  have field1 : reserve1Read (updateFinalPackedWordH sevm b old0 old1 balance0 balance1) = balance1 := by
    rw [updateFinalPackedWordH, fields.2.1]
    exact PackedWord.lowMask_eq_self_of_lt (k := 112) (by decide) bound1
  have oracleLogs : (updateOracleWorldH sevm b old0 old1).logs = b.logs := by
    unfold updateOracleWorldH
    split
    · simp only [updateAccumulatorPostH, logs_afterStoreH, afterSloadH_logs]
    · exact afterSloadH_logs _ _ _
  unfold updateWorldH updateSyncPost
  rw [logs_addLog, updatePackedPostH, logs_afterStoreH, oracleLogs, field0, field1]
  simp only [encodeWords, List.flatMap_cons, List.flatMap_nil, List.append_nil]

theorem updateWorld_account_frameH {sevm : Sevm} {b : Devm} {old0 old1 balance0 balance1 : B256}
    {a : Adr} (foreign : a ≠ sevm.currentTarget) :
    (updateWorldH sevm b old0 old1 balance0 balance1).getAcct a = b.getAcct a := by
  have store (base : Devm) (key value : B256) :
      (afterSstoreH sevm base key value).getAcct a = base.getAcct a := by
    unfold afterSstoreH Devm.getAcct
    show (State.setStorVal _ _ _ _).get a = _
    unfold State.setStorVal
    dsimp only
    have target : sevm.currentTarget ≠ a := Ne.symm foreign
    split
    · rw [State.get_setPresent_ne _ target]
      unfold storageAccessH
      split
      · rfl
      · split <;> rfl
    · rw [State.get_set_ne _ target]
      unfold storageAccessH
      split
      · rfl
      · split <;> rfl
  have load (base : Devm) (key : B256) : (afterSloadH sevm base key).getAcct a = base.getAcct a := by
    unfold afterSloadH
    split
    · exact afterSload_getAcct _
    · rfl
  unfold updateWorldH updateSyncPost
  rw [getAcct_addLog]
  unfold updatePackedPostH
  rw [store, load]
  unfold updateOracleWorldH
  split
  · unfold updateAccumulatorPostH
    rw [store, load, store, load, load]
  · exact load _ _

theorem updateWorld_outputH (sevm : Sevm) (b : Devm) (old0 old1 balance0 balance1 : B256) :
    (updateWorldH sevm b old0 old1 balance0 balance1).output = b.output := by
  unfold updateWorldH updateSyncPost
  rw [output_addLog]
  unfold updatePackedPostH
  rw [afterSstoreH_output, afterSloadH_output]
  unfold updateOracleWorldH
  split
  · simp only [updateAccumulatorPostH, afterSstoreH_output, afterSloadH_output]
  · exact afterSloadH_output _ _ _

theorem update_source_resultH {st : State} {ctx : Context} {sevm : Sevm} {b : Devm}
    {old0 old1 balance0 balance1 : B256}
    (slots : ReserveSlotMatches st sevm b)
    (cum0 : b.getStorVal sevm.currentTarget 9 = st.price0CumulativeLast)
    (cum1 : b.getStorVal sevm.currentTarget 10 = st.price1CumulativeLast)
    (time : ctx.timestamp = sevm.benvStat.time) (pair : ctx.pair = sevm.currentTarget)
    (oldBound0 : old0.toNat < 2 ^ 112) (oldBound1 : old1.toNat < 2 ^ 112)
    (bound0 : balance0.toNat < 2 ^ 112) (bound1 : balance1.toNat < 2 ^ 112) :
    ∃ post event oracle,
      st.update ctx balance0 balance1 old0.toNat old1.toNat = .ok (post, event, oracle) ∧
      ReserveSlotMatches post sevm (updateWorldH sevm b old0 old1 balance0 balance1) ∧
      (updateWorldH sevm b old0 old1 balance0 balance1).getStorVal sevm.currentTarget 9 = post.price0CumulativeLast ∧
      (updateWorldH sevm b old0 old1 balance0 balance1).getStorVal sevm.currentTarget 10 = post.price1CumulativeLast ∧
      event = .sync balance0.toNat balance1.toNat ∧
      (updateWorldH sevm b old0 old1 balance0 balance1).logs =
        b.logs ++ [⟨ctx.pair, [updateSyncTopic], encodeWords [balance0, balance1]⟩] := by
  unfold State.update
  rw [dite_eq_left bound0, dite_eq_left bound1, time]
  have cumulative := updateOracleWorld_cumulatives_sourceH slots cum0 cum1 oldBound0 oldBound1
  have packed := updatePackedWord_layout
    ((updateOracleWorldH sevm b old0 old1).getStorVal sevm.currentTarget 8)
    balance0 balance1 (updateTimestampWord sevm.benvStat.time)
  rw [updateOracleWorld_slot8H] at packed
  refine ⟨_, _, _, rfl, ?_, ?_, ?_, rfl, ?_⟩
  · unfold ReserveSlotMatches
    rw [updateWorld_slot8H, updateFinalPackedWordH, updateOracleWorld_slot8H,
      packed.1, packed.2.1, packed.2.2]
    refine ⟨?_, ?_, ?_⟩
    · rw [show reserveMask112 = (2 ^ 112 - 1).toB256 from rfl,
        PackedWord.lowMask_eq_self_of_lt (k := 112) (by decide) bound0]
      exact (toB256_toNat balance0).symm
    · rw [show reserveMask112 = (2 ^ 112 - 1).toB256 from rfl,
        PackedWord.lowMask_eq_self_of_lt (k := 112) (by decide) bound1]
      exact (toB256_toNat balance1).symm
    · rw [updateTimestampWord, B256.and_comm reserveMask32 sevm.benvStat.time,
        B256.and_idem_right, ← updateTimestampWord_source]
      exact B256.and_comm _ _
  · rw [updateWorld_oracle_slotH (by decide : (9 : B256) ≠ 8)]
    exact cumulative.1
  · rw [updateWorld_oracle_slotH (by decide : (10 : B256) ≠ 8)]
    exact cumulative.2
  · rw [pair]
    exact updateWorld_logsH bound0 bound1

/-- Source acceptance exposes exactly the two uint112 balance bounds. -/
theorem update_source_guards {st post : State} {ctx : Context} {balance0 balance1 : B256}
    {old0 old1 : Nat} {event : Event} {oracle : OracleUpdate}
    (accepted : st.update ctx balance0 balance1 old0 old1 = .ok (post, event, oracle)) :
    balance0.toNat < 2 ^ 112 ∧ balance1.toNat < 2 ^ 112 := by
  unfold State.update at accepted
  split at accepted
  · rename_i bound0
    split at accepted
    · rename_i bound1
      exact ⟨bound0, bound1⟩
    · cases accepted
  · cases accepted

theorem update_source_result_of_okH {st post : State} {ctx : Context} {sevm : Sevm} {b : Devm}
    {old0 old1 balance0 balance1 : B256} {event : Event} {oracle : OracleUpdate}
    (slots : ReserveSlotMatches st sevm b)
    (cum0 : b.getStorVal sevm.currentTarget 9 = st.price0CumulativeLast)
    (cum1 : b.getStorVal sevm.currentTarget 10 = st.price1CumulativeLast)
    (time : ctx.timestamp = sevm.benvStat.time) (pair : ctx.pair = sevm.currentTarget)
    (oldBound0 : old0.toNat < 2 ^ 112) (oldBound1 : old1.toNat < 2 ^ 112)
    (accepted : st.update ctx balance0 balance1 old0.toNat old1.toNat = .ok (post, event, oracle)) :
    ReserveSlotMatches post sevm (updateWorldH sevm b old0 old1 balance0 balance1) ∧
    (updateWorldH sevm b old0 old1 balance0 balance1).getStorVal sevm.currentTarget 9 = post.price0CumulativeLast ∧
    (updateWorldH sevm b old0 old1 balance0 balance1).getStorVal sevm.currentTarget 10 = post.price1CumulativeLast ∧
    event = .sync balance0.toNat balance1.toNat ∧
    (updateWorldH sevm b old0 old1 balance0 balance1).logs =
      b.logs ++ [⟨ctx.pair, [updateSyncTopic], encodeWords [balance0, balance1]⟩] := by
  obtain ⟨bound0, bound1⟩ := update_source_guards accepted
  obtain ⟨post', event', oracle', source, correspondence⟩ :=
    update_source_resultH slots cum0 cum1 time pair oldBound0 oldBound1 bound0 bound1
  have equal := Except.ok.inj (accepted.symm.trans source)
  obtain ⟨postEq, eventOracleEq⟩ := Prod.mk.inj equal
  obtain ⟨eventEq, oracleEq⟩ := Prod.mk.inj eventOracleEq
  cases postEq
  cases eventEq
  cases oracleEq
  exact correspondence

end Blanc.Lift.UniswapV2Pair
