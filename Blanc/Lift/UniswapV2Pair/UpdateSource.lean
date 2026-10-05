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

/-- The conditional cumulative writes preserve the current packed reserve slot. -/
theorem updateOracleWorld_slot8 (sevm : Sevm) (b : Devm) (old0 old1 : B256) :
    (updateOracleWorld sevm b old0 old1).getStorVal sevm.currentTarget 8 =
      b.getStorVal sevm.currentTarget 8 := by
  unfold updateOracleWorld
  split
  · unfold updateAccumulatorPost
    rw [getStorVal_afterStore, Stor.get_set_ne _ (by decide : (10 : B256) ≠ 8)]
    change (afterSstore sevm (afterSload sevm (afterSload sevm b 8) 9) 9 _).getStorVal
      sevm.currentTarget 8 = _
    rw [getStorVal_afterStore, Stor.get_set_ne _ (by decide : (9 : B256) ≠ 8)]
    exact getStorVal_afterSload
  · exact getStorVal_afterSload

/-- Every storage key outside slots8,9,10, and all foreign-account storage,
is preserved by the actual update metadata image. -/
theorem updateWorld_storage_frame {sevm : Sevm} {b : Devm} {old0 old1 balance0 balance1 : B256}
    {a : Adr} {k : B256}
    (frame : a ≠ sevm.currentTarget ∨ (k ≠ 8 ∧ k ≠ 9 ∧ k ≠ 10)) :
    (updateWorld sevm b old0 old1 balance0 balance1).getStorVal a k = b.getStorVal a k := by
  unfold updateWorld updateSyncPost
  change (Devm.getStor (Devm.addLog _ _) a).get k = _
  rw [getStor_addLog]
  by_cases account : a = sevm.currentTarget
  · subst a
    obtain ⟨key8, key9, key10⟩ := frame.resolve_left (not_ne_iff.mpr rfl)
    unfold updatePackedPost
    rw [getStor_afterStore, Stor.get_set_ne _ (Ne.symm key8)]
    change (updateOracleWorld sevm b old0 old1).getStorVal sevm.currentTarget k = _
    unfold updateOracleWorld
    split
    · unfold updateAccumulatorPost
      rw [getStorVal_afterStore, Stor.get_set_ne _ (Ne.symm key10)]
      change (afterSstore sevm (afterSload sevm (afterSload sevm b 8) 9) 9 _).getStorVal
        sevm.currentTarget k = _
      rw [getStorVal_afterStore, Stor.get_set_ne _ (Ne.symm key9)]
      exact getStorVal_afterSload
    · exact getStorVal_afterSload
  · unfold updatePackedPost
    rw [getStor_afterStore_ne account]
    unfold updateOracleWorld
    split
    · unfold updateAccumulatorPost
      rw [getStor_afterStore_ne account, getStor_afterStore_ne account, afterSload_getStor]
      rfl
    · rw [afterSload_getStor]
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

/-- Both actual cumulative slots implement the source's conditional modular
additions using independently cached reserve parameters. -/
theorem updateOracleWorld_cumulatives_source {st : State} {sevm : Sevm} {b : Devm}
    {old0 old1 : B256} (slots : ReserveSlotMatches st sevm b)
    (cum0 : b.getStorVal sevm.currentTarget 9 = st.price0CumulativeLast)
    (cum1 : b.getStorVal sevm.currentTarget 10 = st.price1CumulativeLast)
    (bound0 : old0.toNat < 2 ^ 112) (bound1 : old1.toNat < 2 ^ 112) :
    let dt := (sevm.benvStat.time.toNat % 2 ^ 32 + 2 ^ 32 - st.blockTimestampLast.toNat) % 2 ^ 32
    let active := dt > 0 ∧ old0.toNat ≠ 0 ∧ old1.toNat ≠ 0
    (updateOracleWorld sevm b old0 old1).getStorVal sevm.currentTarget 9 =
      st.price0CumulativeLast + (if active then (old1.toNat * 2 ^ 112 / old0.toNat) * dt else 0).toB256 ∧
    (updateOracleWorld sevm b old0 old1).getStorVal sevm.currentTarget 10 =
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
    unfold updateOracleWorld
    rw [ite_eq_left active, ite_eq_left sourceActive, ite_eq_left sourceActive]
    constructor
    · unfold updateAccumulatorPost
      rw [getStorVal_afterStore, Stor.get_set_ne _ (by decide : (10 : B256) ≠ 9)]
      change (afterSstore sevm (afterSload sevm (afterSload sevm b 8) 9) 9 _).getStorVal
        sevm.currentTarget 9 = _
      rw [getStorVal_afterStore, Stor.get_set_self,
        updateAccumulatorWord_source bound0 bound1 nz0, getStorVal_afterSload, cum0, elapsed]
    · unfold updateAccumulatorPost
      rw [getStorVal_afterStore, Stor.get_set_self,
        updateAccumulatorWord_source bound1 bound0 nz1]
      rw [getStorVal_afterStore, Stor.get_set_ne _ (by decide : (9 : B256) ≠ 10)]
      change (afterSload sevm b 8).getStorVal sevm.currentTarget 10 + _ = _
      rw [getStorVal_afterSload, cum1, elapsed]
  · have sourceInactive := (not_congr activeEq).mp active
    unfold updateOracleWorld
    rw [ite_eq_right active, ite_eq_right sourceInactive, ite_eq_right sourceInactive]
    simp only [getStorVal_afterSload, cum0, cum1, show (0 : Nat).toB256 = 0 from rfl,
      B256.add_zero, and_self]

/-- The final selected word is the actual single packed SSTORE value. -/
theorem updateWorld_slot8 (sevm : Sevm) (b : Devm) (old0 old1 balance0 balance1 : B256) :
    (updateWorld sevm b old0 old1 balance0 balance1).getStorVal sevm.currentTarget 8 =
      updateFinalPackedWord sevm b old0 old1 balance0 balance1 := by
  unfold updateWorld updateSyncPost
  change (Devm.getStor (Devm.addLog _ _) _).get 8 = _
  rw [getStor_addLog, updatePackedPost, getStor_afterStore, Stor.get_set_self]
  rfl

/-- The final packed SSTORE leaves both conditional cumulative slots intact. -/
theorem updateWorld_oracle_slot {sevm : Sevm} {b : Devm} {old0 old1 balance0 balance1 key : B256}
    (other : key ≠ 8) :
    (updateWorld sevm b old0 old1 balance0 balance1).getStorVal sevm.currentTarget key =
      (updateOracleWorld sevm b old0 old1).getStorVal sevm.currentTarget key := by
  unfold updateWorld updateSyncPost
  change (Devm.getStor (Devm.addLog _ _) _).get key = _
  rw [getStor_addLog, updatePackedPost, getStor_afterStore, Stor.get_set_ne _ (Ne.symm other)]
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

/-- Every foreign account, including its nonce, balance, code and complete
storage map, is preserved. -/
theorem updateWorld_account_frame {sevm : Sevm} {b : Devm} {old0 old1 balance0 balance1 : B256}
    {a : Adr} (foreign : a ≠ sevm.currentTarget) :
    (updateWorld sevm b old0 old1 balance0 balance1).getAcct a = b.getAcct a := by
  have store (base : Devm) (key value : B256) :
      (afterSstore sevm base key value).getAcct a = base.getAcct a := by
    obtain ⟨stor, account⟩ := afterSstore_getAcct (sevm := sevm) (b := base)
      (key := key) (value := value) a
    have storage := congrArg Acct.stor account
    change (afterSstore sevm base key value).getStor a = stor at storage
    rw [afterSstore_getStor_ne _ _ _ _ _ (Ne.symm foreign)] at storage
    rw [← storage] at account
    exact account
  unfold updateWorld updateSyncPost
  rw [getAcct_addLog]
  unfold updatePackedPost
  rw [store, afterSload_getAcct]
  unfold updateOracleWorld
  split
  · unfold updateAccumulatorPost
    rw [store, afterSload_getAcct, store, afterSload_getAcct, afterSload_getAcct]
  · exact afterSload_getAcct _

/-- The shared routine preserves the enclosing output field. -/
theorem updateWorld_output (sevm : Sevm) (b : Devm) (old0 old1 balance0 balance1 : B256) :
    (updateWorld sevm b old0 old1 balance0 balance1).output = b.output := by
  unfold updateWorld updateSyncPost
  rw [output_addLog]
  unfold updatePackedPost
  rw [afterSstore_output, afterSload_output]
  unfold updateOracleWorld
  split
  · simp only [updateAccumulatorPost, afterSstore_output, afterSload_output]
  · exact afterSload_output _ _ _

/-- Actual shared update metadata represents the accepted source computation.
Incoming current slots and cached old reserves are independent inputs. -/
theorem update_source_result {st : State} {ctx : Context} {sevm : Sevm} {b : Devm}
    {old0 old1 balance0 balance1 : B256}
    (slots : ReserveSlotMatches st sevm b)
    (cum0 : b.getStorVal sevm.currentTarget 9 = st.price0CumulativeLast)
    (cum1 : b.getStorVal sevm.currentTarget 10 = st.price1CumulativeLast)
    (time : ctx.timestamp = sevm.benvStat.time) (pair : ctx.pair = sevm.currentTarget)
    (oldBound0 : old0.toNat < 2 ^ 112) (oldBound1 : old1.toNat < 2 ^ 112)
    (bound0 : balance0.toNat < 2 ^ 112) (bound1 : balance1.toNat < 2 ^ 112) :
    ∃ post event oracle,
      st.update ctx balance0 balance1 old0.toNat old1.toNat = .ok (post, event, oracle) ∧
      ReserveSlotMatches post sevm (updateWorld sevm b old0 old1 balance0 balance1) ∧
      (updateWorld sevm b old0 old1 balance0 balance1).getStorVal sevm.currentTarget 9 = post.price0CumulativeLast ∧
      (updateWorld sevm b old0 old1 balance0 balance1).getStorVal sevm.currentTarget 10 = post.price1CumulativeLast ∧
      event = .sync balance0.toNat balance1.toNat ∧
      (updateWorld sevm b old0 old1 balance0 balance1).logs =
        b.logs ++ [⟨ctx.pair, [updateSyncTopic], encodeWords [balance0, balance1]⟩] := by
  unfold State.update
  rw [dite_eq_left bound0, dite_eq_left bound1, time]
  have cumulative := updateOracleWorld_cumulatives_source slots cum0 cum1 oldBound0 oldBound1
  have packed := updatePackedWord_layout
    ((updateOracleWorld sevm b old0 old1).getStorVal sevm.currentTarget 8)
    balance0 balance1 (updateTimestampWord sevm.benvStat.time)
  rw [updateOracleWorld_slot8] at packed
  refine ⟨_, _, _, rfl, ?_, ?_, ?_, rfl, ?_⟩
  · unfold ReserveSlotMatches
    rw [updateWorld_slot8, updateFinalPackedWord, updateOracleWorld_slot8,
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
  · rw [updateWorld_oracle_slot (by decide : (9 : B256) ≠ 8)]
    exact cumulative.1
  · rw [updateWorld_oracle_slot (by decide : (10 : B256) ≠ 8)]
    exact cumulative.2
  · rw [pair]
    exact updateWorld_logs bound0 bound1

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

/-- Correspondence for the exact State.update result supplied by a caller. -/
theorem update_source_result_of_ok {st post : State} {ctx : Context} {sevm : Sevm} {b : Devm}
    {old0 old1 balance0 balance1 : B256} {event : Event} {oracle : OracleUpdate}
    (slots : ReserveSlotMatches st sevm b)
    (cum0 : b.getStorVal sevm.currentTarget 9 = st.price0CumulativeLast)
    (cum1 : b.getStorVal sevm.currentTarget 10 = st.price1CumulativeLast)
    (time : ctx.timestamp = sevm.benvStat.time) (pair : ctx.pair = sevm.currentTarget)
    (oldBound0 : old0.toNat < 2 ^ 112) (oldBound1 : old1.toNat < 2 ^ 112)
    (accepted : st.update ctx balance0 balance1 old0.toNat old1.toNat = .ok (post, event, oracle)) :
    ReserveSlotMatches post sevm (updateWorld sevm b old0 old1 balance0 balance1) ∧
    (updateWorld sevm b old0 old1 balance0 balance1).getStorVal sevm.currentTarget 9 = post.price0CumulativeLast ∧
    (updateWorld sevm b old0 old1 balance0 balance1).getStorVal sevm.currentTarget 10 = post.price1CumulativeLast ∧
    event = .sync balance0.toNat balance1.toNat ∧
    (updateWorld sevm b old0 old1 balance0 balance1).logs =
      b.logs ++ [⟨ctx.pair, [updateSyncTopic], encodeWords [balance0, balance1]⟩] := by
  obtain ⟨bound0, bound1⟩ := update_source_guards accepted
  obtain ⟨post', event', oracle', source, correspondence⟩ :=
    update_source_result slots cum0 cum1 time pair oldBound0 oldBound1 bound0 bound1
  have equal := Except.ok.inj (accepted.symm.trans source)
  obtain ⟨postEq, eventOracleEq⟩ := Prod.mk.inj equal
  obtain ⟨eventEq, oracleEq⟩ := Prod.mk.inj eventOracleEq
  cases postEq
  cases eventEq
  cases oracleEq
  exact correspondence

/-- Successful actual shared bytecode derives source acceptance, exact selected
poststate, Sync log, caller tail, complete memory, mutability and frame facts. -/
theorem update_source_inv_at {st : State} {ctx : Context} {sevm : Sevm} {b : Devm}
    {R : List B256} {M : Mem} {G n : Nat} {p old0 old1 balance0 balance1 tag : B256} {o : Outcome}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem p n M)
    (low : 96 ≤ p.toNat) (high : p.toNat + 64 < 2 ^ 256)
    (slots : ReserveSlotMatches st sevm b)
    (cum0 : b.getStorVal sevm.currentTarget 9 = st.price0CumulativeLast)
    (cum1 : b.getStorVal sevm.currentTarget 10 = st.price1CumulativeLast)
    (time : ctx.timestamp = sevm.benvStat.time) (pair : ctx.pair = sevm.currentTarget)
    (oldBound0 : old0.toNat < 2 ^ 112) (oldBound1 : old1.toNat < 2 ^ 112)
    (run : SFunc.Run cert.prog sevm
      (St b (old1 :: old0 :: balance1 :: balance0 :: tag :: R) M G) t_22e0_c60 o) :
    sevm.isStatic = false ∧ ∃ gas post event oracle,
      o = .returned (St (updateWorld sevm b old0 old1 balance0 balance1) R
        (updateMemoryAt sevm b M p old0 old1 balance0 balance1) gas) ∧
      st.update ctx balance0 balance1 old0.toNat old1.toNat = .ok (post, event, oracle) ∧
      ReserveSlotMatches post sevm (updateWorld sevm b old0 old1 balance0 balance1) ∧
      (updateWorld sevm b old0 old1 balance0 balance1).getStorVal sevm.currentTarget 9 = post.price0CumulativeLast ∧
      (updateWorld sevm b old0 old1 balance0 balance1).getStorVal sevm.currentTarget 10 = post.price1CumulativeLast ∧
      event = .sync balance0.toNat balance1.toNat ∧
      (updateWorld sevm b old0 old1 balance0 balance1).logs =
        b.logs ++ [⟨ctx.pair, [updateSyncTopic], encodeWords [balance0, balance1]⟩] ∧
      (∀ a k, a ≠ sevm.currentTarget ∨ (k ≠ 8 ∧ k ≠ 9 ∧ k ≠ 10) →
        (updateWorld sevm b old0 old1 balance0 balance1).getStorVal a k = b.getStorVal a k) ∧
      (∀ a, a ≠ sevm.currentTarget →
        (updateWorld sevm b old0 old1 balance0 balance1).getAcct a = b.getAcct a) ∧
      (updateWorld sevm b old0 old1 balance0 balance1).output = b.output := by
  obtain ⟨bound0, bound1, mutable, gas, result⟩ := update_inv_at fork mem low high run
  obtain ⟨post, event, oracle, source, reserves, price0, price1, sync, logs⟩ :=
    update_source_result slots cum0 cum1 time pair oldBound0 oldBound1 bound0 bound1
  exact ⟨mutable, gas, post, event, oracle, result, source, reserves, price0, price1,
    sync, logs, fun _ _ frame => updateWorld_storage_frame frame,
    fun _ foreign => updateWorld_account_frame foreign, updateWorld_output _ _ _ _ _ _⟩

/-- Source acceptance and the actual primitive affordability conditions construct
the exact shared bytecode run, with precise selected state, Sync event and frame.
No callee endpoint or total-gas-only store-safety premise is assumed. -/
theorem update_source_exact_at {st post : State} {ctx : Context} {event : Event}
    {oracle : OracleUpdate} {sevm : Sevm} {b : Devm} {R : List B256} {M : Mem}
    {G n headerLoad load9 store9 load10 store10 load8 store8 : Nat}
    {p old0 old1 balance0 balance1 tag : B256}
    (fork : CoveredFork sevm.benvStat.fork) (mem : PtrMem p n M)
    (low : 96 ≤ p.toNat) (high : p.toNat + 64 < 2 ^ 256)
    (slots : ReserveSlotMatches st sevm b)
    (cum0 : b.getStorVal sevm.currentTarget 9 = st.price0CumulativeLast)
    (cum1 : b.getStorVal sevm.currentTarget 10 = st.price1CumulativeLast)
    (time : ctx.timestamp = sevm.benvStat.time) (pair : ctx.pair = sevm.currentTarget)
    (oldBound0 : old0.toNat < 2 ^ 112) (oldBound1 : old1.toNat < 2 ^ 112)
    (accepted : st.update ctx balance0 balance1 old0.toNat old1.toNat = .ok (post, event, oracle))
    (static : sevm.isStatic = false) (room : R.length ≤ 1008)
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
    (sentry8 : gCallStipend < G + updateSyncGasAt n p + store8)
    (sentry10 : updateOracleActive sevm b old0 old1 →
      gCallStipend < G + updateSyncGasAt n p + load8 + store8 + 110 + store10)
    (sentry9 : updateOracleActive sevm b old0 old1 →
      gCallStipend < G + updateSyncGasAt n p + load8 + store8 + 110 +
        load10 + store10 + 42 + 149 + store9) :
    SFunc.RunExact cert.prog sevm
      (St b (old1 :: old0 :: balance1 :: balance0 :: tag :: R) M
        (G + updateSyncGasAt n p + load8 + store8 + 110 +
          (if updateOracleActive sevm b old0 old1 then load9 + store9 + load10 + store10 + 382 else 0) +
          17 + 20 +
          (if updateOraclePrefixWord (b.getStorVal sevm.currentTarget 8) sevm.benvStat.time old0 = 0
            then 0 else 17) + headerLoad + 75 +
          (if updateElapsedWord (b.getStorVal sevm.currentTarget 8) sevm.benvStat.time &&& reserveMask32 = 0
            then 0 else 17) + 60)) t_22e0_c60
      (.returned (St (updateWorld sevm b old0 old1 balance0 balance1) R
        (updateMemoryAt sevm b M p old0 old1 balance0 balance1) G)) ∧
    ReserveSlotMatches post sevm (updateWorld sevm b old0 old1 balance0 balance1) ∧
    (updateWorld sevm b old0 old1 balance0 balance1).getStorVal sevm.currentTarget 9 = post.price0CumulativeLast ∧
    (updateWorld sevm b old0 old1 balance0 balance1).getStorVal sevm.currentTarget 10 = post.price1CumulativeLast ∧
    event = .sync balance0.toNat balance1.toNat ∧
    (updateWorld sevm b old0 old1 balance0 balance1).logs =
      b.logs ++ [⟨ctx.pair, [updateSyncTopic], encodeWords [balance0, balance1]⟩] ∧
    (∀ a k, a ≠ sevm.currentTarget ∨ (k ≠ 8 ∧ k ≠ 9 ∧ k ≠ 10) →
      (updateWorld sevm b old0 old1 balance0 balance1).getStorVal a k = b.getStorVal a k) ∧
    (∀ a, a ≠ sevm.currentTarget →
      (updateWorld sevm b old0 old1 balance0 balance1).getAcct a = b.getAcct a) ∧
    (updateWorld sevm b old0 old1 balance0 balance1).output = b.output := by
  obtain ⟨bound0, bound1⟩ := update_source_guards accepted
  obtain ⟨reserves, price0, price1, sync, logs⟩ :=
    update_source_result_of_ok slots cum0 cum1 time pair oldBound0 oldBound1 accepted
  exact ⟨update_exact_at fork mem low high static bound0 bound1 room headerCharge packedLoadCharge
    packedStoreCharge oracleCharges sentry8 sentry10 sentry9,
    reserves, price0, price1, sync, logs, fun _ _ frame => updateWorld_storage_frame frame,
    fun _ foreign => updateWorld_account_frame foreign, updateWorld_output _ _ _ _ _ _⟩


end Blanc.Lift.UniswapV2Pair
