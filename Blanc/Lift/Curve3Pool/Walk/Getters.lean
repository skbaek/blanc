import Blanc.Lift.Curve3Pool.Walk.Quiet

/-!
# Safety: the public getters, inverted

The twelve scalar getters share one tree shape (`getterTree`: `SLOAD` of the slot, one-word
`RETURN`) behind the non-payable guard, and `coins(i)`/`balances(i)` share `arrayGetterTree`
(the index check `i < 3`, `keccak(slot) + i`, `SLOAD`, one-word `RETURN`). `safe_getter` and
`safe_arrayGetter` invert each shape once; the per-getter theorems instantiate them (the tree
equality is definitional). Bodies: `coins` `t_5083_c0`, `balances` `t_50c3_c0`, `fee`
`t_5103_c0`, `admin_fee` `t_512a_c0`, `owner` `t_5151_c0`, `initial_A` `t_5178_c0`, `future_A`
`t_519f_c0`, `initial_A_time` `t_51c6_c0`, `future_A_time` `t_51ed_c0`,
`admin_actions_deadline` `t_5214_c0`, `transfer_ownership_deadline` `t_523b_c0`, `future_fee`
`t_5262_c0`, `future_admin_fee` `t_5289_c0`, `future_owner` `t_52b0_c0`.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune
open Blanc.StableSwapNewton

section

variable {sevm : Sevm} {b : Devm} {s : State}

local notation "stor₀" => Devm.getStor b sevm.currentTarget

/-- The scalar getter tree: `PUSH1 slot SLOAD PUSH1 0 MSTORE PUSH1 32 PUSH1 0 RETURN`. -/
def getterTree (sl : UInt8) : SFunc :=
  .next (.push [sl] (by simp only [List.length_singleton]; omega)) (.next (.reg .sload) (.next (.push [0x00] (by decide))
    (.next (.reg .mstore) (.next (.push [0x20] (by decide)) (.next (.push [0x00] (by decide))
      (.last .return_))))))

/-- **A scalar getter is safe**: its body returns the word stored at its slot. -/
theorem safe_getter {s : State} {c : Call} {sl h l : UInt8} {fail : SFunc}
    (hfork : CoveredFork sevm.benvStat.fork) (hf : fail.noOk = true) (hdec : decodeCall sevm = c)
    (hfp : footprint c = [])
    (hstep : (quietEnv sevm).value = 0 → step s (quietEnv sevm) c =
      some (viewOut s ((b.getStor sevm.currentTarget).get (Bytes.toB256 [sl])).toNat)) :
    QuietSafe sevm b s (vyNonpayable h l fail (getterTree sl)) := by
  intro G post run
  have run := run.cut
  unfold quietSt at run
  obtain ⟨hv, G1, run⟩ := ric_vyNonpayable hf run
  unfold getterTree at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G2, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G3, rfl⟩ := ri_sload hfork s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_mstore s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G6, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G7, rfl⟩ := ri_push s1
  cases run with
  | last hl =>
  obtain ⟨hout, hstor, hlogs⟩ := ri_return hl
  refine ⟨_, hdec ▸ hstep (quietEnv_value hv), ?_⟩
  refine quietLands_ret ((QStep.refl sevm b).sload _) (hdec ▸ hfp) rfl rfl rfl ?_ hstor hlogs
  rw [hout, show (Bytes.toB256 [0x00]).toNat = 0 from by decide,
    show (Bytes.toB256 [0x20]).toNat = 32 from by decide, Mem.read_write_word_of_wf (vyMem_wf Mem.wf_empty _),
    getStorVal_eq_getStor, word, Jaune.toB256_toNat]

-- SEGMENT: safeScalarGetters
/-- `fee()`: returns the word at slot 2. -/
theorem safe_feeGetter (hfork : CoveredFork sevm.benvStat.fork) (hc : Checkpoint stor₀ s)
    (hsel : Sevm.selector sevm = selFee) (hlen : 4 ≤ sevm.data.length) :
    QuietSafe sevm b s t_5103_c0 :=
  safe_getter (sl := 0x2) (fail := t_5109_c0) hfork rfl (decodeCall_at (k := 26) rfl hsel hlen) rfl
    fun hv => by
      simp only [callAt, step, body, hv, ite_true]
      rw [show Bytes.toB256 [0x2] = feeSlot from by decide, hc.abs.fee]

/-- `adminFee()`: returns the word at slot 3. -/
theorem safe_adminFeeGetter (hfork : CoveredFork sevm.benvStat.fork) (hc : Checkpoint stor₀ s)
    (hsel : Sevm.selector sevm = selAdminFee) (hlen : 4 ≤ sevm.data.length) :
    QuietSafe sevm b s t_512a_c0 :=
  safe_getter (sl := 0x3) (fail := t_5130_c0) hfork rfl (decodeCall_at (k := 27) rfl hsel hlen) rfl
    fun hv => by
      simp only [callAt, step, body, hv, ite_true]
      rw [show Bytes.toB256 [0x3] = adminFeeSlot from by decide, hc.abs.adminFee]

/-- `owner()`: returns the word at slot 4. -/
theorem safe_ownerGetter (hfork : CoveredFork sevm.benvStat.fork) (hc : Checkpoint stor₀ s)
    (hsel : Sevm.selector sevm = selOwner) (hlen : 4 ≤ sevm.data.length) :
    QuietSafe sevm b s t_5151_c0 :=
  safe_getter (sl := 0x4) (fail := t_5157_c0) hfork rfl (decodeCall_at (k := 28) rfl hsel hlen) rfl
    fun hv => by
      simp only [callAt, step, body, hv, ite_true]
      rw [show Bytes.toB256 [0x4] = ownerSlot from by decide, hc.abs.owner]

/-- `initialA()`: returns the word at slot 6. -/
theorem safe_initialAGetter (hfork : CoveredFork sevm.benvStat.fork) (hc : Checkpoint stor₀ s)
    (hsel : Sevm.selector sevm = selInitialA) (hlen : 4 ≤ sevm.data.length) :
    QuietSafe sevm b s t_5178_c0 :=
  safe_getter (sl := 0x6) (fail := t_517e_c0) hfork rfl (decodeCall_at (k := 29) rfl hsel hlen) rfl
    fun hv => by
      simp only [callAt, step, body, hv, ite_true]
      rw [show Bytes.toB256 [0x6] = initialASlot from by decide, hc.abs.initialA]

/-- `futureA()`: returns the word at slot 7. -/
theorem safe_futureAGetter (hfork : CoveredFork sevm.benvStat.fork) (hc : Checkpoint stor₀ s)
    (hsel : Sevm.selector sevm = selFutureA) (hlen : 4 ≤ sevm.data.length) :
    QuietSafe sevm b s t_519f_c0 :=
  safe_getter (sl := 0x7) (fail := t_51a5_c0) hfork rfl (decodeCall_at (k := 30) rfl hsel hlen) rfl
    fun hv => by
      simp only [callAt, step, body, hv, ite_true]
      rw [show Bytes.toB256 [0x7] = futureASlot from by decide, hc.abs.futureA]

/-- `initialATime()`: returns the word at slot 8. -/
theorem safe_initialATimeGetter (hfork : CoveredFork sevm.benvStat.fork) (hc : Checkpoint stor₀ s)
    (hsel : Sevm.selector sevm = selInitialATime) (hlen : 4 ≤ sevm.data.length) :
    QuietSafe sevm b s t_51c6_c0 :=
  safe_getter (sl := 0x8) (fail := t_51cc_c0) hfork rfl (decodeCall_at (k := 31) rfl hsel hlen) rfl
    fun hv => by
      simp only [callAt, step, body, hv, ite_true]
      rw [show Bytes.toB256 [0x8] = initialATimeSlot from by decide, hc.abs.initialATime]

/-- `futureATime()`: returns the word at slot 9. -/
theorem safe_futureATimeGetter (hfork : CoveredFork sevm.benvStat.fork) (hc : Checkpoint stor₀ s)
    (hsel : Sevm.selector sevm = selFutureATime) (hlen : 4 ≤ sevm.data.length) :
    QuietSafe sevm b s t_51ed_c0 :=
  safe_getter (sl := 0x9) (fail := t_51f3_c0) hfork rfl (decodeCall_at (k := 32) rfl hsel hlen) rfl
    fun hv => by
      simp only [callAt, step, body, hv, ite_true]
      rw [show Bytes.toB256 [0x9] = futureATimeSlot from by decide, hc.abs.futureATime]

/-- `adminActionsDeadline()`: returns the word at slot 10. -/
theorem safe_adminActionsDeadlineGetter (hfork : CoveredFork sevm.benvStat.fork) (hc : Checkpoint stor₀ s)
    (hsel : Sevm.selector sevm = selAdminActionsDeadline) (hlen : 4 ≤ sevm.data.length) :
    QuietSafe sevm b s t_5214_c0 :=
  safe_getter (sl := 0xa) (fail := t_521a_c0) hfork rfl (decodeCall_at (k := 33) rfl hsel hlen) rfl
    fun hv => by
      simp only [callAt, step, body, hv, ite_true]
      rw [show Bytes.toB256 [0xa] = adminActionsDeadlineSlot from by decide, hc.abs.adminActionsDeadline]

/-- `transferOwnershipDeadline()`: returns the word at slot 11. -/
theorem safe_transferOwnershipDeadlineGetter (hfork : CoveredFork sevm.benvStat.fork) (hc : Checkpoint stor₀ s)
    (hsel : Sevm.selector sevm = selTransferOwnershipDeadline) (hlen : 4 ≤ sevm.data.length) :
    QuietSafe sevm b s t_523b_c0 :=
  safe_getter (sl := 0xb) (fail := t_5241_c0) hfork rfl (decodeCall_at (k := 34) rfl hsel hlen) rfl
    fun hv => by
      simp only [callAt, step, body, hv, ite_true]
      rw [show Bytes.toB256 [0xb] = transferOwnershipDeadlineSlot from by decide, hc.abs.transferOwnershipDeadline]

/-- `futureFee()`: returns the word at slot 12. -/
theorem safe_futureFeeGetter (hfork : CoveredFork sevm.benvStat.fork) (hc : Checkpoint stor₀ s)
    (hsel : Sevm.selector sevm = selFutureFee) (hlen : 4 ≤ sevm.data.length) :
    QuietSafe sevm b s t_5262_c0 :=
  safe_getter (sl := 0xc) (fail := t_5268_c0) hfork rfl (decodeCall_at (k := 35) rfl hsel hlen) rfl
    fun hv => by
      simp only [callAt, step, body, hv, ite_true]
      rw [show Bytes.toB256 [0xc] = futureFeeSlot from by decide, hc.abs.futureFee]

/-- `futureAdminFee()`: returns the word at slot 13. -/
theorem safe_futureAdminFeeGetter (hfork : CoveredFork sevm.benvStat.fork) (hc : Checkpoint stor₀ s)
    (hsel : Sevm.selector sevm = selFutureAdminFee) (hlen : 4 ≤ sevm.data.length) :
    QuietSafe sevm b s t_5289_c0 :=
  safe_getter (sl := 0xd) (fail := t_528f_c0) hfork rfl (decodeCall_at (k := 36) rfl hsel hlen) rfl
    fun hv => by
      simp only [callAt, step, body, hv, ite_true]
      rw [show Bytes.toB256 [0xd] = futureAdminFeeSlot from by decide, hc.abs.futureAdminFee]

/-- `futureOwner()`: returns the word at slot 14. -/
theorem safe_futureOwnerGetter (hfork : CoveredFork sevm.benvStat.fork) (hc : Checkpoint stor₀ s)
    (hsel : Sevm.selector sevm = selFutureOwner) (hlen : 4 ≤ sevm.data.length) :
    QuietSafe sevm b s t_52b0_c0 :=
  safe_getter (sl := 0xe) (fail := t_52b6_c0) hfork rfl (decodeCall_at (k := 37) rfl hsel hlen) rfl
    fun hv => by
      simp only [callAt, step, body, hv, ite_true]
      rw [show Bytes.toB256 [0xe] = futureOwnerSlot from by decide, hc.abs.futureOwner]

/-- The array getter's index check and element load: `PUSH1 4 CALLDATALOAD PUSH1 3 DUP2 LT`,
`PUSH2 ok JUMPI`, then `keccak(sl) + i`, `SLOAD`, and the one-word `RETURN`. -/
def arrayGetterTree (h l sl : UInt8) (fail : SFunc) : SFunc :=
  .next (.push [0x04] (by decide)) (.next (.reg .calldataload) (.next (.push [0x03] (by decide))
    (.next (.reg (.dup 1)) (.next (.reg .lt) (.next (.push [h, l] (by simp only [List.length_cons, List.length_nil]; omega))
      (.branch fail (.dest (.next (.push [sl] (by simp only [List.length_singleton]; omega))
        (.next (.push [0xc0] (by decide)) (.next (.reg .mstore) (.next (.push [0x20] (by decide))
          (.next (.push [0xc0] (by decide)) (.next (.reg .keccak256) (.next (.reg .add)
            (.next (.reg .sload) (.next (.push [0x00] (by decide)) (.next (.reg .mstore)
              (.next (.push [0x20] (by decide)) (.next (.push [0x00] (by decide))
                (.last .return_))))))))))))))))))))

/-- **An array getter is safe**: for an index below 3 it returns the word at
`keccak(sl) + i`. -/
theorem safe_arrayGetter {s : State} {c : Call} {sl h l h' l' : UInt8} {fail fail' : SFunc}
    {base : B256} (hfork : CoveredFork sevm.benvStat.fork) (hf : fail.noOk = true)
    (hf' : fail'.noOk = true) (hbase : Bytes.keccak (Bytes.toB256 [sl]).toBytes = base)
    (hdec : decodeCall sevm = c) (hfp : footprint c = [])
    (hstep : (quietEnv sevm).value = 0 → ∀ i : Fin 3, (Sevm.argWord sevm 0).toNat = i.val →
      step s (quietEnv sevm) c =
        some (viewOut s ((b.getStor sevm.currentTarget).get (base + Nat.toB256 i.val)).toNat)) :
    QuietSafe sevm b s (vyNonpayable h l fail (arrayGetterTree h' l' sl fail')) := by
  intro G post run
  have hwf0 : Mem.Wf (vyMem Mem.empty (Sevm.dataWord sevm 0)) := vyMem_wf Mem.wf_empty _
  have run := run.cut
  unfold quietSt at run
  obtain ⟨hv, G1, run⟩ := ric_vyNonpayable hf run
  unfold arrayGetterTree at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G2, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G3, rfl⟩ := ri_calldataload s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G6, rfl⟩ := ri_lt s1
  obtain ⟨hi, G7, run⟩ := ric_assertJump hf' run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G8, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G9, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G10, rfl⟩ := ri_mstore s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G11, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G12, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G13, rfl⟩ := ri_keccak s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G14, rfl⟩ := ri_add s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G15, rfl⟩ := ri_sload hfork s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G16, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G17, rfl⟩ := ri_mstore s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G18, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G19, rfl⟩ := ri_push s1
  cases run with
  | last hl =>
  obtain ⟨hout, hstor, hlogs⟩ := ri_return hl
  clear * - hout hstor hlogs hi hstep hdec hfp hv hwf0 hbase hfork
  have ha0 : Sevm.dataWord sevm (Bytes.toB256 [4]) = Sevm.argWord sevm 0 := rfl
  rw [ha0] at hi hout
  have hiN : (Sevm.argWord sevm 0).toNat < 3 := by
    have h := hi
    unfold B256.ltCheck at h
    split at h
    · rename_i hlt
      exact (B256.lt_iff_toNat_lt_toNat.mp hlt).trans_eq (by decide)
    · exact absurd rfl h
  have hidx : Nat.toB256 (⟨_, hiN⟩ : Fin 3).val = Sevm.argWord sevm 0 := Jaune.toB256_toNat _
  refine ⟨_, hdec ▸ hstep (quietEnv_value hv) ⟨_, hiN⟩ rfl, ?_⟩
  refine quietLands_ret ((QStep.refl sevm b).sload _) (hdec ▸ hfp) rfl rfl rfl ?_ hstor hlogs
  rw [hout, show (Bytes.toB256 [0x00]).toNat = 0 from by decide,
    show (Bytes.toB256 [0x20]).toNat = 32 from by decide,
    show (Bytes.toB256 [0xc0]).toNat = 192 from by decide,
    Mem.read_snd_eq, Mem.read_write_word_of_wf (Mem.Wf.extend (Mem.Wf.write hwf0 _ _) _ _),
    Mem.read_write_word_of_wf hwf0, hbase, getStorVal_eq_getStor, word, Jaune.toB256_toNat, hidx]

/-- `coins(i)`. -/
theorem safe_coinsGetter (hfork : CoveredFork sevm.benvStat.fork) (hc : Checkpoint stor₀ s)
    (hsel : Sevm.selector sevm = selCoins) (hlen : 4 ≤ sevm.data.length) :
    QuietSafe sevm b s t_5083_c0 :=
  safe_arrayGetter (sl := 0x00) (base := coinsBase) (fail := t_5089_c0) (fail' := t_5099_c0) hfork rfl rfl
    (by rw [show Bytes.toB256 [0x00] = 0 from by decide]; exact coinsBase_eq)
    (decodeCall_at (k := 24) rfl hsel hlen) rfl
    fun hv i hi => by
      simp only [callAt, step, body, hv, ite_true, arg, hi, idx, i.isLt, dite_true, bind,
        Option.bind, Fin.eta]
      rw [← hc.abs.coins i]
      rfl

/-- `balances(i)`. -/
theorem safe_balancesGetter (hfork : CoveredFork sevm.benvStat.fork) (hc : Checkpoint stor₀ s)
    (hsel : Sevm.selector sevm = selBalances) (hlen : 4 ≤ sevm.data.length) :
    QuietSafe sevm b s t_50c3_c0 :=
  safe_arrayGetter (sl := 0x01) (base := balancesBase) (fail := t_50c9_c0) (fail' := t_50d9_c0) hfork rfl rfl
    (by rw [show Bytes.toB256 [0x01] = 1 from by decide]; exact balancesBase_eq)
    (decodeCall_at (k := 25) rfl hsel hlen) rfl
    fun hv i hi => by
      simp only [callAt, step, body, hv, ite_true, arg, hi, idx, i.isLt, dite_true, bind,
        Option.bind, Fin.eta]
      rw [← hc.abs.balances i]
      rfl

end

end Blanc.Lift.Curve3Pool
