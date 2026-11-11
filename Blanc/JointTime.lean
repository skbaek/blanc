import JauneConsensus.Facts.PendingDeposits

/-!
# Genesis time across the pending-deposit pass

Project the actual successful state updates and reuse the existing pending
step characterization and list-loop relation. No queue or fork invariant is
required for this unchanged field.
-/

namespace Blanc

open JauneConsensus JauneConsensus.Facts

variable {P : Preset} {f : CFork}

/-- Registry insertion changes only the fields in its original record update. -/
theorem addValidatorToRegistry_genesis_time (pre post : BeaconState P f)
    (pubkey : BLSPubkey) (credentials : Bytes32) (amount : U64)
    (h : addValidatorToRegistry pre pubkey credentials amount = .ok post) :
    post.genesis_time = pre.genesis_time := by
  unfold addValidatorToRegistry at h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  cases h
  rfl

/-- Each actual classification outcome preserves genesis time. -/
theorem applyPendingDeposit_genesis_time (ctx : Ctx) (pre post : BeaconState P f)
    (deposit : PendingDeposit) (h : applyPendingDeposit ctx pre deposit = .ok post) :
    post.genesis_time = pre.genesis_time := by
  rw [applyPendingDeposit_eq] at h
  obtain ⟨outcome, _, h⟩ := bind_eq_ok_iff.mp h
  cases outcome with
  | newValidator =>
    exact addValidatorToRegistry_genesis_time pre post _ _ _ h
  | topUp index =>
    obtain ⟨_, _, _, _, _, frame⟩ := increaseBalance_spec h
    exact congrArg (fun state => state.genesis_time) frame
  | noCredit => cases h; rfl

/-- Replacing the pending queue preserves the original genesis field. -/
theorem setPendingDeposits_genesis_time (pre post : BeaconState P f)
    (pending : SszList PendingDeposit P.PENDING_DEPOSITS_LIMIT)
    (h : pre.setPendingDeposits pending = .ok post) :
    post.genesis_time = pre.genesis_time := by
  unfold BeaconState.setPendingDeposits at h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  cases h
  rfl

/-- Updating the carried churn allowance preserves genesis time. -/
theorem setDepositBalanceToConsume_genesis_time (pre post : BeaconState P f) (amount : Gwei)
    (h : pre.setDepositBalanceToConsume amount = .ok post) :
    post.genesis_time = pre.genesis_time := by
  unfold BeaconState.setDepositBalanceToConsume at h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  cases h
  rfl

/-- The original successful pending-deposit pass preserves genesis time. -/
theorem processPendingDeposits_genesis_time (ctx : Ctx) (pre post : BeaconState P f)
    (h : processPendingDeposits ctx pre = .ok post) :
    post.genesis_time = pre.genesis_time := by
  rw [processPendingDeposits_eq] at h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨nextEpoch, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨available, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨finalizedSlot, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨requestsStart, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨pending, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨result, loop, h⟩ := bind_eq_ok_iff.mp h
  have loop_time : result.2.2.2.2.genesis_time = pre.genesis_time := by
    rw [pendingDepositsLoop_eq_forIn] at loop
    refine list_forIn_rel
      (fun a b : PendingDepositsAcc P f =>
        b.2.2.2.2.genesis_time = a.2.2.2.2.genesis_time)
      (fun _ => rfl) (fun _ _ _ first second => second.trans first)
      (pendingDepositStep ctx nextEpoch available finalizedSlot requestsStart) ?_
      pending.toArray.toList (U64.zero, 0, #[], false, pre) result loop
    intro deposit acc r step
    rcases acc with ⟨pa, idx, postponed, flag, state⟩
    rcases pendingDepositStep_spec step with ⟨_, rfl⟩ | ⟨_, moves⟩
    · rfl
    rcases moves with ⟨_, state', _, applied, rfl⟩ | ⟨_, rfl⟩ |
      ⟨_, _, _, _, rfl⟩ | ⟨_, state', _, _, _, applied, rfl⟩
    · exact applyPendingDeposit_genesis_time ctx state state' deposit applied
    · rfl
    · rfl
    · exact applyPendingDeposit_genesis_time ctx state state' deposit applied
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨queued, queue, h⟩ := bind_eq_ok_iff.mp h
  have queue_time := setPendingDeposits_genesis_time result.2.2.2.2 queued _ queue
  have final_time : post.genesis_time = queued.genesis_time := by
    split at h
    · obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
      exact setDepositBalanceToConsume_genesis_time queued post _ h
    · exact setDepositBalanceToConsume_genesis_time queued post _ h
  exact final_time.trans (queue_time.trans loop_time)

/-- A successful checked millisecond clock has its exact natural-number value. -/
theorem computeTimeAtSlotMs_nat
    (cfg : Config) (originMs : U64) (slot : Slot) (timeMs : U64)
    (h : computeTimeAtSlotMs cfg originMs slot = .ok timeMs) :
    timeMs.toNat = originMs.toNat + slot.toNat * cfg.SLOT_DURATION_MS := by
  unfold computeTimeAtSlotMs at h
  obtain ⟨duration, hduration, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨offset, hoffset, htime⟩ := bind_eq_ok_iff.mp h
  rw [U64.toNat_add? htime, U64.toNat_mul? hoffset, U64.toNat_ofNat? hduration]

/-- Whole-second slots lie on the grid of the actual converted genesis origin. -/
theorem computeTimeAtSlotOf_grid
    (cfg : Config) (genesis : U64) (slot : Slot) (time : U64)
    (whole : cfg.SLOT_DURATION_MS % 1000 = 0)
    (h : computeTimeAtSlotOf cfg genesis slot = .ok time) :
    ∃ originMs : U64, secondsToMilliseconds genesis = .ok originMs ∧
      time.toNat = originMs.toNat / 1000 +
        (cfg.SLOT_DURATION_MS / 1000) * slot.toNat := by
  unfold computeTimeAtSlotOf at h
  obtain ⟨originMs, horigin, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨timeMs, htimeMs, h⟩ := bind_eq_ok_iff.mp h
  unfold millisecondsToSeconds at h
  obtain ⟨thousand, hthousand, hdiv⟩ := bind_eq_ok_iff.mp h
  refine ⟨originMs, horigin, ?_⟩
  have time_nat := U64.toNat_div? hdiv
  rw [U64.toNat_ofNat? hthousand, computeTimeAtSlotMs_nat cfg originMs slot timeMs htimeMs] at time_nat
  have duration_grid : cfg.SLOT_DURATION_MS / 1000 * 1000 = cfg.SLOT_DURATION_MS := by
    have := Nat.mod_add_div cfg.SLOT_DURATION_MS 1000
    omega
  have offset_grid :
      cfg.SLOT_DURATION_MS / 1000 * slot.toNat * 1000 =
        slot.toNat * cfg.SLOT_DURATION_MS := by
    calc
      _ = (cfg.SLOT_DURATION_MS / 1000 * 1000) * slot.toNat := by ac_rfl
      _ = cfg.SLOT_DURATION_MS * slot.toNat := by rw [duration_grid]
      _ = _ := Nat.mul_comm _ _
  rw [← offset_grid, Nat.add_mul_div_right _ _ (by decide)] at time_nat
  exact time_nat

/-- Two successful clocks with the same genesis conversion cancel that origin. -/
theorem successful_clock_cancel
    (cfg : Config) (genesis : U64) (slot0 slot1 : Slot) (time0 time1 : U64)
    (whole : cfg.SLOT_DURATION_MS % 1000 = 0)
    (h0 : computeTimeAtSlotOf cfg genesis slot0 = .ok time0)
    (h1 : computeTimeAtSlotOf cfg genesis slot1 = .ok time1) :
    time0.toNat + (cfg.SLOT_DURATION_MS / 1000) * slot1.toNat =
      time1.toNat + (cfg.SLOT_DURATION_MS / 1000) * slot0.toNat := by
  obtain ⟨origin0, h0origin, h0time⟩ := computeTimeAtSlotOf_grid cfg genesis slot0 time0 whole h0
  obtain ⟨origin1, h1origin, h1time⟩ := computeTimeAtSlotOf_grid cfg genesis slot1 time1 whole h1
  have same : origin0 = origin1 := by
    simpa only [Except.ok.injEq] using h0origin.symm.trans h1origin
  rw [← same] at h1time
  omega


end Blanc
