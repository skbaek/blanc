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

end Blanc
