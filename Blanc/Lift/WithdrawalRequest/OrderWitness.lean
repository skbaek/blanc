import Blanc.Lift.WithdrawalRequest.IgnoreWitnesses

/-!
# The closed instance of the EIP-7002 P2 order control

`Facts.order_sensitive` proves that, for one validator, folding
`[partial V, full exit V]` differs from folding `[full exit V, partial V]`, under
premises about the pre-state: both requests classify as a partial withdrawal and
a full exit of the same validator, both applications succeed, the fork is
Electra or later, and `MIN_VALIDATOR_WITHDRAWABILITY_DELAY` is nonzero. This
module exhibits a concrete minimal-preset Electra state meeting every premise,
so the control is not vacuous.

The state `orderState` is `stateWith` over `IgnoreWitnesses.lean`'s `baseState`:
one validator with the 0x02 compounding credential `cred02` (address bytes
`witAddr`), active since epoch 0 and never exiting, effective balance 32 ETH
(`MIN_ACTIVATION_BALANCE`), actual balance 33 ETH, slot 800 (epoch 100, past
`SHARD_COMMITTEE_PERIOD` = 64), and an empty pending-partial queue. The partial
request `orderPartial` asks for a thousand gwei and the full-exit request
`orderFull` carries `FULL_EXIT_REQUEST_AMOUNT`; both name `witPubkey` from
`witAddr`. `order_matters_witness` instantiates `Facts.order_sensitive` there.
-/

namespace Blanc.Lift.WithdrawalRequest

open Jaune JauneConsensus

/-- The compounding validator of the order witness: 0x02 credential, active
since genesis, never exiting, effective balance `MIN_ACTIVATION_BALANCE`. -/
def orderValidator : Validator :=
  witValidator cred02 U64.zero FAR_FUTURE_EPOCH (U64.lit 32000000000)

/-- The order-witness state: `orderValidator` with a 33 ETH balance at slot 800
(epoch 100) and no pending partial withdrawals. -/
def orderState : BeaconState Preset.minimal .electra :=
  stateWith (oneVal orderValidator) (oneBal (U64.lit 33000000000)) (U64.lit 800)
    SszList.empty

/-- The partial withdrawal request: a thousand gwei for `witPubkey`. -/
def orderPartial : WithdrawalRequest := witRequest witPubkey (U64.lit 1000)

/-- The full-exit request for `witPubkey`. -/
def orderFull : WithdrawalRequest := witRequest witPubkey FULL_EXIT_REQUEST_AMOUNT

/-- A computation whose `isOk` test passes returns some value. -/
private theorem exists_ok_of_isOk {ε α : Type} {e : Except ε α}
    (h : e.isOk = true) : ∃ a, e = .ok a := by
  cases e with
  | error _ => cases h
  | ok a => exact ⟨a, rfl⟩

private theorem orderState_validators :
    orderState.validators.toArray = #[orderValidator] := rfl

/-- The partial request classifies as a thousand-gwei partial withdrawal of
validator 0. -/
theorem orderPartial_classify :
    Facts.classifyWithdrawalRequest Config.minimal orderState orderPartial =
      .ok (.partialWithdrawal U64.zero (U64.lit 1000)) := by
  unfold Facts.classifyWithdrawalRequest
  rw [validatorIndexOf_some_of_singleton orderState_validators (by decide)]
  rfl

/-- The full-exit request classifies as a full exit of validator 0. -/
theorem orderFull_classify :
    Facts.classifyWithdrawalRequest Config.minimal orderState orderFull =
      .ok (.fullExit U64.zero) := by
  unfold Facts.classifyWithdrawalRequest
  rw [validatorIndexOf_some_of_singleton orderState_validators (by decide)]
  rfl

/-- Applying the classified partial withdrawal succeeds on `orderState`. -/
theorem orderPartial_apply_ok :
    (Facts.applyWithdrawalOutcome Config.minimal orderState orderPartial
      (.partialWithdrawal U64.zero (U64.lit 1000))).isOk = true := by
  rfl

/-- Applying the classified full exit succeeds on `orderState`. -/
theorem orderFull_apply_ok :
    (Facts.applyWithdrawalOutcome Config.minimal orderState orderFull
      (.fullExit U64.zero)).isOk = true := by
  rfl

/-- P2 order control, closed: on `orderState`, a partial withdrawal and a full
exit for the same pubkey give different results in the two orders. -/
theorem order_matters_witness :
    ∃ (s : BeaconState Preset.minimal .electra) (wp wf : WithdrawalRequest),
      wp.validator_pubkey = wf.validator_pubkey ∧
      Facts.foldWithdrawalRequests Config.minimal s [wp, wf] ≠
        Facts.foldWithdrawalRequests Config.minimal s [wf, wp] := by
  obtain ⟨s1, hap⟩ := exists_ok_of_isOk orderPartial_apply_ok
  obtain ⟨s2, haf⟩ := exists_ok_of_isOk orderFull_apply_ok
  exact ⟨orderState, orderPartial, orderFull,
    Facts.order_sensitive (by decide) ⟨_, rfl, by decide⟩ orderPartial_classify
      orderFull_classify hap haf⟩

end Blanc.Lift.WithdrawalRequest
