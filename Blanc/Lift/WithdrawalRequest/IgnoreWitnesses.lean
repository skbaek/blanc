import JauneConsensus.Facts.WithdrawalOrder

/-!
# Concrete witnesses for each EIP-7002 ignore reason (P2)

For each constructor `r` of `Facts.WithdrawalIgnoreReason`, a closed theorem
`ignore_witness_<reason>` exhibiting a minimal-preset Electra state and a request
that `Facts.classifyWithdrawalRequest` ignores for exactly that reason, plus the
summary `every_ignore_reason_occurs` over every reason.

Each state is built by `stateWith` over one closed `baseState`: a single
validator (a good 0x01-credentialed validator, perturbed one field per reason),
a single balance, slot 800 (epoch 100), and a pending-partial queue that is
empty except where the reason needs entries. The summary
`every_ignore_reason_occurs` covers every reason, `partialQueueFull` included.

Queue-limit note: the minimal preset's `PENDING_PARTIAL_WITHDRAWALS_LIMIT` is
64, small enough to build, so `partialQueueFull` is witnessed with 64 replicated
entries. The mainnet limit (134217728) is not built.
-/

namespace Blanc.Lift.WithdrawalRequest

open Jaune JauneConsensus

/-- Test address shared by every witness request and credential. -/
def witAddr : ExecutionAddress := 0x1111111111111111111111111111111111111111

/-- 0x01 execution credential whose address bytes are `witAddr`. -/
def cred01 : Bytes32 :=
  0x0100000000000000000000001111111111111111111111111111111111111111

/-- 0x02 compounding credential whose address bytes are `witAddr`. -/
def cred02 : Bytes32 :=
  0x0200000000000000000000001111111111111111111111111111111111111111

/-- BLS (0x00) credential: not an execution credential. -/
def credBLS : Bytes32 :=
  0x0000000000000000000000000000000000000000000000000000000000000000

/-- The registry pubkey used by every witness validator. -/
def witPubkey : BLSPubkey := ⟨Array.replicate 48 7, by decide⟩

/-- A pubkey no witness registry contains. -/
def otherPubkey : BLSPubkey := ⟨Array.replicate 48 9, by decide⟩

/-- A validator with credential `cred`, activation epoch `act`, exit epoch `ext`
and effective balance `eff`. -/
def witValidator (cred : Bytes32) (act ext eff : U64) : Validator :=
  { pubkey := witPubkey
    withdrawal_credentials := cred
    effective_balance := eff
    slashed := false
    activation_eligibility_epoch := U64.zero
    activation_epoch := act
    exit_epoch := ext
    withdrawable_epoch := FAR_FUTURE_EPOCH }

/-- The good validator every reason perturbs: 0x01-credentialed, active since
genesis, never exiting, funded at `MIN_ACTIVATION_BALANCE`. -/
def goodValidator : Validator :=
  witValidator cred01 U64.zero FAR_FUTURE_EPOCH (U64.lit 32000000000)

/-- One fits in the validator registry limit. -/
private theorem one_le_registryLimit :
    1 ≤ Preset.minimal.VALIDATOR_REGISTRY_LIMIT := by decide

/-- A one-entry registry. -/
def oneVal (v : Validator) : SszList Validator Preset.minimal.VALIDATOR_REGISTRY_LIMIT :=
  ⟨#[v], by show (1 : Nat) ≤ _; exact one_le_registryLimit⟩

/-- A one-entry balance list. -/
def oneBal (b : Gwei) : SszList Gwei Preset.minimal.VALIDATOR_REGISTRY_LIMIT :=
  ⟨#[b], by show (1 : Nat) ≤ _; exact one_le_registryLimit⟩

/-- The pending-partial entry shared by the nonzero queues. -/
def pendingEntry : PendingPartialWithdrawal :=
  { validator_index := U64.zero, amount := U64.lit 1000,
    withdrawable_epoch := U64.zero }

/-- A one-entry pending-partial queue paying validator 0 a thousand gwei. -/
def onePending :
    SszList PendingPartialWithdrawal Preset.minimal.PENDING_PARTIAL_WITHDRAWALS_LIMIT :=
  ⟨#[pendingEntry], by decide⟩

/-- A full pending-partial queue: 64 replicated entries. -/
def fullPending :
    SszList PendingPartialWithdrawal Preset.minimal.PENDING_PARTIAL_WITHDRAWALS_LIMIT :=
  ⟨Array.replicate 64 pendingEntry, by decide⟩

/-- Closed Electra base state over the minimal preset: default-like fields,
empty validator and balance lists, slot zero, no pending partials. -/
def baseState : BeaconState Preset.minimal .electra :=
  { genesis_time := U64.zero
    genesis_validators_root := 0
    slot := U64.zero
    fork :=
      { previous_version := ⟨#[0, 0, 0, 0], by decide⟩
        current_version := ⟨#[0, 0, 0, 0], by decide⟩
        epoch := U64.zero }
    latest_block_header :=
      { slot := U64.zero
        proposer_index := U64.zero
        parent_root := 0
        state_root := 0
        body_root := 0 }
    block_roots := ⟨Array.replicate 64 (0 : B256), by decide⟩
    state_roots := ⟨Array.replicate 64 (0 : B256), by decide⟩
    historical_roots := SszList.empty
    eth1_data := { deposit_root := 0, deposit_count := U64.zero, block_hash := 0 }
    eth1_data_votes := SszList.empty
    eth1_deposit_index := U64.zero
    validators := SszList.empty
    balances := SszList.empty
    randao_mixes := ⟨Array.replicate 64 (0 : B256), by decide⟩
    slashings := ⟨Array.replicate 64 U64.zero, by decide⟩
    previous_epoch_participation := SszList.empty
    current_epoch_participation := SszList.empty
    justification_bits := ⟨#[false, false, false, false], by decide⟩
    previous_justified_checkpoint := { epoch := U64.zero, root := 0 }
    current_justified_checkpoint := { epoch := U64.zero, root := 0 }
    finalized_checkpoint := { epoch := U64.zero, root := 0 }
    inactivity_scores := SszList.empty
    current_sync_committee :=
      { pubkeys := ⟨Array.replicate 32 witPubkey, by decide⟩
        aggregate_pubkey := witPubkey }
    next_sync_committee :=
      { pubkeys := ⟨Array.replicate 32 witPubkey, by decide⟩
        aggregate_pubkey := witPubkey }
    latest_execution_payload_header :=
      { parent_hash := 0
        fee_recipient := 0
        state_root := 0
        receipts_root := 0
        logs_bloom :=
          ⟨⟨List.replicate 256 (0 : UInt8)⟩, by
            show (List.replicate 256 (0 : UInt8)).length = _
            exact List.length_replicate⟩
        prev_randao := 0
        block_number := U64.zero
        gas_limit := U64.zero
        gas_used := U64.zero
        timestamp := U64.zero
        extra_data := SszList.empty
        base_fee_per_gas := UIntN.zero
        block_hash := 0
        transactions_root := 0
        withdrawals_root := 0
        blob_gas_used := U64.zero
        excess_blob_gas := U64.zero }
    next_withdrawal_index := U64.zero
    next_withdrawal_validator_index := U64.zero
    historical_summaries := SszList.empty
    deposit_requests_start_index := U64.zero
    deposit_balance_to_consume := U64.zero
    exit_balance_to_consume := U64.zero
    earliest_exit_epoch := U64.zero
    consolidation_balance_to_consume := U64.zero
    earliest_consolidation_epoch := U64.zero
    pending_deposits := SszList.empty
    pending_partial_withdrawals := SszList.empty
    pending_consolidations := SszList.empty
    proposer_lookahead := () }

/-- The base state with one validator list, balance list, slot and queue. -/
def stateWith (vs : SszList Validator Preset.minimal.VALIDATOR_REGISTRY_LIMIT)
    (bs : SszList Gwei Preset.minimal.VALIDATOR_REGISTRY_LIMIT)
    (slot : Slot)
    (pending : SszList PendingPartialWithdrawal
      Preset.minimal.PENDING_PARTIAL_WITHDRAWALS_LIMIT) :
    BeaconState Preset.minimal .electra :=
  { genesis_time := baseState.genesis_time
    genesis_validators_root := baseState.genesis_validators_root
    slot := slot
    fork := baseState.fork
    latest_block_header := baseState.latest_block_header
    block_roots := baseState.block_roots
    state_roots := baseState.state_roots
    historical_roots := baseState.historical_roots
    eth1_data := baseState.eth1_data
    eth1_data_votes := baseState.eth1_data_votes
    eth1_deposit_index := baseState.eth1_deposit_index
    validators := vs
    balances := bs
    randao_mixes := baseState.randao_mixes
    slashings := baseState.slashings
    previous_epoch_participation := baseState.previous_epoch_participation
    current_epoch_participation := baseState.current_epoch_participation
    justification_bits := baseState.justification_bits
    previous_justified_checkpoint := baseState.previous_justified_checkpoint
    current_justified_checkpoint := baseState.current_justified_checkpoint
    finalized_checkpoint := baseState.finalized_checkpoint
    inactivity_scores := baseState.inactivity_scores
    current_sync_committee := baseState.current_sync_committee
    next_sync_committee := baseState.next_sync_committee
    latest_execution_payload_header := baseState.latest_execution_payload_header
    next_withdrawal_index := baseState.next_withdrawal_index
    next_withdrawal_validator_index := baseState.next_withdrawal_validator_index
    historical_summaries := baseState.historical_summaries
    deposit_requests_start_index := baseState.deposit_requests_start_index
    deposit_balance_to_consume := baseState.deposit_balance_to_consume
    exit_balance_to_consume := baseState.exit_balance_to_consume
    earliest_exit_epoch := baseState.earliest_exit_epoch
    consolidation_balance_to_consume := baseState.consolidation_balance_to_consume
    earliest_consolidation_epoch := baseState.earliest_consolidation_epoch
    pending_deposits := baseState.pending_deposits
    pending_partial_withdrawals := pending
    pending_consolidations := baseState.pending_consolidations
    proposer_lookahead := baseState.proposer_lookahead }

/-- A request from `witAddr` for `key` of `amount`. -/
def witRequest (key : BLSPubkey) (amount : Gwei) : WithdrawalRequest :=
  { source_address := witAddr, validator_pubkey := key, amount := amount }

/-- Lookup in a one-validator registry misses when the pubkeys differ.
`Array.findIdx?` does not reduce by kernel defeq, so this unfolds
`validatorIndexOf` and closes the singleton case by the exact `simp only`
list below. -/
theorem validatorIndexOf_none_of_singleton {v : Validator} {key : BLSPubkey}
    {s : BeaconState Preset.minimal .electra}
    (hvals : s.validators.toArray = #[v])
    (hne : (v.pubkey == key) = false) :
    validatorIndexOf s key = .ok none := by
  unfold validatorIndexOf
  rw [hvals]
  simp only [ExceptT.stM_eq, List.findIdx?_toArray, List.findIdx?_singleton,
    hne, Bool.false_eq_true, ↓reduceIte]
  rfl

/-- Lookup in a one-validator registry hits index 0 when the pubkeys agree. -/
theorem validatorIndexOf_some_of_singleton {v : Validator} {key : BLSPubkey}
    {s : BeaconState Preset.minimal .electra}
    (hvals : s.validators.toArray = #[v])
    (heq : (v.pubkey == key) = true) :
    validatorIndexOf s key = .ok (some U64.zero) := by
  unfold validatorIndexOf
  rw [hvals]
  simp only [ExceptT.stM_eq, List.findIdx?_toArray, List.findIdx?_singleton,
    heq, ↓reduceIte, bind_pure_comp]
  rfl

/-- The queue-full reason occurs: 64 pending entries at the minimal limit. -/
theorem ignore_witness_partialQueueFull :
    ∃ (s : BeaconState Preset.minimal .electra) (wr : WithdrawalRequest),
      Facts.classifyWithdrawalRequest Config.minimal s wr =
        .ok (.ignored .partialQueueFull) := by
  refine ⟨stateWith (oneVal goodValidator) (oneBal (U64.lit 32000000000))
    (U64.lit 800) fullPending, witRequest witPubkey (U64.lit 1000), ?_⟩
  exact Facts.classify_ignored_partialQueueFull rfl (by decide)

/-- The unknown-pubkey reason occurs: the request key is not in the registry. -/
theorem ignore_witness_unknownPubkey :
    ∃ (s : BeaconState Preset.minimal .electra) (wr : WithdrawalRequest),
      Facts.classifyWithdrawalRequest Config.minimal s wr =
        .ok (.ignored .unknownPubkey) := by
  refine ⟨stateWith (oneVal goodValidator) (oneBal (U64.lit 32000000000))
    (U64.lit 800) SszList.empty, witRequest otherPubkey (U64.lit 1000), ?_⟩
  have hvals : (stateWith (oneVal goodValidator) (oneBal (U64.lit 32000000000))
    (U64.lit 800) SszList.empty).validators.toArray = #[goodValidator] := rfl
  exact Facts.classify_ignored_unknownPubkey rfl (by decide)
    (validatorIndexOf_none_of_singleton hvals (by decide))

/-- The bad-credential-or-source reason occurs: a BLS (0x00) credential. -/
theorem ignore_witness_badCredentialOrSource :
    ∃ (s : BeaconState Preset.minimal .electra) (wr : WithdrawalRequest),
      Facts.classifyWithdrawalRequest Config.minimal s wr =
        .ok (.ignored .badCredentialOrSource) := by
  refine ⟨stateWith
    (oneVal (witValidator credBLS U64.zero FAR_FUTURE_EPOCH
      (U64.lit 32000000000))) (oneBal (U64.lit 32000000000))
    (U64.lit 800) SszList.empty, witRequest witPubkey (U64.lit 1000), ?_⟩
  have hvals : (stateWith
      (oneVal (witValidator credBLS U64.zero FAR_FUTURE_EPOCH
        (U64.lit 32000000000))) (oneBal (U64.lit 32000000000))
      (U64.lit 800) SszList.empty).validators.toArray =
      #[witValidator credBLS U64.zero FAR_FUTURE_EPOCH
        (U64.lit 32000000000)] := rfl
  exact Facts.classify_ignored_badCredentialOrSource rfl (by decide)
    (validatorIndexOf_some_of_singleton hvals (by decide)) rfl (by decide)

/-- The not-active reason occurs: activation epoch 200 is after epoch 100. -/
theorem ignore_witness_notActive :
    ∃ (s : BeaconState Preset.minimal .electra) (wr : WithdrawalRequest),
      Facts.classifyWithdrawalRequest Config.minimal s wr =
        .ok (.ignored .notActive) := by
  refine ⟨stateWith
    (oneVal (witValidator cred01 (U64.lit 200) FAR_FUTURE_EPOCH
      (U64.lit 32000000000))) (oneBal (U64.lit 32000000000))
    (U64.lit 800) SszList.empty, witRequest witPubkey (U64.lit 1000), ?_⟩
  have hvals : (stateWith
      (oneVal (witValidator cred01 (U64.lit 200) FAR_FUTURE_EPOCH
        (U64.lit 32000000000))) (oneBal (U64.lit 32000000000))
      (U64.lit 800) SszList.empty).validators.toArray =
      #[witValidator cred01 (U64.lit 200) FAR_FUTURE_EPOCH
        (U64.lit 32000000000)] := rfl
  exact Facts.classify_ignored_notActive rfl (by decide)
    (validatorIndexOf_some_of_singleton hvals (by decide)) rfl (by decide) rfl
    (by decide)

/-- The already-exiting reason occurs: exit epoch 150 is set. -/
theorem ignore_witness_alreadyExiting :
    ∃ (s : BeaconState Preset.minimal .electra) (wr : WithdrawalRequest),
      Facts.classifyWithdrawalRequest Config.minimal s wr =
        .ok (.ignored .alreadyExiting) := by
  refine ⟨stateWith
    (oneVal (witValidator cred01 U64.zero (U64.lit 150)
      (U64.lit 32000000000))) (oneBal (U64.lit 32000000000))
    (U64.lit 800) SszList.empty, witRequest witPubkey (U64.lit 1000), ?_⟩
  have hvals : (stateWith
      (oneVal (witValidator cred01 U64.zero (U64.lit 150)
        (U64.lit 32000000000))) (oneBal (U64.lit 32000000000))
      (U64.lit 800) SszList.empty).validators.toArray =
      #[witValidator cred01 U64.zero (U64.lit 150) (U64.lit 32000000000)] := rfl
  exact Facts.classify_ignored_alreadyExiting rfl (by decide)
    (validatorIndexOf_some_of_singleton hvals (by decide)) rfl (by decide) rfl
    (by decide) (by decide)

/-- The too-early reason occurs: epoch 100 is before activation 90 plus
`SHARD_COMMITTEE_PERIOD` (64). -/
theorem ignore_witness_tooEarly :
    ∃ (s : BeaconState Preset.minimal .electra) (wr : WithdrawalRequest),
      Facts.classifyWithdrawalRequest Config.minimal s wr =
        .ok (.ignored .tooEarly) := by
  refine ⟨stateWith
    (oneVal (witValidator cred01 (U64.lit 90) FAR_FUTURE_EPOCH
      (U64.lit 32000000000))) (oneBal (U64.lit 32000000000))
    (U64.lit 800) SszList.empty, witRequest witPubkey (U64.lit 1000), ?_⟩
  have hvals : (stateWith
      (oneVal (witValidator cred01 (U64.lit 90) FAR_FUTURE_EPOCH
        (U64.lit 32000000000))) (oneBal (U64.lit 32000000000))
      (U64.lit 800) SszList.empty).validators.toArray =
      #[witValidator cred01 (U64.lit 90) FAR_FUTURE_EPOCH
        (U64.lit 32000000000)] := rfl
  exact Facts.classify_ignored_tooEarly rfl (by decide)
    (validatorIndexOf_some_of_singleton hvals (by decide)) rfl (by decide) rfl
    (by decide) (by decide) rfl rfl (by decide)

/-- The full-exit-with-pending-balance reason occurs: a full exit while a
thousand gwei remain pending for the validator. -/
theorem ignore_witness_fullExitPendingBalance :
    ∃ (s : BeaconState Preset.minimal .electra) (wr : WithdrawalRequest),
      Facts.classifyWithdrawalRequest Config.minimal s wr =
        .ok (.ignored .fullExitPendingBalance) := by
  refine ⟨stateWith (oneVal goodValidator) (oneBal (U64.lit 32000000000))
    (U64.lit 800) onePending,
    witRequest witPubkey FULL_EXIT_REQUEST_AMOUNT, ?_⟩
  have hvals : (stateWith (oneVal goodValidator) (oneBal (U64.lit 32000000000))
    (U64.lit 800) onePending).validators.toArray = #[goodValidator] := rfl
  exact Facts.classify_ignored_fullExitPendingBalance (cfg := Config.minimal)
    (s := stateWith (oneVal goodValidator) (oneBal (U64.lit 32000000000))
      (U64.lit 800) onePending)
    (wr := witRequest witPubkey FULL_EXIT_REQUEST_AMOUNT) rfl (by decide)
    (validatorIndexOf_some_of_singleton hvals (by decide)) rfl (by decide) rfl
    (by decide) (by decide) rfl rfl (by decide) rfl (by decide) (by decide)

/-- The not-compounding reason occurs: a partial withdrawal with a 0x01
credential. -/
theorem ignore_witness_notCompounding :
    ∃ (s : BeaconState Preset.minimal .electra) (wr : WithdrawalRequest),
      Facts.classifyWithdrawalRequest Config.minimal s wr =
        .ok (.ignored .notCompounding) := by
  refine ⟨stateWith (oneVal goodValidator) (oneBal (U64.lit 32000000000))
    (U64.lit 800) SszList.empty, witRequest witPubkey (U64.lit 1000), ?_⟩
  have hvals : (stateWith (oneVal goodValidator) (oneBal (U64.lit 32000000000))
    (U64.lit 800) SszList.empty).validators.toArray = #[goodValidator] := rfl
  exact Facts.classify_ignored_notCompounding (cfg := Config.minimal)
    (s := stateWith (oneVal goodValidator) (oneBal (U64.lit 32000000000))
      (U64.lit 800) SszList.empty)
    (wr := witRequest witPubkey (U64.lit 1000)) rfl (by decide)
    (validatorIndexOf_some_of_singleton hvals (by decide)) rfl (by decide) rfl
    (by decide) (by decide) rfl rfl (by decide) rfl (by decide) rfl rfl rfl
    (by decide)

/-- The insufficient-effective-balance reason occurs: a 0x02-credentialed
partial withdrawal with effective balance below `MIN_ACTIVATION_BALANCE`. -/
theorem ignore_witness_insufficientEffectiveBalance :
    ∃ (s : BeaconState Preset.minimal .electra) (wr : WithdrawalRequest),
      Facts.classifyWithdrawalRequest Config.minimal s wr =
        .ok (.ignored .insufficientEffectiveBalance) := by
  refine ⟨stateWith
    (oneVal (witValidator cred02 U64.zero FAR_FUTURE_EPOCH (U64.lit 1000)))
    (oneBal (U64.lit 32000000000)) (U64.lit 800) SszList.empty,
    witRequest witPubkey (U64.lit 1000), ?_⟩
  have hvals : (stateWith
      (oneVal (witValidator cred02 U64.zero FAR_FUTURE_EPOCH (U64.lit 1000)))
      (oneBal (U64.lit 32000000000)) (U64.lit 800)
      SszList.empty).validators.toArray =
      #[witValidator cred02 U64.zero FAR_FUTURE_EPOCH (U64.lit 1000)] := rfl
  exact Facts.classify_ignored_insufficientEffectiveBalance (cfg := Config.minimal)
    (s := stateWith
      (oneVal (witValidator cred02 U64.zero FAR_FUTURE_EPOCH (U64.lit 1000)))
      (oneBal (U64.lit 32000000000)) (U64.lit 800) SszList.empty)
    (wr := witRequest witPubkey (U64.lit 1000)) rfl (by decide)
    (validatorIndexOf_some_of_singleton hvals (by decide)) rfl (by decide) rfl
    (by decide) (by decide) rfl rfl (by decide) rfl (by decide) rfl rfl rfl
    (by decide) (by decide)

/-- The no-excess reason occurs: a 0x02-credentialed partial withdrawal whose
balance is exactly `MIN_ACTIVATION_BALANCE` with nothing pending. -/
theorem ignore_witness_noExcess :
    ∃ (s : BeaconState Preset.minimal .electra) (wr : WithdrawalRequest),
      Facts.classifyWithdrawalRequest Config.minimal s wr =
        .ok (.ignored .noExcess) := by
  refine ⟨stateWith
    (oneVal (witValidator cred02 U64.zero FAR_FUTURE_EPOCH
      (U64.lit 32000000000))) (oneBal (U64.lit 32000000000))
    (U64.lit 800) SszList.empty, witRequest witPubkey (U64.lit 1000), ?_⟩
  have hvals : (stateWith
      (oneVal (witValidator cred02 U64.zero FAR_FUTURE_EPOCH
        (U64.lit 32000000000))) (oneBal (U64.lit 32000000000))
      (U64.lit 800) SszList.empty).validators.toArray =
      #[witValidator cred02 U64.zero FAR_FUTURE_EPOCH
        (U64.lit 32000000000)] := rfl
  exact Facts.classify_ignored_noExcess (cfg := Config.minimal)
    (s := stateWith
      (oneVal (witValidator cred02 U64.zero FAR_FUTURE_EPOCH
        (U64.lit 32000000000))) (oneBal (U64.lit 32000000000))
      (U64.lit 800) SszList.empty)
    (wr := witRequest witPubkey (U64.lit 1000)) rfl (by decide)
    (validatorIndexOf_some_of_singleton hvals (by decide)) rfl (by decide) rfl
    (by decide) (by decide) rfl rfl (by decide) rfl (by decide) rfl rfl rfl
    (by decide) (by decide) (by decide)

/-- Every ignore reason occurs on a closed witness. -/
theorem every_ignore_reason_occurs (r : Facts.WithdrawalIgnoreReason) :
    ∃ (s : BeaconState Preset.minimal .electra) (wr : WithdrawalRequest),
      Facts.classifyWithdrawalRequest Config.minimal s wr = .ok (.ignored r) := by
  cases r with
  | partialQueueFull => exact ignore_witness_partialQueueFull
  | unknownPubkey => exact ignore_witness_unknownPubkey
  | badCredentialOrSource => exact ignore_witness_badCredentialOrSource
  | notActive => exact ignore_witness_notActive
  | alreadyExiting => exact ignore_witness_alreadyExiting
  | tooEarly => exact ignore_witness_tooEarly
  | fullExitPendingBalance => exact ignore_witness_fullExitPendingBalance
  | notCompounding => exact ignore_witness_notCompounding
  | insufficientEffectiveBalance => exact ignore_witness_insufficientEffectiveBalance
  | noExcess => exact ignore_witness_noExcess

end Blanc.Lift.WithdrawalRequest
