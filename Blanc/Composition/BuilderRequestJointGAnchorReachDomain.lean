import Blanc.Composition.BuilderRequestJointGAnchorReachStep

/-!
# The Gloas transition keeps the signing domain's inputs

Goal `eip8282-charge-once-v1`, outcome C4: `DomainKept`, the fact about Jaune's Gloas transition that
`BidSigned` at a later state reads. No step of Gloas `process_slots` or `process_block` writes `fork` or
`genesis_validators_root` (`DomFrame`; only the fork upgrades write `fork`).

Each lemma is a run of Jaune's relation-parametric generator (`JauneConsensus.Facts.Gloas.Step`) at `domFrame`,
in the order of `JauneConsensus.Facts.Gloas.FinalizedNotAhead`'s `FinSlot` family, with the leaf lemmas
registered locally as `gstep_of` rules; the slot loop is read through `slotTick_cases`.
-/

namespace Blanc.Lift.BuilderRequest

open Jaune JauneConsensus ExecutionTrace Blanc JauneConsensus.Facts JauneConsensus.Facts.Gloas
  JauneConsensus.Facts.Gloas.Inv

variable {P : Preset}

/-- `DomFrame` as a step relation. -/
def domFrame : StepRel (Gloas.BeaconState P) where
  R := DomFrame
  refl _ := ⟨rfl, rfl⟩
  trans h₁ h₂ := h₁.trans h₂

/-- Peel the binds of a successful run `h : c = .ok x`, splitting where a conditional or a tuple match stands
in the way. For the long checks-then-write steps, whose writes are at the end: cheaper than the generator,
which tries every registered rule at every bind. -/
local macro "peel " h:ident : tactic =>
  `(tactic| repeat' (first
    | (obtain ⟨_, _, $h:ident⟩ := bind_eq_ok_iff.mp $h)
    | (split at $h:ident)))

/-! ## The Gloas block -/

section Block

local macro_rules
  | `(tactic| gstep_close) => `(tactic| exact (show DomFrame _ _ from ⟨rfl, rfl⟩))

theorem increaseBalance_dom (s : GSt P) (i : ValidatorIndex) (d : Gwei) :
    Ok (JauneConsensus.Gloas.increaseBalance s i d) (domFrame.R s) := by
  unfold JauneConsensus.Gloas.increaseBalance; gvcg

theorem decreaseBalance_dom (s : GSt P) (i : ValidatorIndex) (d : Gwei) :
    Ok (JauneConsensus.Gloas.decreaseBalance s i d) (domFrame.R s) := by
  unfold JauneConsensus.Gloas.decreaseBalance; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (increaseBalance_dom _ _ _) $h; exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (decreaseBalance_dom _ _ _) $h; exact hh))

theorem computeExitEpochAndUpdateChurn_dom (cfg : Config) (s : GSt P) (b : Gwei) :
    Ok (JauneConsensus.Gloas.computeExitEpochAndUpdateChurn cfg s b)
      (fun p => domFrame.R s p.1) := by
  unfold JauneConsensus.Gloas.computeExitEpochAndUpdateChurn; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (computeExitEpochAndUpdateChurn_dom _ _ _) $h; exact hh))

theorem initiateValidatorExit_dom (cfg : Config) (s : GSt P) (i : ValidatorIndex) :
    Ok (JauneConsensus.Gloas.initiateValidatorExit cfg s i) (domFrame.R s) := by
  unfold JauneConsensus.Gloas.initiateValidatorExit; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (initiateValidatorExit_dom _ _ _) $h; exact hh))

theorem queueExcessActiveBalance_dom (s : GSt P) (i : ValidatorIndex) :
    Ok (JauneConsensus.Gloas.queueExcessActiveBalance s i) (domFrame.R s) := by
  unfold JauneConsensus.Gloas.queueExcessActiveBalance; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (queueExcessActiveBalance_dom _ _) $h; exact hh))

theorem switchToCompoundingValidator_dom (s : GSt P) (i : ValidatorIndex) :
    Ok (JauneConsensus.Gloas.switchToCompoundingValidator s i) (domFrame.R s) := by
  unfold JauneConsensus.Gloas.switchToCompoundingValidator; gvcg
  all_goals exact StepRel.ok_rebase domFrame ⟨rfl, rfl⟩ (queueExcessActiveBalance_dom _ _)

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (switchToCompoundingValidator_dom _ _) $h; exact hh))

theorem computeConsolidationEpochAndUpdateChurn_dom (cfg : Config) (s : GSt P) (b : Gwei) :
    Ok (JauneConsensus.Gloas.computeConsolidationEpochAndUpdateChurn cfg s b)
      (fun p => domFrame.R s p.1) := by
  unfold JauneConsensus.Gloas.computeConsolidationEpochAndUpdateChurn; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (computeConsolidationEpochAndUpdateChurn_dom _ _ _) $h; exact hh))

theorem processWithdrawalRequest_dom (cfg : Config) (s : GSt P) (wr : WithdrawalRequest) :
    Ok (JauneConsensus.Gloas.processWithdrawalRequest cfg s wr) (domFrame.R s) := by
  unfold JauneConsensus.Gloas.processWithdrawalRequest; gvcg
  all_goals exact fun x hx => initiateValidatorExit_dom _ _ _ x hx

theorem processConsolidationRequest_dom (cfg : Config) (s : GSt P) (cr : ConsolidationRequest) :
    Ok (JauneConsensus.Gloas.processConsolidationRequest cfg s cr) (domFrame.R s) := by
  unfold JauneConsensus.Gloas.processConsolidationRequest; gvcg
  all_goals exact switchToCompoundingValidator_dom _ _

theorem settleBuilderPayment_dom (s : GSt P) (i : U64) :
    Ok (JauneConsensus.Gloas.settleBuilderPayment s i) (domFrame.R s) := by
  unfold JauneConsensus.Gloas.settleBuilderPayment; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (processWithdrawalRequest_dom _ _ _) $h; exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (processConsolidationRequest_dom _ _ _) $h; exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (settleBuilderPayment_dom _ _) $h; exact hh))

section Prefix

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (refine domFrame.trans ?_ (StepRel.forIn_array_rel domFrame id ?_ _ _ $h)
               · exact (show DomFrame _ _ from ⟨rfl, rfl⟩)
               · intro _ _; gvcg))

theorem applyParentPrefix_dom (ctx : Ctx) (s : GSt P)
    (r : JauneConsensus.Gloas.ExecutionRequests) :
    Ok (JauneConsensus.Gloas.applyParentPrefix ctx s r) (domFrame.R s) := by
  unfold JauneConsensus.Gloas.applyParentPrefix; gvcg

end Prefix

theorem processBuilderDepositRequest_dom (ctx : Ctx) (s : GSt P)
    (r : JauneConsensus.Gloas.BuilderDepositRequest) :
    Ok (JauneConsensus.Gloas.processBuilderDepositRequest ctx s r) (domFrame.R s) := by
  intro s' h
  have := (processBuilderDepositRequest_frame h).2.2.2.2.2
  rw [this]; exact ⟨rfl, rfl⟩

theorem processBuilderExitRequest_dom (cfg : Config) (s : GSt P)
    (r : JauneConsensus.Gloas.BuilderExitRequest) :
    Ok (JauneConsensus.Gloas.processBuilderExitRequest cfg s r) (domFrame.R s) := by
  intro s' h
  have := (processBuilderExitRequest_frame h).2.2.2.2.2
  rw [this]; exact ⟨rfl, rfl⟩

theorem applyParentSuffix_dom (st0 s : GSt P) :
    Ok (JauneConsensus.Gloas.applyParentSuffix st0 s) (domFrame.R s) := by
  unfold JauneConsensus.Gloas.applyParentSuffix; gvcg

theorem processParentExecutionPayload_dom (ctx : Ctx) (s : GSt P)
    (blk : JauneConsensus.Gloas.BeaconBlock P) :
    Ok (JauneConsensus.Gloas.processParentExecutionPayload ctx s blk) (domFrame.R s) := by
  intro s1 h1
  rcases processParentExecutionPayload_cases h1 with ⟨rfl, _⟩ | ⟨_, a, d, e, ha, hd, he, hs⟩
  · exact domFrame.refl _
  have pa := applyParentPrefix_dom ctx s _ a ha
  have pd : DomFrame s d := forIn_yield_inv (DomFrame s) _
    (fun _ _ _ hI hm => domFrame.trans hI (processBuilderDepositRequest_dom _ _ _ _ hm)) _ _ _ hd pa
  have pe : DomFrame s e := forIn_yield_inv (DomFrame s) _
    (fun _ _ _ hI hm => domFrame.trans hI (processBuilderExitRequest_dom _ _ _ _ hm)) _ _ _ he pd
  exact domFrame.trans pe (applyParentSuffix_dom _ _ _ hs)

theorem processBlockHeader_dom (s : GSt P) (blk : JauneConsensus.Gloas.BeaconBlock P) :
    Ok (JauneConsensus.Gloas.processBlockHeader s blk) (domFrame.R s) := by
  intro s' h
  rw [(processBlockHeader_post h).2.2]; exact ⟨rfl, rfl⟩

theorem applyWithdrawals_dom (s : GSt P) (ws : Array JauneConsensus.Withdrawal) :
    Ok (JauneConsensus.Gloas.applyWithdrawals s ws) (domFrame.R s) := by
  unfold JauneConsensus.Gloas.applyWithdrawals; gvcg

theorem updateNextWithdrawalIndex_dom (s : GSt P) (ws : Array JauneConsensus.Withdrawal) :
    Ok (JauneConsensus.Gloas.updateNextWithdrawalIndex s ws) (domFrame.R s) := by
  unfold JauneConsensus.Gloas.updateNextWithdrawalIndex; gvcg

theorem updateNextWithdrawalBuilderIndex_dom (s : GSt P) (n : U64) :
    Ok (JauneConsensus.Gloas.updateNextWithdrawalBuilderIndex s n) (domFrame.R s) := by
  unfold JauneConsensus.Gloas.updateNextWithdrawalBuilderIndex; gvcg

theorem updateNextWithdrawalValidatorIndex_dom (s : GSt P) (ws : Array JauneConsensus.Withdrawal) :
    Ok (JauneConsensus.Gloas.updateNextWithdrawalValidatorIndex s ws) (domFrame.R s) := by
  unfold JauneConsensus.Gloas.updateNextWithdrawalValidatorIndex; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (applyWithdrawals_dom _ _) $h; exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (updateNextWithdrawalIndex_dom _ _) $h; exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (updateNextWithdrawalBuilderIndex_dom _ _) $h; exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (updateNextWithdrawalValidatorIndex_dom _ _) $h; exact hh))

theorem processWithdrawals_dom (s : GSt P) :
    Ok (JauneConsensus.Gloas.processWithdrawals s) (domFrame.R s) := by
  unfold JauneConsensus.Gloas.processWithdrawals; gvcg
  all_goals exact updateNextWithdrawalValidatorIndex_dom _ _

theorem processExecutionPayloadBid_dom (ctx : Ctx) (s : GSt P)
    (sb : JauneConsensus.Gloas.SignedExecutionPayloadBid) :
    Ok (JauneConsensus.Gloas.processExecutionPayloadBid ctx s sb) (domFrame.R s) := by
  intro s' h
  unfold JauneConsensus.Gloas.processExecutionPayloadBid at h
  dsimp only at h
  peel h
  all_goals
    rename_i w hst
    obtain rfl : _ = s' := Except.ok.inj h
    refine domFrame.trans (b := w) ?_ (show DomFrame _ _ from ⟨rfl, rfl⟩)
    cases hst
    exact (show DomFrame _ _ from ⟨rfl, rfl⟩)

theorem processRandao_dom (ctx : Ctx) (s : GSt P) (body : JauneConsensus.Gloas.BeaconBlockBody P) :
    Ok (JauneConsensus.Gloas.processRandao ctx s body) (domFrame.R s) := by
  unfold JauneConsensus.Gloas.processRandao; gvcg

theorem processEth1Data_dom (s : GSt P) (body : JauneConsensus.Gloas.BeaconBlockBody P) :
    Ok (JauneConsensus.Gloas.processEth1Data s body) (domFrame.R s) := by
  unfold JauneConsensus.Gloas.processEth1Data; gvcg

theorem processSyncAggregate_dom (ctx : Ctx) (s : GSt P) (sa : SyncAggregate P) :
    Ok (JauneConsensus.Gloas.processSyncAggregate ctx s sa) (domFrame.R s) := by
  intro s' h
  unfold JauneConsensus.Gloas.processSyncAggregate at h
  dsimp only at h
  peel h
  all_goals
    rename_i w hloop
    obtain rfl : w = s' := Except.ok.inj h
    refine StepRel.forIn_array_rel domFrame id ?_ _ _ hloop
    intro _ _
    gvcg

theorem slashValidator_dom (cfg : Config) (s : GSt P) (i : ValidatorIndex)
    (wb : Option ValidatorIndex) :
    Ok (JauneConsensus.Gloas.slashValidator cfg s i wb) (domFrame.R s) := by
  unfold JauneConsensus.Gloas.slashValidator; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (slashValidator_dom _ _ _ _) $h; exact hh))

theorem processProposerSlashing_dom (ctx : Ctx) (s : GSt P) (ps : ProposerSlashing) :
    Ok (JauneConsensus.Gloas.processProposerSlashing ctx s ps) (domFrame.R s) := by
  unfold JauneConsensus.Gloas.processProposerSlashing; gvcg
  all_goals exact slashValidator_dom _ _ _ _

theorem processAttesterSlashing_dom (ctx : Ctx) (s : GSt P)
    (as : JauneConsensus.Gloas.AttesterSlashing) :
    Ok (JauneConsensus.Gloas.processAttesterSlashing ctx s as) (domFrame.R s) := by
  unfold JauneConsensus.Gloas.processAttesterSlashing; gvcg

theorem processVoluntaryExit_dom (ctx : Ctx) (s : GSt P) (sve : SignedVoluntaryExit) :
    Ok (JauneConsensus.Gloas.processVoluntaryExit ctx s sve) (domFrame.R s) := by
  unfold JauneConsensus.Gloas.processVoluntaryExit; gvcg
  all_goals exact fun x hx => initiateValidatorExit_dom _ _ _ x hx

theorem processBlsToExecutionChange_dom (ctx : Ctx) (s : GSt P)
    (sac : SignedBLSToExecutionChange) :
    Ok (JauneConsensus.Gloas.processBlsToExecutionChange ctx s sac) (domFrame.R s) := by
  unfold JauneConsensus.Gloas.processBlsToExecutionChange; gvcg

theorem processPayloadAttestation_dom (ctx : Ctx) (s : GSt P)
    (pa : JauneConsensus.Gloas.PayloadAttestation P) :
    Ok (JauneConsensus.Gloas.processPayloadAttestation ctx s pa) (domFrame.R s) := by
  unfold JauneConsensus.Gloas.processPayloadAttestation; gvcg

section Attestation

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (increaseBalance_dom _ _ _) $h; exact (domFrame.trans (by split <;> exact ⟨rfl, rfl⟩) hh)))

theorem processAttestation_dom (ctx : Ctx) (s : GSt P)
    (a : JauneConsensus.Gloas.Attestation P) (ps : Slot) :
    Ok (JauneConsensus.Gloas.processAttestation ctx s a ps) (domFrame.R s) := by
  intro s' h
  unfold JauneConsensus.Gloas.processAttestation at h
  dsimp only at h
  peel h
  all_goals
    cases h
    have hinc := increaseBalance_dom _ _ _ _ ‹JauneConsensus.Gloas.increaseBalance _ _ _ = .ok _›
    refine domFrame.trans (domFrame.trans ?_ hinc) (show DomFrame _ _ from ⟨rfl, rfl⟩)
    exact (show DomFrame _ _ from ⟨rfl, rfl⟩)

end Attestation

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (processProposerSlashing_dom _ _ _) $h; exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (processAttesterSlashing_dom _ _ _) $h; exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (processAttestation_dom _ _ _ _) $h; exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (processVoluntaryExit_dom _ _ _) $h; exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (processBlsToExecutionChange_dom _ _ _) $h; exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (processPayloadAttestation_dom _ _ _) $h; exact hh))

theorem processOperations_dom (ctx : Ctx) (s : GSt P)
    (body : JauneConsensus.Gloas.BeaconBlockBody P) (ps : Slot) :
    Ok (JauneConsensus.Gloas.processOperations ctx s body ps) (domFrame.R s) := by
  unfold JauneConsensus.Gloas.processOperations; gvcg

/-- **A Gloas block keeps the finalized checkpoint and the slot.** -/
theorem processBlock_domFrame {ctx : Ctx} {s s' : GSt P} {blk : JauneConsensus.Gloas.BeaconBlock P}
    (h : JauneConsensus.Gloas.processBlock ctx s blk = .ok s') : DomFrame s s' := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, h1, h2, h3, h4, h5, h6, h7, h8⟩ := processBlock_phases h
  exact domFrame.trans (processParentExecutionPayload_dom _ _ _ _ h1)
    (domFrame.trans (processBlockHeader_dom _ _ _ h2)
    (domFrame.trans (processWithdrawals_dom _ _ h3)
    (domFrame.trans (processExecutionPayloadBid_dom _ _ _ _ h4)
    (domFrame.trans (processRandao_dom _ _ _ _ h5)
    (domFrame.trans (processEth1Data_dom _ _ _ h6)
    (domFrame.trans (processOperations_dom _ _ _ _ _ h7)
      (processSyncAggregate_dom _ _ _ _ h8)))))))

end Block

/-! ## The Gloas epoch and the slot loop -/

section Epoch

local macro_rules
  | `(tactic| gstep_close) => `(tactic| exact (show DomFrame _ _ from ⟨rfl, rfl⟩))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (increaseBalance_dom _ _ _) $h; exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (decreaseBalance_dom _ _ _) $h; exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (computeExitEpochAndUpdateChurn_dom _ _ _) $h; exact hh))
local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (initiateValidatorExit_dom _ _ _) $h; exact hh))

theorem addValidatorToRegistry_dom (s : GSt P) (pk : BLSPubkey) (wc : Bytes32) (amount : Gwei) :
    Ok (JauneConsensus.Gloas.addValidatorToRegistry s pk wc amount) (domFrame.R s) := by
  unfold JauneConsensus.Gloas.addValidatorToRegistry; gvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (addValidatorToRegistry_dom _ _ _ _) $h; exact hh))

theorem applyPendingDeposit_dom (ctx : Ctx) (s : GSt P) (d : PendingDeposit) :
    Ok (JauneConsensus.Gloas.applyPendingDeposit ctx s d) (domFrame.R s) := by
  unfold JauneConsensus.Gloas.applyPendingDeposit; gvcg
  · exact addValidatorToRegistry_dom _ _ _ _
  · exact increaseBalance_dom _ _ _

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (applyPendingDeposit_dom _ _ _) $h; exact hh))

theorem processInactivityUpdates_dom (cfg : Config) (s : GSt P) :
    Ok (JauneConsensus.Gloas.processInactivityUpdates cfg s) (domFrame.R s) := by
  unfold JauneConsensus.Gloas.processInactivityUpdates; gvcg

theorem processRewardsAndPenalties_dom (cfg : Config) (s : GSt P) :
    Ok (JauneConsensus.Gloas.processRewardsAndPenalties cfg s) (domFrame.R s) := by
  unfold JauneConsensus.Gloas.processRewardsAndPenalties; gvcg

theorem processRegistryUpdates_dom (cfg : Config) (s : GSt P) :
    Ok (JauneConsensus.Gloas.processRegistryUpdates cfg s) (domFrame.R s) := by
  unfold JauneConsensus.Gloas.processRegistryUpdates; gvcg

theorem processSlashings_dom (cfg : Config) (s : GSt P) :
    Ok (JauneConsensus.Gloas.processSlashings cfg s) (domFrame.R s) := by
  unfold JauneConsensus.Gloas.processSlashings; gvcg

theorem processEth1DataReset_dom (cfg : Config) (s : GSt P) :
    Ok (JauneConsensus.Gloas.processEth1DataReset cfg s) (domFrame.R s) := by
  unfold JauneConsensus.Gloas.processEth1DataReset; gvcg

section PendingDeposits

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (refine StepRel.forIn_array_rel _ (fun x => x.2.2.2.2) ?_ _ _ $h; intro _ _; gvcg))

theorem processPendingDeposits_dom (ctx : Ctx) (s : GSt P) :
    Ok (JauneConsensus.Gloas.processPendingDeposits ctx s) (domFrame.R s) := by
  unfold JauneConsensus.Gloas.processPendingDeposits; gvcg

end PendingDeposits

theorem processPendingConsolidations_dom (cfg : Config) (s : GSt P) :
    Ok (JauneConsensus.Gloas.processPendingConsolidations cfg s) (domFrame.R s) := by
  unfold JauneConsensus.Gloas.processPendingConsolidations; gvcg

theorem processBuilderPendingPayments_dom (cfg : Config) (s : GSt P) :
    Ok (JauneConsensus.Gloas.processBuilderPendingPayments cfg s) (domFrame.R s) := by
  unfold JauneConsensus.Gloas.processBuilderPendingPayments; gvcg

theorem processEffectiveBalanceUpdates_dom (cfg : Config) (s : GSt P) :
    Ok (JauneConsensus.Gloas.processEffectiveBalanceUpdates cfg s) (domFrame.R s) := by
  unfold JauneConsensus.Gloas.processEffectiveBalanceUpdates; gvcg

theorem processSlashingsReset_dom (cfg : Config) (s : GSt P) :
    Ok (JauneConsensus.Gloas.processSlashingsReset cfg s) (domFrame.R s) := by
  unfold JauneConsensus.Gloas.processSlashingsReset; gvcg

theorem processRandaoMixesReset_dom (cfg : Config) (s : GSt P) :
    Ok (JauneConsensus.Gloas.processRandaoMixesReset cfg s) (domFrame.R s) := by
  unfold JauneConsensus.Gloas.processRandaoMixesReset; gvcg

theorem processHistoricalSummariesUpdate_dom (cfg : Config) (s : GSt P) :
    Ok (JauneConsensus.Gloas.processHistoricalSummariesUpdate cfg s) (domFrame.R s) := by
  unfold JauneConsensus.Gloas.processHistoricalSummariesUpdate; gvcg

theorem processParticipationFlagUpdates_dom (cfg : Config) (s : GSt P) :
    Ok (JauneConsensus.Gloas.processParticipationFlagUpdates cfg s) (domFrame.R s) := by
  unfold JauneConsensus.Gloas.processParticipationFlagUpdates; gvcg

theorem processSyncCommitteeUpdates_dom (ctx : Ctx) (s : GSt P) :
    Ok (JauneConsensus.Gloas.processSyncCommitteeUpdates ctx s) (domFrame.R s) := by
  unfold JauneConsensus.Gloas.processSyncCommitteeUpdates; gvcg

theorem processProposerLookahead_dom (cfg : Config) (s : GSt P) :
    Ok (JauneConsensus.Gloas.processProposerLookahead cfg s) (domFrame.R s) := by
  unfold JauneConsensus.Gloas.processProposerLookahead; gvcg

theorem processPtcWindow_dom (cfg : Config) (s : GSt P) :
    Ok (JauneConsensus.Gloas.processPtcWindow cfg s) (domFrame.R s) := by
  unfold JauneConsensus.Gloas.processPtcWindow; gvcg

theorem weighJustificationAndFinalization_dom (s : GSt P) (t p c : Gwei) :
    Ok (JauneConsensus.Gloas.weighJustificationAndFinalization s t p c) (domFrame.R s) := by
  unfold JauneConsensus.Gloas.weighJustificationAndFinalization; jvcg

local macro_rules
  | `(tactic| gstep_of $h) =>
    `(tactic| (have hh := StepRel.of_ok (weighJustificationAndFinalization_dom _ _ _ _) $h; exact hh))

theorem processJustificationAndFinalization_dom (cfg : Config) (s : GSt P) :
    Ok (JauneConsensus.Gloas.processJustificationAndFinalization cfg s) (domFrame.R s) := by
  unfold JauneConsensus.Gloas.processJustificationAndFinalization; gvcg
  all_goals exact weighJustificationAndFinalization_dom _ _ _ _

/-- `process_epoch` keeps the signing domain's inputs. -/
theorem processEpoch_dom {ctx : Ctx} {s s' : GSt P}
    (h : JauneConsensus.Gloas.processEpoch ctx s = .ok s') : DomFrame s s' := by
  unfold JauneConsensus.Gloas.processEpoch at h
  obtain ⟨x1, h1, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x2, h2, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x3, h3, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x4, h4, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x5, h5, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x6, h6, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x7, h7, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x8, h8, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x9, h9, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x10, h10, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x11, h11, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x12, h12, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x13, h13, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x14, h14, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x15, h15, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨x16, h16, h⟩ := bind_eq_ok_iff.mp h
  exact domFrame.trans (processJustificationAndFinalization_dom _ _ _ h1)
    (domFrame.trans (processInactivityUpdates_dom _ _ _ h2)
    (domFrame.trans (processRewardsAndPenalties_dom _ _ _ h3)
    (domFrame.trans (processRegistryUpdates_dom _ _ _ h4)
    (domFrame.trans (processSlashings_dom _ _ _ h5)
    (domFrame.trans (processEth1DataReset_dom _ _ _ h6)
    (domFrame.trans (processPendingDeposits_dom _ _ _ h7)
    (domFrame.trans (processPendingConsolidations_dom _ _ _ h8)
    (domFrame.trans (processBuilderPendingPayments_dom _ _ _ h9)
    (domFrame.trans (processEffectiveBalanceUpdates_dom _ _ _ h10)
    (domFrame.trans (processSlashingsReset_dom _ _ _ h11)
    (domFrame.trans (processRandaoMixesReset_dom _ _ _ h12)
    (domFrame.trans (processHistoricalSummariesUpdate_dom _ _ _ h13)
    (domFrame.trans (processParticipationFlagUpdates_dom _ _ _ h14)
    (domFrame.trans (processSyncCommitteeUpdates_dom _ _ _ h15)
    (domFrame.trans (processProposerLookahead_dom _ _ _ h16)
      (processPtcWindow_dom _ _ _ h))))))))))))))))

theorem processSlot_dom (s : GSt P) :
    Ok (JauneConsensus.Gloas.processSlot s) (domFrame.R s) := by
  rw [processSlot_eq]
  intro s' h
  unfold processSlotH at h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  cases h
  refine ⟨?_, ?_⟩ <;> split <;> rfl

end Epoch

/-- **Gloas `process_slots` keeps the signing domain's inputs.** -/
theorem processSlots_dom {ctx : Ctx} {s s' : GSt P} {slot : U64}
    (h : JauneConsensus.Gloas.processSlots ctx s slot = .ok s') : DomFrame s s' := by
  unfold JauneConsensus.Gloas.processSlots JauneConsensus.Gloas.processSlotsWith at h
  obtain ⟨_, _, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨spe, hspe, h⟩ := bind_eq_ok_iff.mp h
  obtain ⟨out, hout, h⟩ := bind_eq_ok_iff.mp h
  cases h
  refine range_forIn_inv (DomFrame s) (fun a b x hb hx => ?_) hout (domFrame.refl _)
  obtain ⟨st1, h1, hx⟩ := bind_eq_ok_iff.mp hx
  obtain ⟨next, hn, hx⟩ := bind_eq_ok_iff.mp hx
  obtain ⟨r, hr, hx⟩ := bind_eq_ok_iff.mp hx
  have f1 : DomFrame s st1 := domFrame.trans hb (processSlot_dom _ _ h1)
  simp only [] at hx
  split at hx
  · obtain ⟨st2, he, hx⟩ := bind_eq_ok_iff.mp hx
    cases hx
    exact domFrame.trans (domFrame.trans f1 (processEpoch_dom he)) (show DomFrame _ _ from ⟨rfl, rfl⟩)
  · cases hx
    exact domFrame.trans f1 (show DomFrame _ _ from ⟨rfl, rfl⟩)

/-- **The Gloas transition keeps the signing domain's inputs** (`DomainKept`): no step of `process_slots` or
`process_block` writes `fork` or `genesis_validators_root`. -/
theorem domainKept (ctx : Ctx) : DomainKept ctx P where
  slots := processSlots_dom
  block := processBlock_domFrame
  toBid h1 h2 h3 := domFrame.trans (processParentExecutionPayload_dom _ _ _ _ h1)
    (domFrame.trans (processBlockHeader_dom _ _ _ h2) (processWithdrawals_dom _ _ h3))

end Blanc.Lift.BuilderRequest
