import Blanc.Composition.DepositConsensusOutcomes
import Blanc.Lift.Witness
import JauneConsensus.Facts.AnchorInvControls
import JauneConsensus.Facts.Gloas.BuilderAuth

/-! Actual executions witnessing the original deposit outcomes and pass controls. -/
namespace Blanc.Composition.DepositLedgerControls

open Jaune JauneConsensus JauneConsensus.Facts
open Blanc.Corpus.Freeze.Deposit

private def positiveDeposit : PendingDeposit :=
  { ctrlDeposit with amount := U64.one, signature := zeroBLSSignature, slot := U64.one }

private def existingState : BeaconState Preset.minimal .electra :=
  { ctrlBaseState with
    validators := ⟨#[ctrlValidator], by decide⟩,
    balances := ⟨#[U64.one], by decide⟩ }

private def registrationState (key : BLSPubkey) : BeaconState Preset.minimal .electra :=
  (addValidatorToRegistry ctrlBaseState key 0 U64.one).toOption.getD ctrlBaseState

private theorem registration_execution : ∀ key : BLSPubkey,
    addValidatorToRegistry ctrlBaseState key 0 U64.one = .ok (registrationState key) := by
  kernel_forall_rfl

private theorem registration_growth : ∀ key : BLSPubkey,
    (registrationState key).balances.length = ctrlBaseState.balances.length + 1 := by
  kernel_forall_rfl

private def toppedState : BeaconState Preset.minimal .electra :=
  (applyPendingDeposit (jointCtx Config.minimal true) existingState positiveDeposit).toOption.getD
    existingState

private theorem zeroSignature_rejected (key : BLSPubkey) :
    isValidDepositSignature (jointCtx Config.minimal true) key 0 U64.one zeroBLSSignature =
      .ok false := by
  have version : versionOf Config.minimal.GENESIS_FORK_VERSION =
      .ok ⟨#[0, 0, 0, 1], by decide⟩ := rfl
  simp only [isValidDepositSignature, computeDomainDefault, version, ok_bind', pure_bind]
  exact congrArg Except.ok
    (JauneConsensus.Facts.Gloas.blsVerify_true_of_head_zero _ _ _ rfl)

/-- All three original positive-amount outcomes execute, with their exact balance effects. -/
theorem outcomeWitnesses : D9OutcomeWitnesses := by
  constructor
  · have executed : applyPendingDeposit (jointCtx Config.minimal false) ctrlBaseState positiveDeposit =
        .ok (registrationState positiveDeposit.pubkey) := by kernel_rfl
    obtain ⟨o, outcome⟩ := DepositConsensusOutcomes.applyOutcome_of_success Config.minimal false
      ctrlBaseState (registrationState positiveDeposit.pubkey) positiveDeposit executed
    have classified : classifyApply (jointCtx Config.minimal false) ctrlBaseState positiveDeposit =
        .ok .newValidator := by kernel_rfl
    obtain rfl : o = .newValidator := Except.ok.inj (outcome.1.symm.trans classified)
    exact ⟨Config.minimal, ctrlBaseState, _, positiveDeposit, by decide, rfl, outcome,
      registration_growth _⟩
  constructor
  · have executed : applyPendingDeposit (jointCtx Config.minimal true) existingState positiveDeposit =
        .ok toppedState := by kernel_rfl
    obtain ⟨o, outcome⟩ := DepositConsensusOutcomes.applyOutcome_of_success Config.minimal true
      existingState toppedState positiveDeposit executed
    have classified : classifyApply (jointCtx Config.minimal true) existingState positiveDeposit =
        .ok (.topUp 0) := by kernel_rfl
    obtain rfl : o = .topUp 0 := Except.ok.inj (outcome.1.symm.trans classified)
    exact ⟨Config.minimal, existingState, toppedState, positiveDeposit, 0, by decide, rfl, outcome⟩
  · have executed : applyPendingDeposit (jointCtx Config.minimal true) ctrlBaseState positiveDeposit =
        .ok ctrlBaseState := by kernel_rfl
    obtain ⟨o, outcome⟩ := DepositConsensusOutcomes.applyOutcome_of_success Config.minimal true
      ctrlBaseState ctrlBaseState positiveDeposit executed
    have classified : classifyApply (jointCtx Config.minimal true) ctrlBaseState positiveDeposit =
        .ok .noCredit := by kernel_rfl
    obtain rfl : o = .noCredit := Except.ok.inj (outcome.1.symm.trans classified)
    exact ⟨Config.minimal, ctrlBaseState, ctrlBaseState, positiveDeposit, by decide, rfl, outcome⟩

/-- Real BLS registration and zero-signature rejection share one exact closed input state. -/
theorem blsOnNewValidatorConditional : D9BlsOnNewValidatorConditional := by
  refine ⟨Config.minimal, ctrlBaseState, 0, U64.one, by decide, rfl, by decide, ?_, ?_⟩
  · intro key sig absent valid
    let d : PendingDeposit :=
      { pubkey := key, withdrawal_credentials := 0, amount := U64.one,
        signature := sig, slot := U64.one }
    have executed : applyPendingDeposit (jointCtx Config.minimal true) ctrlBaseState d =
        .ok (registrationState key) := by
      unfold applyPendingDeposit
      dsimp only [d]
      rw [absent, valid]
      exact registration_execution key
    obtain ⟨o, outcome⟩ := DepositConsensusOutcomes.applyOutcome_of_success Config.minimal true
      ctrlBaseState (registrationState key) d executed
    have classified : classifyApply (jointCtx Config.minimal true) ctrlBaseState d = .ok .newValidator := by
      unfold classifyApply
      dsimp only [d]
      rw [absent, valid]
      rfl
    obtain rfl : o = .newValidator := Except.ok.inj (outcome.1.symm.trans classified)
    exact ⟨_, outcome, registration_growth key⟩
  · intro key absent
    let d : PendingDeposit :=
      { pubkey := key, withdrawal_credentials := 0, amount := U64.one,
        signature := zeroBLSSignature, slot := U64.one }
    have signature := zeroSignature_rejected key
    have executed : applyPendingDeposit (jointCtx Config.minimal true) ctrlBaseState d = .ok ctrlBaseState := by
      unfold applyPendingDeposit
      dsimp only [d]
      rw [absent, signature]
      rfl
    obtain ⟨o, outcome⟩ := DepositConsensusOutcomes.applyOutcome_of_success Config.minimal true
      ctrlBaseState ctrlBaseState d executed
    have classified : classifyApply (jointCtx Config.minimal true) ctrlBaseState d = .ok .noCredit := by
      unfold classifyApply
      dsimp only [d]
      rw [absent, signature]
      rfl
    obtain rfl : o = .noCredit := Except.ok.inj (outcome.1.symm.trans classified)
    exact outcome

private def passCtx : Ctx := jointCtx Config.minimal false
private def available : U64 := U64.lit 64000000000
private def finalSlot : Slot := U64.lit 8

private def postponedValidator : Validator :=
  { ctrlValidator with withdrawable_epoch := FAR_FUTURE_EPOCH }
private def postponedState : BeaconState Preset.minimal .electra :=
  { ctrlBaseState with
    validators := ⟨#[postponedValidator], by decide⟩,
    balances := ⟨#[U64.one], by decide⟩,
    pending_deposits := ⟨#[positiveDeposit], by decide⟩ }
private def postponedResult : PassResult Preset.minimal .electra :=
  ⟨postponedState, 1, U64.zero, [(none, positiveDeposit)], [], none⟩

private def bridgeState : BeaconState Preset.minimal .electra :=
  { ctrlBaseState with
    deposit_requests_start_index := U64.one,
    pending_deposits := ⟨#[positiveDeposit], by decide⟩ }
private def bridgeResult : PassResult Preset.minimal .electra :=
  ⟨bridgeState, 0, U64.zero, [], [], some .bridge⟩

private def finalityDeposit : PendingDeposit := { positiveDeposit with slot := U64.lit 9 }
private def finalityState : BeaconState Preset.minimal .electra :=
  { ctrlBaseState with pending_deposits := ⟨#[finalityDeposit], by decide⟩ }
private def finalityResult : PassResult Preset.minimal .electra :=
  ⟨finalityState, 0, U64.zero, [], [], some .finality⟩

private def countDeposit : PendingDeposit := { positiveDeposit with amount := U64.zero }
private def countQueue : TQueue := List.replicate 17 (none, countDeposit)
private def countState : BeaconState Preset.minimal .electra :=
  { existingState with
    pending_deposits := ⟨(countQueue.map Prod.snd).toArray, by decide⟩ }
private def countApplied : List (Applied Preset.minimal .electra) :=
  List.replicate 16 ⟨none, countDeposit, countState, .withdrawn⟩
private def countResult : PassResult Preset.minimal .electra :=
  ⟨countState, 16, U64.zero, [], countApplied, some .count⟩
private def countPost : BeaconState Preset.minimal .electra :=
  { countState with pending_deposits := ⟨#[countDeposit], by decide⟩ }

private def churnDeposit : PendingDeposit :=
  { positiveDeposit with amount := U64.lit 64000000001 }
private def churnState : BeaconState Preset.minimal .electra :=
  { ctrlBaseState with pending_deposits := ⟨#[churnDeposit], by decide⟩ }
private def churnResult : PassResult Preset.minimal .electra :=
  ⟨churnState, 0, U64.zero, [], [], some .churn⟩
private def churnPost : BeaconState Preset.minimal .electra :=
  { churnState with deposit_balance_to_consume := available }

/-- An actual exiting deposit is postponed; actual derived passes realize every original stop. -/
theorem passWitnesses : D9PassWitnesses := by
  constructor
  · refine ⟨passCtx, postponedState, postponedState,
      [(none, positiveDeposit)], [(none, positiveDeposit)], [],
      U64.one, available, finalSlot, U64.zero, postponedResult, (none, positiveDeposit),
      ?_, ?_, ?_, ?_, List.mem_cons_self, 0, postponedValidator, ?_, ?_, by decide, by decide⟩
    all_goals kernel_rfl
  · intro stop
    cases stop with
    | bridge =>
      refine ⟨passCtx, bridgeState, bridgeState, [(none, positiveDeposit)],
        [(none, positiveDeposit)], [], U64.one, available, finalSlot, U64.one,
        bridgeResult, ?_, ?_, ?_, ?_, rfl⟩
      all_goals kernel_rfl
    | finality =>
      refine ⟨passCtx, finalityState, finalityState, [(none, finalityDeposit)],
        [(none, finalityDeposit)], [], U64.one, available, finalSlot, U64.zero,
        finalityResult, ?_, ?_, ?_, ?_, rfl⟩
      all_goals kernel_rfl
    | count =>
      refine ⟨passCtx, countState, countPost, countQueue, [(none, countDeposit)],
        countApplied, U64.one, available, finalSlot, U64.zero, countResult,
        ?_, ?_, ?_, ?_, rfl⟩
      all_goals kernel_rfl
    | churn =>
      refine ⟨passCtx, churnState, churnPost, [(none, churnDeposit)],
        [(none, churnDeposit)], [], U64.one, available, finalSlot, U64.zero,
        churnResult, ?_, ?_, ?_, ?_, rfl⟩
      all_goals kernel_rfl

private def replayState : BeaconState Preset.minimal .electra :=
  { existingState with pending_deposits := ⟨#[positiveDeposit], by decide⟩ }
private def replayApplied : Applied Preset.minimal .electra :=
  ⟨some 0, positiveDeposit, replayState, .withdrawn⟩

/-- The real positive tagged occurrence balances; retaining that applied occurrence breaks it. -/
theorem replayControl : D9ReplayControl := by
  refine ⟨jointCtx Config.minimal true, replayState, [(some 0, positiveDeposit)],
    toppedState, toppedState, [], [(some 0, positiveDeposit)], [replayApplied], [replayApplied],
    ?_, by decide, ?_, ?_, ?_, by decide +kernel, by decide +kernel⟩
  · kernel_rfl
  · exact ⟨replayApplied, List.mem_cons_self, rfl, by decide⟩
  · kernel_rfl
  · kernel_rfl

end Blanc.Composition.DepositLedgerControls
