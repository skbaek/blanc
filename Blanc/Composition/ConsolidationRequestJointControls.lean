import Blanc.Composition.Corpus.Freeze.ConsolidationJoint
import JauneConsensus.Facts.ConsolidationRequest
import JauneConsensus.Facts.AnchorInvControls
import Blanc.ConcreteRun
import Blanc.Composition.ConsolidationRequestJoint
import Blanc.ConsensusSszConsolidation

namespace Blanc.Composition.ConsolidationRequestJointControls

open Jaune JauneConsensus Blanc
open Blanc.Corpus.Freeze.ConsolidationJoint
open Blanc.Composition.ConsolidationRequestJoint

private def sourceKey : BLSPubkey := Facts.ctrlValidator.pubkey
private def targetKey : BLSPubkey := ⟨Array.replicate 48 1, Array.size_replicate⟩
private def unknownKey : BLSPubkey := ⟨Array.replicate 48 2, Array.size_replicate⟩

private def source : Validator :=
  { Facts.ctrlValidator with
    pubkey := sourceKey,
    withdrawal_credentials := (1 : B256) <<< 248,
    effective_balance := U64.lit 8192000000000, exit_epoch := FAR_FUTURE_EPOCH }
private def target : Validator :=
  { source with pubkey := targetKey, withdrawal_credentials := (2 : B256) <<< 248 }

/-- Arbitrary closed processing state; no claim of a valid joint-chain witness. -/
private def ordinary : BeaconState Preset.minimal .electra :=
  { Facts.ctrlBaseState with
    slot := U64.lit 512,
    validators := ⟨#[source, target], by decide⟩,
    balances := ⟨#[U64.lit 32000000000, U64.lit 32000000000], by decide⟩ }
private def request : ConsolidationRequest :=
  { source_address := 0, source_pubkey := sourceKey, target_pubkey := targetKey }
private def fullQueue : SszList PendingConsolidation Preset.minimal.PENDING_CONSOLIDATIONS_LIMIT :=
  ⟨Array.replicate 64 { source_index := U64.zero, target_index := U64.one }, by decide⟩

/-- Each enumerated reason has its own closed input, preserving the preceding guards. -/
private def ignoredInput : IgnoreReason → BeaconState Preset.minimal .electra × ConsolidationRequest
  | .sourceIsTarget => (ordinary, { request with source_address := 1, target_pubkey := sourceKey })
  | .queueFull => ({ ordinary with pending_consolidations := fullQueue }, request)
  | .churnTooLow => (Facts.ctrlBaseState, request)
  | .unknownSource => (ordinary, { request with source_pubkey := unknownKey })
  | .unknownTarget => (ordinary, { request with target_pubkey := unknownKey })
  | .badSourceCredentialOrAddress => (ordinary, { request with source_address := 1 })
  | .targetNotCompounding =>
      ({ ordinary with validators := ⟨#[source, { target with withdrawal_credentials := (1 : B256) <<< 248 }], by decide⟩ }, request)
  | .sourceNotActive =>
      ({ ordinary with validators := ⟨#[{ source with activation_epoch := U64.lit 65 }, target], by decide⟩ }, request)
  | .targetNotActive =>
      ({ ordinary with validators := ⟨#[source, { target with activation_epoch := U64.lit 65 }], by decide⟩ }, request)
  | .sourceExiting =>
      ({ ordinary with validators := ⟨#[{ source with exit_epoch := U64.lit 65 }, target], by decide⟩ }, request)
  | .targetExiting =>
      ({ ordinary with validators := ⟨#[source, { target with exit_epoch := U64.lit 65 }], by decide⟩ }, request)
  | .sourceTooEarly =>
      ({ ordinary with validators := ⟨#[{ source with activation_epoch := U64.one }, target], by decide⟩ }, request)
  | .sourcePendingWithdrawal =>
      ({ ordinary with pending_partial_withdrawals :=
        ⟨#[{ validator_index := U64.zero, amount := U64.one, withdrawable_epoch := U64.zero }], by decide⟩ }, request)

private theorem ignored_class (reason : IgnoreReason) :
    classify Config.minimal (ignoredInput reason).1 (ignoredInput reason).2 = .ok (.ignored reason) := by
  cases reason <;> kernel_rfl

private theorem ignored_process (reason : IgnoreReason) :
    processConsolidationRequest Config.minimal (ignoredInput reason).1 (ignoredInput reason).2 =
      .ok (ignoredInput reason).1 := by
  rw [classifySound, ignored_class]
  rfl

private def switchSource : Validator := { source with effective_balance := U64.lit 32000000000 }

private def switchState : BeaconState Preset.minimal .electra :=
  { ordinary with
    validators := ⟨#[switchSource], by decide⟩,
    balances := ⟨#[U64.lit 32000000000], by decide⟩ }
private def switchRequest : ConsolidationRequest := { request with target_pubkey := sourceKey }

private theorem switch_class :
    classify Config.minimal switchState switchRequest = .ok (.switchToCompounding U64.zero) := by
  kernel_rfl

private theorem pending_class :
    classify Config.minimal ordinary request = .ok (.pendingConsolidation U64.zero U64.one) := by
  kernel_rfl

private def pendingPost : BeaconState Preset.minimal .electra :=
  { ordinary with
    consolidation_balance_to_consume := U64.lit 256000000000,
    earliest_consolidation_epoch := U64.lit 90,
    validators := ⟨#[{ source with exit_epoch := U64.lit 90, withdrawable_epoch := U64.lit 346 }, target], by decide⟩,
    pending_consolidations := ⟨#[{ source_index := U64.zero, target_index := U64.one }], by decide⟩ }

private def switchPost : BeaconState Preset.minimal .electra :=
  { switchState with validators := ⟨#[{ source with
    effective_balance := U64.lit 32000000000,
    withdrawal_credentials := (2 : B256) <<< 248 }], by decide⟩ }

private theorem pending_process :
    processConsolidationRequest Config.minimal ordinary request = .ok pendingPost := by
  kernel_rfl
private theorem pending_mutant :
    processConsolidationRequestNoSourceCheck Config.minimal ordinary
      { request with source_address := 1 } = .ok pendingPost := by
  kernel_rfl
private theorem switch_process :
    processConsolidationRequest Config.minimal switchState switchRequest = .ok switchPost := by
  kernel_rfl
private theorem switch_mutant :
    processConsolidationRequestNoSourceCheck Config.minimal switchState
      { switchRequest with source_address := 1 } = .ok switchPost := by
  kernel_rfl

private theorem pending_changed : pendingPost ≠ ordinary := by
  intro same
  have queue := congrArg pendingList same
  change ([{ source_index := U64.zero, target_index := U64.one }] : List PendingConsolidation) = [] at queue
  cases queue

private theorem switch_changed : switchPost ≠ switchState := by
  intro same
  have credential := congrArg
    (fun st : BeaconState Preset.minimal .electra =>
      (st.validators.toArray[0]?).map (·.withdrawal_credentials)) same
  change some ((2 : B256) <<< 248) = some ((1 : B256) <<< 248) at credential
  exact (by decide : (some ((2 : B256) <<< 248) : Option B256) ≠ some ((1 : B256) <<< 248)) credential

/-- Both source-check deletions bite on the exact same ordinary and equal-key inputs. -/
theorem c_s9_auth_control : C_S9_auth_control := by
  constructor
  · refine ⟨ordinary, { request with source_address := 1 }, U64.zero, U64.one, source,
      by decide, ?_, ?_, rfl, ?_, by decide,
      ignored_class .badSourceCredentialOrAddress, ignored_process .badSourceCredentialOrAddress,
      pendingPost, pending_mutant, pending_changed, rfl⟩
    · kernel_rfl
    · kernel_rfl
    · kernel_rfl
  · refine ⟨switchState, { switchRequest with source_address := 1 }, U64.zero, switchSource,
      rfl, ?_, rfl, ?_, by decide, ?_, ?_, switchPost, switch_mutant, switch_changed⟩
    · kernel_rfl
    · kernel_rfl
    · kernel_rfl
    · rw [classifySound]
      have classified : classify Config.minimal switchState
          { switchRequest with source_address := 1 } = .ok (.ignored .sourceIsTarget) := by
        kernel_rfl
      rw [classified]
      rfl

private def fullSwitch : BeaconState Preset.minimal .electra :=
  { switchState with pending_consolidations := fullQueue }
private def fullEmpty : BeaconState Preset.minimal .electra :=
  { Facts.ctrlBaseState with pending_consolidations := fullQueue }
private def unknownBoth : BeaconState Preset.minimal .electra :=
  { ordinary with validators := ⟨#[target], by decide⟩ }
private def badTargetValidator : Validator := { target with withdrawal_credentials := (1 : B256) <<< 248 }
private def badTargetState : BeaconState Preset.minimal .electra :=
  { ordinary with validators := ⟨#[source, badTargetValidator], by decide⟩ }

/-- All thirteen ignores, both actual actions, and all five literal priority comparisons. -/
theorem c_s9_fate_witnesses : C_S9_fate_witnesses := by
  refine ⟨?_, ⟨switchState, switchPost, switchRequest, U64.zero,
      switch_class, switch_process, switch_changed⟩,
    ⟨ordinary, pendingPost, request, U64.zero, U64.one,
      pending_class, pending_process, rfl⟩, ?_, ?_, ?_, ?_, ?_⟩
  · intro reason
    exact ⟨(ignoredInput reason).1, (ignoredInput reason).2, ignored_class reason, ignored_process reason⟩
  · refine ⟨fullSwitch, switchRequest, fullQueue, U64.zero, U64.zero,
      rfl, rfl, ?_, by decide, ?_⟩ <;> kernel_rfl
  · refine ⟨fullEmpty, { switchRequest with source_address := 1 }, fullQueue, U64.zero,
      rfl, ?_, rfl, rfl, ?_, by decide, ?_⟩ <;> kernel_rfl
  · refine ⟨fullEmpty, request, fullQueue, U64.zero,
      by decide, rfl, rfl, ?_, by decide, ?_, ?_⟩ <;> kernel_rfl
  · refine ⟨unknownBoth, { request with target_pubkey := unknownKey },
      by decide, ?_, ?_, ?_⟩ <;> kernel_rfl
  · refine ⟨badTargetState, { request with source_address := 1 }, U64.zero, U64.one,
      source, badTargetValidator, by decide, ?_, ?_, rfl, rfl, by decide, ?_, ?_⟩ <;> kernel_rfl

private theorem aligned (a b : ConsolidationRequest) :
    PositionalFate [] [[Ssz.serialize a], [Ssz.serialize b]] [[a], [b]] []
      [Ssz.serialize a, Ssz.serialize b] := by
  intro n hn
  change n < 2 at hn
  have cases : n = 0 ∨ n = 1 := by omega
  rcases cases with rfl | rfl
  · exact .inr (.inl ⟨by decide, (by change 0 < 2; decide), 0, 0, [a], a, rfl, rfl, rfl, rfl⟩)
  · exact .inr (.inl ⟨by decide, (by change 1 < 2; decide), 1, 0, [b], b, rfl, rfl, rfl, rfl⟩)

private theorem one_late (a b : ConsolidationRequest) :
    ¬ PositionalFate [] [[Ssz.serialize a], [Ssz.serialize b]] [[], [a]] []
      [Ssz.serialize a, Ssz.serialize b] := by
  intro fate
  have atOne := fate 1 (by change 1 < 2; decide)
  rcases atOne with ⟨before, _⟩ | middle | ⟨after, _⟩
  · change 1 < 0 at before
    omega
  · obtain ⟨_, _, j, k, crs, cr, step, request, position, _⟩ := middle
    cases j with
    | zero =>
      change some [] = some crs at step
      cases Option.some.inj step
      simp only [List.getElem?_nil, reduceCtorEq] at request
    | succ j =>
      cases j with
      | zero =>
        change some [a] = some crs at step
        cases Option.some.inj step
        simp only [List.take_succ_cons, List.take_zero, List.flatten_cons, List.flatten_nil,
          List.append_nil, List.length_nil, Nat.zero_add, Nat.sub_zero] at position
        change k = 1 at position
        subst k
        cases request
      | succ j =>
        simp only [List.getElem?_cons_succ, List.getElem?_nil, reduceCtorEq] at step
  · change 2 ≤ 1 at after
    omega

private theorem swapped (a b : ConsolidationRequest) (different : a ≠ b) :
    ¬ PositionalFate [] [[Ssz.serialize a], [Ssz.serialize b]] [[b], [a]] []
      [Ssz.serialize a, Ssz.serialize b] := by
  intro fate
  have atZero := fate 0 (by change 0 < 2; decide)
  rcases atZero with ⟨before, _⟩ | middle | ⟨after, _⟩
  · change 0 < 0 at before
    omega
  · obtain ⟨_, _, j, k, crs, cr, step, request, position, serialized⟩ := middle
    cases j with
    | zero =>
      change some [b] = some crs at step
      cases Option.some.inj step
      simp only [List.take_zero, List.flatten_nil, List.length_nil, Nat.zero_add, Nat.sub_zero] at position
      change k = 0 at position
      subst k
      change some b = some cr at request
      cases Option.some.inj request
      exact different (Blanc.ConsensusSsz.serialize_consolidationRequest_injective
        (Option.some.inj serialized))
    | succ j =>
      cases j with
      | zero =>
        change some [a] = some crs at step
        cases Option.some.inj step
        simp only [List.take_succ_cons, List.take_zero, List.flatten_cons, List.flatten_nil,
          List.append_nil, List.length_nil, List.length_cons, Nat.zero_add, Nat.sub_zero] at position
        change 1 + k = 0 at position
        omega
      | succ j =>
        simp only [List.getElem?_cons_succ, List.getElem?_nil, reduceCtorEq] at step
  · change 2 ≤ 0 at after
    omega

/-- Actual list-mismatch refusal plus the literal abstract aligned/late/swapped seam controls. -/
theorem c_s9_seam_control : C_S9_seam_control := by
  constructor
  · intro P cfg ccfg bls s s' b req fk st bout converted fork body mismatch successful
    obtain ⟨_, actualReq, actualConverted, engine⟩ := jointStep_engine successful
    have same : actualReq = req := Except.ok.inj (actualConverted.symm.trans converted)
    subst same
    obtain ⟨error, refused⟩ := engineVerdict_rejects_of_requests_ne fork body mismatch
    rw [engine] at refused
    cases refused
  · refine ⟨request, { request with source_address := 1 }, by decide, aligned _ _, one_late _ _, ?_⟩
    exact swapped _ _ (by decide)

end Blanc.Composition.ConsolidationRequestJointControls
