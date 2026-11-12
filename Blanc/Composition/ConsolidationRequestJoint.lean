import Blanc.Composition.Corpus.Freeze.ConsolidationJoint
import Blanc.JointFeed
import Blanc.Lift.ConsolidationRequest.RequestCodec
import JauneConsensus.Facts.ConsolidationRequest

namespace Blanc.Composition.ConsolidationRequestJoint

open Jaune JauneConsensus Blanc ExecutionTrace
open Blanc.Corpus.Freeze.ConsolidationJoint
open Blanc.Composition.ConsolidationRequestPublic

/-- The frozen reasons retain the canonical classifier's thirteen constructors. -/
def canonicalReason : IgnoreReason → Facts.ConsolidationIgnoreReason
  | .sourceIsTarget => .sourceIsTarget
  | .queueFull => .queueFull
  | .churnTooLow => .churnTooLow
  | .unknownSource => .unknownSource
  | .unknownTarget => .unknownTarget
  | .badSourceCredentialOrAddress => .badSourceCredentialOrAddress
  | .targetNotCompounding => .targetNotCompounding
  | .sourceNotActive => .sourceNotActive
  | .targetNotActive => .targetNotActive
  | .sourceExiting => .sourceExiting
  | .targetExiting => .targetExiting
  | .sourceTooEarly => .sourceTooEarly
  | .sourcePendingWithdrawal => .sourcePendingWithdrawal

/-- Structural conversion only; the canonical function remains the one classifier. -/
def canonicalOutcome : Outcome → Facts.ConsolidationOutcome
  | .ignored r => .ignored (canonicalReason r)
  | .switchToCompounding i => .switchToCompounding i
  | .pendingConsolidation s t => .pendingConsolidation s t

private theorem canonical_classify {P : Preset} {f : CFork}
    (cfg : Config) (st : BeaconState P f) (cr : ConsolidationRequest) :
    canonicalOutcome <$> classify cfg st cr = Facts.classifyConsolidationRequest cfg st cr := by
  unfold classify Facts.classifyConsolidationRequest
  cases h0 : isValidSwitchToCompoundingRequest st cr with
  | error e => rfl
  | ok switch =>
    simp only [Except.bind_ok]
    cases switch with
    | true =>
      cases hi : validatorIndexOf st cr.source_pubkey with
      | error e => rfl
      | ok opt => cases opt <;> rfl
    | false =>
      cases hb1 : (cr.source_pubkey == cr.target_pubkey) with
      | true => rfl
      | false =>
        cases h_q : st.pendingConsolidations with
        | error e => rfl
        | ok q =>
          simp only [Except.bind_ok]
          cases hb2 : (q.length == P.PENDING_CONSOLIDATIONS_LIMIT) with
          | true => rfl
          | false =>
            cases h_churn : getConsolidationChurnLimit cfg st with
            | error e => rfl
            | ok churn =>
              simp only [Except.bind_ok]
              by_cases hc : churn.toNat ≤ P.MIN_ACTIVATION_BALANCE
              · simp only [hc, ite_true]
                rfl
              · simp only [hc, ite_false]
                cases h_si : validatorIndexOf st cr.source_pubkey with
                | error e => rfl
                | ok opt =>
                  simp only [Except.bind_ok]
                  cases opt with
                  | none => rfl
                  | some si =>
                    cases h_ti : validatorIndexOf st cr.target_pubkey with
                    | error e => rfl
                    | ok opt =>
                      simp only [Except.bind_ok]
                      cases opt with
                      | none => rfl
                      | some ti =>
                        cases h_source : st.validators.get si.toNat "process_consolidation_request" with
                        | error e => rfl
                        | ok source =>
                          simp only [Except.bind_ok]
                          cases h_target : st.validators.get ti.toNat "process_consolidation_request" with
                          | error e => rfl
                          | ok target =>
                            simp only [Except.bind_ok]
                            cases hb3 : (!(hasExecutionWithdrawalCredential source && source.withdrawal_credentials.toBytes.drop 12 == cr.source_address.toBytes)) with
                            | true => rfl
                            | false =>
                              cases hb4 : (!hasCompoundingWithdrawalCredential target) with
                              | true => rfl
                              | false =>
                                cases h_current : getCurrentEpoch st with
                                | error e => rfl
                                | ok current =>
                                  simp only [Except.bind_ok]
                                  cases hb5 : (!isActiveValidator source current) with
                                  | true => rfl
                                  | false =>
                                    cases hb6 : (!isActiveValidator target current) with
                                    | true => rfl
                                    | false =>
                                      cases hb7 : (source.exit_epoch != FAR_FUTURE_EPOCH) with
                                      | true => rfl
                                      | false =>
                                        cases hb8 : (target.exit_epoch != FAR_FUTURE_EPOCH) with
                                        | true => rfl
                                        | false =>
                                          cases h_period : c64 cfg.SHARD_COMMITTEE_PERIOD with
                                          | error e => rfl
                                          | ok period =>
                                            simp only [Except.bind_ok]
                                            cases h_actSum : U64.add? source.activation_epoch period "process_consolidation_request" with
                                            | error e => rfl
                                            | ok actSum =>
                                              simp only [Except.bind_ok]
                                              by_cases hc2 : current < actSum
                                              · simp only [hc2, ite_true]
                                                rfl
                                              · simp only [hc2, ite_false]
                                                cases h_pending : getPendingBalanceToWithdraw st si with
                                                | error e => rfl
                                                | ok pending =>
                                                  simp only [Except.bind_ok]
                                                  by_cases hc3 : U64.zero < pending
                                                  · simp only [hc3, ite_true]
                                                    rfl
                                                  · simp only [hc3, ite_false]
                                                    rfl

private theorem canonical_apply {P : Preset} {f : CFork}
    (cfg : Config) (st : BeaconState P f) (cr : ConsolidationRequest) (o : Outcome) :
    Facts.applyConsolidationOutcome cfg st cr (canonicalOutcome o) = applyOutcome cfg st cr o := by
  cases o <;> rfl

/-- The original frozen classifier/apply pair is the actual consensus function. -/
theorem classifySound : ClassifySound := by
  intro P f cfg st cr
  rw [Facts.processConsolidationRequest_eq, ← canonical_classify, bind_map_left]
  apply bind_congr
  intro o
  exact canonical_apply cfg st cr o

private theorem canonical_classified {P : Preset} {f : CFork}
    {cfg : Config} {st : BeaconState P f} {cr : ConsolidationRequest} {o : Outcome}
    (classified : classify cfg st cr = .ok o) :
    Facts.classifyConsolidationRequest cfg st cr = .ok (canonicalOutcome o) := by
  rw [← canonical_classify, classified]
  rfl

private theorem outcome_means {P : Preset} {f : CFork}
    {cfg : Config} {st st' : BeaconState P f} {cr : ConsolidationRequest} {o : Outcome}
    (classified : classify cfg st cr = .ok o)
    (applied : applyOutcome cfg st cr o = .ok st') : OutcomeMeans st st' cr o := by
  have canonical := canonical_classified classified
  cases o with
  | ignored r =>
    change Except.ok st = Except.ok st' at applied
    exact (Except.ok.inj applied).symm
  | switchToCompounding i =>
    obtain ⟨valid, index⟩ := (Facts.classifyConsolidation_spec canonical).1 i rfl
    exact ⟨valid, index, applied⟩
  | pendingConsolidation s t =>
    have checks := (Facts.classifyConsolidation_spec canonical).2 s t rfl
    have actual : Facts.applyConsolidationOutcome cfg st cr (.pendingConsolidation s t) = .ok st' :=
      applied
    have effects := Facts.applyConsolidation_pending_spec actual
    have distinct := checks.source_ne_target
    obtain ⟨_, _, _, _, si, ti, vs, vt, hvs, hvt, _, _, compounding,
      current, epoch, _, active, _, exiting, _⟩ := checks
    exact ⟨si, ti, distinct, effects.2.2.2.1,
      vt, current, hvt, epoch, compounding, active, exiting⟩

private theorem classified_authorized {P : Preset} {f : CFork}
    {cfg : Config} {st : BeaconState P f} {cr : ConsolidationRequest} {o : Outcome} {V : ValidatorIndex}
    (classified : classify cfg st cr = .ok o)
    (acts : o = .switchToCompounding V ∨ ∃ T, o = .pendingConsolidation V T) :
    validatorIndexOf st cr.source_pubkey = .ok (some V) ∧
      ∃ validator, st.validators.toArray[V.toNat]? = some validator ∧
        hasExecutionWithdrawalCredential validator = true ∧
        validator.withdrawal_credentials.toBytes.drop 12 = cr.source_address.toBytes := by
  have canonical := canonical_classified classified
  have noignore : ∀ r, canonicalOutcome o ≠ .ignored r := by
    rcases acts with rfl | ⟨T, rfl⟩ <;> intro r impossible <;> cases impossible
  have index : validatorIndexOf st cr.source_pubkey = .ok (some V) := by
    rcases acts with rfl | ⟨T, rfl⟩
    · exact (Facts.classifyConsolidation_spec canonical).1 V rfl |>.2
    · exact (Facts.classifyConsolidation_spec canonical).2 V T rfl |>.2.2.2.2.1
  obtain ⟨i, validator, hi, hv, credential, address, _⟩ :=
    Facts.classifyConsolidation_authorized canonical noignore
  have same : i = V := Option.some.inj (Except.ok.inj (hi.symm.trans index))
  subst same
  exact ⟨index, validator, hv, credential, address⟩

private theorem joint_trace_of_step
    {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {anchor final : JointState P} (run : JointRun cfg ccfg bls anchor final)
    {j : Nat} {D : JointRunStep (P := P) cfg ccfg bls}
    (step : run.steps[j]? = some D) {requests : ExecutionRequests P}
    (read : Gated.read D.block.2.message.body.execution_requests
      "NewPayloadRequest: execution_requests" = .ok requests) :
    ∃ tr, jointConsolidationTrace ccfg bls D.pre D.block = .ok tr ∧
      tr.length = requests.consolidations.toArray.toList.length + 1 := by
  have actual := run.steps_jointStep step
  have fork : D.block.1.atLeast .electra = true := by
    rcases (jointStep_engine actual).1 with h | h <;> rw [h] <;> rfl
  have reqeq : Gated.get fork D.block.2.message.body.execution_requests = requests :=
    Except.ok.inj ((Facts.gated_read_get fork _ _).symm.trans read)
  obtain ⟨st, input, post, block⟩ := jointStep_processBlock actual
  change processBlockWith (jointCtx ccfg bls) st D.block.2.message = .ok post at block
  rw [Facts.processBlockWith_split] at block
  obtain ⟨before, beforeEq, rest⟩ := Except.bind_eq_ok block
  obtain ⟨afterOps, opsEq, sync⟩ := Except.bind_eq_ok rest
  rw [Facts.processOperations_split _ _ _ fork] at opsEq
  obtain ⟨pre, preEq, rest⟩ := Except.bind_eq_ok opsEq
  obtain ⟨withdrawn, withdrawalEq, postEq⟩ := Except.bind_eq_ok rest
  rw [reqeq] at withdrawalEq
  rw [Facts.postRequests_eq_foldConsolidationRequests _ _ _ fork, reqeq] at postEq
  obtain ⟨tr, hne, trace, last⟩ := Facts.stepTrace_of_foldlM
    (fun s cr => processConsolidationRequest ccfg s cr) (consolidationTrace ccfg)
    (fun _ => rfl) (fun _ _ _ => rfl) _ _ _ postEq
  refine ⟨tr, ?_, (Facts.stepTrace_spec
    (fun s cr => processConsolidationRequest ccfg s cr) (consolidationTrace ccfg)
    (fun _ => rfl) (fun _ _ _ => rfl) _ _ _ trace).1⟩
  simp only [jointConsolidationTrace, input, Except.bind_ok, beforeEq,
    preEq, read, withdrawalEq, trace]

private theorem joint_trace_step {P : Preset} {ccfg : Config} {bls : Bool}
    {s : JointState P} {b : AnySignedBlock P} {requests : ExecutionRequests P}
    (read : Gated.read b.2.message.body.execution_requests
      "NewPayloadRequest: execution_requests" = .ok requests)
    {tr : List (BeaconState P b.1)}
    (trace : jointConsolidationTrace ccfg bls s b = .ok tr)
    {k : Nat} {cr : ConsolidationRequest}
    (request : requests.consolidations.toArray[k]? = some cr)
    {m : BeaconState P b.1} (mid : tr[k]? = some m) :
    ∃ m', tr[k + 1]? = some m' ∧ processConsolidationRequest ccfg m cr = .ok m' := by
  unfold jointConsolidationTrace at trace
  obtain ⟨st, _, trace⟩ := Except.bind_eq_ok trace
  obtain ⟨before, _, trace⟩ := Except.bind_eq_ok trace
  obtain ⟨pre, _, trace⟩ := Except.bind_eq_ok trace
  rw [read] at trace
  simp only [Except.bind_ok] at trace
  obtain ⟨withdrawn, _, trace⟩ := Except.bind_eq_ok trace
  have spec := Facts.stepTrace_spec
    (fun s cr => processConsolidationRequest ccfg s cr) (consolidationTrace ccfg)
    (fun _ => rfl) (fun _ _ _ => rfl) _ _ _ trace
  have next : k + 1 < tr.length := by
    have bound := (Array.getElem?_eq_some_iff.mp request).1
    rw [spec.1, Array.length_toList]
    omega
  refine ⟨tr[k + 1], List.getElem?_eq_getElem next, ?_⟩
  exact spec.2.2 k cr m _ (by simpa only [Array.getElem?_toList] using request)
    mid (List.getElem?_eq_getElem next)

end Blanc.Composition.ConsolidationRequestJoint
