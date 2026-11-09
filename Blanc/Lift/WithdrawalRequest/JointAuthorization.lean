import Blanc.Lift.WithdrawalRequest.JointHistory
import Blanc.Lift.WithdrawalRequest.RequestCodec
import Blanc.Lift.WithdrawalRequest.HeadlineHistory
import JauneConsensus.Facts.Operations
import JauneConsensus.Facts.WithdrawalRequest

/-!
# EIP-7002 authorization across the layers (P1)

Along a valid joint chain, every application of the 7002 path that initiates a validator's
exit or appends a pending partial withdrawal for it consumes a request that is, position for
position, a committed paid submission of the joint execution history, and whose public key
resolves (first match) to that validator, whose execution withdrawal credential carries the
request's source address in bytes 12..32 in the mid-block state.

* The run's type-1 feed (`JointRun.withdrawalFeed`) is the concatenation, over the run's steps
  in order, of each beacon block's `execution_requests.withdrawals`. Its serialization is
  exactly what the joint history emits after the pre-anchor history
  (`JointRun.emissions_toExec`), so the feed's position `i` is submission `E₀ + i`.
* The mid-block state of step `D`'s request `k` is element `k` of `jointWithdrawalTrace`: the
  states of the withdrawal-requests fold of the `process_block` the joint step runs, computed
  with the same calls as the step (`jointBlockInput`, `Facts.blockBeforeOps`,
  `Facts.preRequests`, `Facts.withdrawalRequestTrace`). Every step has this trace
  (`ValidJoint.jointWithdrawalTrace_ok`).
-/

namespace Blanc.Lift.WithdrawalRequest

open Jaune JauneConsensus ExecutionTrace

/-! ## The mid-block states of a joint step -/

/-- The states of a joint step's withdrawal-requests fold: the state before each of the beacon
block's withdrawal requests, then the state after the last. Computed with the same calls as
the `process_block` the joint step runs. -/
def jointWithdrawalTrace {P : Preset} (ccfg : Config) (bls : Bool) (s : JointState P)
    (b : AnySignedBlock P) : M (List (BeaconState P b.1)) := do
  let st ← jointBlockInput ccfg bls s b
  let st ← Facts.blockBeforeOps (jointCtx ccfg bls) st b.2.message
  let st ← Facts.preRequests (jointCtx ccfg bls) st b.2.message.body
  let requests ← Gated.read b.2.message.body.execution_requests
    "NewPayloadRequest: execution_requests"
  Facts.withdrawalRequestTrace ccfg st requests.withdrawals.toArray.toList

/-- A successful withdrawal-requests fold has a trace. -/
theorem withdrawalRequestTrace_ok_of_fold {P : Preset} {f : CFork} {cfg : Config} :
    ∀ {reqs : List WithdrawalRequest} {st st' : BeaconState P f},
      Facts.foldWithdrawalRequests cfg st reqs = .ok st' →
      ∃ tr, Facts.withdrawalRequestTrace cfg st reqs = .ok tr
  | [], st, _, _ => ⟨[st], rfl⟩
  | wr :: rest, st, st', h => by
    unfold Facts.foldWithdrawalRequests at h
    rw [List.foldlM_cons] at h
    obtain ⟨mid, hmid, h⟩ := Except.bind_eq_ok h
    obtain ⟨tr, htr⟩ := withdrawalRequestTrace_ok_of_fold (reqs := rest) h
    exact ⟨st :: tr, by
      simp only [Facts.withdrawalRequestTrace, hmid, htr, Except.bind_ok]
      rfl⟩

/-- A successful joint step has a withdrawal-requests trace with one state per request plus
the final state. -/
theorem jointWithdrawalTrace_ok {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {s s' : JointState P} {b : AnySignedBlock P} (h : jointStep cfg ccfg bls s b = .ok s')
    {requests : ExecutionRequests P}
    (hread : Gated.read b.2.message.body.execution_requests
      "NewPayloadRequest: execution_requests" = .ok requests) :
    ∃ tr, jointWithdrawalTrace ccfg bls s b = .ok tr ∧
      tr.length = requests.withdrawals.toArray.toList.length + 1 := by
  obtain ⟨hcf, -⟩ := jointStep_engine h
  have hel : b.1.atLeast .electra = true := by
    rcases hcf with hcf | hcf <;> rw [hcf] <;> rfl
  obtain ⟨st, hst, post, hpost⟩ := jointStep_processBlock h
  unfold processBlock at hpost
  rw [Facts.processBlockWith_split] at hpost
  obtain ⟨st0, h0, hpost⟩ := Except.bind_eq_ok hpost
  obtain ⟨st1, h1, -⟩ := Except.bind_eq_ok hpost
  rw [Facts.processOperations_split _ _ _ hel] at h1
  obtain ⟨st2, h2, h1⟩ := Except.bind_eq_ok h1
  obtain ⟨st3, h3, -⟩ := Except.bind_eq_ok h1
  have hget : Gated.get hel b.2.message.body.execution_requests = requests := by
    rw [Facts.gated_read_get hel] at hread
    exact Except.ok.inj hread
  rw [hget] at h3
  obtain ⟨tr, htr⟩ := withdrawalRequestTrace_ok_of_fold h3
  refine ⟨tr, ?_, (Facts.withdrawalRequestTrace_spec ccfg _ _ tr htr).1⟩
  simp only [jointWithdrawalTrace, hst, h0, h2, hread, htr, Except.bind_ok]

/-! ## The run's type-1 feed -/

/-- The withdrawal requests of a joint run step's beacon block (empty if the block has no
execution requests, which a successful step rules out). -/
def stepWithdrawalRequests {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    (D : JointRunStep (P := P) cfg ccfg bls) : List WithdrawalRequest :=
  match Gated.read D.block.2.message.body.execution_requests
      "NewPayloadRequest: execution_requests" with
  | .ok requests => requests.withdrawals.toArray.toList
  | .error _ => []

/-- The run's type-1 feed: the beacon blocks' withdrawal requests, over the run's steps in
order. -/
noncomputable def withdrawalFeed {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {s₀ s : JointState P} (run : JointRun cfg ccfg bls s₀ s) : List WithdrawalRequest :=
  run.steps.flatMap stepWithdrawalRequests

/-- The feed position of request `k` of step `j`: the requests of the earlier steps, plus `k`. -/
noncomputable def feedPosition {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {s₀ s : JointState P} (run : JointRun cfg ccfg bls s₀ s) (j k : Nat) : Nat :=
  ((run.steps.take j).flatMap stepWithdrawalRequests).length + k

/-- A step's execution block emits, as type-1 records, its beacon block's withdrawal requests
serialized. -/
theorem blockWithdrawals_step {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    (D : JointRunStep (P := P) cfg ccfg bls) :
    blockWithdrawals D.stepTrace.trace = (stepWithdrawalRequests D).map Ssz.serialize := by
  obtain ⟨requests, hread, records⟩ := JointStepTrace.withdrawalRequestRecords_eq D.stepTrace
  rw [blockWithdrawals, records, stepWithdrawalRequests, hread]

/-- The joint history emits the pre-anchor history's records, then the run's feed serialized. -/
theorem emissions_toExec {P : Preset} {cfg : ChainConfig} {ccfg : Config}
    {bls : Bool} {s₀ : JointState P} {checkpoint : BlockChain}
    (pre : ConfiguredHistoryTrace cfg checkpoint s₀.exec) :
    {s : JointState P} → (run : JointRun cfg ccfg bls s₀ s) →
    emissions (run.toExec pre) = emissions pre ++ (withdrawalFeed run).map Ssz.serialize
  | _, .nil => by
    rw [JointRun.toExec_nil, withdrawalFeed, JointRun.steps_nil, List.flatMap_nil, List.map_nil,
      List.append_nil]
  | _, .snoc run b step bound => by
    rw [JointRun.toExec_snoc, emissions, emissions_toExec pre run, withdrawalFeed,
      withdrawalFeed, JointRun.steps_snoc, List.flatMap_append, List.map_append,
      List.append_assoc, List.flatMap_singleton,
      ← blockWithdrawals_step ⟨_, _, b, JointStepTrace.choose step bound⟩]
    rfl

/-- Request `k` of step `j` sits at the step's feed position. -/
theorem withdrawalFeed_getElem? {P : Preset} {cfg : ChainConfig} {ccfg : Config}
    {bls : Bool} {s₀ s : JointState P} (run : JointRun cfg ccfg bls s₀ s) {j k : Nat}
    {D : JointRunStep (P := P) cfg ccfg bls} (hD : run.steps[j]? = some D)
    {wr : WithdrawalRequest} (hwr : (stepWithdrawalRequests D)[k]? = some wr) :
    (withdrawalFeed run)[feedPosition run j k]? = some wr := by
  obtain ⟨hj, hDj⟩ := List.getElem?_eq_some_iff.mp hD
  have hsplit : run.steps = run.steps.take j ++ D :: run.steps.drop (j + 1) := by
    conv_lhs => rw [← List.take_append_drop j run.steps]
    rw [List.drop_eq_getElem_cons hj, hDj]
  rw [withdrawalFeed, feedPosition, hsplit, List.take_left' (List.length_take_of_le hj.le),
    List.flatMap_append, List.flatMap_cons, List.getElem?_append_right (Nat.le_add_right _ _),
    Nat.add_sub_cancel_left, List.getElem?_append_left (List.getElem?_eq_some_iff.mp hwr).1]
  exact hwr

/-- In a joint step's mid-block trace, request `k` takes state `k` to state `k + 1`. -/
theorem jointWithdrawalTrace_step {P : Preset} {ccfg : Config} {bls : Bool}
    {s : JointState P} {b : AnySignedBlock P} {requests : ExecutionRequests P}
    (hread : Gated.read b.2.message.body.execution_requests
      "NewPayloadRequest: execution_requests" = .ok requests)
    {tr : List (BeaconState P b.1)} (htr : jointWithdrawalTrace ccfg bls s b = .ok tr)
    {k : Nat} {wr : WithdrawalRequest} (hwr : requests.withdrawals.toArray[k]? = some wr)
    {m : BeaconState P b.1} (hm : tr[k]? = some m) :
    ∃ m', tr[k + 1]? = some m' ∧ processWithdrawalRequest ccfg m wr = .ok m' := by
  unfold jointWithdrawalTrace at htr
  obtain ⟨_, -, htr⟩ := Except.bind_eq_ok htr
  obtain ⟨_, -, htr⟩ := Except.bind_eq_ok htr
  obtain ⟨st, -, htr⟩ := Except.bind_eq_ok htr
  rw [hread, Except.bind_ok] at htr
  have hk : requests.withdrawals.toArray.toList[k]? = some wr := by
    rw [Array.getElem?_toList]
    exact hwr
  obtain ⟨hlen, -, hstep⟩ := Facts.withdrawalRequestTrace_spec ccfg _ st tr htr
  have hlt : k + 1 < tr.length := by
    rw [hlen]
    exact Nat.succ_lt_succ (List.getElem?_eq_some_iff.mp hk).1
  exact ⟨tr[k + 1], List.getElem?_eq_getElem hlt, hstep k wr m _ hk hm
    (List.getElem?_eq_getElem hlt)⟩

/-! ## P1 -/

/-- Request `k` of step `j` is the run's feed element at its feed position `i`, and its
serialization is the joint history's committed paid submission `E₀ + i` (`history_fifo` and
`emissions_toExec`). -/
theorem ValidJoint.submission_of_feed {P : Preset}
    {cfg : ChainConfig} {ccfg : Config}
    {bls : Bool} {checkpoint : BlockChain} {anchor final : JointState P}
    (v : ValidJoint cfg ccfg bls checkpoint anchor final)
    {j k : Nat} {D : JointRunStep (P := P) cfg ccfg bls} (stepD : v.run.steps[j]? = some D)
    {wr : WithdrawalRequest} (hstep : (stepWithdrawalRequests D)[k]? = some wr) :
    (withdrawalFeed v.run)[feedPosition v.run j k]? = some wr ∧
    (submissions (v.run.toExec v.pre))[(emissions v.pre).length +
      feedPosition v.run j k]? = some (Ssz.serialize wr) := by
  have hfeed := withdrawalFeed_getElem? v.run stepD hstep
  have hsub : (submissions (v.run.toExec v.pre))[(emissions v.pre).length +
      feedPosition v.run j k]? = some (Ssz.serialize wr) := by
    have hlt : feedPosition v.run j k < ((withdrawalFeed v.run).map Ssz.serialize).length := by
      rw [List.length_map]
      exact (List.getElem?_eq_some_iff.mp hfeed).1
    rw [v.history_fifo, emissions_toExec, List.append_assoc,
      List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left,
      List.getElem?_append_left hlt, List.getElem?_map, hfeed, Option.map_some]
  exact ⟨hfeed, hsub⟩

/-- Every step of a valid joint chain has its mid-block trace: one state per withdrawal request
of its beacon block, plus the final state. -/
theorem ValidJoint.jointWithdrawalTrace_ok {P : Preset}
    {cfg : ChainConfig} {ccfg : Config}
    {bls : Bool} {checkpoint : BlockChain} {anchor final : JointState P}
    (v : ValidJoint cfg ccfg bls checkpoint anchor final)
    {j : Nat} {D : JointRunStep (P := P) cfg ccfg bls} (stepD : v.run.steps[j]? = some D)
    {requests : ExecutionRequests P}
    (hread : Gated.read D.block.2.message.body.execution_requests
      "NewPayloadRequest: execution_requests" = .ok requests) :
    ∃ tr, jointWithdrawalTrace ccfg bls D.pre D.block = .ok tr ∧
      tr.length = requests.withdrawals.toArray.toList.length + 1 :=
  Blanc.Lift.WithdrawalRequest.jointWithdrawalTrace_ok (v.run.steps_jointStep stepD) hread

/-- **P1, authorization across the layers.** Along a valid joint chain, take step `j` of the
run, its beacon block's execution requests `requests`, and its withdrawal request `k`, `wr`.
Let `m` be the mid-block state at which `process_withdrawal_request` processes `wr` (element
`k` of the step's `jointWithdrawalTrace`). If `wr` classifies in `m` as a full exit or a
partial withdrawal of validator `V`, then:
* `m` is where the step applies that outcome: the next mid-block state is
  `applyWithdrawalOutcome` of it (`processWithdrawalRequest_eq`), so this is an application of
  the 7002 path that initiates `V`'s exit or appends a pending partial withdrawal for `V`;
* the record of `wr` is the committed paid submission at position `E₀ + i` of the joint
  history, where `E₀` counts the records emitted before the anchor and `i` is `(j, k)`'s
  position in the run's type-1 feed (`wr` is the feed's element `i`);
* `wr.validator_pubkey` resolves to `V` in `m` (`validatorIndexOf`, the spec's first match);
* the validator at `V` in `m` has an execution withdrawal credential whose bytes 12..32 are
  `wr.source_address`, which is the caller the contract recorded for that submission (the
  record's first 20 bytes). -/
theorem ValidJoint.authorization {P : Preset}
    {cfg : ChainConfig} {ccfg : Config}
    {bls : Bool} {checkpoint : BlockChain} {anchor final : JointState P}
    (v : ValidJoint cfg ccfg bls checkpoint anchor final)
    {j : Nat} {D : JointRunStep (P := P) cfg ccfg bls} (stepD : v.run.steps[j]? = some D)
    {requests : ExecutionRequests P}
    (hread : Gated.read D.block.2.message.body.execution_requests
      "NewPayloadRequest: execution_requests" = .ok requests)
    {k : Nat} {wr : WithdrawalRequest} (hwr : requests.withdrawals.toArray[k]? = some wr)
    {tr : List (BeaconState P D.block.1)}
    (htr : jointWithdrawalTrace ccfg bls D.pre D.block = .ok tr)
    {m : BeaconState P D.block.1} (hm : tr[k]? = some m)
    {o : Facts.WithdrawalOutcome} {V : ValidatorIndex}
    (hclass : Facts.classifyWithdrawalRequest ccfg m wr = .ok o)
    (ho : o = .fullExit V ∨ ∃ amount, o = .partialWithdrawal V amount) :
    (∃ m', tr[k + 1]? = some m' ∧ Facts.applyWithdrawalOutcome ccfg m wr o = .ok m') ∧
    (withdrawalFeed v.run)[feedPosition v.run j k]? = some wr ∧
    (submissions (v.run.toExec v.pre))[(emissions v.pre).length + feedPosition v.run j k]? =
      some (Ssz.serialize wr) ∧
    validatorIndexOf m wr.validator_pubkey = .ok (some V) ∧
    ∃ validator, m.validators.get V.toNat "process_withdrawal_request" = .ok validator ∧
      hasExecutionWithdrawalCredential validator = true ∧
      validator.withdrawal_credentials.toBytes.drop 12 = wr.source_address.toBytes ∧
      validator.withdrawal_credentials.toBytes.drop 12 = (Ssz.serialize wr).take 20 := by
  have hstep : (stepWithdrawalRequests D)[k]? = some wr := by
    rw [stepWithdrawalRequests, hread, Array.getElem?_toList]
    exact hwr
  obtain ⟨hfeed, hsub⟩ := v.submission_of_feed stepD hstep
  obtain ⟨hindex, validator, hget, hcred, hsource⟩ :=
    Facts.classify_fullExit_or_partial_spec hclass ho
  have happly : ∃ m', tr[k + 1]? = some m' ∧ Facts.applyWithdrawalOutcome ccfg m wr o = .ok m' := by
    obtain ⟨m', hm', hproc⟩ := jointWithdrawalTrace_step hread htr hwr hm
    rw [Facts.processWithdrawalRequest_eq, hclass, Except.bind_ok] at hproc
    exact ⟨m', hm', hproc⟩
  refine ⟨happly, hfeed, hsub, hindex, validator, hget, hcred, hsource, ?_⟩
  have hlen : wr.source_address.toBytes.length = 20 := by
    simp only [Adr.toBytes, List.length_append, UInt32.length_toBytes, B128.length_toBytes]
  rw [hsource, Blanc.ConsensusSsz.serialize_withdrawalRequest, List.append_assoc,
    List.take_left' hlen]

/-! ## P1 negative control -/

/-- **P1 negative control, step fact.** If the pending partial-withdrawal queue does not
refuse this amount, the request's public key resolves to `V`, and the validator at `V` lacks an
execution withdrawal credential whose address is the request's source, then
`classifyWithdrawalRequest` ignores the request for `badCredentialOrSource`. -/
theorem classify_badCredentialOrSource {P : Preset} {f : CFork} {cfg : Config}
    {state : BeaconState P f} {wr : WithdrawalRequest} {q} {V : ValidatorIndex} {v}
    (hq : state.pendingPartialWithdrawals = .ok q)
    (hlim : ¬ ((q.length == P.PENDING_PARTIAL_WITHDRAWALS_LIMIT &&
      !(wr.amount == FULL_EXIT_REQUEST_AMOUNT)) = true))
    (hidx : validatorIndexOf state wr.validator_pubkey = .ok (some V))
    (hget : state.validators.get V.toNat "process_withdrawal_request" = .ok v)
    (hbad : ¬ (hasExecutionWithdrawalCredential v = true ∧
      v.withdrawal_credentials.toBytes.drop 12 = wr.source_address.toBytes)) :
    Facts.classifyWithdrawalRequest cfg state wr = .ok (.ignored .badCredentialOrSource) := by
  unfold Facts.classifyWithdrawalRequest
  dsimp only
  rw [hq]
  simp only [Except.bind_ok]
  rw [ite_eq_right hlim]
  rw [hidx]
  simp only [Except.bind_ok]
  rw [hget]
  simp only [Except.bind_ok]
  have hcond : ((!(hasExecutionWithdrawalCredential v &&
      v.withdrawal_credentials.toBytes.drop 12 == wr.source_address.toBytes)) = true) := by
    cases hc : (hasExecutionWithdrawalCredential v &&
      v.withdrawal_credentials.toBytes.drop 12 == wr.source_address.toBytes)
    · rfl
    · exfalso
      simp only [Bool.and_eq_true, beq_iff_eq] at hc
      exact hbad hc
  rw [ite_eq_left hcond]
  rfl

/-- **P1 negative control, joint form.** Take a joint step's mid-block trace `tr` (for
every step of a valid joint chain it exists, `ValidJoint.jointWithdrawalTrace_ok`), the beacon
block's withdrawal request `wr` at index `k`, and the state `m = tr[k]` at which
`process_withdrawal_request` processes it. If `wr`'s public key resolves in `m` to a validator
whose withdrawal credential is not an execution credential carrying `wr.source_address`, and
the partial-withdrawal queue does not refuse it first, then `wr` is ignored for
`badCredentialOrSource` and the next mid-block state is `m` itself: a request from any address
other than the validator's withdrawal address changes no consensus state. -/
theorem jointWithdrawalTrace_badCredentialOrSource {P : Preset} {ccfg : Config} {bls : Bool}
    {s : JointState P} {b : AnySignedBlock P} {requests : ExecutionRequests P}
    (hread : Gated.read b.2.message.body.execution_requests
      "NewPayloadRequest: execution_requests" = .ok requests)
    {tr : List (BeaconState P b.1)} (htr : jointWithdrawalTrace ccfg bls s b = .ok tr)
    {k : Nat} {wr : WithdrawalRequest} (hwr : requests.withdrawals.toArray[k]? = some wr)
    {m : BeaconState P b.1} (hm : tr[k]? = some m)
    {q} {V : ValidatorIndex} {validator}
    (hq : m.pendingPartialWithdrawals = .ok q)
    (hlim : ¬ ((q.length == P.PENDING_PARTIAL_WITHDRAWALS_LIMIT &&
      !(wr.amount == FULL_EXIT_REQUEST_AMOUNT)) = true))
    (hidx : validatorIndexOf m wr.validator_pubkey = .ok (some V))
    (hget : m.validators.get V.toNat "process_withdrawal_request" = .ok validator)
    (hbad : ¬ (hasExecutionWithdrawalCredential validator = true ∧
      validator.withdrawal_credentials.toBytes.drop 12 = wr.source_address.toBytes)) :
    Facts.classifyWithdrawalRequest ccfg m wr = .ok (.ignored .badCredentialOrSource) ∧
    tr[k + 1]? = some m := by
  have hclass := classify_badCredentialOrSource (cfg := ccfg) hq hlim hidx hget hbad
  obtain ⟨m', hm', hproc⟩ := jointWithdrawalTrace_step hread htr hwr hm
  rw [Facts.processWithdrawalRequest_eq, hclass, Except.bind_ok, Facts.apply_ignored] at hproc
  obtain rfl := Except.ok.inj hproc
  exact ⟨hclass, hm'⟩

end Blanc.Lift.WithdrawalRequest
