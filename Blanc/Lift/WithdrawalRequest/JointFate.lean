import Blanc.ListFlatMapPosition
import Blanc.Lift.WithdrawalRequest.JointAuthorization

/-!
# The fate of every paid EIP-7002 submission along a valid joint chain (P2)

Let `H = v.run.toExec v.pre` be a valid joint chain's joint history, `subs = submissions H`
its committed paid submissions (occurrence-indexed records), `E₀ = (emissions v.pre).length`
the records emitted before the anchor and `E = (emissions H).length`. Every occurrence
`n < subs.length` has exactly one fate, decided by which of the disjoint ranges `n` is in
(`ValidJoint.fate`):

* (a) `n < E₀`: emitted before the anchor, as the pre-anchor history's record `n`;
* (b) `E₀ ≤ n < E`: emitted by the run, as request `k` of the beacon block of step `j`, where
  `(j, k)` is the unique pair at feed position `n − E₀` (`feedPosition_inj`). In the mid-block
  state `m` at which `process_withdrawal_request` processes it, `classifyWithdrawalRequest`
  gives exactly one outcome `o`, and the next mid-block state is `applyWithdrawalOutcome` of
  `m` for `o`. The outcome's meaning is Jaune's W2a: `classify_fullExit_iff`,
  `classify_partial_amount`, `classify_fullExit_or_partial_spec` and `apply_ignored`
  (`ValidJoint.fate_outcome` restates the ignored and partial cases);
* (c) `E ≤ n`: still in the contract's queue at the chain's end, at position `n − E`.

The fee is retained in every case (`ValidJoint.fee_retained`, Blanc's E9 payments theorem
`history_payments` on the joint history).
-/

namespace Blanc.Lift.WithdrawalRequest

open Jaune JauneConsensus ExecutionTrace

/-! ## The feed position is a bijection -/

/-- Every position of the run's type-1 feed is request `k` of some step `j`. -/
theorem withdrawalFeed_position {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {s₀ s : JointState P} (run : JointRun cfg ccfg bls s₀ s) {i : Nat}
    (hi : i < (withdrawalFeed run).length) :
    ∃ j k, ∃ D : JointRunStep (P := P) cfg ccfg bls, ∃ wr,
      run.steps[j]? = some D ∧ (stepWithdrawalRequests D)[k]? = some wr ∧
        feedPosition run j k = i := by
  obtain ⟨j, k, hj, hk, hpos⟩ :=
    Blanc.List.exists_flatMap_position stepWithdrawalRequests run.steps hi
  exact ⟨j, k, run.steps[j], (stepWithdrawalRequests run.steps[j])[k],
    List.getElem?_eq_getElem hj, List.getElem?_eq_getElem hk, hpos⟩

/-- Two requests of the run at the same feed position are the same request of the same step. -/
theorem feedPosition_inj {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {s₀ s : JointState P} (run : JointRun cfg ccfg bls s₀ s) {j k j' k' : Nat}
    {D D' : JointRunStep (P := P) cfg ccfg bls} {wr wr' : WithdrawalRequest}
    (hD : run.steps[j]? = some D) (hwr : (stepWithdrawalRequests D)[k]? = some wr)
    (hD' : run.steps[j']? = some D') (hwr' : (stepWithdrawalRequests D')[k']? = some wr')
    (h : feedPosition run j k = feedPosition run j' k') : j = j' ∧ k = k' := by
  obtain ⟨hj, rfl⟩ := List.getElem?_eq_some_iff.mp hD
  obtain ⟨hj', rfl⟩ := List.getElem?_eq_some_iff.mp hD'
  exact Blanc.List.flatMap_position_inj stepWithdrawalRequests run.steps hj hj'
    (List.getElem?_eq_some_iff.mp hwr).1 (List.getElem?_eq_some_iff.mp hwr').1 h

/-- A request of a step's feed is a withdrawal request of its beacon block's execution
requests. -/
theorem stepWithdrawalRequests_getElem? {P : Preset} {cfg : ChainConfig} {ccfg : Config}
    {bls : Bool} {D : JointRunStep (P := P) cfg ccfg bls} {k : Nat} {wr : WithdrawalRequest}
    (h : (stepWithdrawalRequests D)[k]? = some wr) :
    ∃ requests, Gated.read D.block.2.message.body.execution_requests
        "NewPayloadRequest: execution_requests" = .ok requests ∧
      requests.withdrawals.toArray[k]? = some wr := by
  unfold stepWithdrawalRequests at h
  split at h
  · rename_i requests hread
    refine ⟨requests, hread, ?_⟩
    rw [← Array.getElem?_toList]
    exact h
  · rw [List.getElem?_nil] at h
    cases h

/-! ## P2 -/

/-- **P2, the fate of every paid submission (occurrence-indexed).** Along a valid joint chain
with joint history `H = v.run.toExec v.pre`, every committed paid submission `n` of `H` meets
exactly one of three fates; the index ranges are disjoint, so exactly one disjunct holds.
* (a) `n < E₀`: it is the pre-anchor history's emitted record `n`.
* (b) `E₀ ≤ n < E`: it is the serialized request `wr` at index `k` of the beacon block of step
  `j` of the run, where `feedPosition v.run j k = n − E₀` (the pair is unique,
  `feedPosition_inj`). At the mid-block state `m` (element `k` of the step's
  `jointWithdrawalTrace`), `classifyWithdrawalRequest` gives exactly one outcome `o`, and the
  step's next mid-block state is `applyWithdrawalOutcome` of `m` for `o`
  (`processWithdrawalRequest_eq`).
* (c) `E ≤ n`: it is the final queue's entry `n − E`. -/
theorem ValidJoint.fate {P : Preset}
    {cfg : ChainConfig} {ccfg : Config}
    {bls : Bool} {checkpoint : BlockChain} {anchor final : JointState P}
    (v : ValidJoint cfg ccfg bls checkpoint anchor final)
    {n : Nat} (hn : n < (submissions (v.run.toExec v.pre)).length) :
    (n < (emissions v.pre).length ∧
      (emissions v.pre)[n]? = some (submissions (v.run.toExec v.pre))[n]) ∨
    ((emissions v.pre).length ≤ n ∧ n < (emissions (v.run.toExec v.pre)).length ∧
      ∃ j k, ∃ D : JointRunStep (P := P) cfg ccfg bls, ∃ requests : ExecutionRequests P,
      ∃ wr, ∃ tr : List (BeaconState P D.block.1), ∃ m : BeaconState P D.block.1,
        v.run.steps[j]? = some D ∧
        Gated.read D.block.2.message.body.execution_requests
          "NewPayloadRequest: execution_requests" = .ok requests ∧
        requests.withdrawals.toArray[k]? = some wr ∧
        feedPosition v.run j k = n - (emissions v.pre).length ∧
        Ssz.serialize wr = (submissions (v.run.toExec v.pre))[n] ∧
        jointWithdrawalTrace ccfg bls D.pre D.block = .ok tr ∧ tr[k]? = some m ∧
        ∃ o, Facts.classifyWithdrawalRequest ccfg m wr = .ok o ∧
          (∀ o', Facts.classifyWithdrawalRequest ccfg m wr = .ok o' → o' = o) ∧
          ∃ m', tr[k + 1]? = some m' ∧ Facts.applyWithdrawalOutcome ccfg m wr o = .ok m') ∨
    ((emissions (v.run.toExec v.pre)).length ≤ n ∧
      (remainingQueue (v.run.toExec v.pre))[n - (emissions (v.run.toExec v.pre)).length]? =
        some (submissions (v.run.toExec v.pre))[n]) := by
  have hsubs := v.history_fifo
  have hem := emissions_toExec (bls := bls) v.pre v.run
  have hget : (submissions (v.run.toExec v.pre))[n]? =
      some (submissions (v.run.toExec v.pre))[n] := List.getElem?_eq_getElem hn
  by_cases ha : n < (emissions v.pre).length
  · refine .inl ⟨ha, ?_⟩
    have hlt : n < (emissions (v.run.toExec v.pre)).length := by
      rw [hem, List.length_append]
      omega
    rw [← hget, hsubs, List.getElem?_append_left hlt, hem, List.getElem?_append_left ha]
  by_cases hc : (emissions (v.run.toExec v.pre)).length ≤ n
  · refine .inr (.inr ⟨hc, ?_⟩)
    rw [← hget, hsubs, List.getElem?_append_right hc]
  refine .inr (.inl ⟨Nat.le_of_not_lt ha, Nat.lt_of_not_le hc, ?_⟩)
  have hi : n - (emissions v.pre).length < (withdrawalFeed v.run).length := by
    have hlen := congrArg List.length hem
    rw [List.length_append, List.length_map] at hlen
    omega
  obtain ⟨j, k, D, wr, stepD, hstep, hpos⟩ := withdrawalFeed_position v.run hi
  obtain ⟨requests, hread, hwr⟩ := stepWithdrawalRequests_getElem? hstep
  have hfeed := withdrawalFeed_getElem? v.run stepD hstep
  have hser : Ssz.serialize wr = (submissions (v.run.toExec v.pre))[n] := by
    have hlt : n < (emissions (v.run.toExec v.pre)).length := Nat.lt_of_not_le hc
    have h : (submissions (v.run.toExec v.pre))[n]? = some (Ssz.serialize wr) := by
      rw [hsubs, List.getElem?_append_left hlt, hem,
        List.getElem?_append_right (Nat.le_of_not_lt ha), List.getElem?_map, ← hpos, hfeed,
        Option.map_some]
    exact Option.some.inj (h.symm.trans hget)
  obtain ⟨tr, htr, hlen⟩ := v.jointWithdrawalTrace_ok stepD hread
  have hk : k < tr.length := by
    have := (Array.getElem?_eq_some_iff.mp hwr).1
    rw [hlen, Array.length_toList]
    omega
  obtain ⟨m', hm', hproc⟩ :=
    jointWithdrawalTrace_step hread htr hwr (List.getElem?_eq_getElem hk)
  rw [Facts.processWithdrawalRequest_eq] at hproc
  obtain ⟨o, hclass, happly⟩ := Except.bind_eq_ok hproc
  refine ⟨j, k, D, requests, wr, tr, tr[k], stepD, hread, hwr, hpos, hser, htr,
    List.getElem?_eq_getElem hk, o, hclass, fun o' h' => Except.ok.inj (h'.symm.trans hclass),
    m', hm', happly⟩

/-- **(b)'s outcome, read through W2a.** In the setting of `ValidJoint.fate` (b), an ignored
request leaves the mid-block state unchanged (`apply_ignored`), and a partial withdrawal
appends exactly `min (balance − MIN_ACTIVATION_BALANCE − pending) wr.amount`, with `balance`
and `pending` read from the mid-block state, for a nonzero requested amount
(`classify_partial_amount`). A full exit holds exactly under `classify_fullExit_iff`. -/
theorem ValidJoint.fate_outcome {P : Preset} {f : CFork} {ccfg : Config}
    {m m' : BeaconState P f} {wr : WithdrawalRequest} {o : Facts.WithdrawalOutcome}
    (hclass : Facts.classifyWithdrawalRequest ccfg m wr = .ok o)
    (happly : Facts.applyWithdrawalOutcome ccfg m wr o = .ok m') :
    (∀ r, o = .ignored r → m' = m) ∧
    (∀ V amount, o = .partialWithdrawal V amount →
      ∃ balance pending, m.balances.get V.toNat "process_withdrawal_request" = .ok balance ∧
        getPendingBalanceToWithdraw m V = .ok pending ∧
        amount.toNat =
          min (balance.toNat - P.MIN_ACTIVATION_BALANCE - pending.toNat) wr.amount.toNat ∧
        wr.amount ≠ U64.zero) := by
  refine ⟨fun r ho => ?_, fun V amount ho => ?_⟩
  · rw [ho, Facts.apply_ignored] at happly
    exact (Except.ok.inj happly).symm
  · rw [ho] at hclass
    exact Facts.classify_partial_amount hclass

/-- **The fee is retained (E9 on the joint history).** Along a valid joint chain, the EIP-7002
predeploy's balance at the chain's end is at least its checkpoint balance plus the value of
every committed submission of the joint history, whatever each submission's fate. -/
theorem ValidJoint.fee_retained {P : Preset}
    {cfg : ChainConfig} {ccfg : Config}
    {bls : Bool} {checkpoint : BlockChain} {anchor final : JointState P}
    (v : ValidJoint cfg ccfg bls checkpoint anchor final) :
    (checkpoint.state.bal withdrawalRequestPredeployAddress).toNat +
        submissionPaid (v.run.toExec v.pre) ≤
      (final.exec.state.bal withdrawalRequestPredeployAddress).toNat :=
  history_payments v.deployment v.admission (v.run.toExec v.pre)

end Blanc.Lift.WithdrawalRequest
