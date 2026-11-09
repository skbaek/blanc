import Blanc.Lift.WithdrawalRequest.JointAuthorization
import Blanc.ConsensusSsz
import JauneConsensus.Facts.ExpectedWithdrawals

/-!
# Round-trip crediting safety along a valid joint chain (P4)

Fix a step `D` of a valid joint chain and let `st` be the beacon state its `process_withdrawals`
reads (`jointWithdrawalsInput`: `process_block_header` applied to the state the step hands to
`process_block`), with `(ws, processed) = get_expected_withdrawals st`.

* **Recipient** (`ValidJoint.crediting_recipient`). Every `w ∈ ws` names a validator of `st`
  whose withdrawal address is `w.address`. The step's execution block carries exactly
  `ws` (the `require` of `process_withdrawals` plus the payload conversion), so the body run
  credits exactly the fold `processWithdrawalsState pre (ws.map toExecution)` before its
  request pass, and each address's balance moves only by the withdrawals in `ws` addressed
  to it.
* **Amount and loop floor** (`ValidJoint.crediting_loop1`). `ws` splits as the pending-partial
  loop's emissions `ws1` followed by the sweep's; each `w ∈ ws1` comes from a distinct
  processed pending entry `p` with `w.amount ≤ p.amount`, and leaves the loop's running
  balance of its validator (the state balance minus what `ws` already withdrew from it) at
  least `MIN_ACTIVATION_BALANCE` above `w.amount`.
* **Compounding recipient** (`ValidJoint.crediting_loop1_compounding`). Under the anchor
  invariant at `st` (an explicit hypothesis until joint-step preservation is composed), every
  loop-1 payment goes to a validator with a compounding credential.
* **Same address as the request** (`ValidJoint.crediting_address`). A partial withdrawal the
  7002 path appended for `V` at a mid-block state `m` (P1's hypotheses) is paid, at any later
  `st` with `AddrStable m st` (an explicit hypothesis), to the request's `source_address`.
-/

namespace Blanc.Lift.WithdrawalRequest

open Jaune JauneConsensus ExecutionTrace

/-- The execution withdrawals of a joint step's block are the expected withdrawals of the
state its `process_withdrawals` reads. -/
theorem payloadWithdrawals_eq_expected {P : Preset} {b : AnySignedBlock P}
    {ws : Array JauneConsensus.Withdrawal}
    (hpay : b.2.message.body.execution_payload.withdrawals.toArray = ws) :
    payloadWithdrawals b = ws.toList.map JauneConsensus.Withdrawal.toExecution := by
  rw [payloadWithdrawals, ExecutionPayload.executionWithdrawals, hpay]

/-- **P4 (1), recipient.** At step `D` of a valid joint chain, with `st` the state
`process_withdrawals` reads and `ws` its expected withdrawals:
* every `w ∈ ws` names a validator of `st` whose withdrawal address is `w.address`
  (`Facts.AllRecipientOk`);
* the step's execution block carries exactly `ws` converted (`Withdrawal.toExecution`, which
  keeps `address` as `recipient`);
* the body's request pass starts from the fold `processWithdrawalsState` of exactly those
  withdrawals over the post-transaction state, and its final state is the body's;
* in that fold, each address `a`'s balance is what crediting only the `w ∈ ws` with
  `w.address = a` gives. -/
theorem ValidJoint.crediting_recipient {P : Preset} {cfg : ChainConfig} {ccfg : Config}
    {bls : Bool} {checkpoint : BlockChain} {anchor final : JointState P}
    (v : ValidJoint cfg ccfg bls checkpoint anchor final)
    {j : Nat} {D : JointRunStep (P := P) cfg ccfg bls} (stepD : v.run.steps[j]? = some D) :
    ∃ st, jointWithdrawalsInput ccfg bls D.pre D.block = .ok st ∧
      ∃ (ws : Array JauneConsensus.Withdrawal) (processed : Nat),
        getExpectedWithdrawals st = .ok (ws, processed) ∧
        Facts.AllRecipientOk st ws ∧
        D.stepTrace.trace.block.wds = ws.toList.map JauneConsensus.Withdrawal.toExecution ∧
        Nonempty (RequestsTrace
          (D.stepTrace.trace.bodyTrace.transactionBenv.withState
            (processWithdrawalsState D.stepTrace.trace.bodyTrace.transactionBenv.state
              (ws.toList.map JauneConsensus.Withdrawal.toExecution)))
          (D.stepTrace.trace.bodyTrace.transactionBout.withWithdrawalsTrie
            (processWithdrawalsTrie D.stepTrace.trace.bodyTrace.transactionBout.withdrawalsTrie
              (ws.toList.map JauneConsensus.Withdrawal.toExecution)))
          D.stepTrace.trace.bodyState D.stepTrace.trace.bodyTrace.requestBout) ∧
        ∀ (pre : State) (a : Adr),
          (processWithdrawalsState pre (ws.toList.map JauneConsensus.Withdrawal.toExecution)).bal a =
            (processWithdrawalsState pre ((ws.toList.filter fun w => decide (w.address = a)).map
              JauneConsensus.Withdrawal.toExecution)).bal a := by
  obtain ⟨st, hst, ws, processed, hge, hpay, -⟩ :=
    jointStep_processWithdrawals (v.run.steps_jointStep stepD)
  have hwds : D.stepTrace.trace.block.wds =
      ws.toList.map JauneConsensus.Withdrawal.toExecution := by
    rw [D.stepTrace.block_wds, payloadWithdrawals_eq_expected hpay]
  refine ⟨st, hst, ws, processed, hge, Facts.getExpected_recipient st ws processed hge, hwds,
    ⟨?_⟩, ?_⟩
  · have hreq := D.stepTrace.trace.bodyTrace.requests
    rw [D.stepTrace.trace.bodyTrace.requestState_eq] at hreq
    exact hwds ▸ hreq
  · intro pre a
    rw [processWithdrawalsState_bal_filter a, List.filter_map]
    rfl

/-- Steps of a joint run are Electra or Fulu blocks, so the pending-partial queue exists. -/
theorem JointRunStep.atLeast_electra {P : Preset} {cfg : ChainConfig} {ccfg : Config}
    {bls : Bool} {s₀ s : JointState P} {run : JointRun cfg ccfg bls s₀ s} {j : Nat}
    {D : JointRunStep (P := P) cfg ccfg bls} (stepD : run.steps[j]? = some D) :
    D.block.1.atLeast .electra = true := by
  obtain ⟨hcf, -⟩ := jointStep_engine (run.steps_jointStep stepD)
  rcases hcf with hcf | hcf <;> rw [hcf] <;> rfl

/-- **P4 (2), amount and loop floor.** At step `D` of a valid joint chain, with `st` the state
`process_withdrawals` reads, `l` its pending partial withdrawals and `(ws, processed)` its
expected withdrawals, which the payload carries: `ws = ws1 ++ ws2` where `ws1` is the
pending-partial loop's emissions. `Facts.Loop1Witness` gives distinct processed pending entries,
in order, one per `w ∈ ws1`, for the same validator and with `w.amount ≤ p.amount`;
`Facts.Loop1Floor` gives, for each `w ∈ ws1`, the loop's running balance `balU` of its
validator (state balance minus the amount `ws` already withdrew from it) with
`MIN_ACTIVATION_BALANCE ≤ balU - w.amount`. -/
theorem ValidJoint.crediting_loop1 {P : Preset} {cfg : ChainConfig} {ccfg : Config}
    {bls : Bool} {checkpoint : BlockChain} {anchor final : JointState P}
    (v : ValidJoint cfg ccfg bls checkpoint anchor final)
    {j : Nat} {D : JointRunStep (P := P) cfg ccfg bls} (stepD : v.run.steps[j]? = some D) :
    ∃ st, jointWithdrawalsInput ccfg bls D.pre D.block = .ok st ∧
      ∃ (ws : Array JauneConsensus.Withdrawal) (processed : Nat),
        getExpectedWithdrawals st = .ok (ws, processed) ∧
        D.block.2.message.body.execution_payload.withdrawals.toArray = ws ∧
        ∃ (ws1 ws2 : Array JauneConsensus.Withdrawal) (l : SszList PendingPartialWithdrawal
            P.PENDING_PARTIAL_WITHDRAWALS_LIMIT),
          st.pendingPartialWithdrawals = .ok l ∧
          ws.toList = ws1.toList ++ ws2.toList ∧
          Facts.Loop1Witness ws1 l.toArray processed ∧
          Facts.Loop1Floor st ws1 P.MIN_ACTIVATION_BALANCE := by
  obtain ⟨st, hst, ws, processed, hge, hpay, -⟩ :=
    jointStep_processWithdrawals (v.run.steps_jointStep stepD)
  obtain ⟨ws1, ws2, pending, hsplit, hpend, hwit, hfloor⟩ :=
    Facts.loop1_emissions st ws processed hge
  rw [dite_eq_left (JointRunStep.atLeast_electra stepD)] at hpend
  obtain ⟨l, hl, rfl⟩ := hpend
  exact ⟨st, hst, ws, processed, hge, hpay, ws1, ws2, l, hl, hsplit, hwit, hfloor⟩

/-- **P4 (3), compounding recipient.** Under the anchor invariant at the state
`process_withdrawals` reads (**explicit hypothesis** `hinv`, to be discharged by joint-step
preservation of `Facts.AnchorInv`), every pending-partial loop emission `w ∈ ws1` of
`ValidJoint.crediting_loop1` is for a validator with a compounding withdrawal credential. -/
theorem ValidJoint.crediting_loop1_compounding {P : Preset} {f : CFork}
    {st : BeaconState P f} {l : SszList PendingPartialWithdrawal
      P.PENDING_PARTIAL_WITHDRAWALS_LIMIT} {ws1 : Array JauneConsensus.Withdrawal}
    {processed : Nat} (hl : st.pendingPartialWithdrawals = .ok l)
    (hwit : Facts.Loop1Witness ws1 l.toArray processed)
    (hinv : Facts.AnchorInv st) {w : JauneConsensus.Withdrawal} (hw : w ∈ ws1.toList) :
    ∃ validator, st.validators.toArray[w.validator_index.toNat]? = some validator ∧
      hasCompoundingWithdrawalCredential validator = true := by
  obtain ⟨-, -, chosen, hsub, hlen, hpair⟩ := hwit
  obtain ⟨i, hi, hwi⟩ := List.getElem_of_mem hw
  have hci : i < chosen.length := by
    rw [hlen]
    simpa only [Array.length_toList] using hi
  have hp := hpair i w chosen[i] (by rw [← hwi]; exact List.getElem?_eq_getElem hi)
    (List.getElem?_eq_getElem hci)
  have hmem : chosen[i] ∈ l.toArray.toList :=
    (List.take_sublist _ _).subset (hsub.subset (List.getElem_mem hci))
  obtain ⟨validator, hv, hc⟩ := hinv.1 l hl chosen[i] hmem
  exact ⟨validator, by rw [hp.1]; exact hv, hc⟩

/-- **P4 (3), same address as the request.** Take an application of the 7002 path that P1
covers: step `j₀`'s withdrawal request `k₀`, `wr`, classified at its mid-block state `m` as a
partial withdrawal of validator `V` (so a pending partial withdrawal for `V` is appended).
At step `j` let `st` be the state `process_withdrawals` reads and `ws` its expected
withdrawals. Given **address stability** from `m` to `st` (**explicit hypothesis**
`hstable : Facts.AddrStable m st`, to be discharged by joint-step preservation along the
run), every `w ∈ ws` paid to `V`, in particular the loop-1 payment of that pending entry,
goes to the request's `source_address`, the address P1 checked. -/
theorem ValidJoint.crediting_address {P : Preset} {cfg : ChainConfig} {ccfg : Config}
    {bls : Bool} {checkpoint : BlockChain} {anchor final : JointState P}
    (v : ValidJoint cfg ccfg bls checkpoint anchor final)
    {j₀ : Nat} {D₀ : JointRunStep (P := P) cfg ccfg bls} (stepD₀ : v.run.steps[j₀]? = some D₀)
    {requests : ExecutionRequests P}
    (hread : Gated.read D₀.block.2.message.body.execution_requests
      "NewPayloadRequest: execution_requests" = .ok requests)
    {k₀ : Nat} {wr : WithdrawalRequest} (hwr : requests.withdrawals.toArray[k₀]? = some wr)
    {tr : List (BeaconState P D₀.block.1)}
    (htr : jointWithdrawalTrace ccfg bls D₀.pre D₀.block = .ok tr)
    {m : BeaconState P D₀.block.1} (hm : tr[k₀]? = some m)
    {V : ValidatorIndex} {amount : Gwei}
    (hclass : Facts.classifyWithdrawalRequest ccfg m wr = .ok (.partialWithdrawal V amount))
    {f : CFork} {st : BeaconState P f} {ws : Array JauneConsensus.Withdrawal} {processed : Nat}
    (hge : getExpectedWithdrawals st = .ok (ws, processed))
    (hstable : Facts.AddrStable m st)
    {w : JauneConsensus.Withdrawal} (hw : w ∈ ws.toList) (hV : w.validator_index = V) :
    w.address = wr.source_address := by
  obtain ⟨-, -, -, -, validator, hget, hcred, hsource, -⟩ :=
    v.authorization stepD₀ hread hwr htr hm hclass (.inr ⟨amount, rfl⟩)
  obtain ⟨v', hv', -, hdrop⟩ := hstable V.toNat validator (Facts.get_ok hget) hcred
  obtain ⟨v'', hv'', haddr⟩ := Facts.getExpected_recipient st ws processed hge w hw
  rw [hV, hv'] at hv''
  cases hv''
  unfold withdrawalAddress at haddr
  rw [hdrop, hsource, ConsensusSsz.toAdr?_toBytes] at haddr
  exact (Except.ok.inj haddr).symm

end Blanc.Lift.WithdrawalRequest
