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
* **Compounding recipient** (`ValidJoint.crediting_loop1_compounding`). Every loop-1 payment
  goes to a validator with a compounding credential: the anchor invariant holds at `st`
  (`ValidJoint.anchorInv_at_withdrawals`), carried from the anchor by Jaune's `Facts.Pres` along
  the run and through the step's slots, upgrade and header.
* **Same address as the request** (`ValidJoint.crediting_address`). A partial withdrawal the
  7002 path appended for `V` at a mid-block state `m` of step `j₀` (P1's hypotheses) is paid,
  at the `st` of any later step `j > j₀`, to the request's `source_address`: the withdrawal
  address of every execution-credentialed validator is stable from `m` to `st`
  (`ValidJoint.addrStable_mid_to_withdrawals`), through the rest of block `j₀` (the remaining
  withdrawal requests, the consolidation requests, the sync aggregate), the steps between,
  and step `j`'s slots and header. In block `j₀` itself the entry is appended after
  `process_withdrawals` ran, so `j₀ < j` loses nothing.
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

/-- Under the anchor invariant at a state with pending partial withdrawals `l`, every
pending-partial loop emission `w ∈ ws1` is for a validator with a compounding withdrawal
credential. -/
theorem crediting_loop1_compounding_of_anchorInv {P : Preset} {f : CFork}
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

/-- **The anchor invariant at every withdrawals input.** At step `D` of a valid joint chain,
the state `process_withdrawals` reads satisfies `Facts.AnchorInv`: the anchor's invariant is
preserved (`Facts.Pres`) along the run to `D.pre`, then by `jointBlockInput` and
`process_block_header`. -/
theorem ValidJoint.anchorInv_at_withdrawals {P : Preset} {cfg : ChainConfig} {ccfg : Config}
    {bls : Bool} {checkpoint : BlockChain} {anchor final : JointState P}
    (v : ValidJoint cfg ccfg bls checkpoint anchor final)
    {j : Nat} {D : JointRunStep (P := P) cfg ccfg bls} (stepD : v.run.steps[j]? = some D)
    {st : BeaconState P D.block.1} (hst : jointWithdrawalsInput ccfg bls D.pre D.block = .ok st) :
    Facts.AnchorInv st :=
  ((JointRun.reach_pre v.run stepD).pres.trans (jointWithdrawalsInput_pres hst)).anchor
    v.anchorInv

/-- **P4 (3), compounding recipient.** At step `D` of a valid joint chain, with `st` the state
`process_withdrawals` reads and `l` its pending partial withdrawals, every pending-partial loop
emission `w ∈ ws1` of `ValidJoint.crediting_loop1` is for a validator with a compounding
withdrawal credential. -/
theorem ValidJoint.crediting_loop1_compounding {P : Preset} {cfg : ChainConfig} {ccfg : Config}
    {bls : Bool} {checkpoint : BlockChain} {anchor final : JointState P}
    (v : ValidJoint cfg ccfg bls checkpoint anchor final)
    {j : Nat} {D : JointRunStep (P := P) cfg ccfg bls} (stepD : v.run.steps[j]? = some D)
    {st : BeaconState P D.block.1} (hst : jointWithdrawalsInput ccfg bls D.pre D.block = .ok st)
    {l : SszList PendingPartialWithdrawal P.PENDING_PARTIAL_WITHDRAWALS_LIMIT}
    {ws1 : Array JauneConsensus.Withdrawal} {processed : Nat}
    (hl : st.pendingPartialWithdrawals = .ok l)
    (hwit : Facts.Loop1Witness ws1 l.toArray processed)
    {w : JauneConsensus.Withdrawal} (hw : w ∈ ws1.toList) :
    ∃ validator, st.validators.toArray[w.validator_index.toNat]? = some validator ∧
      hasCompoundingWithdrawalCredential validator = true :=
  crediting_loop1_compounding_of_anchorInv hl hwit (v.anchorInv_at_withdrawals stepD hst) hw

/-! ## Address stability from a mid-block state -/

/-- The withdrawal-requests fold preserves `Facts.Pres`. -/
theorem foldWithdrawalRequests_pres {P : Preset} {f : CFork} {cfg : Config} :
    ∀ {reqs : List WithdrawalRequest} {st out : BeaconState P f},
      Facts.foldWithdrawalRequests cfg st reqs = .ok out → Facts.Pres st out
  | [], st, out, h => by
    obtain rfl : st = out := Except.ok.inj h
    exact Facts.Pres.refl _
  | wr :: rest, st, out, h => by
    unfold Facts.foldWithdrawalRequests at h
    rw [List.foldlM_cons] at h
    obtain ⟨mid, hmid, h⟩ := Except.bind_eq_ok h
    exact (Facts.processWithdrawalRequest_pres cfg hmid).trans (foldWithdrawalRequests_pres h)

/-- Every state of the withdrawal-requests trace reaches the fold's result (`Facts.Pres`). -/
theorem withdrawalRequestTrace_pres_fold {P : Preset} {f : CFork} {cfg : Config} :
    ∀ {reqs : List WithdrawalRequest} {st out : BeaconState P f} {tr : List (BeaconState P f)}
      {k : Nat} {m : BeaconState P f},
      Facts.withdrawalRequestTrace cfg st reqs = .ok tr →
      Facts.foldWithdrawalRequests cfg st reqs = .ok out → tr[k]? = some m → Facts.Pres m out
  | [], st, out, tr, k, m, htr, hf, hm => by
    obtain rfl : [st] = tr := Except.ok.inj htr
    obtain rfl : st = out := Except.ok.inj hf
    cases k with
    | zero =>
      obtain rfl : st = m := Option.some.inj hm
      exact Facts.Pres.refl _
    | succ k =>
      simp only [List.getElem?_cons_succ, List.getElem?_nil, reduceCtorEq] at hm
  | wr :: rest, st, out, tr, k, m, htr, hf, hm => by
    unfold Facts.foldWithdrawalRequests at hf
    rw [List.foldlM_cons] at hf
    obtain ⟨mid, hmid, hf⟩ := Except.bind_eq_ok hf
    simp only [Facts.withdrawalRequestTrace, hmid, Except.bind_ok] at htr
    obtain ⟨tr', htr', htr⟩ := Except.bind_eq_ok htr
    obtain rfl : st :: tr' = tr := Except.ok.inj htr
    cases k with
    | zero =>
      obtain rfl : st = m := Option.some.inj hm
      exact (Facts.processWithdrawalRequest_pres cfg hmid).trans (foldWithdrawalRequests_pres hf)
    | succ k =>
      rw [List.getElem?_cons_succ] at hm
      exact withdrawalRequestTrace_pres_fold htr' hf hm

/-- The consolidation-requests loop preserves `Facts.Pres`. -/
theorem postRequests_pres {P : Preset} {f : CFork} (ctx : Ctx) {body : BeaconBlockBody P f}
    {s s' : BeaconState P f} (h : Facts.postRequests ctx s body = .ok s') : Facts.Pres s s' := by
  revert s' h
  show Facts.Ok (Facts.postRequests ctx s body) (Facts.Pres s)
  unfold Facts.postRequests
  repeat pstep

/-- Every mid-block state of a successful joint step's withdrawal-requests trace reaches the
step's beacon state (`Facts.Pres`): the remaining withdrawal requests, the consolidation
requests and the sync aggregate; the state-root check only reads the state. -/
theorem jointWithdrawalTrace_pres_post {P : Preset} {cfg : ChainConfig} {ccfg : Config}
    {bls : Bool} {s s' : JointState P} {b : AnySignedBlock P}
    (h : jointStep cfg ccfg bls s b = .ok s') {requests : ExecutionRequests P}
    (hread : Gated.read b.2.message.body.execution_requests
      "NewPayloadRequest: execution_requests" = .ok requests)
    {tr : List (BeaconState P b.1)} (htr : jointWithdrawalTrace ccfg bls s b = .ok tr)
    {k : Nat} {m : BeaconState P b.1} (hm : tr[k]? = some m) : Facts.Pres m s'.beacon := by
  obtain ⟨hcf, -⟩ := jointStep_engine h
  have hel : b.1.atLeast .electra = true := by
    rcases hcf with hcf | hcf <;> rw [hcf] <;> rfl
  obtain ⟨st, hst, post, hpost, hpres⟩ := jointStep_processBlock_post h
  unfold processBlock at hpost
  rw [Facts.processBlockWith_split] at hpost
  obtain ⟨st0, h0, hpost⟩ := Except.bind_eq_ok hpost
  obtain ⟨st1, h1, hsync⟩ := Except.bind_eq_ok hpost
  rw [Facts.processOperations_split _ _ _ hel] at h1
  obtain ⟨st2, h2, h1⟩ := Except.bind_eq_ok h1
  obtain ⟨st3, h3, h4⟩ := Except.bind_eq_ok h1
  have hget : Gated.get hel b.2.message.body.execution_requests = requests := by
    rw [Facts.gated_read_get hel] at hread
    exact Except.ok.inj hread
  rw [hget] at h3
  simp only [jointWithdrawalTrace, hst, h0, h2, hread, Except.bind_ok] at htr
  exact (withdrawalRequestTrace_pres_fold htr h3 hm).trans ((postRequests_pres _ h4).trans
    ((Facts.processSyncAggregate_pres _ hsync).trans hpres))

/-- **Address stability from a mid-block state.** Along a valid joint chain, let `m` be a
mid-block state of step `j₀`'s withdrawal-requests trace and `st` the state step `j`'s
`process_withdrawals` reads, with `j₀ < j`. Then `Facts.AddrStable m st`: the rest of block
`j₀`, the steps strictly between, and step `j`'s slots, upgrade and header each preserve
`Facts.Pres`. -/
theorem ValidJoint.addrStable_mid_to_withdrawals {P : Preset} {cfg : ChainConfig}
    {ccfg : Config} {bls : Bool} {checkpoint : BlockChain} {anchor final : JointState P}
    (v : ValidJoint cfg ccfg bls checkpoint anchor final)
    {j₀ : Nat} {D₀ : JointRunStep (P := P) cfg ccfg bls} (stepD₀ : v.run.steps[j₀]? = some D₀)
    {requests : ExecutionRequests P}
    (hread : Gated.read D₀.block.2.message.body.execution_requests
      "NewPayloadRequest: execution_requests" = .ok requests)
    {tr : List (BeaconState P D₀.block.1)}
    (htr : jointWithdrawalTrace ccfg bls D₀.pre D₀.block = .ok tr)
    {k₀ : Nat} {m : BeaconState P D₀.block.1} (hm : tr[k₀]? = some m)
    {j : Nat} {D : JointRunStep (P := P) cfg ccfg bls} (stepD : v.run.steps[j]? = some D)
    (hj : j₀ < j) {st : BeaconState P D.block.1}
    (hst : jointWithdrawalsInput ccfg bls D.pre D.block = .ok st) :
    Facts.AddrStable m st :=
  ((jointWithdrawalTrace_pres_post (v.run.steps_jointStep stepD₀) hread htr hm).trans
    ((JointRun.reach_post_pre v.run hj stepD₀ stepD).pres.trans
      (jointWithdrawalsInput_pres hst))).addr

/-- Same address as the request, at any state `st` address-stable from the mid-block state
`m` (`hstable`). -/
theorem ValidJoint.crediting_address_of_addrStable {P : Preset} {cfg : ChainConfig} {ccfg : Config}
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

/-- **P4 (3), same address as the request.** Take an application of the 7002 path that P1
covers: step `j₀`'s withdrawal request `k₀`, `wr`, classified at its mid-block state `m` as a
partial withdrawal of validator `V` (so a pending partial withdrawal for `V` is appended).
At any later step `j > j₀` let `st` be the state `process_withdrawals` reads and `ws` its
expected withdrawals. Every `w ∈ ws` paid to `V`, in particular the loop-1 payment of that
pending entry, goes to the request's `source_address`, the address P1 checked. -/
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
    {j : Nat} {D : JointRunStep (P := P) cfg ccfg bls} (stepD : v.run.steps[j]? = some D)
    (hj : j₀ < j) {st : BeaconState P D.block.1}
    (hst : jointWithdrawalsInput ccfg bls D.pre D.block = .ok st)
    {ws : Array JauneConsensus.Withdrawal} {processed : Nat}
    (hge : getExpectedWithdrawals st = .ok (ws, processed))
    {w : JauneConsensus.Withdrawal} (hw : w ∈ ws.toList) (hV : w.validator_index = V) :
    w.address = wr.source_address :=
  v.crediting_address_of_addrStable stepD₀ hread hwr htr hm hclass hge
    (v.addrStable_mid_to_withdrawals stepD₀ hread htr hm stepD hj hst) hw hV

end Blanc.Lift.WithdrawalRequest
