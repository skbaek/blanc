import Blanc.Composition.BuilderRequestJointGFate
import JauneConsensus.Facts.Gloas.StepB5
import JauneConsensus.Facts.Gloas.InvariantsCrossing

/-!
# B5 over a valid Gloas joint chain: the builder balance equation and the carried withdrawals

Goal `eip8282-gloas-cross-layer-v1`, frozen statements rev 3.1 (Plans `recon/statements.md` B5 (i), (iv)).

* `GInv`: the G3a state invariants (`GAnchorInv`'s Gloas arm). They hold at every Gloas state of a valid
  joint chain (`ValidJointG.gInv_pre`): at the anchor (`anchorInv`), established by the crossing
  (`upgrade_to_gloas`, then the first block) and carried by every Gloas step, with the two N7 registry bounds
  at each post-state (`validatorsBound`, `buildersBound`).
* `ValidJointG.builder_balance_equation` (B5(i)): Jaune's per-step `GStepView.builder_balance_equation` at
  every Gloas step of the run, its invariant premises discharged by `GInv` and the N7 bounds.
* `ValidJointG.carried_withdrawals_equal` (B5(iv)): the payload a FULL step settles carries, as lists, the
  `payload_expected_withdrawals` of the state its delivering step ended in (an earlier run step's post-block
  state, or the anchor's); `ValidJointG.withdrawals_early_return` lifts the per-step early return.
-/

namespace Blanc.Lift.BuilderRequest

open Jaune JauneConsensus ExecutionTrace Blanc JauneConsensus.Facts.Gloas JauneConsensus.Facts.Gloas.Inv

variable {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool}

/-! ## The G3a invariants along a run -/

/-- The G3a state invariants of a Gloas state: `GAnchorInv`'s Gloas arm. -/
def GInv (s : Gloas.BeaconState P) : Prop :=
  BuilderPubkeysUnique s ∧ PendingRefsInRange s ∧ ExitedHaveNoPending s ∧ PendingCovered s ∧
    NextBuilderIndexInRange s ∧ NoLiveWeightOnLatestBid s ∧ LatestBidCoherence s ∧
    LatestBidBuilderActive s ∧ FutureEmpty s

/-- `process_block` carries the G3a invariants, with the N7 bounds at its post-state. -/
theorem GInv.processBlock (hdel : 1 ≤ P.MIN_ATTESTATION_INCLUSION_DELAY) (hspe : 2 ≤ P.SLOTS_PER_EPOCH)
    {ctx : Ctx} {s s' : Gloas.BeaconState P} {blk : Gloas.BeaconBlock P}
    (h : Gloas.processBlock ctx s blk = .ok s') (hi : GInv s)
    (vb : s'.validators.toArray.size ≤ 2 ^ 40) (bb : s'.builders.toArray.size ≤ 2 ^ 40) : GInv s' := by
  obtain ⟨g1, g3, g4, g5, g6, -, g8, hA, fe⟩ := hi
  obtain ⟨g7', fe'⟩ := processBlock_noLiveWeight hdel (by omega) h fe
  exact ⟨processBlock_pubkeysUnique h g1, processBlock_pendingRefsInRange hA h g3,
    processBlock_exitedHaveNoPending hA h g4, processBlock_pendingCovered hspe h g5 g3 g4 g8 hA vb bb,
    processBlock_nextBuilderIndexInRange h g6, g7', processBlock_latestBidCoherence h,
    processBlock_latestBidBuilderActive h, fe'⟩

/-- `state_transition` carries the G3a invariants, with the N7 bounds at its post-state. -/
theorem GInv.stateTransition (hq : 2 * P.SLOTS_PER_EPOCH ≤ P.EFFECTIVE_BALANCE_INCREMENT)
    (hdel : 1 ≤ P.MIN_ATTESTATION_INCLUSION_DELAY) (hspe : 2 ≤ P.SLOTS_PER_EPOCH)
    {ctx : Ctx} {s s' : Gloas.BeaconState P} {sb : Gloas.SignedBeaconBlock P} {v : Bool}
    (h : Gloas.stateTransition ctx s sb v = .ok s') (hi : GInv s)
    (vb : s'.validators.toArray.size ≤ 2 ^ 40) (bb : s'.builders.toArray.size ≤ 2 ^ 40) : GInv s' := by
  obtain ⟨g1, g3, g4, g5, g6, g7, g8, hA, fe⟩ := hi
  obtain ⟨g7', fe'⟩ := stateTransition_noLiveWeight hdel (by omega) h ⟨g7, fe⟩
  exact ⟨stateTransition_pubkeysUnique h g1, stateTransition_pendingRefsInRange hq hA h g3,
    stateTransition_exitedHaveNoPending hq hA h g4,
    stateTransition_pendingCovered hq hspe h g5 g3 g4 g7 g8 fe hA vb bb,
    stateTransition_nextBuilderIndexInRange h g6, g7', stateTransition_latestBidCoherence h,
    stateTransition_latestBidBuilderActive h, fe'⟩

/-- A Gloas run step's slots and block transition are Gloas `state_transition`. -/
theorem _root_.Blanc.GloasStepData.stateTransition (D : GloasStepData (P := P) cfg ccfg bls) :
    Gloas.stateTransition (gloasCtx ccfg bls) D.preB D.block = .ok D.postB := by
  rw [← processSlots_then_gloasBlockTransition, D.slots]
  exact D.transition

/-- The joint invariant: `GInv` at a Gloas state, nothing before Gloas. -/
def GInvJ : GJointState P → Prop
  | .pre _ => True
  | .gloas b _ _ => GInv b

/-- Every step carries `GInvJ` from its pre-state to its post-state, given the N7 bounds at the post-state and
the configuration bounds. -/
theorem _root_.Blanc.GJointRunStep.gInvJ (hq : 2 * P.SLOTS_PER_EPOCH ≤ P.EFFECTIVE_BALANCE_INCREMENT)
    (hdel : 1 ≤ P.MIN_ATTESTATION_INCLUSION_DELAY) (hspe : 2 ≤ P.SLOTS_PER_EPOCH)
    (D : GJointRunStep (P := P) cfg ccfg bls) (hpre : GInvJ D.preState)
    (vb : D.postState.validatorCount ≤ 2 ^ 40) (bb : D.postState.builderCount ≤ 2 ^ 40) :
    GInvJ D.postState := by
  cases D with
  | pre D => trivial
  | crossing C =>
    have hu : GInv C.upgraded := crossFromFulu_inv (by omega) C.cross
    show GInv C.postB
    have hp : Gloas.processBlock (gloasCtx ccfg bls) C.postSlots C.block.message = .ok C.postB :=
      applySignedBlockWith_ok C.transition
    have hslots := C.slots
    unfold crossingSlots at hslots
    split at hslots
    · rw [← Except.ok.inj hslots] at hp
      exact GInv.processBlock hdel hspe hp hu vb bb
    · have ht : Gloas.stateTransition (gloasCtx ccfg bls) C.upgraded C.block = .ok C.postB := by
        rw [← processSlots_then_gloasBlockTransition, hslots]
        exact C.transition
      exact GInv.stateTransition hq hdel hspe ht hu vb bb
  | gloas D => exact GInv.stateTransition hq hdel hspe D.stateTransition hpre vb bb

namespace ValidJointG

variable {checkpoint : BlockChain} {anchor final : GJointState P}

/-- The anchor invariant is `GInvJ`. -/
theorem anchor_gInvJ (v : ValidJointG cfg ccfg bls checkpoint anchor final) : GInvJ anchor := by
  have h := v.anchorInv
  rcases anchor with _ | ⟨b, _, _⟩
  · trivial
  · exact h

/-- **The G3a invariants at every Gloas step's pre-state of a valid joint chain.** -/
theorem gInv_pre (v : ValidJointG cfg ccfg bls checkpoint anchor final) {j : Nat}
    {D : GloasStepData (P := P) cfg ccfg bls} (hD : v.run.steps[j]? = some (.gloas D)) : GInv D.preB := by
  suffices key : ∀ {s : GJointState P} (run : GJointRun cfg ccfg bls anchor s),
      (∀ st ∈ run.states, st.validatorCount ≤ 2 ^ 40) → (∀ st ∈ run.states, st.builderCount ≤ 2 ^ 40) →
      GInvJ s ∧ ∀ {j : Nat} {C : GJointRunStep (P := P) cfg ccfg bls}, run.steps[j]? = some C → GInvJ C.preState by
    exact (key v.run v.validatorsBound v.buildersBound).2 hD
  intro s run
  induction run with
  | nil => exact fun _ _ => ⟨v.anchor_gInvJ, fun h => by simp only [GJointRun.steps, List.getElem?_nil,
      reduceCtorEq] at h⟩
  | @snoc s run C hC ih =>
    intro hv hb
    have mem : ∀ st ∈ run.states, st ∈ (run.snoc C hC).states := fun st hst => by
      simp only [GJointRun.states, GJointRun.steps_snoc, List.map_append, List.mem_cons, List.mem_append] at hst ⊢
      rcases hst with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    have hpost : C.postState ∈ (run.snoc C hC).states := GJointRun.end_mem_states _
    obtain ⟨hs, hsteps⟩ := ih (fun st h => hv st (mem st h)) (fun st h => hb st (mem st h))
    have hpre : GInvJ C.preState := hC ▸ hs
    refine ⟨C.gInvJ v.quorumPositive v.inclusionDelay v.slotsPerEpoch hpre (hv _ hpost) (hb _ hpost),
      fun {j} {C'} h => ?_⟩
    rw [GJointRun.steps_snoc] at h
    by_cases hj : j < run.steps.length
    · rw [List.getElem?_append_left hj] at h
      exact hsteps h
    · rw [List.getElem?_append_right (Nat.le_of_not_lt hj), List.getElem?_singleton] at h
      split at h
      · cases h
        exact hpre
      · cases h

/-- The N7 bounds at a Gloas step's post-state. -/
theorem post_bounds (v : ValidJointG cfg ccfg bls checkpoint anchor final) {j : Nat}
    {D : GloasStepData (P := P) cfg ccfg bls} (hD : v.run.steps[j]? = some (.gloas D)) :
    D.postB.validators.toArray.size ≤ 2 ^ 40 ∧ D.postB.builders.toArray.size ≤ 2 ^ 40 := by
  have hmem : (GJointRunStep.gloas D).postState ∈ v.run.states :=
    List.mem_cons_of_mem _ (List.mem_map_of_mem (List.mem_of_getElem? hD))
  exact ⟨v.validatorsBound _ hmem, v.buildersBound _ hmem⟩

/-! ## B5(i): the builder balance equation -/

/-- **B5(i): the only balance-falling site, per Gloas step of a valid joint chain, in `ℕ` with no
saturation.** For a builder `bi` of the step's pre-state that keeps its incarnation through the step's deposit
loop (no request registers a fresh record at `bi`): the builder after the step is the same identity, and its
balance plus the withdrawals the step's `process_withdrawals` routes to it equals its balance before plus the
top-ups credited to it; each routed withdrawal fits the running balance. The G3a premises come from the anchor
and the run (`gInv_pre`), the registry bounds from N7. -/
theorem builder_balance_equation (v : ValidJointG cfg ccfg bls checkpoint anchor final) {j : Nat}
    {D : GloasStepData (P := P) cfg ccfg bls} (stepD : v.run.steps[j]? = some (.gloas D))
    {bi : Gloas.BuilderIndex} {bb : Gloas.Builder} (hb : D.preB.builders.toArray[bi.toNat]? = some bb)
    {trD : List (Gloas.BeaconState P)} (hD : builderDepositTrace ccfg bls D.postSlots D.block = .ok trD)
    (sameIncarnation : NoRegisterAt ccfg bls bi.toNat trD D.builderDeposits) :
    ∃ (ws : List JauneConsensus.Withdrawal) (bb' : Gloas.Builder),
      stepWithdrawals ccfg bls D.postSlots D.block.message = .ok ws ∧
      D.postB.builders.toArray[bi.toNat]? = some bb' ∧ SameIdentity bb bb' ∧
      bb'.balance.toNat + routedSum bi ws =
        bb.balance.toNat + creditedAt ccfg bls bi.toNat trD D.builderDeposits ∧
      (∀ k w, ws[k]? = some w → Routes bi w →
        routedSum bi (ws.take k) + w.amount.toNat ≤
          bb.balance.toNat + creditedAt ccfg bls bi.toNat trD D.builderDeposits) := by
  obtain ⟨g1, g3, g4, g5, g6, g7, g8, hA, fe⟩ := v.gInv_pre stepD
  obtain ⟨vb, bb'⟩ := v.post_bounds stepD
  exact D.view.builder_balance_equation v.quorumPositive v.slotsPerEpoch g5 g3 g4 g7 g8 fe hA vb bb' hb hD
    sameIncarnation

/-! ## B5(iv): carried withdrawals and the early return -/

/-- A Gloas state's delivered payload, if any, passed the envelope check against that state and its
built-upon chain. -/
def EnvChecked (cfg : ChainConfig) (ccfg : Config) (bls : Bool) : GJointState P → Prop
  | .gloas b exec (.delivered e r p) => verifyEnvelopeG cfg ccfg bls b exec e = .ok (r, p)
  | _ => True

theorem envChecked_of_deliverOpt {b : Gloas.BeaconState P} {exec : BlockChain}
    {eo : Option (Gloas.SignedExecutionPayloadEnvelope P)} {s' : GJointState P}
    (h : gloasDeliverOpt cfg ccfg bls b exec eo = .ok s') : EnvChecked cfg ccfg bls s' := by
  rcases gloasDeliverOpt_ok_iff.mp h with ⟨-, rfl⟩ | ⟨e, r, p, -, hv, rfl⟩
  · trivial
  · exact hv

theorem envChecked_post (C : GJointRunStep (P := P) cfg ccfg bls) : EnvChecked cfg ccfg bls C.postState := by
  cases C with
  | pre D => trivial
  | crossing C => exact envChecked_of_deliverOpt C.deliver
  | gloas D => exact envChecked_of_deliverOpt D.deliver

/-- **B5(iv): carried withdrawals.** A FULL step settles the payload its pre-state holds as delivered, and that
payload's withdrawals equal, as lists, the `payload_expected_withdrawals` of the step's pre-state: the post-block
state of the block the payload belongs to (the delivering run step's post-state, or the anchor), against which
the envelope was checked. -/
theorem carried_withdrawals_equal (v : ValidJointG cfg ccfg bls checkpoint anchor final) {j : Nat}
    {D : GloasStepData (P := P) cfg ccfg bls} (stepD : v.run.steps[j]? = some (.gloas D))
    {env : Gloas.SignedExecutionPayloadEnvelope P} {req : Gloas.NewPayloadRequest P} {post : BlockChain}
    (hfull : D.settle = .full env req post) :
    D.preParent = .delivered env req post ∧
      env.message.payload.withdrawals.toArray.toList = D.preB.payload_expected_withdrawals.toArray.toList := by
  obtain ⟨hp, -⟩ := D.view.settled_payload hfull
  have h0 : EnvChecked cfg ccfg bls anchor := by
    have := v.anchorPending
    rcases anchor with _ | ⟨b, exec, _ | _ | ⟨e, r, p⟩⟩ <;> exact this
  have hpre : EnvChecked cfg ccfg bls (GJointRunStep.gloas D).preState :=
    GJointRun.pre_of_post h0 envChecked_post v.run stepD
  simp only [GJointRunStep.preState, hp, EnvChecked] at hpre
  exact ⟨hp, (verifyEnvelopeG_ok_iff.mp hpre).2.1⟩

/-- **B5(iv): the EMPTY-parent early return, per run step.** A Gloas step that settles its parent EMPTY at a
post-slots state whose latest block hash is not the latest bid's withdraws nothing. -/
theorem withdrawals_early_return (v : ValidJointG cfg ccfg bls checkpoint anchor final) {j : Nat}
    {D : GloasStepData (P := P) cfg ccfg bls} (_stepD : v.run.steps[j]? = some (.gloas D))
    (hE : parentFull D.postSlots D.block.message = false)
    (hne : D.postSlots.latest_block_hash ≠ D.postSlots.latest_execution_payload_bid.block_hash) :
    stepWithdrawals ccfg bls D.postSlots D.block.message = .ok [] :=
  D.view.early_return hE hne

end ValidJointG

end Blanc.Lift.BuilderRequest
