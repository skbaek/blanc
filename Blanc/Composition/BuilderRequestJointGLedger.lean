import Blanc.Composition.BuilderRequestJointGBalance

/-!
# B5(iv) over a valid Gloas joint chain: the withdrawal ledger

Goal `eip8282-gloas-cross-layer-v1`, frozen statements rev 3.1 (Plans `recon/statements.md` B5 (iv); design.md
G3-11).

The withdrawals a Gloas step's `process_withdrawals` debits (`stepWithdrawals`, non-empty only past the early
return, so only when the parent settles FULL: `withdrawals_full`) become the post-block state's
`payload_expected_withdrawals`. Every following step settles EMPTY and carries them unchanged, until the first one
that settles FULL: that step builds upon exactly one payload, the delivered envelope's, which carries them as lists
(RBA's `carried_withdrawals_equal`, from G3-11 / the envelope check), and whose execution block credits each
address `Σ amount · 10^9` (the 7002 `processWithdrawalsState_toExecution_bal`, over Jaune's
`Withdrawal.toExecution`). If no later step settles FULL, they are still the final state's
`payload_expected_withdrawals`.

**The frame `ExpectedWithdrawalsFrame`.** The frame of `payload_expected_withdrawals`: Gloas `process_slots` keeps
the field; Gloas `process_block` keeps it over an EMPTY parent (the early return, CL:2074, and no other phase writes
it); over a FULL parent it ends as the withdrawals the step's `process_withdrawals` computed (CL:2086). It is proved
(`expectedWithdrawalsFrame_holds`) from the Mac's G3c frames, Jaune `Facts/Gloas/FirstBlockFrames.lean`, on this
Blanc's Jaune pin (c30cf0a5).
-/

namespace Blanc.Lift.BuilderRequest

open Jaune JauneConsensus ExecutionTrace Blanc JauneConsensus.Facts.Gloas JauneConsensus.Facts.Gloas.Inv

variable {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool}

/-- **G3c's expected-withdrawals frame** (proved: `expectedWithdrawalsFrame_holds`). -/
structure ExpectedWithdrawalsFrame (P : Preset) : Prop where
  /-- Gloas `process_slots` keeps `payload_expected_withdrawals`. -/
  slots : ∀ {ctx : Ctx} {s s' : Gloas.BeaconState P} {slot : Slot}, Gloas.processSlots ctx s slot = .ok s' →
    s'.payload_expected_withdrawals = s.payload_expected_withdrawals
  /-- Gloas `process_block` over an EMPTY parent keeps it. -/
  empty : ∀ {ctx : Ctx} {s s' : Gloas.BeaconState P} {blk : Gloas.BeaconBlock P},
    Gloas.processBlock ctx s blk = .ok s' → parentFull s blk = false →
    s'.payload_expected_withdrawals = s.payload_expected_withdrawals
  /-- Gloas `process_block` over a FULL parent leaves the withdrawals its `process_withdrawals` computed. -/
  full : ∀ {ccfg : Config} {bls : Bool} {s s' : Gloas.BeaconState P} {blk : Gloas.BeaconBlock P}
    {ws : List JauneConsensus.Withdrawal}, Gloas.processBlock (gloasCtx ccfg bls) s blk = .ok s' →
    parentFull s blk = true → stepWithdrawals ccfg bls s blk = .ok ws →
    s'.payload_expected_withdrawals.toArray.toList = ws

/-- Gloas `process_block` over an EMPTY parent keeps `payload_expected_withdrawals`, in any context: the
parent settlement is the identity, the bid then builds on `latest_block_hash`, so `process_withdrawals` returns
early, and no other phase writes the field (G3c's frames). -/
theorem processBlock_pew_of_empty {ctx : Ctx} {s s' : Gloas.BeaconState P} {blk : Gloas.BeaconBlock P}
    (h : Gloas.processBlock ctx s blk = .ok s') (hE : parentFull s blk = false) :
    s'.payload_expected_withdrawals = s.payload_expected_withdrawals := by
  obtain ⟨s1, s2, s3, s4, s5, s6, s7, h1, h2, h3, h4, h5, h6, h7, h8⟩ := processBlock_phases h
  have hpost := afterWithdrawals_pew h4 h5 h6 h7 h8
  obtain ⟨_, _, hm2⟩ := processBlockHeader_post h2
  have w3 := processWithdrawals_wFrame _ _ h3
  have b4 := processExecutionPayloadBid_post h4
  rcases processParentExecutionPayload_cases h1 with ⟨hs1, -⟩ | ⟨hpb, -⟩
  · subst hs1
    have hne : s2.latest_block_hash ≠ s2.latest_execution_payload_bid.block_hash := by
      intro heq
      have hpar : blk.body.signed_execution_payload_bid.message.parent_block_hash = s2.latest_block_hash := by
        rw [b4.2.2.1, w3.2.1]
      have : parentFull s1 blk = true := by
        unfold parentFull
        rw [hpar, heq, hm2]
        exact beq_self_eq_true _
      rw [this] at hE; cases hE
    rw [processWithdrawalsG_early_return s2 hne] at h3
    cases h3
    rw [hpost, hm2]
  · have : parentFull s blk = true := by unfold parentFull; rw [hpb]; exact beq_self_eq_true _
    rw [this] at hE; cases hE

/-- **The expected-withdrawals frame holds** (G3c's `processSlots_pew`, `processBlock_pew_of_empty` and
`processBlock_payloadExpectedWithdrawals`). -/
theorem expectedWithdrawalsFrame_holds : ExpectedWithdrawalsFrame P where
  slots h := processSlots_pew h
  empty h hE := processBlock_pew_of_empty h hE
  full h hF hws := by
    obtain ⟨ws', hws', he⟩ := (processBlock_payloadExpectedWithdrawals h).2 hF
    rw [hws] at hws'
    cases hws'
    exact he

/-! ## One step -/

/-- **A step that withdraws anything settled its parent FULL**: over an EMPTY parent the block's bid builds on
`latest_block_hash` (CL:2193), which then differs from the latest bid's `block_hash`, so `process_withdrawals`
returns early. -/
theorem _root_.Blanc.GloasStepData.withdrawals_full (D : GloasStepData (P := P) cfg ccfg bls)
    {ws : List JauneConsensus.Withdrawal} (hws : stepWithdrawals ccfg bls D.postSlots D.block.message = .ok ws)
    (hne : ws ≠ []) : parentFull D.postSlots D.block.message = true := by
  cases hf : parentFull D.postSlots D.block.message with
  | true => rfl
  | false =>
    exfalso
    have hb := (processBlock_latestBlockHash (gloasBlockTransition_processBlock_eq D.transition)).2
    rw [hf, ite_eq_right (by simp only [Bool.false_eq_true, not_false_eq_true])] at hb
    have hl : D.postSlots.latest_block_hash ≠ D.postSlots.latest_execution_payload_bid.block_hash := by
      intro he
      unfold parentFull at hf
      rw [hb, he, beq_self_eq_true] at hf
      cases hf
    have h0 : stepWithdrawals ccfg bls D.postSlots D.block.message = .ok [] := D.view.early_return hf hl
    rw [hws] at h0
    exact hne (Except.ok.inj h0)

/-- A step's post-parent is never `.landed`. -/
theorem _root_.Blanc.GloasStepData.postParent_ne_landed (D : GloasStepData (P := P) cfg ccfg bls) :
    D.postParent ≠ .landed := by
  rcases gloasDeliverOpt_ok_iff.mp D.deliver with ⟨-, h⟩ | ⟨e, req, postE, -, -, h⟩ <;>
    (injection h with _ _ h3; rw [h3]; exact fun h => by cases h)

/-! ## Consecutive steps of a run -/

end Blanc.Lift.BuilderRequest

namespace Blanc.GJointRun

open Jaune JauneConsensus

variable {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool} {s₀ : GJointState P}

/-- The run ends where its last step ends. -/
theorem last_post : {s : GJointState P} → (run : GJointRun cfg ccfg bls s₀ s) → {k : Nat} →
    {C : GJointRunStep (P := P) cfg ccfg bls} → run.steps[k]? = some C → k + 1 = run.steps.length →
    s = C.postState
  | _, .nil, _, _, h, _ => by simp only [steps, List.getElem?_nil, reduceCtorEq] at h
  | _, .snoc run B _, k, C, hC, hl => by
    rw [steps_snoc] at hC hl
    rw [List.length_append, List.length_singleton] at hl
    rw [List.getElem?_append_right (by omega), show k - run.steps.length = 0 by omega] at hC
    cases hC
    rfl

/-- The step after step `k` starts where step `k` ends. -/
theorem pre_succ : {s : GJointState P} → (run : GJointRun cfg ccfg bls s₀ s) → {k : Nat} →
    {C C' : GJointRunStep (P := P) cfg ccfg bls} → run.steps[k]? = some C → run.steps[k + 1]? = some C' →
    C'.preState = C.postState
  | _, .nil, _, _, _, h, _ => by simp only [steps, List.getElem?_nil, reduceCtorEq] at h
  | _, .snoc run B hB, k, C, C', hC, hC' => by
    rw [steps_snoc] at hC hC'
    have hk1 : k + 1 < run.steps.length + 1 := by
      have := (List.getElem?_eq_some_iff.mp hC').1
      rwa [List.length_append, List.length_singleton] at this
    by_cases hk : k + 1 < run.steps.length
    · rw [List.getElem?_append_left hk] at hC'
      rw [List.getElem?_append_left (by omega)] at hC
      exact pre_succ run hC hC'
    · have hkk : k + 1 = run.steps.length := by omega
      rw [List.getElem?_append_right (by omega), hkk, Nat.sub_self] at hC'
      rw [List.getElem?_append_left (by omega)] at hC
      cases hC'
      rw [hB]
      exact last_post run hC hkk

end Blanc.GJointRun

namespace Blanc.Lift.BuilderRequest

open Jaune JauneConsensus ExecutionTrace Blanc JauneConsensus.Facts.Gloas JauneConsensus.Facts.Gloas.Inv

variable {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool}

/-! ## B5(iv) over a valid joint chain -/

namespace ValidJointG

variable {checkpoint : BlockChain} {anchor final : GJointState P}

/-- Step `k` settles its parent FULL. -/
def FullAt (v : ValidJointG cfg ccfg bls checkpoint anchor final) (k : Nat) : Prop :=
  ∃ Dk : GloasStepData (P := P) cfg ccfg bls, v.run.steps[k]? = some (.gloas Dk) ∧
    parentFull Dk.postSlots Dk.block.message = true

/-- Through EMPTY steps after a withdrawing step `j`, every step is a Gloas step that builds upon nothing and
ends with `payload_expected_withdrawals = ws`. -/
theorem carry (v : ValidJointG cfg ccfg bls checkpoint anchor final) (frame : ExpectedWithdrawalsFrame P)
    {j : Nat} {D : GloasStepData (P := P) cfg ccfg bls} (stepD : v.run.steps[j]? = some (.gloas D))
    {ws : List JauneConsensus.Withdrawal} (hpost : D.postB.payload_expected_withdrawals.toArray.toList = ws) :
    ∀ k, j ≤ k → k < v.run.steps.length → (∀ i, j < i → i ≤ k → ¬ v.FullAt i) →
      ∃ Dk : GloasStepData (P := P) cfg ccfg bls, v.run.steps[k]? = some (.gloas Dk) ∧
        Dk.postB.payload_expected_withdrawals.toArray.toList = ws ∧ (j < k → Dk.kept = []) := by
  intro k hjk
  induction k, hjk using Nat.le_induction with
  | base => exact fun _ _ => ⟨D, stepD, hpost, fun h => absurd h (Nat.lt_irrefl _)⟩
  | succ k hjk ih =>
    intro hk hnf
    obtain ⟨Dk, hDk, hw, -⟩ := ih (by omega) (fun i h1 h2 => hnf i h1 (by omega))
    obtain ⟨C', hC'⟩ : ∃ C', v.run.steps[k + 1]? = some C' := ⟨_, List.getElem?_eq_getElem hk⟩
    have hpre := GJointRun.pre_succ v.run hDk hC'
    cases C' with
    | pre _ => cases hpre
    | crossing _ => cases hpre
    | gloas D' =>
      simp only [GJointRunStep.preState, GJointRunStep.postState, GJointState.gloas.injEq] at hpre
      obtain ⟨hb, -, -⟩ := hpre
      have hf : parentFull D'.postSlots D'.block.message = false := by
        cases h : parentFull D'.postSlots D'.block.message with
        | false => rfl
        | true => exact absurd ⟨D', hC', h⟩ (hnf (k + 1) (by omega) (Nat.le_refl _))
      refine ⟨D', hC', ?_, fun _ => ?_⟩
      · rw [frame.empty (gloasBlockTransition_processBlock_eq D'.transition) hf, frame.slots D'.slots, hb, hw]
      · rcases settleParent_ok_iff.mp D'.settleOk with ⟨hf', -⟩ | ⟨hf', -⟩ | ⟨-, -, -, hs⟩
        · rw [hf] at hf'; cases hf'
        · rw [hf] at hf'; cases hf'
        · rcases D'.keptSpec with ⟨_, _, _, h, -⟩ | ⟨-, hk'⟩
          · rw [hs] at h; cases h
          · exact hk'

/-- **B5(iv): the withdrawal ledger.** The withdrawals `ws` a Gloas step `j` of a valid joint chain debits through
`process_withdrawals` (non-empty, hence past the early return) are, as a whole list, either

* carried by the first payload built upon after step `j`: every step strictly between `j` and some `i > j` builds
  upon nothing, and step `i` settles FULL over a delivered envelope whose payload carries exactly `ws`, builds upon
  exactly that payload's block (block `preBlocks.length + payloadIndex i` of the joint history), whose execution
  withdrawals are `ws` converted (`Withdrawal.toExecution`), crediting each address `a` exactly
  `Σ_{w ∈ ws, w.address = a} w.amount · 10^9` (modulo `2^256`, exact: the 7002 per-address lemma); or
* still outstanding: no step after `j` builds upon anything, and they are the final state's
  `payload_expected_withdrawals`.

Adaptations: `D.expectedWithdrawals` is RBA's `stepWithdrawals`, and `nonEarly` is `w ∈ ws` (a step that returns
early withdraws `[]`), stated for the whole list; the frame of `payload_expected_withdrawals` is
`expectedWithdrawalsFrame_holds` (G3c). -/
theorem withdrawal_ledger (v : ValidJointG cfg ccfg bls checkpoint anchor final)
    {j : Nat} {D : GloasStepData (P := P) cfg ccfg bls} (stepD : v.run.steps[j]? = some (.gloas D))
    {ws : List JauneConsensus.Withdrawal} (hws : stepWithdrawals ccfg bls D.postSlots D.block.message = .ok ws)
    {w : JauneConsensus.Withdrawal} (hw : w ∈ ws) :
    (∃ (i : Nat) (D' : GloasStepData (P := P) cfg ccfg bls) (env : Gloas.SignedExecutionPayloadEnvelope P)
        (req : Gloas.NewPayloadRequest P) (post : BlockChain) (b : KeptBlock),
        j < i ∧ v.run.steps[i]? = some (.gloas D') ∧ D'.settle = .full env req post ∧ D'.kept = [b] ∧
        (∀ k, j < k → k < i → ∃ Dk : GloasStepData (P := P) cfg ccfg bls,
          v.run.steps[k]? = some (.gloas Dk) ∧ Dk.kept = []) ∧
        v.blocks[v.preBlocks.length + v.run.payloadIndex i]? = some b ∧
        env.message.payload.withdrawals.toArray.toList = ws ∧
        b.block.wds = ws.map JauneConsensus.Withdrawal.toExecution ∧
        ∀ (pre : State) (a : Adr), ((processWithdrawalsState pre b.block.wds).bal a).toNat =
          ((pre.bal a).toNat + ((ws.filter fun w => decide (w.address = a)).map
            fun w => w.amount.toNat * 10 ^ 9).sum) % 2 ^ 256) ∨
      (∃ (b : Gloas.BeaconState P) (exec : BlockChain) (par : ParentPayload P), final = .gloas b exec par ∧
        (∀ k, j < k → k < v.run.steps.length → ∃ Dk : GloasStepData (P := P) cfg ccfg bls,
          v.run.steps[k]? = some (.gloas Dk) ∧ Dk.kept = []) ∧
        b.payload_expected_withdrawals.toArray.toList = ws) := by
  classical
  have frame : ExpectedWithdrawalsFrame P := expectedWithdrawalsFrame_holds
  have hfull : parentFull D.postSlots D.block.message = true :=
    D.withdrawals_full hws (List.ne_nil_of_mem hw)
  have hpost := frame.full (gloasBlockTransition_processBlock_eq D.transition) hfull hws
  have hj : j < v.run.steps.length := (List.getElem?_eq_some_iff.mp stepD).1
  have hcarry := v.carry frame stepD hpost
  by_cases hex : ∃ i, j < i ∧ v.FullAt i
  · left
    let i := Nat.find hex
    obtain ⟨hji, D', hD', hf'⟩ := Nat.find_spec hex
    have hmin : ∀ k, j < k → k < i → ¬ v.FullAt k := fun k h1 h2 hk => Nat.find_min hex h2 ⟨h1, hk⟩
    have hi : i < v.run.steps.length := (List.getElem?_eq_some_iff.mp hD').1
    obtain ⟨Dp, hDp, hwp, -⟩ := hcarry (i - 1) (by omega) (by omega)
      (fun k h1 h2 => hmin k h1 (by omega))
    have hpre := GJointRun.pre_succ v.run hDp (show v.run.steps[i - 1 + 1]? = some (.gloas D') by
      rw [show i - 1 + 1 = i by omega]; exact hD')
    simp only [GJointRunStep.preState, GJointRunStep.postState, GJointState.gloas.injEq] at hpre
    obtain ⟨hb, -, hpar⟩ := hpre
    obtain ⟨env, req, post, hs⟩ : ∃ env req post, D'.settle = .full env req post := by
      rcases settleParent_ok_iff.mp D'.settleOk with ⟨-, env, req, post, -, -, -, hs⟩ | ⟨-, hl, -⟩ | ⟨hf, -⟩
      · exact ⟨env, req, post, hs⟩
      · exact absurd (hpar.symm.trans hl) Dp.postParent_ne_landed
      · rw [hf'] at hf; cases hf
    obtain ⟨hp, hcw⟩ := v.carried_withdrawals_equal hD' hs
    obtain ⟨b, hk, hblk, -⟩ := D'.kept_of_full hs
    have hpay : env.message.payload.withdrawals.toArray.toList = ws := by rw [hcw, hb, hwp]
    have hreq : req.execution_payload = env.message.payload := by
      have h0 : EnvChecked cfg ccfg bls anchor := by
        have := v.anchorPending
        rcases anchor with _ | ⟨b, exec, _ | _ | ⟨e, r, p⟩⟩ <;> exact this
      have hpre : EnvChecked cfg ccfg bls (GJointRunStep.gloas D').preState :=
        GJointRun.pre_of_post h0 envChecked_post v.run hD'
      simp only [GJointRunStep.preState, hp, EnvChecked] at hpre
      exact envelopeNewPayloadRequest_payload (verifyEnvelopeG_ok_iff.mp hpre).2.2.1
    have hwds : b.block.wds = ws.map JauneConsensus.Withdrawal.toExecution := by
      rw [hblk, ← hpay]
      simp only [payloadToBlockG, Gloas.ExecutionPayload.executionWithdrawals, hreq]
    refine ⟨i, D', env, req, post, b, hji, hD', hs, hk, fun k h1 h2 => ?_, v.blocks_getElem?_full hD' hk,
      hpay, hwds, fun pre a => ?_⟩
    · obtain ⟨Dk, hDk, -, hkk⟩ := hcarry k (by omega) (by omega) (fun m h1' h2' => hmin m h1' (by omega))
      exact ⟨Dk, hDk, hkk h1⟩
    · rw [hwds]
      exact processWithdrawalsState_toExecution_bal ws pre a
  · right
    have hnf : ∀ k, j < k → ¬ v.FullAt k := fun k h1 hk => hex ⟨k, h1, hk⟩
    obtain ⟨Dl, hDl, hwl, -⟩ := hcarry (v.run.steps.length - 1) (by omega) (by omega)
      (fun k h1 _ => hnf k h1)
    have hfin := GJointRun.last_post v.run hDl (by omega)
    refine ⟨Dl.postB, Dl.postExec, Dl.postParent, hfin, fun k h1 h2 => ?_, hwl⟩
    obtain ⟨Dk, hDk, -, hkk⟩ := hcarry k (by omega) h2 (fun m h1' _ => hnf m h1')
    exact ⟨Dk, hDk, hkk h1⟩

end ValidJointG

end Blanc.Lift.BuilderRequest
