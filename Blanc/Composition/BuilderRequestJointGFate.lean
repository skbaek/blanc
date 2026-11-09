import Blanc.Composition.BuilderRequestJointG
import Blanc.Lift.BuilderRequest.RequestCodecG
import JauneConsensus.Facts.Gloas.StepB246
import JauneConsensus.Facts.Gloas.BuilderAuth
import JauneConsensus.Facts.Gloas.BuilderWitnesses

/-!
# B2 and B4 over a valid Gloas joint chain: deposit fate, exit fate, outcome meanings

Goal `eip8282-gloas-cross-layer-v1`, frozen statements rev 3.1 (Plans `recon/statements.md` B2, B4).

The run-level seam (statements.md §0.7):

* `ParentTied`: a delivered payload is the engine's verdict over the built-upon chain and carries the
  envelope's requests; it holds at the anchor (`AnchorPendingTrace`) and after every step, hence at every
  step's pre-state (`GJointRun.pre_of_post`);
* `GJointRun.block_source`: every built-upon block of the run is a pre-Gloas step's covered-fork block, or the
  payload a Gloas step settles FULL, at that step's `payloadIndex`;
* `ValidJointG.full_output`: that payload's block outputs `get_execution_requests_list` of the settling
  block's `parent_execution_requests`, so it emits exactly the settling block's builder deposits (exits) as
  records (`RequestCodecG`).

The headlines compose Blanc's occurrence-indexed `history_fate` (execution half) with Jaune's per-step
`GStepView.builderDeposit_applied` / `builderExit_applied` (consensus half, traces read at `postSlots`).
-/

namespace Blanc.Lift.BuilderRequest

open Jaune JauneConsensus ExecutionTrace ChainLink Blanc JauneConsensus.Facts.Gloas Occurrence

variable {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool}

/-! ## A Gloas run step, opened -/

/-- A Gloas run step's view (Jaune's `GStepView`), with the step's own post-slots state and settlement. -/
def _root_.Blanc.GloasStepData.view (D : GloasStepData (P := P) cfg ccfg bls) :
    GStepView cfg ccfg bls D.preB D.preExec D.preParent D.block D.env? D.postB D.postExec D.postParent where
  postSlots := D.postSlots
  settle := D.settle
  slots := D.slots
  settled := D.settleOk
  block := D.transition
  stepEnd := by
    rcases gloasDeliverOpt_ok_iff.mp D.deliver with ⟨hn, he⟩ | ⟨e, req, postE, he, hv, hs⟩
    · injection he with _ _ h3
      exact Or.inl ⟨hn, h3⟩
    · injection hs with _ _ h3
      exact Or.inr ⟨e, req, postE, he, hv, h3⟩

/-- A step that settles FULL builds upon exactly the settled payload's block, an Amsterdam block. -/
theorem _root_.Blanc.GloasStepData.kept_of_full (D : GloasStepData (P := P) cfg ccfg bls)
    {env : Gloas.SignedExecutionPayloadEnvelope P} {req : Gloas.NewPayloadRequest P} {post : BlockChain}
    (hs : D.settle = .full env req post) :
    ∃ b, D.kept = [b] ∧ b.block = payloadToBlockG req ∧ b.fork = .amsterdam := by
  rcases D.keptSpec with ⟨env', req', post', hs', b, hk, hb, hf⟩ | ⟨hs', -⟩
  · rw [hs] at hs'
    cases hs'
    exact ⟨b, hk, hb, hf⟩
  · rcases hs' with h | h <;> rw [hs] at h <;> cases h

/-! ## The delivered payload is tied to its envelope -/

/-- A Gloas state's delivered payload, if any, is the engine's verdict on its request over the built-upon
chain, and the request carries the envelope's execution requests. -/
def ParentTied (cfg : ChainConfig) : GJointState P → Prop
  | .gloas _ exec (.delivered e req post) =>
    engineVerdictG cfg exec req = .ok post ∧ req.execution_requests = e.message.execution_requests
  | _ => True

theorem parentTied_of_verify {state : Gloas.BeaconState P} {exec : BlockChain}
    {e : Gloas.SignedExecutionPayloadEnvelope P} {req : Gloas.NewPayloadRequest P} {post : BlockChain}
    (hv : verifyEnvelopeG cfg ccfg bls state exec e = .ok (req, post)) (b : Gloas.BeaconState P) :
    ParentTied cfg (.gloas b exec (.delivered e req post)) := by
  obtain ⟨-, -, hreq, he⟩ := verifyEnvelopeG_ok_iff.mp hv
  exact ⟨he, envelopeNewPayloadRequest_execution_requests hreq⟩

theorem parentTied_of_deliverOpt {post : Gloas.BeaconState P} {exec : BlockChain}
    {env? : Option (Gloas.SignedExecutionPayloadEnvelope P)} {s' : GJointState P}
    (h : gloasDeliverOpt cfg ccfg bls post exec env? = .ok s') : ParentTied cfg s' := by
  rcases gloasDeliverOpt_ok_iff.mp h with ⟨-, rfl⟩ | ⟨e, req, postE, -, hv, rfl⟩
  · trivial
  · exact parentTied_of_verify hv post

/-- Every run step's post-state is tied. -/
theorem _root_.Blanc.GJointRunStep.postState_tied (D : GJointRunStep (P := P) cfg ccfg bls) : ParentTied cfg D.postState := by
  cases D with
  | pre D => trivial
  | crossing D => exact parentTied_of_deliverOpt D.deliver
  | gloas D => exact parentTied_of_deliverOpt D.deliver

/-- A delivered anchor payload is tied. -/
theorem AnchorPendingTrace.tied {s : GJointState P} (h : AnchorPendingTrace cfg ccfg bls s) : ParentTied cfg s := by
  rcases s with _ | ⟨b, exec, _ | _ | ⟨e, req, post⟩⟩
  all_goals first | trivial | exact parentTied_of_verify h b

/-! ## Runs: pre-states, block sources, payload indices -/

end Blanc.Lift.BuilderRequest

namespace Blanc.GJointRun

open Jaune JauneConsensus ExecutionTrace

variable {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool} {s₀ : GJointState P}

/-- A property of the start and of every step's post-state holds at the run's end. -/
theorem end_of_post {Q : GJointState P → Prop} (h₀ : Q s₀)
    (hpost : ∀ D : GJointRunStep (P := P) cfg ccfg bls, Q D.postState) :
    {s : GJointState P} → GJointRun cfg ccfg bls s₀ s → Q s
  | _, .nil => h₀
  | _, .snoc _ D _ => hpost D

/-- A property of the start and of every step's post-state holds at every step's pre-state. -/
theorem pre_of_post {Q : GJointState P → Prop} (h₀ : Q s₀)
    (hpost : ∀ D : GJointRunStep (P := P) cfg ccfg bls, Q D.postState) :
    {s : GJointState P} → (run : GJointRun cfg ccfg bls s₀ s) → {j : Nat} →
    {D : GJointRunStep (P := P) cfg ccfg bls} → run.steps[j]? = some D → Q D.preState
  | _, .nil, _, _, h => by simp only [steps, List.getElem?_nil, reduceCtorEq] at h
  | _, .snoc run C hC, j, D, h => by
    rw [steps_snoc] at h
    by_cases hj : j < run.steps.length
    · rw [List.getElem?_append_left hj] at h
      exact pre_of_post h₀ hpost run h
    · rw [List.getElem?_append_right (Nat.le_of_not_lt hj), List.getElem?_singleton] at h
      split at h
      · cases h
        exact hC ▸ end_of_post h₀ hpost run
      · cases h

/-- **Where a built-upon block of a run comes from.** Every block of `run.blocks` is the covered-fork block of
a pre-Gloas step, or the payload block a Gloas step settles FULL; either way it is the step's only block and
sits at the step's `payloadIndex`. -/
theorem block_source {s : GJointState P} (run : GJointRun cfg ccfg bls s₀ s) {i : Nat}
    (hi : i < run.blocks.length) :
    ∃ j, run.payloadIndex j = i ∧
      ((∃ D : PreStepData (P := P) cfg ccfg bls, run.steps[j]? = some (.pre D) ∧
          run.blocks[i].fork ≠ .amsterdam) ∨
        ∃ (D : GloasStepData (P := P) cfg ccfg bls) (env : Gloas.SignedExecutionPayloadEnvelope P)
          (req : Gloas.NewPayloadRequest P) (post : BlockChain), run.steps[j]? = some (.gloas D) ∧
          D.settle = .full env req post ∧ D.kept = [run.blocks[i]]) := by
  obtain ⟨j, k, hj, hk, pos⟩ := Blanc.List.exists_flatMap_position GJointRunStep.kept run.steps hi
  have get := Blanc.List.getElem?_flatMap_position GJointRunStep.kept run.steps hj hk
  rw [pos] at get
  change run.blocks[i]? = _ at get
  rw [List.getElem?_eq_getElem hi] at get
  have hsj : run.steps[j]? = some run.steps[j] := List.getElem?_eq_getElem hj
  generalize run.steps[j] = D at hk get hsj
  refine ⟨j, ?_⟩
  cases D with
  | pre D =>
    simp only [GJointRunStep.kept, List.length_singleton, Nat.lt_one_iff] at hk
    subst hk
    simp only [GJointRunStep.kept, List.getElem?_cons_zero, Option.some.injEq] at get
    refine ⟨by rw [Nat.add_zero] at pos; exact pos, Or.inl ⟨D, hsj, ?_⟩⟩
    rw [get]
    intro h
    exact absurd (h ▸ D.stepTrace.trace.covered : CoveredFork .amsterdam) (by decide)
  | crossing D => simp only [GJointRunStep.kept, List.length_nil, Nat.not_lt_zero] at hk
  | gloas D =>
    cases hs : D.settle with
    | full env req post =>
      obtain ⟨b, hb, -, -⟩ := D.kept_of_full hs
      simp only [GJointRunStep.kept, hb, List.length_singleton, Nat.lt_one_iff] at hk
      subst hk
      simp only [GJointRunStep.kept, hb, List.getElem?_cons_zero, Option.some.injEq] at get
      refine ⟨by rw [Nat.add_zero] at pos; exact pos, Or.inr ⟨D, env, req, post, hsj, hs, ?_⟩⟩
      rw [hb, get]
    | landed =>
      rcases D.keptSpec with ⟨_, _, _, h, -⟩ | ⟨-, hk'⟩
      · rw [hs] at h; cases h
      · simp only [GJointRunStep.kept, hk', List.length_nil, Nat.not_lt_zero] at hk
    | empty =>
      rcases D.keptSpec with ⟨_, _, _, h, -⟩ | ⟨-, hk'⟩
      · rw [hs] at h; cases h
      · simp only [GJointRunStep.kept, hk', List.length_nil, Nat.not_lt_zero] at hk

/-- Step `j`'s own blocks begin at `payloadIndex j`. -/
theorem blocks_getElem?_payloadIndex {s : GJointState P} (run : GJointRun cfg ccfg bls s₀ s) {j : Nat}
    {D : GJointRunStep (P := P) cfg ccfg bls} {b : KeptBlock} (hD : run.steps[j]? = some D)
    (hk : D.kept = [b]) : run.blocks[run.payloadIndex j]? = some b := by
  obtain ⟨before, after, hb, hl, -, -⟩ := run.extendsBy hD
  rw [hb, hk, ← hl, List.append_assoc, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
  rfl

/-- A step with blocks moves the payload index past them. -/
theorem payloadIndex_lt {s : GJointState P} (run : GJointRun cfg ccfg bls s₀ s) {j j' : Nat}
    {D : GJointRunStep (P := P) cfg ccfg bls} (hD : run.steps[j]? = some D) (hne : D.kept ≠ [])
    (hjj : j < j') : run.payloadIndex j < run.payloadIndex j' := by
  have hj : j < run.steps.length := (List.getElem?_eq_some_iff.mp hD).1
  have e : run.steps.take j' = run.steps.take (j + 1) ++ (run.steps.take j').drop (j + 1) := by
    conv_lhs => rw [← List.take_append_drop (j + 1) (run.steps.take j')]
    rw [List.take_take, Nat.min_eq_left (by omega)]
  have e1 : run.steps.take (j + 1) = run.steps.take j ++ [D] := by
    rw [List.take_add_one, hD]; rfl
  have hpos : 0 < D.kept.length := List.length_pos_iff.mpr hne
  unfold payloadIndex
  rw [e, e1, List.flatMap_append, List.flatMap_append, List.length_append, List.length_append]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  omega

/-- Two steps with blocks at the same payload index are the same step. -/
theorem eq_of_payloadIndex_eq {s : GJointState P} (run : GJointRun cfg ccfg bls s₀ s) {j j' : Nat}
    {D D' : GJointRunStep (P := P) cfg ccfg bls} (hD : run.steps[j]? = some D) (hD' : run.steps[j']? = some D')
    (hne : D.kept ≠ []) (hne' : D'.kept ≠ []) (he : run.payloadIndex j = run.payloadIndex j') : j = j' := by
  rcases Nat.lt_trichotomy j j' with h | h | h
  · exact absurd he (Nat.ne_of_lt (run.payloadIndex_lt hD hne h))
  · exact h
  · exact absurd he.symm (Nat.ne_of_lt (run.payloadIndex_lt hD' hne' h))

end Blanc.GJointRun

namespace Blanc.Lift.BuilderRequest

open Jaune JauneConsensus ExecutionTrace ChainLink Blanc JauneConsensus.Facts.Gloas Occurrence

variable {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool}

/-! ## The payload block's requests -/

namespace ValidJointG

variable {checkpoint : BlockChain} {anchor final : GJointState P}

/-- Every step's pre-state is tied. -/
theorem pre_tied (v : ValidJointG cfg ccfg bls checkpoint anchor final) {j : Nat}
    {D : GJointRunStep (P := P) cfg ccfg bls} (hD : v.run.steps[j]? = some D) : ParentTied cfg D.preState :=
  GJointRun.pre_of_post v.anchorPending.tied GJointRunStep.postState_tied v.run hD

/-- **The settled payload's block outputs the settling block's requests.** A Gloas step that settles FULL
builds upon a block whose output requests are `get_execution_requests_list` of the step block's
`parent_execution_requests` (the envelope's, by value). -/
theorem full_output (v : ValidJointG cfg ccfg bls checkpoint anchor final) {j : Nat}
    {D : GloasStepData (P := P) cfg ccfg bls} (hD : v.run.steps[j]? = some (.gloas D))
    {env : Gloas.SignedExecutionPayloadEnvelope P} {req : Gloas.NewPayloadRequest P} {post : BlockChain}
    (hs : D.settle = .full env req post) {b : KeptBlock} (hk : D.kept = [b]) :
    b.output.requests = Gloas.getExecutionRequestsList D.requests := by
  obtain ⟨-, hp, hreq, he⟩ := D.view.full_iff.mp hs
  have tied : ParentTied cfg (.gloas D.preB D.preExec D.preParent) := v.pre_tied hD
  rw [hp] at tied
  obtain ⟨hv, hx⟩ := tied
  obtain ⟨st, bout, hbody, hr, -⟩ := engineVerdictG_requests hv
  obtain ⟨b', hb', hblk, hf'⟩ := D.kept_of_full hs
  rw [hk] at hb'
  obtain rfl := List.head_eq_of_cons_eq hb'
  have hkh := D.keptHistory
  rw [hk] at hkh
  obtain ⟨hnil, step⟩ := KeptHistory.snoc_inv (blocks := []) hkh
  have hpar := KeptHistory.nil_inv hnil
  have happ := step.body.applied
  simp only [KeptBlock.benv, hpar, hf', hblk] at happ
  rw [hbody] at happ
  obtain ⟨-, rfl⟩ := Prod.mk.inj (Except.ok.inj happ)
  rw [hr, hx]
  exact congrArg _ hreq.symm

/-- **The source of an emitting run block.** A block of the joint history past the prefix that emits a record
of a builder contract is the payload block of exactly one Gloas step that settles FULL, at that step's payload
index, and outputs the step block's requests. -/
theorem emitting_source (v : ValidJointG cfg ccfg bls checkpoint anchor final) {c : Delivery.Contract} {R : Reading c}
    {ty : UInt8} (hcov : ∀ b ∈ v.blocks, b.fork ≠ .amsterdam → blockEmissions R ty b = [])
    {bj k : Nat} (hbj : bj < v.blocks.length) (hpre : v.preBlocks.length ≤ bj)
    (hk : k < (blockEmissions R ty v.blocks[bj]).length) :
    ∃ (j : Nat) (D : GloasStepData (P := P) cfg ccfg bls) (env : Gloas.SignedExecutionPayloadEnvelope P)
      (req : Gloas.NewPayloadRequest P) (post : BlockChain),
      v.run.steps[j]? = some (.gloas D) ∧ D.settle = .full env req post ∧
      v.run.payloadIndex j = bj - v.preBlocks.length ∧ D.kept = [v.blocks[bj]] ∧
      v.blocks[bj].output.requests = Gloas.getExecutionRequestsList D.requests := by
  have hi : bj - v.preBlocks.length < v.run.blocks.length := by
    have : v.blocks.length = v.preBlocks.length + v.run.blocks.length := List.length_append
    omega
  have hget : v.blocks[bj] = v.run.blocks[bj - v.preBlocks.length] := List.getElem_append_right hpre
  obtain ⟨j, hj, hsrc⟩ := v.run.block_source hi
  rcases hsrc with ⟨D, -, hf⟩ | ⟨D, env, req, post, hD, hs, hk'⟩
  · rw [← hget] at hf
    rw [hcov _ (List.getElem_mem hbj) hf] at hk
    exact absurd hk (Nat.not_lt_zero _)
  · rw [← hget] at hk'
    exact ⟨j, D, env, req, post, hD, hs, hj, hk', v.full_output hD hs hk'⟩

/-- Two FULL Gloas steps whose payload blocks have the same index are the same step. -/
theorem full_step_unique (v : ValidJointG cfg ccfg bls checkpoint anchor final) {j j' : Nat}
    {D D' : GloasStepData (P := P) cfg ccfg bls} (hD : v.run.steps[j]? = some (.gloas D))
    (hD' : v.run.steps[j']? = some (.gloas D')) {b b' : KeptBlock} (hk : D.kept = [b]) (hk' : D'.kept = [b'])
    (he : v.run.payloadIndex j = v.run.payloadIndex j') : j = j' :=
  v.run.eq_of_payloadIndex_eq hD hD' (by simp only [GJointRunStep.kept, hk]; exact List.cons_ne_nil _ _)
    (by simp only [GJointRunStep.kept, hk']; exact List.cons_ne_nil _ _) he

/-- The payload block of a FULL step `j` is block `preBlocks.length + payloadIndex j` of the joint history. -/
theorem blocks_getElem?_full (v : ValidJointG cfg ccfg bls checkpoint anchor final) {j : Nat}
    {D : GloasStepData (P := P) cfg ccfg bls} (hD : v.run.steps[j]? = some (.gloas D)) {b : KeptBlock}
    (hk : D.kept = [b]) : v.blocks[v.preBlocks.length + v.run.payloadIndex j]? = some b := by
  rw [List.getElem?_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
  exact v.run.blocks_getElem?_payloadIndex hD hk

/-- At the deposit contract, a covered-fork block of the joint history emits nothing. -/
theorem deposit_covered (v : ValidJointG cfg ccfg bls checkpoint anchor final) :
    ∀ b ∈ v.blocks, b.fork ≠ .amsterdam → Deposit.Indexed.blockEmissions b = [] := fun b hb hf => by
  obtain ⟨pre, post, split⟩ := List.append_of_mem hb
  exact ((Deposit.Indexed.history_block v.depositClean split).2.1 hf).1

/-- At the exit contract, a covered-fork block of the joint history emits nothing. -/
theorem exit_covered (v : ValidJointG cfg ccfg bls checkpoint anchor final) :
    ∀ b ∈ v.blocks, b.fork ≠ .amsterdam → Exit.Indexed.blockEmissions b = [] := fun b hb hf => by
  obtain ⟨pre, post, split⟩ := List.append_of_mem hb
  exact ((Exit.Indexed.history_block v.exitClean split).2.1 hf).1

/-! ## B2: deposit fate -/

/-- **B2: every committed deposit submission on the built-upon history has exactly one fate.** It was
(a) emitted by a block of the pre-anchor history; or (b) emitted by a run block, as record `k` of block `bj`
(`history_fate`'s unique pair), and then applied by the Gloas step `j` that settles that block FULL, at deposit
trace position `k` of the trace read at the step's post-slots state, with exactly one classification outcome
and its effect, and no other step and position lands on the same occurrence; or (c) still queued at the end. -/
theorem deposit_fate (v : ValidJointG cfg ccfg bls checkpoint anchor final) {n : Nat}
    (_hn : n < (Deposit.Indexed.submissions v.blocks).length) :
    (n < (Deposit.Indexed.emissions v.preBlocks).length ∧
      (Deposit.Indexed.emissions v.preBlocks)[n]? = (Deposit.Indexed.submissions v.blocks)[n]?) ∨
    ((Deposit.Indexed.emissions v.preBlocks).length ≤ n ∧ n < (Deposit.Indexed.emissions v.blocks).length ∧
      ∃ bj k, ∃ hbj : bj < v.blocks.length, k < (Deposit.Indexed.blockEmissions v.blocks[bj]).length ∧
        (Deposit.Indexed.emissions (v.blocks.take bj)).length + k = n ∧
        (Deposit.Indexed.blockEmissions v.blocks[bj])[k]? = (Deposit.Indexed.submissions v.blocks)[n]? ∧
        v.preBlocks.length ≤ bj ∧
      ∃ (j : Nat) (D : GloasStepData (P := P) cfg ccfg bls) (req : Gloas.BuilderDepositRequest)
        (tr : List (Gloas.BeaconState P)) (m : Gloas.BeaconState P),
        v.run.steps[j]? = some (.gloas D) ∧ D.isFull ∧ v.run.payloadIndex j = bj - v.preBlocks.length ∧
        D.builderDeposits[k]? = some req ∧ Ssz.serialize req = (Deposit.Indexed.submissions v.blocks)[n]! ∧
        builderDepositTrace ccfg bls D.postSlots D.block = .ok tr ∧ tr[k]? = some m ∧
        ∃ o, classifyBuilderDeposit ccfg bls m req = .ok o ∧
          (∀ o', classifyBuilderDeposit ccfg bls m req = .ok o' → o' = o) ∧
          ∃ m', tr[k + 1]? = some m' ∧ applyBuilderDepositOutcome ccfg m req o = .ok m' ∧
          (∀ (j' k' : Nat) (D' : GloasStepData (P := P) cfg ccfg bls) req', v.run.steps[j']? = some (.gloas D') →
            D'.builderDeposits[k']? = some req' →
            (Deposit.Indexed.emissions (v.blocks.take (v.preBlocks.length + v.run.payloadIndex j'))).length + k' = n →
            j' = j ∧ k' = k)) ∨
    ((Deposit.Indexed.emissions v.blocks).length ≤ n ∧
      (Deposit.Indexed.remainingQueue final.exec)[n - (Deposit.Indexed.emissions v.blocks).length]? =
        (Deposit.Indexed.submissions v.blocks)[n]?) := by
  have H := v.depositClean
  have fifo := Deposit.Indexed.history_fifo H
  have fate := Occurrence.history_fate Deposit.Indexed.reading Deposit.linked H.premises n
  rw [Deposit.Indexed.start_queue, List.nil_append] at fate
  have hpre : v.blocks.take v.preBlocks.length = v.preBlocks := List.take_left' rfl
  have hemis : Deposit.Indexed.emissions v.blocks =
      Deposit.Indexed.emissions v.preBlocks ++ Deposit.Indexed.emissions v.run.blocks :=
    emissions_append _ _ _
  rcases fate with ⟨hE, bj, k, hbj, hk, pos, get, anchorIff, uniq⟩ | ⟨hE, hq⟩
  · by_cases ha : n < (Deposit.Indexed.emissions v.preBlocks).length
    · left
      refine ⟨ha, ?_⟩
      rw [fifo, List.getElem?_append_left hE]
      show _ = (Deposit.Indexed.emissions v.blocks)[n]?
      rw [hemis, List.getElem?_append_left ha]
    · right; left
      have hge : v.preBlocks.length ≤ bj := by
        by_contra hlt
        have := (anchorIff v.preBlocks.length).mp (by omega)
        rw [hpre] at this
        exact ha this
      obtain ⟨j, D, env, req, post, hD, hs, hidx, hkD, hout⟩ := v.emitting_source v.deposit_covered hbj hge hk
      have hem : blockEmissions Deposit.Indexed.reading 3 v.blocks[bj] =
          D.requests.builder_deposits.toArray.toList.map Ssz.serialize := RequestCodecG.deposit_blockEmissions hout
      have hkl : k < D.builderDeposits.length := by
        have := hk
        rw [hem, List.length_map] at this
        exact this
      obtain ⟨req0, hreq0⟩ : ∃ r, D.builderDeposits[k]? = some r := ⟨_, List.getElem?_eq_getElem hkl⟩
      have hser : (submissions Deposit.contract v.blocks)[n]? = some (Ssz.serialize req0) := by
        rw [← get, hem, List.getElem?_map, hreq0]
        rfl
      obtain ⟨-, -, -, tr, m, m', o, -, -, -, -, -, htr, hm, hc, hu, hm', happ⟩ :=
        D.view.builderDeposit_applied hreq0
      refine ⟨Nat.le_of_not_lt ha, hE, bj, k, hbj, hk, pos, get, hge, j, D, req0, tr, m, hD,
        ⟨env, req, post, hs⟩, hidx, hreq0, ?_, htr, hm, o, hc, hu, m', hm', happ, ?_⟩
      · show _ = (submissions Deposit.contract v.blocks)[n]!
        rw [List.getElem!_eq_getElem?_getD, hser]
        rfl
      · intro j' k' D' r' hD' hr' pos'
        obtain ⟨env2, req2, post2, -, -, -, -, hs2, -, -, -, -, -, -, -, -, -, -⟩ :=
          D'.view.builderDeposit_applied hr'
        obtain ⟨b', hb', -, -⟩ := D'.kept_of_full hs2
        have hem' : blockEmissions Deposit.Indexed.reading 3 b' =
            D'.requests.builder_deposits.toArray.toList.map Ssz.serialize :=
          RequestCodecG.deposit_blockEmissions (v.full_output hD' hs2 hb')
        obtain ⟨hi', hbi⟩ := List.getElem?_eq_some_iff.mp (v.blocks_getElem?_full hD' hb')
        have hk' : k' < (blockEmissions Deposit.Indexed.reading 3
            v.blocks[v.preBlocks.length + v.run.payloadIndex j']).length := by
          rw [hbi, hem', List.length_map]
          exact (List.getElem?_eq_some_iff.mp hr').1
        obtain ⟨h1, rfl⟩ := uniq _ k' hi' hk' pos'
        exact ⟨(v.full_step_unique hD hD' hkD hb' (by omega)).symm, rfl⟩
  · right; right
    exact ⟨hE, hq⟩

/-! ## B4: exit fate -/

/-- **B4: every committed exit submission on the built-upon history has exactly one fate**, as B2: emitted
before the anchor; or emitted by a run block and applied by the step that settles it FULL, at exit trace
position `k` of the trace read at the step's post-slots state, with one classification outcome and its effect,
at a unique step and position; or still queued at the end. -/
theorem exit_fate (v : ValidJointG cfg ccfg bls checkpoint anchor final) {n : Nat}
    (_hn : n < (Exit.Indexed.submissions v.blocks).length) :
    (n < (Exit.Indexed.emissions v.preBlocks).length ∧
      (Exit.Indexed.emissions v.preBlocks)[n]? = (Exit.Indexed.submissions v.blocks)[n]?) ∨
    ((Exit.Indexed.emissions v.preBlocks).length ≤ n ∧ n < (Exit.Indexed.emissions v.blocks).length ∧
      ∃ bj k, ∃ hbj : bj < v.blocks.length, k < (Exit.Indexed.blockEmissions v.blocks[bj]).length ∧
        (Exit.Indexed.emissions (v.blocks.take bj)).length + k = n ∧
        (Exit.Indexed.blockEmissions v.blocks[bj])[k]? = (Exit.Indexed.submissions v.blocks)[n]? ∧
        v.preBlocks.length ≤ bj ∧
      ∃ (j : Nat) (D : GloasStepData (P := P) cfg ccfg bls) (req : Gloas.BuilderExitRequest)
        (tr : List (Gloas.BeaconState P)) (m : Gloas.BeaconState P),
        v.run.steps[j]? = some (.gloas D) ∧ D.isFull ∧ v.run.payloadIndex j = bj - v.preBlocks.length ∧
        D.builderExits[k]? = some req ∧ Ssz.serialize req = (Exit.Indexed.submissions v.blocks)[n]! ∧
        builderExitTrace ccfg bls D.postSlots D.block = .ok tr ∧ tr[k]? = some m ∧
        ∃ o, classifyBuilderExit ccfg m req = .ok o ∧
          (∀ o', classifyBuilderExit ccfg m req = .ok o' → o' = o) ∧
          ∃ m', tr[k + 1]? = some m' ∧ applyBuilderExitOutcome ccfg m req o = .ok m' ∧
          (∀ (j' k' : Nat) (D' : GloasStepData (P := P) cfg ccfg bls) req', v.run.steps[j']? = some (.gloas D') →
            D'.builderExits[k']? = some req' →
            (Exit.Indexed.emissions (v.blocks.take (v.preBlocks.length + v.run.payloadIndex j'))).length + k' = n →
            j' = j ∧ k' = k)) ∨
    ((Exit.Indexed.emissions v.blocks).length ≤ n ∧
      (Exit.Indexed.remainingQueue final.exec)[n - (Exit.Indexed.emissions v.blocks).length]? =
        (Exit.Indexed.submissions v.blocks)[n]?) := by
  have H := v.exitClean
  have fifo := Exit.Indexed.history_fifo H
  have fate := Occurrence.history_fate Exit.Indexed.reading Exit.linked H.premises n
  rw [Exit.Indexed.start_queue, List.nil_append] at fate
  have hpre : v.blocks.take v.preBlocks.length = v.preBlocks := List.take_left' rfl
  have hemis : Exit.Indexed.emissions v.blocks =
      Exit.Indexed.emissions v.preBlocks ++ Exit.Indexed.emissions v.run.blocks :=
    emissions_append _ _ _
  rcases fate with ⟨hE, bj, k, hbj, hk, pos, get, anchorIff, uniq⟩ | ⟨hE, hq⟩
  · by_cases ha : n < (Exit.Indexed.emissions v.preBlocks).length
    · left
      refine ⟨ha, ?_⟩
      rw [fifo, List.getElem?_append_left hE]
      show _ = (Exit.Indexed.emissions v.blocks)[n]?
      rw [hemis, List.getElem?_append_left ha]
    · right; left
      have hge : v.preBlocks.length ≤ bj := by
        by_contra hlt
        have := (anchorIff v.preBlocks.length).mp (by omega)
        rw [hpre] at this
        exact ha this
      obtain ⟨j, D, env, req, post, hD, hs, hidx, hkD, hout⟩ := v.emitting_source v.exit_covered hbj hge hk
      have hem : blockEmissions Exit.Indexed.reading 4 v.blocks[bj] =
          D.requests.builder_exits.toArray.toList.map Ssz.serialize := RequestCodecG.exit_blockEmissions hout
      have hkl : k < D.builderExits.length := by
        have := hk
        rw [hem, List.length_map] at this
        exact this
      obtain ⟨req0, hreq0⟩ : ∃ r, D.builderExits[k]? = some r := ⟨_, List.getElem?_eq_getElem hkl⟩
      have hser : (submissions Exit.contract v.blocks)[n]? = some (Ssz.serialize req0) := by
        rw [← get, hem, List.getElem?_map, hreq0]
        rfl
      obtain ⟨-, -, -, tr, m, m', o, -, -, -, -, -, htr, hm, hc, hu, hm', happ⟩ :=
        D.view.builderExit_applied hreq0
      refine ⟨Nat.le_of_not_lt ha, hE, bj, k, hbj, hk, pos, get, hge, j, D, req0, tr, m, hD,
        ⟨env, req, post, hs⟩, hidx, hreq0, ?_, htr, hm, o, hc, hu, m', hm', happ, ?_⟩
      · show _ = (submissions Exit.contract v.blocks)[n]!
        rw [List.getElem!_eq_getElem?_getD, hser]
        rfl
      · intro j' k' D' r' hD' hr' pos'
        obtain ⟨env2, req2, post2, -, -, -, -, hs2, -, -, -, -, -, -, -, -, -, -⟩ :=
          D'.view.builderExit_applied hr'
        obtain ⟨b', hb', -, -⟩ := D'.kept_of_full hs2
        have hem' : blockEmissions Exit.Indexed.reading 4 b' =
            D'.requests.builder_exits.toArray.toList.map Ssz.serialize :=
          RequestCodecG.exit_blockEmissions (v.full_output hD' hs2 hb')
        obtain ⟨hi', hbi⟩ := List.getElem?_eq_some_iff.mp (v.blocks_getElem?_full hD' hb')
        have hk' : k' < (blockEmissions Exit.Indexed.reading 4
            v.blocks[v.preBlocks.length + v.run.payloadIndex j']).length := by
          rw [hbi, hem', List.length_map]
          exact (List.getElem?_eq_some_iff.mp hr').1
        obtain ⟨h1, rfl⟩ := uniq _ k' hi' hk' pos'
        exact ⟨(v.full_step_unique hD hD' hkD hb' (by omega)).symm, rfl⟩
  · right; right
    exact ⟨hE, hq⟩

/-! ## B2: the outcome meaning -/

/-- **B2: what each deposit outcome means.** At a request's mid-list state `m`, its classification is, in the
spec's order, an iff against the spec's conditions (Jaune's `classifyBuilderDeposit_meaning`), and the
outcome's effect `m'` is the spec's (Jaune's `classifyBuilderDeposit_effect`): an ignored request leaves the
state unchanged, a top-up credits exactly the amount at the same incarnation (resetting an exited, swept
builder's withdrawable epoch), a registration writes the fresh record at `get_index_for_new_builder`. -/
theorem deposit_outcome_meaning {m m' : Gloas.BeaconState P} {r : Gloas.BuilderDepositRequest}
    {o : BuilderDepositOutcome} (hc : classifyBuilderDeposit ccfg bls m r = .ok o)
    (ha : applyBuilderDepositOutcome ccfg m r o = .ok m') :
    ((o = .ignoredPrefix ↔ Gloas.isBuilderWithdrawalCredential r.withdrawal_credentials = false) ∧
      (∀ i a reset, o = .topUp i a reset ↔
        Gloas.isBuilderWithdrawalCredential r.withdrawal_credentials = true ∧
        firstMatch m.builders r.pubkey = some i ∧ a = r.amount ∧
        ∃ b, m.builders.toArray[i]? = some b ∧
          (reset = true ↔ b.withdrawable_epoch ≠ FAR_FUTURE_EPOCH ∧ b.balance = U64.zero)) ∧
      (o = .ignoredBadSignature ↔
        Gloas.isBuilderWithdrawalCredential r.withdrawal_credentials = true ∧
        (∀ b ∈ m.builders.toArray, b.pubkey ≠ r.pubkey) ∧
        ∃ dom, builderDepositDomain ccfg = some dom ∧
          blsVerify bls r.pubkey (computeSigningRoot (builderDepositMessage r) dom) r.signature = false) ∧
      (∀ i a, o = .register i a ↔
        Gloas.isBuilderWithdrawalCredential r.withdrawal_credentials = true ∧
        (∀ b ∈ m.builders.toArray, b.pubkey ≠ r.pubkey) ∧
        (∃ dom, builderDepositDomain ccfg = some dom ∧
          blsVerify bls r.pubkey (computeSigningRoot (builderDepositMessage r) dom) r.signature = true) ∧
        a = r.amount ∧
        ∃ idx, Gloas.getIndexForNewBuilder m = .ok idx ∧ idx.toNat = i)) ∧
    ((o = .ignoredPrefix → m' = m) ∧ (o = .ignoredBadSignature → m' = m) ∧
      (∀ i a reset, o = .topUp i a reset → ∃ b b', m.builders.toArray[i]? = some b ∧
        m'.builders.toArray[i]? = some b' ∧
        m'.builders.toArray.size = m.builders.toArray.size ∧
        (∀ j, j ≠ i → m'.builders.toArray[j]? = m.builders.toArray[j]?) ∧
        b'.pubkey = b.pubkey ∧ b'.version = b.version ∧
        b'.execution_address = b.execution_address ∧ b'.deposit_epoch = b.deposit_epoch ∧
        b'.balance.toNat = b.balance.toNat + a.toNat ∧
        (reset = true → ∃ e, Gloas.getCurrentEpoch m = .ok e ∧
          b'.withdrawable_epoch.toNat = e.toNat + ccfg.MIN_BUILDER_WITHDRAWABILITY_DELAY) ∧
        (reset = false → b'.withdrawable_epoch = b.withdrawable_epoch) ∧
        m' = { m with builders := m'.builders }) ∧
      (∀ i a, o = .register i a → ∃ addr e,
        Jaune.Bytes.toAdr? (r.withdrawal_credentials.toBytes.drop 12) = some addr ∧
        computeEpochAtSlot P m.slot = .ok e ∧
        m'.builders.toArray[i]? = some (freshBuilder r.pubkey addr a e) ∧
        m.builders.toArray.size ≤ m'.builders.toArray.size ∧
        (∀ j, j ≠ i → m'.builders.toArray[j]? = m.builders.toArray[j]?) ∧
        m' = { m with builders := m'.builders })) :=
  ⟨classifyBuilderDeposit_meaning hc,
    classifyBuilderDeposit_effect (ctx := gloasCtx ccfg bls) hc
      (by
        rw [processBuilderDepositRequest_eq]
        show classifyBuilderDeposit ccfg bls m r >>= applyBuilderDepositOutcome ccfg m r = _
        rw [hc]
        exact ha)⟩

/-! ## B6: latency, occurrence-indexed -/

/-- B6 at the deposit contract (`cap = 64`). -/
theorem latency_indexed_deposit (v : ValidJointG cfg ccfg bls checkpoint anchor final) {j q : Nat}
    {B D : KeptBlock} {r : Bytes}
    (hB : v.blocks[j]? = some B) (hD : v.blocks[j + q / 64]? = some D)
    (amsterdam : ∀ i ≤ q / 64, ∀ x, v.blocks[j + i]? = some x → x.fork = .amsterdam)
    (queued : (Deposit.Indexed.queueAtRequests B)[q]? = some r) :
    (Deposit.Indexed.blockEmissions D)[q % 64]? = some r ∧
    (∀ i ≤ q % 64, (Deposit.Indexed.blockEmissions D)[i]? = (Deposit.Indexed.queueAtRequests B)[64 * (q / 64) + i]?) ∧
    (Deposit.Indexed.submissions v.blocks)[(Deposit.Indexed.emissions (v.blocks.take j)).length + q]? = some r ∧
    (Deposit.Indexed.emissions (v.blocks.take j)).length + q =
      (Deposit.Indexed.emissions (v.blocks.take (j + q / 64))).length + q % 64 ∧
    (v.preBlocks.length ≤ j + q / 64 → ∃ (j' : Nat) (S : GloasStepData (P := P) cfg ccfg bls) (req : _),
      v.run.steps[j']? = some (.gloas S) ∧ S.isFull ∧
      v.run.payloadIndex j' = j + q / 64 - v.preBlocks.length ∧ S.builderDeposits[q % 64]? = some req ∧
      Ssz.serialize req = r) := by
  obtain ⟨h1, h2, h3, h4⟩ := Deposit.Indexed.history_latency v.depositClean hB hD amsterdam queued
  refine ⟨h1, h2, h3, h4, fun hpre => ?_⟩
  obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hD
  have hk : q % 64 < (Deposit.Indexed.blockEmissions v.blocks[j + q / 64]).length :=
    (List.getElem?_eq_some_iff.mp h1).1
  obtain ⟨j', S, env, req, post, hS, hs, hidx, -, hout⟩ := v.emitting_source v.deposit_covered hlt hpre hk
  have hem := RequestCodecG.deposit_blockEmissions hout
  rw [hem, List.getElem?_map] at h1
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp h1
  exact ⟨j', S, x, hS, ⟨env, req, post, hs⟩, hidx, hx, rfl⟩

/-- B6 at the exit contract (`cap = 16`). -/
theorem latency_indexed_exit (v : ValidJointG cfg ccfg bls checkpoint anchor final) {j q : Nat}
    {B D : KeptBlock} {r : Bytes}
    (hB : v.blocks[j]? = some B) (hD : v.blocks[j + q / 16]? = some D)
    (amsterdam : ∀ i ≤ q / 16, ∀ x, v.blocks[j + i]? = some x → x.fork = .amsterdam)
    (queued : (Exit.Indexed.queueAtRequests B)[q]? = some r) :
    (Exit.Indexed.blockEmissions D)[q % 16]? = some r ∧
    (∀ i ≤ q % 16, (Exit.Indexed.blockEmissions D)[i]? = (Exit.Indexed.queueAtRequests B)[16 * (q / 16) + i]?) ∧
    (Exit.Indexed.submissions v.blocks)[(Exit.Indexed.emissions (v.blocks.take j)).length + q]? = some r ∧
    (Exit.Indexed.emissions (v.blocks.take j)).length + q =
      (Exit.Indexed.emissions (v.blocks.take (j + q / 16))).length + q % 16 ∧
    (v.preBlocks.length ≤ j + q / 16 → ∃ (j' : Nat) (S : GloasStepData (P := P) cfg ccfg bls) (req : _),
      v.run.steps[j']? = some (.gloas S) ∧ S.isFull ∧
      v.run.payloadIndex j' = j + q / 16 - v.preBlocks.length ∧ S.builderExits[q % 16]? = some req ∧
      Ssz.serialize req = r) := by
  obtain ⟨h1, h2, h3, h4⟩ := Exit.Indexed.history_latency v.exitClean hB hD amsterdam queued
  refine ⟨h1, h2, h3, h4, fun hpre => ?_⟩
  obtain ⟨hlt, rfl⟩ := List.getElem?_eq_some_iff.mp hD
  have hk : q % 16 < (Exit.Indexed.blockEmissions v.blocks[j + q / 16]).length :=
    (List.getElem?_eq_some_iff.mp h1).1
  obtain ⟨j', S, env, req, post, hS, hs, hidx, -, hout⟩ := v.emitting_source v.exit_covered hlt hpre hk
  have hem := RequestCodecG.exit_blockEmissions hout
  rw [hem, List.getElem?_map] at h1
  obtain ⟨x, hx, rfl⟩ := Option.map_eq_some_iff.mp h1
  exact ⟨j', S, x, hS, ⟨env, req, post, hs⟩, hidx, hx, rfl⟩

/-- **B6: latency under ePBS, for post-crossing Amsterdam payloads**, at both builder contracts (`ty = 3`,
cap 64: deposits; `ty = 4`, cap 16: exits). Execution half: Blanc's `history_latency`, as is. Consensus half: a
run block that emits the record is the payload a Gloas step settles FULL, and that step's block carries the
record's request at the same position. -/
theorem latency_indexed (v : ValidJointG cfg ccfg bls checkpoint anchor final) :
    (∀ {j q : Nat} {B D : KeptBlock} {r : Bytes},
      v.blocks[j]? = some B → v.blocks[j + q / 64]? = some D →
      (∀ i ≤ q / 64, ∀ x, v.blocks[j + i]? = some x → x.fork = .amsterdam) →
      (Deposit.Indexed.queueAtRequests B)[q]? = some r →
      (Deposit.Indexed.blockEmissions D)[q % 64]? = some r ∧
      (∀ i ≤ q % 64, (Deposit.Indexed.blockEmissions D)[i]? =
        (Deposit.Indexed.queueAtRequests B)[64 * (q / 64) + i]?) ∧
      (Deposit.Indexed.submissions v.blocks)[(Deposit.Indexed.emissions (v.blocks.take j)).length + q]? = some r ∧
      (Deposit.Indexed.emissions (v.blocks.take j)).length + q =
        (Deposit.Indexed.emissions (v.blocks.take (j + q / 64))).length + q % 64 ∧
      (v.preBlocks.length ≤ j + q / 64 → ∃ (j' : Nat) (S : GloasStepData (P := P) cfg ccfg bls) (req : _),
        v.run.steps[j']? = some (.gloas S) ∧ S.isFull ∧
        v.run.payloadIndex j' = j + q / 64 - v.preBlocks.length ∧ S.builderDeposits[q % 64]? = some req ∧
        Ssz.serialize req = r)) ∧
    (∀ {j q : Nat} {B D : KeptBlock} {r : Bytes},
      v.blocks[j]? = some B → v.blocks[j + q / 16]? = some D →
      (∀ i ≤ q / 16, ∀ x, v.blocks[j + i]? = some x → x.fork = .amsterdam) →
      (Exit.Indexed.queueAtRequests B)[q]? = some r →
      (Exit.Indexed.blockEmissions D)[q % 16]? = some r ∧
      (∀ i ≤ q % 16, (Exit.Indexed.blockEmissions D)[i]? = (Exit.Indexed.queueAtRequests B)[16 * (q / 16) + i]?) ∧
      (Exit.Indexed.submissions v.blocks)[(Exit.Indexed.emissions (v.blocks.take j)).length + q]? = some r ∧
      (Exit.Indexed.emissions (v.blocks.take j)).length + q =
        (Exit.Indexed.emissions (v.blocks.take (j + q / 16))).length + q % 16 ∧
      (v.preBlocks.length ≤ j + q / 16 → ∃ (j' : Nat) (S : GloasStepData (P := P) cfg ccfg bls) (req : _),
        v.run.steps[j']? = some (.gloas S) ∧ S.isFull ∧
        v.run.payloadIndex j' = j + q / 16 - v.preBlocks.length ∧ S.builderExits[q % 16]? = some req ∧
        Ssz.serialize req = r)) :=
  ⟨fun hB hD am qd => v.latency_indexed_deposit hB hD am qd, fun hB hD am qd => v.latency_indexed_exit hB hD am qd⟩

end ValidJointG

end Blanc.Lift.BuilderRequest
