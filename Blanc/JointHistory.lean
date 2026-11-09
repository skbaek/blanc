import JauneConsensus.Joint
import JauneConsensus.Facts.Joint
import Blanc.ExecutionHistory
import Blanc.ExecutionHistoryExtension

/-!
# Joint execution–consensus histories

A joint run is a sequence of successful `JauneConsensus.jointStep`s from a joint anchor. Each
step's engine verdict is one configured execution block transition with its body run, so a
joint run extends any configured execution history ending at the anchor's execution chain
(`JointRun.toExec`). Coverage is not assumed: the joint step admits only Electra and Fulu
blocks, whose paired execution forks (Prague; Osaka, BPO1, BPO2) are exactly `coveredForks`.
-/

namespace Blanc

open Jaune JauneConsensus ExecutionTrace

/-! ## The engine verdict as a configured block transition -/

/-- A consensus fork the joint step admits pairs only with covered execution forks. -/
theorem coveredFork_of_consensusFork? {f : Jaune.Fork} {cf : CFork}
    (hpair : f.consensusFork? = some cf) (hcf : cf = .electra ∨ cf = .fulu) :
    CoveredFork f := by
  rcases hcf with rfl | rfl <;> cases f <;> simp_all only [Fork.consensusFork?, reduceCtorEq, Option.some.injEq, CoveredFork, coveredForks, List.mem_cons, List.not_mem_nil, or_self, or_false, or_true]

/-- A successful configured transition from its parts. -/
theorem stateTransitionUsing_of_scheduled {cfg : ChainConfig} {pre post : BlockChain}
    {block : Block} {fork : Jaune.Fork}
    (hid : cfg.checkChainId pre = .ok ())
    (hfork : cfg.forkAt block.header.number block.header.timestamp = .ok fork)
    (hrun : stateTransitionScheduledE cfg fork pre block = .ok (.ok post)) :
    stateTransitionUsing cfg pre block = .ok post := by
  simp only [stateTransitionUsing, hid, hfork, hrun, Except.mapError, bind, Except.bind]

/-- What a successful engine verdict for an Electra or Fulu block establishes about the
execution side: the converted block's selected fork is covered, the configured transition
succeeds with the verdict's chain, and the body run produces exactly the request list. -/
theorem engineVerdict_ok {P : Preset} {cfg : ChainConfig} {cf : CFork} {pre post : BlockChain}
    {req : NewPayloadRequest P} (h : engineVerdict cfg cf pre req = .ok post)
    (hcf : cf = .electra ∨ cf = .fulu) :
    ∃ (fork : Jaune.Fork) (bodyState : State) (blockOutput : BlockOutput),
      cfg.forkAt (payloadToBlock req).header.number (payloadToBlock req).header.timestamp =
        .ok fork ∧
      fork.consensusFork? = some cf ∧
      CoveredFork fork ∧
      stateTransitionUsing cfg pre (payloadToBlock req) = .ok post ∧
      applyBody (initBenv fork pre (payloadToBlock req).header) (payloadToBlock req).txs
        (payloadToBlock req).ommers (payloadToBlock req).wds = .ok (bodyState, blockOutput) ∧
      blockOutput.requests = req.executionRequests := by
  obtain ⟨-, -, -, hid, fork, hf, hpair, -, hs, bodyState, blockOutput, hrun, hreq⟩ :=
    engineVerdict_ok_iff.mp h
  exact ⟨fork, bodyState, blockOutput, hf, hpair, coveredFork_of_consensusFork? hpair hcf,
    stateTransitionUsing_of_scheduled hid hf hs, hrun, hreq⟩

/-! ## The joint step's engine verdict -/

/-- A successful joint transition ran the engine on the block's own request, and its execution
chain is the engine's. -/
theorem jointTransitionAt_engine {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {f : CFork} {beacon beacon' : BeaconState P f} {exec exec' : BlockChain}
    {signedBlock : SignedBeaconBlock P f} {atSlot : Bool}
    (h : jointTransitionAt cfg ccfg bls beacon exec signedBlock atSlot = .ok (beacon', exec')) :
    ∃ req, NewPayloadRequest.ofBlock signedBlock.message = .ok req ∧
      engineVerdict cfg f exec req = .ok exec' := by
  unfold jointTransitionAt at h
  obtain ⟨req, hreq, h⟩ := Except.bind_eq_ok h
  refine ⟨req, hreq, ?_⟩
  cases hv : engineVerdict cfg f exec req with
  | error =>
    simp only [hv, bind, Except.bind, pure, Except.pure, throw, throwThe, MonadExceptOf.throw] at h
    split at h
    · repeat (first | contradiction | split at h)
    · repeat (first | contradiction | split at h)
  | ok e =>
    simp only [hv, bind, Except.bind, pure, Except.pure] at h
    split at h <;> repeat (first | contradiction | split at h)
    all_goals (cases h; rfl)

/-- A successful joint step admits only Electra and Fulu blocks, ran the engine on the block's
own request, and its execution chain is the engine's. -/
theorem jointStep_engine {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {s s' : JointState P} {b : AnySignedBlock P}
    (h : jointStep cfg ccfg bls s b = .ok s') :
    (b.1 = .electra ∨ b.1 = .fulu) ∧
      ∃ req, NewPayloadRequest.ofBlock b.2.message = .ok req ∧
        engineVerdict cfg b.1 s.exec req = .ok s'.exec := by
  obtain ⟨sf, beacon, exec⟩ := s
  obtain ⟨bf, signedBlock⟩ := b
  cases sf <;> cases bf <;> simp only [jointStep] at h <;> try (simp only [ExceptT.stM_eq, throw, throwThe, MonadExceptOf.throw, reduceCtorEq] at h; done)
  · obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
    obtain ⟨⟨_, _⟩, ht, h⟩ := Except.bind_eq_ok h
    cases h
    exact ⟨.inl rfl, jointTransitionAt_engine ht⟩
  · obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
    obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
    split at h
    · obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
      obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
      obtain ⟨⟨_, _⟩, ht, h⟩ := Except.bind_eq_ok h
      cases h
      exact ⟨.inr rfl, jointTransitionAt_engine ht⟩
    · obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
      obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
      obtain ⟨⟨_, _⟩, ht, h⟩ := Except.bind_eq_ok h
      cases h
      exact ⟨.inr rfl, jointTransitionAt_engine ht⟩
  · obtain ⟨⟨_, _⟩, ht, h⟩ := Except.bind_eq_ok h
    cases h
    exact ⟨.inr rfl, jointTransitionAt_engine ht⟩

/-- The request `process_execution_payload` builds carries the block body's own payload. -/
theorem ofBlock_executionPayload {P : Preset} {f : CFork} {block : BeaconBlock P f}
    {req : NewPayloadRequest P} (h : NewPayloadRequest.ofBlock block = .ok req) :
    req.executionPayload = block.body.execution_payload := by
  unfold NewPayloadRequest.ofBlock at h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  cases h
  rfl

/-- The request `process_execution_payload` builds carries the body's execution requests as
`get_execution_requests_list`. -/
theorem ofBlock_executionRequests {P : Preset} {f : CFork} {block : BeaconBlock P f}
    {req : NewPayloadRequest P} (h : NewPayloadRequest.ofBlock block = .ok req) :
    ∃ requests : ExecutionRequests P,
      Gated.read block.body.execution_requests "NewPayloadRequest: execution_requests" =
        .ok requests ∧
      req.executionRequests = getExecutionRequestsList requests := by
  unfold NewPayloadRequest.ofBlock at h
  obtain ⟨requests, hread, h⟩ := Except.bind_eq_ok h
  cases h
  exact ⟨requests, hread, rfl⟩

/-! ## The beacon state a joint step hands to `process_block` -/

/-- The beacon context of a joint step whose engine verdict passed. -/
abbrev jointCtx (ccfg : Config) (bls : Bool) : Ctx := { cfg := ccfg, blsActive := bls }

/-- The beacon state a joint step hands to `process_block`, computed with the same calls as
`jointStep`: within a fork, `process_slots` to the block's slot; across Electra → Fulu, the
guarded `process_slots` to the fork slot, `upgrade_to_fulu`, then `process_slots` to the
block's slot unless the block is at the fork slot. Other fork pairs are refused. -/
def jointBlockInput {P : Preset} (ccfg : Config) (bls : Bool) :
    (s : JointState P) → (b : AnySignedBlock P) → M (BeaconState P b.1)
  | ⟨.electra, beacon, _⟩, ⟨.electra, sb⟩ =>
    processSlots (jointCtx ccfg bls) beacon sb.message.slot
  | ⟨.fulu, beacon, _⟩, ⟨.fulu, sb⟩ =>
    processSlots (jointCtx ccfg bls) beacon sb.message.slot
  | ⟨.electra, beacon, _⟩, ⟨.fulu, sb⟩ =>
    U64.ofNat? (fuluForkSlot (P := P) ccfg) "joint step: Fulu fork slot" >>= fun forkSlot =>
    (if beacon.slot < forkSlot then processSlots (jointCtx ccfg bls) beacon forkSlot
      else pure beacon) >>= fun beacon =>
    upgradeToFulu ccfg beacon >>= fun beacon =>
    if sb.message.slot == beacon.slot then pure beacon
    else processSlots (jointCtx ccfg bls) beacon sb.message.slot
  | _, _ => throw (.assert "joint step: fork pair outside Electra and Fulu")

/-- A successful state transition ran `process_slots` to the block's slot and then
`process_block` on the result. -/
theorem stateTransition_processBlock {P : Preset} {f : CFork} {ctx : Ctx}
    {state state' : BeaconState P f} {sb : SignedBeaconBlock P f}
    (h : stateTransition ctx state sb = .ok state') :
    ∃ st, processSlots ctx state sb.message.slot = .ok st ∧
      ∃ post, processBlock ctx st sb.message = .ok post := by
  unfold JauneConsensus.stateTransition stateTransitionWith at h
  obtain ⟨st, hslots, h⟩ := Except.bind_eq_ok h
  refine ⟨st, hslots, ?_⟩
  simp only [ite_true] at h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  obtain ⟨post, hpost, _⟩ := Except.bind_eq_ok h
  exact ⟨post, hpost⟩

/-- A successful joint step ran `process_block` on the beacon state `jointBlockInput`
computes. -/
theorem jointStep_processBlock {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {s s' : JointState P} {b : AnySignedBlock P}
    (h : jointStep cfg ccfg bls s b = .ok s') :
    ∃ st, jointBlockInput ccfg bls s b = .ok st ∧
      ∃ post, processBlock (jointCtx ccfg bls) st b.2.message = .ok post := by
  obtain ⟨sf, beacon, exec⟩ := s
  obtain ⟨bf, sb⟩ := b
  cases sf <;> cases bf
  all_goals try (simp only [jointStep, ExceptT.stM_eq, throw, throwThe, MonadExceptOf.throw,
    reduceCtorEq] at h; done)
  · obtain ⟨-, _, _, _, -, -, hbeacon, -⟩ := jointStep_electra_ok_iff.mp h
    exact stateTransition_processBlock hbeacon
  · obtain ⟨-, -, _, forkSlot, beacon1, beacon2, _, _, hforkSlot, hslots, hup, -, -, hbeacon, -⟩ :=
      jointStep_cross_ok_iff.mp h
    by_cases hat : (sb.message.slot == beacon2.slot) = true
    · rw [ite_eq_left hat] at hbeacon
      obtain ⟨_, _, hbeacon⟩ := Except.bind_eq_ok hbeacon
      obtain ⟨_, _, hbeacon⟩ := Except.bind_eq_ok hbeacon
      obtain ⟨post, hpost, -⟩ := Except.bind_eq_ok hbeacon
      refine ⟨beacon2, ?_, post, hpost⟩
      simp only [jointBlockInput, hforkSlot, Except.bind_ok, hslots, hup, hat, ↓reduceIte]
      rfl
    · rw [ite_eq_right hat] at hbeacon
      obtain ⟨st, hst, post, hpost⟩ := stateTransition_processBlock hbeacon
      refine ⟨st, ?_, post, hpost⟩
      simp only [jointBlockInput, hforkSlot, Except.bind_ok, hslots, hup, hat]
      exact hst
  · obtain ⟨_, _, _, _, -, hbeacon, -⟩ := jointStep_fulu_ok_iff.mp h
    exact stateTransition_processBlock hbeacon

/-! ## Joint runs -/

/-- The execution withdrawals of a signed block's payload: the withdrawals the converted
execution block credits. -/
def payloadWithdrawals {P : Preset} (b : AnySignedBlock P) : List Jaune.Withdrawal :=
  b.2.message.body.execution_payload.executionWithdrawals

/-- The configured execution block trace of one successful joint step. The converted block is
the engine's block for the request the step built, and its body run produced exactly that
request's list. -/
structure JointStepTrace {P : Preset} (cfg : ChainConfig) (ccfg : Config) (bls : Bool)
    (s s' : JointState P) (b : AnySignedBlock P) : Type where
  req : NewPayloadRequest P
  ofBlock : NewPayloadRequest.ofBlock b.2.message = .ok req
  engine : engineVerdict cfg b.1 s.exec req = .ok s'.exec
  trace : ConfiguredBlockTrace cfg s.exec s'.exec
  block_eq : trace.block = payloadToBlock req
  requests_eq : trace.blockOutput.requests = req.executionRequests

/-- Every successful joint step with the balance no-wrap bound has a configured execution
block trace. -/
theorem nonempty_jointStepTrace {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {s s' : JointState P} {b : AnySignedBlock P}
    (step : jointStep cfg ccfg bls s b = .ok s')
    (bound : sum s.exec.state.bal + wdsum (payloadWithdrawals b) < 2 ^ 256) :
    Nonempty (JointStepTrace cfg ccfg bls s s' b) := by
  obtain ⟨hcf, req, hreq, hengine⟩ := jointStep_engine step
  obtain ⟨fork, bodyState, blockOutput, hfork, -, hcovered, htransition, hbody, hrequests⟩ :=
    engineVerdict_ok hengine hcf
  have hwds : (payloadToBlock req).wds = payloadWithdrawals b := by
    simp only [payloadToBlock, payloadWithdrawals, ofBlock_executionPayload hreq]
  obtain ⟨fork', bodyState', blockOutput', hfork', hrules, hbody', hpost⟩ :=
    exists_configuredBody_of_transition htransition
  obtain rfl : fork' = fork := Except.ok.inj (hfork'.symm.trans hfork)
  obtain ⟨rfl, rfl⟩ : bodyState' = bodyState ∧ blockOutput' = blockOutput := by
    have := Except.ok.inj (hbody'.symm.trans hbody)
    exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
  rcases exists_appliedBodyTrace hbody hcovered with ⟨bodyTrace⟩
  exact ⟨{
    req := req
    ofBlock := hreq
    engine := hengine
    trace := {
      block := payloadToBlock req
      bound := hwds ▸ bound
      fork := fork'
      forkAt := hfork
      rules := fork'.ruleSet
      rulesEq := rfl
      rulesAt := hrules
      covered := hcovered
      transition := htransition
      bodyState := bodyState'
      blockOutput := blockOutput'
      bodyRun := hbody
      bodyTrace := bodyTrace
      postEq := hpost }
    block_eq := rfl
    requests_eq := hrequests }⟩

/-- The chosen execution block trace of a successful joint step. -/
noncomputable def JointStepTrace.choose {P : Preset} {cfg : ChainConfig} {ccfg : Config}
    {bls : Bool} {s s' : JointState P} {b : AnySignedBlock P}
    (step : jointStep cfg ccfg bls s b = .ok s')
    (bound : sum s.exec.state.bal + wdsum (payloadWithdrawals b) < 2 ^ 256) :
    JointStepTrace cfg ccfg bls s s' b :=
  Classical.choice (nonempty_jointStepTrace step bound)

/-- A joint run from `s₀`: successful joint steps, each with the balance no-wrap bound the
configured execution block trace needs. Snoc-shaped, like `ConfiguredHistoryTrace.step`. -/
inductive JointRun {P : Preset} (cfg : ChainConfig) (ccfg : Config) (bls : Bool)
    (s₀ : JointState P) : JointState P → Type
  | nil : JointRun cfg ccfg bls s₀ s₀
  | snoc {s s' : JointState P} :
      JointRun cfg ccfg bls s₀ s → (b : AnySignedBlock P) →
      jointStep cfg ccfg bls s b = .ok s' →
      sum s.exec.state.bal + wdsum (payloadWithdrawals b) < 2 ^ 256 →
      JointRun cfg ccfg bls s₀ s'

/-- Extend a configured execution history ending at the anchor's execution chain by the run's
engine blocks. -/
noncomputable def JointRun.toExec {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {s₀ : JointState P} {checkpoint : BlockChain}
    (pre : ConfiguredHistoryTrace cfg checkpoint s₀.exec) :
    {s : JointState P} → JointRun cfg ccfg bls s₀ s → ConfiguredHistoryTrace cfg checkpoint s.exec
  | _, .nil => pre
  | _, .snoc run _ step bound => .step (run.toExec pre) (JointStepTrace.choose step bound).trace

theorem JointRun.toExec_nil {P : Preset} {cfg : ChainConfig} {ccfg : Config}
    {bls : Bool} {s₀ : JointState P} {checkpoint : BlockChain}
    (pre : ConfiguredHistoryTrace cfg checkpoint s₀.exec) :
    (JointRun.nil : JointRun cfg ccfg bls s₀ s₀).toExec pre = pre := rfl

theorem JointRun.toExec_snoc {P : Preset} {cfg : ChainConfig} {ccfg : Config}
    {bls : Bool} {s₀ s s' : JointState P} {checkpoint : BlockChain}
    (pre : ConfiguredHistoryTrace cfg checkpoint s₀.exec) (run : JointRun cfg ccfg bls s₀ s)
    (b : AnySignedBlock P) (step : jointStep cfg ccfg bls s b = .ok s')
    (bound : sum s.exec.state.bal + wdsum (payloadWithdrawals b) < 2 ^ 256) :
    (run.snoc b step bound).toExec pre =
      .step (run.toExec pre) (JointStepTrace.choose step bound).trace := rfl

/-! ## The steps of a joint run -/

/-- One step of a joint run: its endpoints, its signed beacon block, and the chosen execution
block trace that `JointRun.toExec` appends for it. -/
structure JointRunStep {P : Preset} (cfg : ChainConfig) (ccfg : Config) (bls : Bool) : Type where
  pre : JointState P
  post : JointState P
  block : AnySignedBlock P
  stepTrace : JointStepTrace cfg ccfg bls pre post block

/-- The steps of a joint run, in order. Step `j` carries the `j`-th execution block that
`JointRun.toExec` appends after the pre-anchor history. -/
noncomputable def JointRun.steps {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {s₀ : JointState P} :
    {s : JointState P} → JointRun cfg ccfg bls s₀ s → List (JointRunStep (P := P) cfg ccfg bls)
  | _, .nil => []
  | _, .snoc run b step bound => run.steps ++ [⟨_, _, b, JointStepTrace.choose step bound⟩]

theorem JointRun.steps_nil {P : Preset} {cfg : ChainConfig} {ccfg : Config} {bls : Bool}
    {s₀ : JointState P} : (JointRun.nil : JointRun cfg ccfg bls s₀ s₀).steps = [] := rfl

theorem JointRun.steps_snoc {P : Preset} {cfg : ChainConfig} {ccfg : Config}
    {bls : Bool} {s₀ s s' : JointState P} (run : JointRun cfg ccfg bls s₀ s)
    (b : AnySignedBlock P) (step : jointStep cfg ccfg bls s b = .ok s')
    (bound : sum s.exec.state.bal + wdsum (payloadWithdrawals b) < 2 ^ 256) :
    (run.snoc b step bound).steps = run.steps ++ [⟨_, _, b, JointStepTrace.choose step bound⟩] :=
  rfl

/-- The last element of `l ++ [x]` at index `i` is `x` exactly at `i = l.length`. -/
private theorem getElem?_append_singleton_of_not_lt {α : Type} {l : List α} {x y : α} {i : Nat}
    (hi : ¬i < l.length) (h : (l ++ [x])[i]? = some y) : i = l.length ∧ x = y := by
  rw [List.getElem?_append_right (by omega)] at h
  cases hk : i - l.length with
  | zero =>
    rw [hk, List.getElem?_cons_zero, Option.some.injEq] at h
    exact ⟨by omega, h⟩
  | succ k =>
    rw [hk, List.getElem?_cons_succ, List.getElem?_nil] at h
    exact absurd h (by simp only [reduceCtorEq, not_false_eq_true])

/-- The joint history through step `i` of a run extends to the whole joint history by the
remaining steps: `run.toExec pre` is some configured history to step `i`'s execution chain,
followed by step `i`'s execution block, followed by exactly `steps.length - 1 - i` blocks. -/
theorem JointRun.extendsBy_toExec {P : Preset} {cfg : ChainConfig} {ccfg : Config}
    {bls : Bool} {s₀ : JointState P} {checkpoint : BlockChain}
    (pre : ConfiguredHistoryTrace cfg checkpoint s₀.exec) :
    {s : JointState P} → (run : JointRun cfg ccfg bls s₀ s) → {i : Nat} →
    {A : JointRunStep (P := P) cfg ccfg bls} → run.steps[i]? = some A →
    ∃ history : ConfiguredHistoryTrace cfg checkpoint A.pre.exec,
      (ConfiguredHistoryTrace.step history A.stepTrace.trace).ExtendsBy (run.toExec pre)
        (run.steps.length - 1 - i)
  | _, .nil, _, _, h => by
    simp only [JointRun.steps, List.getElem?_nil, reduceCtorEq] at h
  | _, .snoc run b step bound, i, A, h => by
    rw [JointRun.steps_snoc] at h
    rw [JointRun.steps_snoc, List.length_append, List.length_singleton, JointRun.toExec_snoc]
    by_cases hi : i < run.steps.length
    · rw [List.getElem?_append_left hi] at h
      obtain ⟨history, ext⟩ := JointRun.extendsBy_toExec pre run h
      refine ⟨history, ?_⟩
      rw [show run.steps.length + 1 - 1 - i = run.steps.length - 1 - i + 1 by omega]
      exact ext.step _
    · obtain ⟨hlen, rfl⟩ := getElem?_append_singleton_of_not_lt hi h
      refine ⟨run.toExec pre, ?_⟩
      rw [show run.steps.length + 1 - 1 - i = 0 by omega]
      exact .refl

/-- Steps `i ≤ j` of a joint run: for some configured histories to their execution chains,
the history through step `j` extends the history through step `i` by exactly `j - i` blocks,
and the whole joint history extends the history through step `j` by the remaining
`steps.length - 1 - j` blocks. -/
theorem JointRun.extendsBy_steps {P : Preset} {cfg : ChainConfig} {ccfg : Config}
    {bls : Bool} {s₀ : JointState P} {checkpoint : BlockChain}
    (pre : ConfiguredHistoryTrace cfg checkpoint s₀.exec) :
    {s : JointState P} → (run : JointRun cfg ccfg bls s₀ s) → {i j : Nat} →
    {A C : JointRunStep (P := P) cfg ccfg bls} → i ≤ j →
    run.steps[i]? = some A → run.steps[j]? = some C →
    ∃ (historyA : ConfiguredHistoryTrace cfg checkpoint A.pre.exec)
      (historyC : ConfiguredHistoryTrace cfg checkpoint C.pre.exec),
      (ConfiguredHistoryTrace.step historyA A.stepTrace.trace).ExtendsBy
        (ConfiguredHistoryTrace.step historyC C.stepTrace.trace) (j - i) ∧
      (ConfiguredHistoryTrace.step historyC C.stepTrace.trace).ExtendsBy (run.toExec pre)
        (run.steps.length - 1 - j)
  | _, .nil, _, _, _, _, _, h, _ => by
    simp only [JointRun.steps, List.getElem?_nil, reduceCtorEq] at h
  | _, .snoc run b step bound, i, j, A, C, hij, hA, hC => by
    rw [JointRun.steps_snoc] at hA hC
    rw [JointRun.steps_snoc, List.length_append, List.length_singleton, JointRun.toExec_snoc]
    by_cases hj : j < run.steps.length
    · rw [List.getElem?_append_left hj] at hC
      rw [List.getElem?_append_left (by omega)] at hA
      obtain ⟨historyA, historyC, ext, tail⟩ := JointRun.extendsBy_steps pre run hij hA hC
      refine ⟨historyA, historyC, ext, ?_⟩
      rw [show run.steps.length + 1 - 1 - j = run.steps.length - 1 - j + 1 by omega]
      exact tail.step _
    · obtain ⟨hlen, rfl⟩ := getElem?_append_singleton_of_not_lt hj hC
      by_cases hi : i < run.steps.length
      · rw [List.getElem?_append_left hi] at hA
        obtain ⟨historyA, ext⟩ := JointRun.extendsBy_toExec pre run hA
        refine ⟨historyA, run.toExec pre, ?_, ?_⟩
        · rw [show j - i = run.steps.length - 1 - i + 1 by omega]
          exact ext.step _
        · rw [show run.steps.length + 1 - 1 - j = 0 by omega]
          exact .refl
      · obtain ⟨hlen', rfl⟩ := getElem?_append_singleton_of_not_lt hi hA
        refine ⟨run.toExec pre, run.toExec pre, ?_, ?_⟩
        · rw [show j - i = 0 by omega]
          exact .refl
        · rw [show run.steps.length + 1 - 1 - j = 0 by omega]
          exact .refl

/-- Every step of a joint run is a successful joint step between its endpoints. -/
theorem JointRun.steps_jointStep {P : Preset} {cfg : ChainConfig} {ccfg : Config}
    {bls : Bool} {s₀ : JointState P} :
    {s : JointState P} → (run : JointRun cfg ccfg bls s₀ s) → {j : Nat} →
    {D : JointRunStep (P := P) cfg ccfg bls} → run.steps[j]? = some D →
    jointStep cfg ccfg bls D.pre D.block = .ok D.post
  | _, .nil, _, _, h => by
    simp only [JointRun.steps, List.getElem?_nil, reduceCtorEq] at h
  | _, .snoc run b step bound, j, D, h => by
    rw [JointRun.steps_snoc] at h
    by_cases hj : j < run.steps.length
    · rw [List.getElem?_append_left hj] at h
      exact JointRun.steps_jointStep run h
    · obtain ⟨-, rfl⟩ := getElem?_append_singleton_of_not_lt hj h
      exact step

end Blanc
