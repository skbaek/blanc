import JauneConsensus.Joint
import Blanc.ExecutionHistory

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
  rcases hcf with rfl | rfl <;> cases f <;> simp_all [Fork.consensusFork?, CoveredFork, coveredForks]

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
  simp only [engineVerdict, bind, Except.bind, throw, throwThe, MonadExceptOf.throw,
    Except.mapError, pure, Except.pure] at h
  split at h
  · simp at h
  split at h
  · simp at h
  cases hb : blobVersionedHashesOf req.executionPayload.txBytes with
  | error => simp [hb] at h
  | ok hashes =>
  simp only [hb] at h
  split at h
  · simp at h
  cases hid : cfg.checkChainId pre with
  | error => simp [hid] at h
  | ok u =>
  simp only [hid] at h
  cases hf : cfg.forkAt (payloadToBlock req).header.number (payloadToBlock req).header.timestamp with
  | error => simp [hf] at h
  | ok fork =>
  simp only [hf] at h
  split at h
  · simp at h
  rename_i hpair
  have hpair : fork.consensusFork? = some cf := by simpa using hpair
  cases hs : stateTransitionScheduledE cfg fork pre (payloadToBlock req) with
  | error => simp [hs] at h
  | ok r =>
  cases r with
  | error => simp [hs] at h
  | ok post' =>
  simp only [hs] at h
  cases hrun : applyBody (initBenv fork pre (payloadToBlock req).header) (payloadToBlock req).txs
      (payloadToBlock req).ommers (payloadToBlock req).wds with
  | error => simp [hrun] at h
  | ok out =>
  simp only [hrun] at h
  split at h
  · simp at h
  rename_i hreq
  cases h
  exact ⟨fork, out.1, out.2, rfl, hpair, coveredFork_of_consensusFork? hpair hcf,
    stateTransitionUsing_of_scheduled hid hf hs, hrun, by simpa using hreq⟩

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
  cases sf <;> cases bf <;> simp only [jointStep] at h <;> try (simp [throw, throwThe, MonadExceptOf.throw] at h; done)
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

@[simp] theorem JointRun.toExec_nil {P : Preset} {cfg : ChainConfig} {ccfg : Config}
    {bls : Bool} {s₀ : JointState P} {checkpoint : BlockChain}
    (pre : ConfiguredHistoryTrace cfg checkpoint s₀.exec) :
    (JointRun.nil : JointRun cfg ccfg bls s₀ s₀).toExec pre = pre := rfl

@[simp] theorem JointRun.toExec_snoc {P : Preset} {cfg : ChainConfig} {ccfg : Config}
    {bls : Bool} {s₀ s s' : JointState P} {checkpoint : BlockChain}
    (pre : ConfiguredHistoryTrace cfg checkpoint s₀.exec) (run : JointRun cfg ccfg bls s₀ s)
    (b : AnySignedBlock P) (step : jointStep cfg ccfg bls s b = .ok s')
    (bound : sum s.exec.state.bal + wdsum (payloadWithdrawals b) < 2 ^ 256) :
    (run.snoc b step bound).toExec pre =
      .step (run.toExec pre) (JointStepTrace.choose step bound).trace := rfl

end Blanc
