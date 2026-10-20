import Blanc.ExecutionStagedBodyTrace
import Blanc.Ladder

/-!
Contract-neutral retained traces for configured chain histories.  This layer
sits above the raw block-body carrier because `BlockChain.ReachUsing` and its
balance bound are owned by the generic contract ladder.
-/

namespace Blanc

open Jaune

namespace ExecutionTrace

/-- One configured chain transition together with the fork selected at the
block number and timestamp and the retained trace of the body that produced its
post-state.  Coverage is recorded for this actual selected transition, rather
than inferred from an unrelated whole schedule. -/
structure ConfiguredBlockTrace (cfg : ChainConfig)
    (pre post : BlockChain) : Type where
  block : Block
  bound : sum pre.state.bal + wdsum block.wds < 2 ^ 256
  fork : Fork
  forkAt : cfg.forkAt block.header.number block.header.timestamp = .ok fork
  rules : ForkRules
  rulesEq : fork.ruleSet = rules
  rulesAt : cfg.rulesAt block.header.number block.header.timestamp = .ok rules
  covered : CoveredFork fork
  transition : stateTransitionUsing cfg pre block = .ok post
  bodyState : State
  blockOutput : BlockOutput
  bodyRun : applyBody (initBenv fork pre block.header)
    block.txs block.ommers block.wds = .ok (bodyState, blockOutput)
  bodyTrace : AppliedBodyTrace (initBenv fork pre block.header)
    block.txs block.ommers block.wds bodyState blockOutput
  postEq : post = ⟨appendBlock pre.blocks block, bodyState, pre.chainId⟩

/-- Extract the selected fork and exact body endpoints from the configured
scheduled transition. Scheduled ommer validation remains in the actual core;
this theorem neither substitutes a static transition nor assumes coverage. -/
theorem exists_configuredBody_of_transition
    {cfg : ChainConfig} {pre post : BlockChain} {block : Block}
    (h : stateTransitionUsing cfg pre block = .ok post) :
    ∃ (fork : Fork) (bodyState : State) (blockOutput : BlockOutput),
      cfg.forkAt block.header.number block.header.timestamp = .ok fork ∧
      cfg.rulesAt block.header.number block.header.timestamp = .ok fork.ruleSet ∧
      applyBody (initBenv fork pre block.header)
        block.txs block.ommers block.wds = .ok (bodyState, blockOutput) ∧
      post = ⟨appendBlock pre.blocks block, bodyState, pre.chainId⟩ := by
  have hId := stateTransitionUsing_success_chainId_eq h
  rw [stateTransitionUsing_eq_of_chainId_eq hId] at h
  obtain ⟨fork, hFork, hWith⟩ := Except.bind_eq_ok h
  rw [Except.mapError_eq_ok_iff] at hFork
  have hScheduled : stateTransitionScheduledE cfg fork pre block = .ok (.ok post) := by
    cases hs : stateTransitionScheduledE cfg fork pre block with
    | error err => rw [hs] at hWith; cases hWith
    | ok result =>
      rw [hs] at hWith
      have hResult : result = .ok post := Except.mapError_eq_ok_iff.mp hWith
      exact congrArg Except.ok hResult
  have hCore := stateTransitionScheduledE_eq_ok_iff.mp hScheduled
  rw [stateTransitionCoreE] at hCore
  obtain ⟨_, _, hCore⟩ := Except.bind_eq_ok hCore
  obtain ⟨_, _, hCore⟩ := Except.bind_eq_ok hCore
  dsimp only at hCore
  obtain ⟨⟨bodyState, blockOutput⟩, hBody, hCore⟩ := Except.bind_eq_ok hCore
  rw [Except.mapError_eq_ok_iff] at hBody
  dsimp only at hCore
  obtain ⟨_, _, hCore⟩ := Except.bind_eq_ok hCore
  obtain ⟨_, _, hFinal⟩ := Except.bind_eq_ok hCore
  have hRules : cfg.rulesAt block.header.number block.header.timestamp = .ok fork.ruleSet := by
    simp only [ChainConfig.rulesAt, hFork, Except.bind_ok]
    cases fork <;> rfl
  exact ⟨fork, bodyState, blockOutput, hFork, hRules, hBody, (Except.ok.inj hFinal).symm⟩

/-- Every successful configured transition admits the exact selected-rule body
trace that produced it. -/
theorem exists_configuredBlockTrace_of_transition
    {cfg : ChainConfig} {pre post : BlockChain} {block : Block}
    (bound : sum pre.state.bal + wdsum block.wds < 2 ^ 256)
    (h : stateTransitionUsing cfg pre block = .ok post)
    (hcovered : ∀ {fork}, cfg.forkAt block.header.number block.header.timestamp = .ok fork →
      CoveredFork fork) :
    Nonempty (ConfiguredBlockTrace cfg pre post) := by
  obtain ⟨fork, bodyState, blockOutput, hFork, hRules, hBody, hPost⟩ :=
    exists_configuredBody_of_transition h
  have hcoveredFork : CoveredFork fork := hcovered hFork
  rcases exists_appliedBodyTrace hBody hcoveredFork with ⟨bodyTrace⟩
  exact ⟨{
    block := block
    bound := bound
    fork := fork
    forkAt := hFork
    rules := fork.ruleSet
    rulesEq := rfl
    rulesAt := hRules
    covered := hcoveredFork
    transition := h
    bodyState := bodyState
    blockOutput := blockOutput
    bodyRun := hBody
    bodyTrace := bodyTrace
    postEq := hPost
  }⟩

/-- Exact retained replay of every block in a configured reachability
derivation. -/
inductive ConfiguredHistoryTrace (cfg : ChainConfig)
    (checkpoint : BlockChain) : BlockChain → Type
  | refl
      (hcfg : cfg.Valid)
      (hctx : checkpoint.ValidContext)
      (hid : cfg.chainId = checkpoint.chainId) :
      ConfiguredHistoryTrace cfg checkpoint checkpoint
  | step {current future : BlockChain} :
      ConfiguredHistoryTrace cfg checkpoint current →
      ConfiguredBlockTrace cfg current future →
      ConfiguredHistoryTrace cfg checkpoint future

/-- Forgetting retained execution evidence recovers the configured chain
reachability derivation. -/
theorem ConfiguredHistoryTrace.toReachUsing
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTrace cfg checkpoint future) :
    BlockChain.ReachUsing cfg checkpoint future := by
  induction history with
  | refl hcfg hctx hid =>
      exact .refl checkpoint hcfg hctx hid
  | step prior block ih =>
      exact .step ih block.bound block.transition

/-- Configured reachability is never more permissive than the retained trace
carrier: every reach has an exact block/body replay, including the empty
history. -/
theorem exists_configuredHistoryTrace_of_reachUsing
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    (h : BlockChain.ReachUsing cfg checkpoint future)
    (hcovered : ∀ {pre post block},
      stateTransitionUsing cfg pre block = .ok post →
      ∀ {fork}, cfg.forkAt block.header.number block.header.timestamp = .ok fork → CoveredFork fork) :
    Nonempty (ConfiguredHistoryTrace cfg checkpoint future) := by
  induction h with
  | refl hcfg hctx hid =>
      exact ⟨.refl hcfg hctx hid⟩
  | step prior bound transition ih =>
      rcases ih with ⟨history⟩
      rcases exists_configuredBlockTrace_of_transition bound transition
        (hcovered transition) with
        ⟨block⟩
      exact ⟨.step history block⟩

/-- Capabilities needed to retain an actual successful body in a selected
fork domain. They do not assert enabled optional passes or modern settlement
laws. Domain theorems, rather than programme assumptions, supply them. -/
structure BodyStageCapabilities (F : Fork → Prop) : Prop where
  stateGas_none : ∀ {fork}, F fork → fork.ruleSet.stateGas = none
  requests_covered : ∀ {fork}, F fork →
    fork.ruleSet.header.requestsHash = true → CoveredFork fork

/-- A configured block with its actual selected fork in `F`, exact retained
body stages and a reward-inclusive no-wrap budget. -/
structure ConfiguredBlockTraceIn (F : Fork → Prop) (cfg : ChainConfig)
    (pre post : BlockChain) : Type where
  block : Block
  bound : sum pre.state.bal + wdsum block.wds + cfg.rewardAt block < 2 ^ 256
  fork : Fork
  forkIn : F fork
  forkAt : cfg.forkAt block.header.number block.header.timestamp = .ok fork
  rules : ForkRules
  rulesEq : fork.ruleSet = rules
  rulesAt : cfg.rulesAt block.header.number block.header.timestamp = .ok rules
  transition : stateTransitionUsing cfg pre block = .ok post
  bodyState : State
  blockOutput : BlockOutput
  bodyRun : applyBody (initBenv fork pre block.header)
    block.txs block.ommers block.wds = .ok (bodyState, blockOutput)
  bodyTrace : StagedBodyTrace (initBenv fork pre block.header)
    block.txs block.ommers block.wds bodyState blockOutput
  postEq : post = ⟨appendBlock pre.blocks block, bodyState, pre.chainId⟩

/-- Retain one actual configured transition using its selected domain and
explicit extraction capabilities. The budget is evidence, not a conclusion
inferred from successful execution. -/
theorem exists_configuredBlockTraceIn_of_transition
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain} {block : Block}
    (bound : sum pre.state.bal + wdsum block.wds + cfg.rewardAt block < 2 ^ 256)
    (h : stateTransitionUsing cfg pre block = .ok post)
    (hF : ∀ {fork},
      cfg.forkAt block.header.number block.header.timestamp = .ok fork → F fork)
    (capabilities : BodyStageCapabilities F) :
    Nonempty (ConfiguredBlockTraceIn F cfg pre post) := by
  obtain ⟨fork, bodyState, blockOutput, hFork, hRules, hBody, hPost⟩ :=
    exists_configuredBody_of_transition h
  have forkIn : F fork := hF hFork
  rcases exists_stagedBodyTrace hBody (capabilities.stateGas_none forkIn)
    (capabilities.requests_covered forkIn) with ⟨bodyTrace⟩
  exact ⟨{
    block := block
    bound := bound
    fork := fork
    forkIn := forkIn
    forkAt := hFork
    rules := fork.ruleSet
    rulesEq := rfl
    rulesAt := hRules
    transition := h
    bodyState := bodyState
    blockOutput := blockOutput
    bodyRun := hBody
    bodyTrace := bodyTrace
    postEq := hPost
  }⟩

/-- Dropping the nonnegative reward term recovers the unchanged ReachUsing
step bound. This does not prove the stronger bound in the other direction. -/
theorem ConfiguredBlockTraceIn.withdrawalsBound
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTraceIn F cfg pre post) :
    sum pre.state.bal + wdsum trace.block.wds < 2 ^ 256 :=
  Nat.lt_of_le_of_lt (Nat.le_add_right _ _) trace.bound

/-- A Type-valued retained block spine over the selected fork domain. -/
inductive ConfiguredHistoryTraceIn (F : Fork → Prop) (cfg : ChainConfig)
    (checkpoint : BlockChain) : BlockChain → Type
  | refl
      (hcfg : cfg.Valid)
      (hctx : checkpoint.ValidContext)
      (hid : cfg.chainId = checkpoint.chainId) :
      ConfiguredHistoryTraceIn F cfg checkpoint checkpoint
  | step {current future : BlockChain} :
      ConfiguredHistoryTraceIn F cfg checkpoint current →
      ConfiguredBlockTraceIn F cfg current future →
      ConfiguredHistoryTraceIn F cfg checkpoint future

/-- Forgetting the retained spine and nonnegative reward term produces the
original configured reachability derivation without changing its meaning. -/
theorem ConfiguredHistoryTraceIn.toReachUsing
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future) :
    BlockChain.ReachUsing cfg checkpoint future := by
  induction history with
  | refl hcfg hctx hid =>
      exact .refl checkpoint hcfg hctx hid
  | step prior block ih =>
      exact .step ih block.withdrawalsBound block.transition

/-- Sufficient reward-budget evidence for the historical converse: every
successful extension of every reachable prefix that satisfies the old bound
also satisfies the reward-inclusive bound. ReachUsing alone supplies no such
budget, nor a Type-valued block-occurrence witness. -/
def ConfiguredRewardBudget (cfg : ChainConfig) (checkpoint : BlockChain) : Prop :=
  ∀ {pre post : BlockChain} {block : Block},
    BlockChain.ReachUsing cfg checkpoint pre →
    sum pre.state.bal + wdsum block.wds < 2 ^ 256 →
    stateTransitionUsing cfg pre block = .ok post →
    sum pre.state.bal + wdsum block.wds + cfg.rewardAt block < 2 ^ 256

/-- A configured reach has a retained historical replay under explicit
selected-domain, extraction-capability and prefix reward-budget evidence. -/
theorem exists_configuredHistoryTraceIn_of_reachUsing
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (h : BlockChain.ReachUsing cfg checkpoint future)
    (hF : ∀ {pre post : BlockChain} {block : Block},
      BlockChain.ReachUsing cfg checkpoint pre →
      sum pre.state.bal + wdsum block.wds < 2 ^ 256 →
      stateTransitionUsing cfg pre block = .ok post →
      ∀ {fork},
        cfg.forkAt block.header.number block.header.timestamp = .ok fork → F fork)
    (capabilities : BodyStageCapabilities F)
    (budget : ConfiguredRewardBudget cfg checkpoint) :
    Nonempty (ConfiguredHistoryTraceIn F cfg checkpoint future) := by
  induction h with
  | refl hcfg hctx hid =>
      exact ⟨.refl hcfg hctx hid⟩
  | step prior bound transition ih =>
      rcases ih with ⟨history⟩
      rcases exists_configuredBlockTraceIn_of_transition
        (budget prior bound transition) transition (hF prior bound transition)
        capabilities with ⟨block⟩
      exact ⟨.step history block⟩

/-- The unchanged modern domain supplies the explicit extraction capabilities. -/
theorem BodyStageCapabilities.covered : BodyStageCapabilities CoveredFork := {
  stateGas_none := fun {_fork} h => h.stateGas_none
  requests_covered := fun {_fork} h _ => h
}

/-- The actual selected modern fork pays no proof-of-work reward. -/
theorem ConfiguredBlockTrace.rewardAt_eq_zero
    {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTrace cfg pre post) : cfg.rewardAt trace.block = 0 := by
  apply ChainConfig.rewardAt_eq_zero trace.forkAt
  exact trace.covered.cases (motive := fun f => f.ruleSet.pow = none) rfl rfl rfl rfl

/-- Embed a modern configured block with its supplied retained body. The
extra budget term is discharged from the actual selected modern fork. -/
def ConfiguredBlockTrace.toIn
    {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTrace cfg pre post) :
    ConfiguredBlockTraceIn CoveredFork cfg pre post := {
  block := trace.block
  bound := by simpa only [trace.rewardAt_eq_zero, Nat.add_zero] using trace.bound
  fork := trace.fork
  forkIn := trace.covered
  forkAt := trace.forkAt
  rules := trace.rules
  rulesEq := trace.rulesEq
  rulesAt := trace.rulesAt
  transition := trace.transition
  bodyState := trace.bodyState
  blockOutput := trace.blockOutput
  bodyRun := trace.bodyRun
  bodyTrace := trace.bodyTrace.toStaged trace.covered
  postEq := trace.postEq
}

/-- A selected covered block in any retained domain has the original modern
carrier. Coverage is explicit; membership in `F` alone does not imply it. -/
def ConfiguredBlockTraceIn.toModern
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTraceIn F cfg pre post)
    (covered : CoveredFork trace.fork) : ConfiguredBlockTrace cfg pre post := {
  block := trace.block
  bound := trace.withdrawalsBound
  fork := trace.fork
  forkAt := trace.forkAt
  rules := trace.rules
  rulesEq := trace.rulesEq
  rulesAt := trace.rulesAt
  covered := covered
  transition := trace.transition
  bodyState := trace.bodyState
  blockOutput := trace.blockOutput
  bodyRun := trace.bodyRun
  bodyTrace := trace.bodyTrace.toModern covered
  postEq := trace.postEq
}

/-- Lift modern block embedding through the supplied retained history. -/
def ConfiguredHistoryTrace.toIn
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTrace cfg checkpoint future) :
    ConfiguredHistoryTraceIn CoveredFork cfg checkpoint future :=
  match history with
  | .refl hcfg hctx hid => .refl hcfg hctx hid
  | .step prior block => .step prior.toIn block.toIn

/-- A history whose actual selected forks are covered recovers the original
modern carrier without extracting a new replay witness. -/
def ConfiguredHistoryTraceIn.toModern
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn CoveredFork cfg checkpoint future) :
    ConfiguredHistoryTrace cfg checkpoint future :=
  match history with
  | .refl hcfg hctx hid => .refl hcfg hctx hid
  | .step prior block => .step prior.toModern (block.toModern block.forkIn)

/-- The modern-to-domain block bridge uses the supplied body's adapter. -/
theorem ConfiguredBlockTrace.toIn_bodyTrace
    {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTrace cfg pre post) :
    trace.toIn.bodyTrace = trace.bodyTrace.toStaged trace.covered := rfl

/-- The domain-to-modern block bridge uses the supplied body's adapter. -/
theorem ConfiguredBlockTraceIn.toModern_bodyTrace
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTraceIn F cfg pre post)
    (covered : CoveredFork trace.fork) :
    (trace.toModern covered).bodyTrace = trace.bodyTrace.toModern covered := rfl

end ExecutionTrace

end Blanc
