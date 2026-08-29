import Blanc.ExecutionTrace
import Blanc.Ladder

/-!
Contract-neutral retained traces for configured chain histories.  This layer
sits above the raw block-body carrier because `BlockChain.ReachUsing` and its
balance bound are owned by the generic contract ladder.
-/

namespace Blanc

open Jaune

namespace ExecutionTrace

/-- One configured chain transition together with the rule set selected at
the block timestamp and the retained trace of the body that produced its
post-state.  The carrier is schedule-parametric: one history may cross fork
activations without changing relations or discarding which rules each block
actually used. -/
structure ConfiguredBlockTrace (cfg : ChainConfig)
    (pre post : BlockChain) : Type where
  block : Block
  bound : sum pre.state.bal + wdsum block.wds < 2 ^ 256
  rules : ForkRules
  rulesAt : cfg.rulesAt block.header.timestamp = .ok rules
  transition : stateTransitionUsing cfg pre block = .ok post
  bodyState : State
  blockOutput : BlockOutput
  bodyRun : applyBody (initBenv rules pre block.header)
    block.txs block.wds = .ok (bodyState, blockOutput)
  bodyTrace : AppliedBodyTrace (initBenv rules pre block.header)
    block.txs block.wds bodyState blockOutput
  postEq : post = ⟨appendBlock pre.blocks block, bodyState, pre.chainId⟩

/-- Every successful configured transition admits the exact selected-rule body
trace that produced it. -/
theorem exists_configuredBlockTrace_of_transition
    {cfg : ChainConfig} {pre post : BlockChain} {block : Block}
    (bound : sum pre.state.bal + wdsum block.wds < 2 ^ 256)
    (h : stateTransitionUsing cfg pre block = .ok post) :
    Nonempty (ConfiguredBlockTrace cfg pre post) := by
  have hId : cfg.chainId = pre.chainId :=
    stateTransitionUsing_success_chainId_eq h
  have hSelected := h
  rw [stateTransitionUsing_eq_of_chainId_eq hId] at hSelected
  obtain ⟨rules, hRules, hWith⟩ := Except.bind_eq_ok hSelected
  rw [Except.mapError_eq_ok_iff] at hRules
  rw [stateTransitionWith_eq_ok_iff, stateTransitionE] at hWith
  obtain ⟨_, _, hWith⟩ := Except.bind_eq_ok hWith
  obtain ⟨_, _, hWith⟩ := Except.bind_eq_ok hWith
  dsimp only at hWith
  obtain ⟨⟨bodyState, blockOutput⟩, hBody, hWith⟩ :=
    Except.bind_eq_ok hWith
  dsimp only at hWith
  obtain ⟨_, _, hFinal⟩ := Except.bind_eq_ok hWith
  rcases exists_appliedBodyTrace hBody with ⟨bodyTrace⟩
  exact ⟨{
    block := block
    bound := bound
    rules := rules
    rulesAt := hRules
    transition := h
    bodyState := bodyState
    blockOutput := blockOutput
    bodyRun := hBody
    bodyTrace := bodyTrace
    postEq := (Except.ok.inj hFinal).symm
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
    (h : BlockChain.ReachUsing cfg checkpoint future) :
    Nonempty (ConfiguredHistoryTrace cfg checkpoint future) := by
  induction h with
  | refl hcfg hctx hid =>
      exact ⟨.refl hcfg hctx hid⟩
  | step prior bound transition ih =>
      rcases ih with ⟨history⟩
      rcases exists_configuredBlockTrace_of_transition bound transition with
        ⟨block⟩
      exact ⟨.step history block⟩

end ExecutionTrace

end Blanc
