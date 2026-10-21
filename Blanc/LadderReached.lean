import Blanc.Ladder
import Blanc.ExecutionHistory

/-!
Reached-segment fork coverage for configured chains.

The configured ladder (`ContractSpec.chainUsing_preserves_inv`) asks that every
fork the schedule can select is covered.  A schedule with historical eras (for
example mainnet's, which selects pre-Prague rules at early timestamps) cannot
discharge that whole-schedule premise.  It can still discharge coverage on the
segment a chain actually reaches: Jaune's header validation makes each accepted
block strictly later than the chain tip, so once the tip is at or past a
timestamp floor every later selection is at or past it too.

This module states that reached-step fact and the ladder theorem it supports.
It adds no premise to the existing whole-schedule theorems.
-/

namespace Blanc

open Jaune

/-- A successful configured transition validated its header against the chain
tip, so the tip exists and is strictly older than the block, and the block
becomes the new tip.  The selected fork and its scheduled run are returned for
callers that go on to execute it. -/
theorem stateTransitionUsing_reachedStep {cfg : ChainConfig} {pre post : BlockChain}
    {block : Block} (h : stateTransitionUsing cfg pre block = .ok post) :
    ∃ f, cfg.forkAt block.header.number block.header.timestamp = .ok f ∧
      stateTransitionScheduledE cfg f pre block = .ok (.ok post) ∧
      (∃ parent, pre.blocks.getLast? = some parent ∧
        parent.header.timestamp < block.header.timestamp) ∧
      post.blocks.getLast? = some block := by
  rw [stateTransitionUsing] at h
  obtain ⟨_, _, h⟩ := Except.bind_eq_ok h
  obtain ⟨f, hf, h⟩ := Except.bind_eq_ok h
  cases hs : stateTransitionScheduledE cfg f pre block with
  | error e => rw [hs] at h; cases h
  | ok r =>
    rw [hs] at h
    have hr : r = .ok post := Except.mapError_eq_ok_iff.mp h
    subst hr
    obtain ⟨hvh, hblocks, _⟩ :=
      stateTransitionCoreE_eq_ok (stateTransitionScheduledE_eq_ok_iff.mp hs)
    obtain ⟨parent, hlast, _, hlt⟩ := validateHeader_succ hvh
    refine ⟨f, Except.mapError_eq_ok_iff.mp hf, hs, ⟨parent, hlast, hlt⟩, ?_⟩
    rw [hblocks]
    exact appendBlock_getLast? _ _

/-- The tip's timestamp floor is carried along any configured reach: every
accepted block is strictly later than the tip it extends. -/
theorem BlockChain.ReachUsing.tip_floor {cfg : ChainConfig} {ch ch' : BlockChain}
    (h_reach : BlockChain.ReachUsing cfg ch ch') {T : Nat}
    (hstart : ∃ parent, ch.blocks.getLast? = some parent ∧
      T ≤ parent.header.timestamp) :
    ∃ parent, ch'.blocks.getLast? = some parent ∧ T ≤ parent.header.timestamp := by
  induction h_reach with
  | refl => exact hstart
  | step _ _ h_st ih =>
    obtain ⟨tip, htip, hfloor⟩ := ih
    obtain ⟨_, _, _, ⟨parent, hlast, hlt⟩, hnew⟩ := stateTransitionUsing_reachedStep h_st
    rw [htip] at hlast
    cases hlast
    exact ⟨_, hnew, Nat.le_of_lt (Nat.lt_of_le_of_lt hfloor hlt)⟩

/-- A step accepted from a tip at or past the timestamp floor selects a fork
that floor coverage covers. -/
theorem stateTransitionUsing_covered_of_reached {cfg : ChainConfig}
    {pre post : BlockChain} {block : Block} (T : Nat)
    (hcov : ∀ (number timestamp : Nat) (f : Fork), T ≤ timestamp →
      cfg.forkAt number timestamp = .ok f → CoveredFork f)
    (hstart : ∃ parent, pre.blocks.getLast? = some parent ∧
      T ≤ parent.header.timestamp)
    (h : stateTransitionUsing cfg pre block = .ok post) {fork : Fork}
    (hf : cfg.forkAt block.header.number block.header.timestamp = .ok fork) :
    CoveredFork fork := by
  obtain ⟨_, _, _, ⟨parent, hlast, hlt⟩, _⟩ := stateTransitionUsing_reachedStep h
  obtain ⟨tip, htip, hfloor⟩ := hstart
  rw [htip] at hlast
  cases hlast
  exact hcov _ _ fork (Nat.le_of_lt (Nat.lt_of_le_of_lt hfloor hlt)) hf

/-- A successful mainnet selection of a covered fork happens at or after
Prague's timestamp: every covered fork mainnet schedules is activated by a
timestamp no earlier than Prague's.  This is the converse direction of
`mainnetChainConfig_covered`. -/
theorem mainnetChainConfig_pragueTimestamp_le_of_covered
    {number timestamp : Nat} {f : Fork}
    (h : mainnetChainConfig.forkAt number timestamp = .ok f) (hf : CoveredFork f) :
    mainnetPragueTimestamp ≤ timestamp := by
  have hvalid : mainnetChainConfig.validate = .ok () := by decide
  have hsome : mainnetChainConfig.forkAt? number timestamp = some f := by
    rw [ChainConfig.forkAt, hvalid] at h
    cases hq : mainnetChainConfig.forkAt? number timestamp with
    | none => simp only [hq, Except.mapError, bind, Except.bind] at h; cases h
    | some g =>
      simp only [hq, Except.mapError, bind, Except.bind, Except.ok.injEq] at h
      rw [h]
  obtain ⟨a, ha, rfl⟩ := Option.map_eq_some_iff.mp hsome
  obtain ⟨hmem, hreached⟩ := List.mem_filter.mp (List.mem_of_getLast? ha)
  unfold CoveredFork coveredForks at hf
  simp only [mainnetChainConfig, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
  all_goals
    clear h ha hsome hvalid
    first
      | exact absurd hf (by decide)
      | (simp only [ForkCriterion.reached, decide_eq_true_eq] at hreached
         simp only [mainnetPragueTimestamp, mainnetOsakaTimestamp, mainnetBpo1Timestamp,
           mainnetBpo2Timestamp] at hreached ⊢
         omega)

namespace ExecutionTrace

/-- **Configured histories on a reached segment.**  The floor variant of
`exists_configuredHistoryTrace_of_reachUsing`: coverage is asked only at or
after the timestamp floor, from a checkpoint whose tip is at or past it. -/
theorem exists_configuredHistoryTrace_of_reachUsing_of_reached
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    (h : BlockChain.ReachUsing cfg checkpoint future) (T : Nat)
    (hcov : ∀ (number timestamp : Nat) (f : Fork), T ≤ timestamp →
      cfg.forkAt number timestamp = .ok f → CoveredFork f)
    (hstart : ∃ parent, checkpoint.blocks.getLast? = some parent ∧
      T ≤ parent.header.timestamp) :
    Nonempty (ConfiguredHistoryTrace cfg checkpoint future) := by
  induction h with
  | refl hcfg hctx hid =>
      exact ⟨.refl hcfg hctx hid⟩
  | step prior bound transition ih =>
      rcases ih with ⟨history⟩
      rcases exists_configuredBlockTrace_of_transition bound transition
        (stateTransitionUsing_covered_of_reached T hcov (prior.tip_floor hstart)
          transition) with ⟨block⟩
      exact ⟨.step history block⟩

end ExecutionTrace

namespace ContractSpec

variable {c : ContractSpec}

/-- **The configured ladder on a reached segment.**  Coverage is required only
at or after the timestamp floor `T`, and the starting tip is at or past `T`;
every block the chain then accepts is strictly later, so each selected fork is
covered and the invariant is preserved.  The floor is carried to the endpoint. -/
theorem chainUsing_preserves_inv_of_reached (wa : Adr) (hp : c.Preserves wa)
    (cfg : ChainConfig) (T : Nat)
    (hcov : ∀ (number timestamp : Nat) (f : Fork), T ≤ timestamp →
      cfg.forkAt number timestamp = .ok f → CoveredFork f)
    {ch ch' : BlockChain} (h_reach : BlockChain.ReachUsing cfg ch ch')
    (h_inv : c.StateInv wa ch.state)
    (hstart : ∃ parent, ch.blocks.getLast? = some parent ∧
      T ≤ parent.header.timestamp) :
    c.StateInv wa ch'.state ∧
      ∃ parent, ch'.blocks.getLast? = some parent ∧ T ≤ parent.header.timestamp := by
  induction h_reach with
  | refl => exact ⟨h_inv, hstart⟩
  | step _ h_bound h_st ih =>
    obtain ⟨hinv, tip, htip, hfloor⟩ := ih
    obtain ⟨f, hf, hs, ⟨parent, hlast, hlt⟩, hnew⟩ := stateTransitionUsing_reachedStep h_st
    rw [htip] at hlast
    cases hlast
    have hfork : CoveredFork f := hcov _ _ f (Nat.le_of_lt (Nat.lt_of_le_of_lt hfloor hlt)) hf
    have hpow : f.ruleSet.pow = none :=
      hfork.cases (motive := fun f => f.ruleSet.pow = none) rfl rfl rfl rfl
    rw [stateTransitionScheduledE_of_pow_none _ f _ _ hpow] at hs
    have hrun : stateTransitionAt f _ _ = .ok _ :=
      stateTransitionAt_eq_ok_iff.mpr (Except.ok.inj hs)
    exact ⟨c.stateTransitionAt_preserves_inv wa hp f _ _ _ hrun h_bound hinv hfork,
      _, hnew, Nat.le_of_lt (Nat.lt_of_le_of_lt hfloor hlt)⟩

end ContractSpec

end Blanc
