import Blanc.Ladder

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
