-- ProrataAccountingHistory.lean : configured block and chain accounting replay.

import Blanc.ProrataAccountingBody
import Blanc.ExecutionHistoryEffects

namespace Blanc

open Jaune

namespace Prorata

open _root_.Blanc.ExecutionTrace

open scoped BigOperators

/-- Rung R8: a whole configured block realizes one PRORATA accounting replay,
from the world the parent chain leaves to the world the imported block
installs.

Nothing is added above rung R7's premises -- and one is removed.  The block
carrier owns its own `wdsum` bound as a structure field, so R7's added
hypothesis is discharged here and reaches no rung above this one.  The
not-yet-created side condition disappears entirely: block preparation opens
`applyBody` on an empty created-account set
(`ConfiguredBlockTrace.not_mem_openingCreatedAccounts`), so R8 asks only for
the state invariant at the parent chain.

The block-preparation boundary contributes no accounting step, because it
moves no value: `initBenv` copies the parent chain's world state verbatim. -/
theorem retainedConfiguredBlockAccountingReplay
    {ca : Adr} {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTrace cfg pre post)
    (inv : prorataSpec.StateInv ca pre.state)
    (blockIndex : Nat) :
    ∃ steps,
      ProrataAccountingReplay offset.toNat
        (AccountingSnapshot.ofState ca pre.state) steps
        (AccountingSnapshot.ofState ca post.state) := by
  obtain ⟨steps, replay⟩ :=
    retainedBodyAccountingReplay (ca := ca) trace.bodyTrace
      (trace.openingState ▸ inv)
      (trace.not_mem_openingCreatedAccounts ca)
      trace.openingBound blockIndex
  refine ⟨steps, ?_⟩
  rw [trace.postState]
  rwa [trace.openingState] at replay

/-- Rung R9: a whole retained configured history realizes one PRORATA
accounting replay, from the world at the checkpoint to the world at any
configured continuation of it.

Nothing is added above rung R8's single premise.  The state invariant is
carried from one block to the next by the generic ladder, through the chain
reachability the history itself projects to
(`ConfiguredHistoryTrace.stateInv`), and `prorataSpec.Preserves ca` is
discharged internally from `prorataSpec_preserves` rather than taken as a
hypothesis.  No not-yet-created side condition is threaded at all: each block
re-establishes it from its own empty created-account set, which is what makes
this induction carry exactly one fact.

The blocks are composed in chain order, and each block's steps are tagged with
that block's own header number rather than a synthetic counter. -/
theorem retainedConfiguredHistoryAccountingReplay
    {ca : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTrace cfg checkpoint future)
    (inv : prorataSpec.StateInv ca checkpoint.state) :
    ∃ steps,
      ProrataAccountingReplay offset.toNat
        (AccountingSnapshot.ofState ca checkpoint.state) steps
        (AccountingSnapshot.ofState ca future.state) := by
  induction history with
  | refl hcfg hctx hid => exact ⟨[], ProrataAccountingReplay.nil_of_eq rfl⟩
  | step prior block ih =>
      obtain ⟨priorSteps, priorReplay⟩ := ih
      obtain ⟨blockSteps, blockReplay⟩ :=
        retainedConfiguredBlockAccountingReplay block
          (prior.stateInv (prorataSpec_preserves ca) inv)
          block.block.header.number
      exact ⟨priorSteps ++ blockSteps, priorReplay.append blockReplay⟩

/-! ## Rung R10: the realized-trace interface

`ProrataTraceRealizes root steps future` supplements configured chain
reachability with the accounting steps the chain actually produced.  It is
block-structured rather than a bare conjunction: a realized trace decomposes,
in chain order, into one retained `ConfiguredBlockTrace` per imported block
together with that block's own exact accounting segment, and the whole step
list is the concatenation of those segments.  Within a block the segments are
laid out in `applyBody` order by rung R7, whose five phases are composed in
exactly the order `applyBody` runs them.

The carrier is schedule-parametric.  `cfg` is an arbitrary validated
`ChainConfig`, so one realized trace may cross fork activations; the
current-mainnet instance is `MainnetDeploymentRoot`, and no fork is named
anywhere below. -/
inductive ProrataTraceRealizes {cfg : ChainConfig} {deployed : BlockChain}
    {ca : Adr} (root : DeploymentRoot cfg deployed ca) :
    List (ProrataAccountingStep offset.toNat) → BlockChain → Prop where
  | refl : ProrataTraceRealizes root [] deployed
  | step {current future : BlockChain}
      {priorSteps blockSteps : List (ProrataAccountingStep offset.toNat)}
      (prior : ProrataTraceRealizes root priorSteps current)
      (block : ConfiguredBlockTrace cfg current future)
      (replay : ProrataAccountingReplay offset.toNat
        (AccountingSnapshot.ofState ca current.state) blockSteps
        (AccountingSnapshot.ofState ca future.state)) :
      ProrataTraceRealizes root (priorSteps ++ blockSteps) future

namespace ProrataTraceRealizes

/-- Every realized trace projects to the configured chain reach it replays:
the carrier never admits a continuation the chain relation does not.  The
reflexive trace projects to the deployment root's own reflexive reach, and
each block contributes its retained bound and its successful configured
transition. -/
theorem toReachUsing {cfg : ChainConfig} {deployed future : BlockChain}
    {ca : Adr} {root : DeploymentRoot cfg deployed ca}
    {steps : List (ProrataAccountingStep offset.toNat)}
    (realizes : ProrataTraceRealizes root steps future) :
    BlockChain.ReachUsing cfg deployed future := by
  induction realizes with
  | refl => exact root.reflReach
  | step prior block replay ih => exact .step ih block.bound block.transition

/-- The realized trace's steps are one connected exact accounting replay from
the deployment root to the continuation, obtained by concatenating the
per-block segments in chain order. -/
theorem toAccountingReplay {cfg : ChainConfig} {deployed future : BlockChain}
    {ca : Adr} {root : DeploymentRoot cfg deployed ca}
    {steps : List (ProrataAccountingStep offset.toNat)}
    (realizes : ProrataTraceRealizes root steps future) :
    ProrataAccountingReplay offset.toNat
      (AccountingSnapshot.ofState ca deployed.state) steps
      (AccountingSnapshot.ofState ca future.state) := by
  induction realizes with
  | refl => exact .nil _
  | step prior block replay ih => exact ih.append replay

end ProrataTraceRealizes

/-- Every retained configured history from the deployment root is realized.
This is rung R9 read one level up: the per-block segments R8 produces are
exactly the block-structured carrier's own segments, and the invariant each
block needs comes from the deployment root through the prefix's chain
reach. -/
theorem prorataTraceRealizes_of_configuredHistoryTrace
    {cfg : ChainConfig} {deployed future : BlockChain} {ca : Adr}
    (root : DeploymentRoot cfg deployed ca)
    (history : ConfiguredHistoryTrace cfg deployed future) :
    ∃ steps, ProrataTraceRealizes root steps future := by
  induction history with
  | refl hcfg hctx hid => exact ⟨[], .refl⟩
  | step prior block ih =>
      obtain ⟨priorSteps, priorRealizes⟩ := ih
      obtain ⟨blockSteps, blockReplay⟩ :=
        retainedConfiguredBlockAccountingReplay block
          (root.reachable_stateInv prior.toReachUsing)
          block.block.header.number
      exact ⟨priorSteps ++ blockSteps, .step priorRealizes block blockReplay⟩

/-- Configured reachability from the deployment root is never more permissive
than the realized-trace carrier: every continuation of the deployed PRORATA
carries an exact accounting trace, and the reflexive reach carries the empty
one.  With `ProrataTraceRealizes.toReachUsing` this pins the carrier exactly
onto chain reachability, so no exact-accounting result stated over it can be
vacuous. -/
theorem prorataTraceRealizes_exists_of_reachUsing
    {cfg : ChainConfig} {deployed future : BlockChain} {ca : Adr}
    (root : DeploymentRoot cfg deployed ca)
    (reach : BlockChain.ReachUsing cfg deployed future) :
    ∃ steps, ProrataTraceRealizes root steps future := by
  rcases exists_configuredHistoryTrace_of_reachUsing reach with ⟨history⟩
  exact prorataTraceRealizes_of_configuredHistoryTrace root history

/-! ## Rung R11: the realized cumulative-dust identity -/

namespace ProrataAccountingPath

/-- The telescope's unclamped boundary lookup at index zero is the connected
path's own first snapshot. -/
theorem snapshotAt_zero {o : Nat} (path : ProrataAccountingPath o) :
    path.snapshotAt 0 = path.first := by
  unfold snapshotAt first
  congr 1

end ProrataAccountingPath

namespace DeploymentRoot

/-- The deployment root's accounting projection is the genesis snapshot: no
shares issued and no target balance.  This is what anchors the cumulative-dust
telescope at `X0 = 1` and `D0 = O`. -/
theorem accountingSnapshot {cfg : ChainConfig} {deployed : BlockChain}
    {ca : Adr} (root : DeploymentRoot cfg deployed ca) :
    AccountingSnapshot.ofState ca deployed.state = ⟨0, 0⟩ := by
  unfold AccountingSnapshot.ofState
  rw [root.emptyStorage, root.zeroBalance]
  rfl

end DeploymentRoot

/-- Rung R11: the SF-frozen cumulative-dust identity, holding over every
realized finite trace of the deployed PRORATA from its own genesis.

The path is the connected carrier `ProrataAccountingReplay.exists_path`
extracts from the realized trace, so its steps are exactly the realized ones
and its boundaries are the realized boundaries -- no connectivity is
reconstructed.  Anchoring at the deployment root discharges the two genesis
constants the frozen statement names: the root's empty storage gives `D0 = O`
and its zero target balance gives `X0 = 1`, which is why the leading term of
the telescope is the bare denominator product rather than a scaled one.

No hypothesis is added.  `2 <= O` is not needed here -- it is the separate
P4 no-profit premise -- and the only arithmetic side condition, `O != 0`, is
discharged from the compiled offset. -/
theorem prorata_realized_dust_trace_exact
    {cfg : ChainConfig} {deployed future : BlockChain} {ca : Adr}
    {steps : List (ProrataAccountingStep offset.toNat)}
    (root : DeploymentRoot cfg deployed ca)
    (realizes : ProrataTraceRealizes root steps future) :
    ∃ path : ProrataAccountingPath offset.toNat,
      path.steps = steps ∧
      path.first = ⟨0, 0⟩ ∧
      path.last = AccountingSnapshot.ofState ca future.state ∧
      path.XAt 0 = 1 ∧
      path.DAt 0 = offset.toNat ∧
      path.XAt steps.length * (∏ j ∈ Finset.range steps.length, path.DAt j) =
        (∏ j ∈ Finset.Icc 1 steps.length, path.DAt j) +
          ∑ i ∈ Finset.range steps.length,
            (path.rhoAt i + path.kappaAt i) *
              (∏ j ∈ Finset.range i, path.DAt j) *
                (∏ j ∈ Finset.Icc (i + 2) steps.length, path.DAt j) := by
  obtain ⟨path, hsteps, hfirst, hlast⟩ :=
    ProrataAccountingReplay.exists_path realizes.toAccountingReplay
  have hgenesis : path.first = ⟨0, 0⟩ := by
    rw [hfirst, root.accountingSnapshot]
  have hzero : path.snapshotAt 0 = ⟨0, 0⟩ := by
    rw [path.snapshotAt_zero, hgenesis]
  have hX : path.XAt 0 = 1 := by
    simp [ProrataAccountingPath.XAt, ProrataAccountingStep.X, hzero]
  have hD : path.DAt 0 = offset.toNat := by
    simp [ProrataAccountingPath.DAt, ProrataAccountingStep.D, hzero]
  refine ⟨path, hsteps, hgenesis, hlast, hX, hD, ?_⟩
  have hexact : path.XAt path.steps.length *
      (∏ j ∈ Finset.range path.steps.length, path.DAt j) =
        path.XAt 0 * (∏ j ∈ Finset.Icc 1 path.steps.length, path.DAt j) +
          ∑ i ∈ Finset.range path.steps.length,
            (path.rhoAt i + path.kappaAt i) *
              (∏ j ∈ Finset.range i, path.DAt j) *
                (∏ j ∈ Finset.Icc (i + 2) path.steps.length, path.DAt j) :=
    ProrataAccountingPath.prorata_dust_trace_exact (by simp) path
  rw [hsteps, hX, Nat.one_mul] at hexact
  exact hexact

end Prorata

end Blanc
