-- ProrataWethVaultLedgerFaithful.lean : real-chain D9 for the pair headlines (faithfulness F6).

import Blanc.Composition.ProrataWethVaultCoalitionHistory

namespace Blanc.Composition.ProrataWethVault

open Jaune
open _root_.Blanc.ExecutionTrace
open scoped BigOperators
open Blanc.ProrataWethVault (offsetN)

/-! ## Real-chain D9 corollaries for the pair headlines -/

/-- Every realized record's owned invocation is an allowance visit of the history's own frames. -/
def PairLedgerFaithful {cfg : ChainConfig} {deployed future : BlockChain} (vault : Adr)
    (history : ConfiguredHistoryTrace cfg deployed future)
    (steps : List (PairStepRecord vault)) : Prop :=
  ∀ call ∈ PairStepRecord.ledger steps, call.visit ∈ history.pairVisits vault

/-- **Faithful existence** (review F1(a)). -/
theorem pairTraceRealizes_faithful_of_configuredHistoryTrace {cfg : ChainConfig}
    {deployed future : BlockChain} {vault : Adr} (root : PairRoot cfg deployed vault)
    (history : ConfiguredHistoryTrace cfg deployed future) :
    ∃ steps, PairTraceRealizes root steps future ∧ PairLedgerFaithful vault history steps := by
  induction history with
  | refl hcfg hctx hid =>
      refine ⟨[], .refl, ?_⟩
      intro call member
      simp [PairStepRecord.ledger] at member
  | step prior block ih =>
      obtain ⟨priorSteps, priorRealizes, priorFaithful⟩ := ih
      obtain ⟨blockSteps, blockReplay, blockOk⟩ :=
        retainedConfiguredBlockPairReplayFaithful block (PairWorldInv.of_history root prior)
          (root.notPrecompile block.rulesAt).2 block.block.header.number
      refine ⟨priorSteps ++ blockSteps,
        .step priorRealizes block blockReplay (fun r member => (blockOk r member).1), ?_⟩
      intro call member
      rw [PairReplay.ledger_append, List.mem_append] at member
      have split : (ConfiguredHistoryTrace.step prior block).pairVisits vault =
          prior.pairVisits vault ++ block.rawFrames.filterMap (Exec.Deriv.pairVisit? vault) := by
        simp only [ConfiguredHistoryTrace.pairVisits, ConfiguredHistoryTrace.rawFrames,
          List.filterMap_append]
      rw [split, List.mem_append]
      rcases member with inPrior | inBlock
      · exact Or.inl (priorFaithful call inPrior)
      · obtain ⟨r, rMember, own⟩ := List.mem_filterMap.mp inBlock
        obtain ⟨d, dMember, visit⟩ := (blockOk r rMember).2 call own
        exact Or.inr (List.mem_filterMap.mpr ⟨d, dMember, visit⟩)

/-- Real-chain D9 gives the recorded ledger's D9 (antitonicity at the realized ledger). -/
theorem PairLedgerFaithful.collision {cfg : ChainConfig} {deployed future : BlockChain}
    {vault : Adr} {history : ConfiguredHistoryTrace cfg deployed future}
    {steps : List (PairStepRecord vault)}
    (faithful : PairLedgerFaithful vault history steps)
    (real : NoVaultVisitKeyCollision (history.pairVisits vault) vault) :
    NoVaultAllowanceKeyCollision (PairStepRecord.ledger steps) vault :=
  noVaultAllowanceKeyCollision_of_visits faithful real

/-- **Backing from real-chain D9.** -/
theorem pair_history_backed {cfg : ChainConfig} {deployed future : BlockChain} {vault : Adr}
    (root : PairRoot cfg deployed vault)
    (history : ConfiguredHistoryTrace cfg deployed future)
    (collision : NoVaultVisitKeyCollision (history.pairVisits vault) vault) :
    PairBacked vault (future.state.getStor vault) (future.state.getStor wethAccount) ∧
      State.Inv wethAccount future.state := by
  obtain ⟨steps, realizes, faithful⟩ :=
    pairTraceRealizes_faithful_of_configuredHistoryTrace root history
  exact pair_reachable_backed root realizes (faithful.collision collision)

/-- **`PairStable` from real-chain D9.** -/
theorem pair_history_stable {cfg : ChainConfig} {deployed future : BlockChain} {vault : Adr}
    (root : PairRoot cfg deployed vault)
    (history : ConfiguredHistoryTrace cfg deployed future)
    (collision : NoVaultVisitKeyCollision (history.pairVisits vault) vault)
    {timestamp : Nat} {rules : ForkRules} (rulesAt : cfg.rulesAt timestamp = .ok rules) :
    PairStable vault rules future.state := by
  obtain ⟨steps, realizes, faithful⟩ :=
    pairTraceRealizes_faithful_of_configuredHistoryTrace root history
  exact pair_reachable_stable root realizes (faithful.collision collision) rulesAt

/-- **P3 from real-chain D9.** -/
theorem pair_history_realized_dust_trace_exact {cfg : ChainConfig} {deployed future : BlockChain}
    {vault : Adr} (root : PairRoot cfg deployed vault)
    (history : ConfiguredHistoryTrace cfg deployed future)
    (collision : NoVaultVisitKeyCollision (history.pairVisits vault) vault) :
    ∃ steps, PairTraceRealizes root steps future ∧ PairLedgerFaithful vault history steps ∧
    ∃ path : FourQuote.RealizedPath vault,
      path.steps = PairStepRecord.fourQuoteSteps steps ∧
      path.snapshotAt 0 = ⟨0, 0⟩ ∧
      path.snapshotAt path.steps.length = FourQuote.stateSnapshot vault future.state ∧
      path.xAt 0 = 1 ∧
      path.dAt 0 = Blanc.ProrataWethVault.offsetN ∧
      path.xAt path.steps.length * (∏ j ∈ Finset.range path.steps.length, path.dAt j) =
        (∏ j ∈ Finset.Icc 1 path.steps.length, path.dAt j) +
          (∑ i ∈ Finset.range path.steps.length,
            path.roundingAt i * (∏ j ∈ Finset.range i, path.dAt j) *
              (∏ j ∈ Finset.Icc (i + 2) path.steps.length, path.dAt j)) +
          (∑ i ∈ Finset.range path.steps.length,
            path.retainedAt i * (∏ j ∈ Finset.range i, path.dAt j) *
              (∏ j ∈ Finset.Icc (i + 2) path.steps.length, path.dAt j)) +
          ∑ i ∈ Finset.range path.steps.length,
            path.creditAt i * (∏ j ∈ Finset.range i, path.dAt j) *
              (∏ j ∈ Finset.Icc (i + 2) path.steps.length, path.dAt j) := by
  obtain ⟨steps, realizes, faithful⟩ :=
    pairTraceRealizes_faithful_of_configuredHistoryTrace root history
  exact ⟨steps, realizes, faithful,
    pair_realized_dust_trace_exact root realizes (faithful.collision collision)⟩

/-- A pair open attack trace from any visit list the ledger is faithful to, and D9 over it. -/
theorem PairOpenAttackTrace.of_visits {cfg : ChainConfig} {deployed : BlockChain} {vault : Adr}
    {root : PairRoot cfg deployed vault} {coalition : Finset Adr} {victim : Adr}
    {charge : PairStepRecord vault → Blanc.Prorata.AttackAttribution}
    {steps : List (PairStepRecord vault)} {future : BlockChain}
    {visits : List AllowanceVisit}
    (realizes : PairTraceRealizes root steps future)
    (faithful : ∀ call ∈ PairStepRecord.ledger steps, call.visit ∈ visits)
    (collision : NoVaultVisitKeyCollision visits vault)
    (victim_not_mem : victim ∉ coalition)
    (coalition_covers : ∀ r ∈ steps, ∀ x : Adr,
      r.provenance.actor = some x → x ≠ victim → x ∈ coalition)
    (schedule : VictimSchedule victim steps) :
    PairOpenAttackTrace root coalition victim charge steps future :=
  ⟨realizes, noVaultAllowanceKeyCollision_of_visits faithful collision, victim_not_mem,
    coalition_covers, schedule⟩

/-- **P4 open context from real-chain D9.** -/
theorem pair_history_attacker_open_context {cfg : ChainConfig} {deployed future : BlockChain}
    {vault : Adr} (root : PairRoot cfg deployed vault)
    (history : ConfiguredHistoryTrace cfg deployed future)
    (collision : NoVaultVisitKeyCollision (history.pairVisits vault) vault) :
    ∃ steps, PairTraceRealizes root steps future ∧ PairLedgerFaithful vault history steps ∧
      ∀ (coalition : Finset Adr) (victim : Adr)
        (charge : PairStepRecord vault → Blanc.Prorata.AttackAttribution),
        victim ∉ coalition →
        (∀ r ∈ steps, ∀ x : Adr, r.provenance.actor = some x → x ≠ victim → x ∈ coalition) →
        VictimSchedule victim steps →
        outA victim charge steps + sharesOut victim steps ≤
          inA victim charge steps + outsideSubsidy victim charge steps + sharesIn victim steps := by
  obtain ⟨steps, realizes, faithful⟩ :=
    pairTraceRealizes_faithful_of_configuredHistoryTrace root history
  refine ⟨steps, realizes, faithful, fun coalition victim charge notMem covers schedule => ?_⟩
  exact pair_attacker_open_context
    (PairOpenAttackTrace.of_visits (charge := charge) realizes faithful collision notMem covers schedule)

/-- **P4 victim loss bound from real-chain D9.** -/
theorem pair_history_victim_loss_bound {cfg : ChainConfig} {deployed future : BlockChain}
    {vault : Adr} (root : PairRoot cfg deployed vault)
    (history : ConfiguredHistoryTrace cfg deployed future)
    (collision : NoVaultVisitKeyCollision (history.pairVisits vault) vault) :
    ∃ steps, PairTraceRealizes root steps future ∧ PairLedgerFaithful vault history steps ∧
      ∀ (victim : Adr) (deposit exit : PairStepRecord vault) (v m p : Nat),
        victimMoves victim steps = [deposit, exit] →
        deposit.flow = .inbound victim victim v m true →
        exit.flow = .outbound victim victim m p true false →
        v - p ≤ Nat.div (deposit.pre.balance + 1) (deposit.pre.supply + offsetN) + 1 := by
  obtain ⟨steps, realizes, faithful⟩ :=
    pairTraceRealizes_faithful_of_configuredHistoryTrace root history
  exact ⟨steps, realizes, faithful, fun victim deposit exit v m p hmoves hdeposit hexit =>
    pair_victim_loss_bound realizes (faithful.collision collision) hmoves hdeposit hexit⟩

end Blanc.Composition.ProrataWethVault
