import Blanc.LadderReached
import Blanc.ExecutionStagedFrames
import Blanc.ExecutionSenderOccurrences

/-!
# Original selected-domain histories on a reached covered segment

Coverage comes from accepted header chronology and a schedule's timestamp
floor. The conversion retains the supplied block bodies rather than extracting
another history from the transition relation. Raw/settled frames and checked
sender occurrences keep their original order and population.
-/

namespace Blanc.ExecutionTrace

open Jaune

/-- Change only fork-membership proofs, using the actual earlier tip to derive
coverage for each block of the supplied history. -/
def ConfiguredHistoryTraceIn.coveredOfReached
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTraceIn F cfg checkpoint future) (floor : Nat)
    (coverage : ∀ number timestamp fork, floor ≤ timestamp →
      cfg.forkAt number timestamp = .ok fork → CoveredFork fork)
    (start : ∃ tip, checkpoint.blocks.getLast? = some tip ∧ floor ≤ tip.header.timestamp) :
    ConfiguredHistoryTraceIn CoveredFork cfg checkpoint future :=
  match trace with
  | .refl valid context chain => .refl valid context chain
  | .step prior block =>
    .step (prior.coveredOfReached floor coverage start)
      { block with
        forkIn := stateTransitionUsing_covered_of_reached floor coverage
          (prior.toReachUsing.tip_floor start) block.transition block.forkAt }

/-- The original raw forest is unchanged, including failed executions. -/
theorem ConfiguredHistoryTraceIn.coveredOfReached_rawFrames
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTraceIn F cfg checkpoint future) (floor : Nat)
    (coverage : ∀ number timestamp fork, floor ≤ timestamp →
      cfg.forkAt number timestamp = .ok fork → CoveredFork fork)
    (start : ∃ tip, checkpoint.blocks.getLast? = some tip ∧ floor ≤ tip.header.timestamp) :
    (trace.coveredOfReached floor coverage start).rawFrames = trace.rawFrames := by
  induction trace with
  | refl => rfl
  | step prior block ih =>
    simp only [ConfiguredHistoryTraceIn.coveredOfReached, ConfiguredHistoryTraceIn.rawFrames,
      ConfiguredBlockTraceIn.rawFrames, ih]

/-- Complete settlement keeps exactly the original retained forest. -/
theorem ConfiguredHistoryTraceIn.coveredOfReached_settledFrames
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTraceIn F cfg checkpoint future) (floor : Nat)
    (coverage : ∀ number timestamp fork, floor ≤ timestamp →
      cfg.forkAt number timestamp = .ok fork → CoveredFork fork)
    (start : ∃ tip, checkpoint.blocks.getLast? = some tip ∧ floor ≤ tip.header.timestamp) :
    (trace.coveredOfReached floor coverage start).settledFrames = trace.settledFrames := by
  induction trace with
  | refl => rfl
  | step prior block ih =>
    simp only [ConfiguredHistoryTraceIn.coveredOfReached, ConfiguredHistoryTraceIn.settledFrames,
      ConfiguredBlockTraceIn.settledFrames, ih]

/-- Checked transactions retain their original admission evidence and order. -/
theorem ConfiguredHistoryTraceIn.coveredOfReached_senderOccurrences
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTraceIn F cfg checkpoint future) (floor : Nat)
    (coverage : ∀ number timestamp fork, floor ≤ timestamp →
      cfg.forkAt number timestamp = .ok fork → CoveredFork fork)
    (start : ∃ tip, checkpoint.blocks.getLast? = some tip ∧ floor ≤ tip.header.timestamp) :
    (trace.coveredOfReached floor coverage start).senderOccurrences = trace.senderOccurrences := by
  induction trace with
  | refl => rfl
  | step prior block ih =>
    simp only [ConfiguredHistoryTraceIn.coveredOfReached,
      ConfiguredHistoryTraceIn.senderOccurrences, ih]

/-- Re-predication does not filter failed transactions or duplicate queries. -/
theorem ConfiguredHistoryTraceIn.coveredOfReached_senderQueries
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTraceIn F cfg checkpoint future) (floor : Nat)
    (coverage : ∀ number timestamp fork, floor ≤ timestamp →
      cfg.forkAt number timestamp = .ok fork → CoveredFork fork)
    (start : ∃ tip, checkpoint.blocks.getLast? = some tip ∧ floor ≤ tip.header.timestamp) :
    (trace.coveredOfReached floor coverage start).senderQueries = trace.senderQueries := by
  rw [ConfiguredHistoryTraceIn.senderQueries, trace.coveredOfReached_senderOccurrences]
  rfl

/-- Align actual stage endpoints before comparing the original transaction
occurrences. The rest of the body carrier need not be identified. -/
private theorem StagedBodyTrace.senderOccurrences_eq_of_components
    (left right : StagedBodyTrace benv txs ommers wds state bout)
    (beacon : HEq left.beacon right.beacon)
    (history : HEq left.history right.history)
    (transactions : HEq left.transactions right.transactions) :
    left.senderOccurrences = right.senderOccurrences := by
  rcases left with ⟨lrun, lbs, lbb, lb, lhs, lhb, lh, ldecoded, ldecode,
    lbenv, lbout, ltxs, ltrun, lws, lwbout, lwrun, lrs, lrbout, lr,
    lrwd, lrwdeq, lsteq, llist, llisteq, lgas, lbouteq⟩
  rcases right with ⟨rrun, rbs, rbb, rb, rhs, rhb, rh, rdecoded, rdecode,
    rbenv, rbout, rtxs, rtrun, rws, rwbout, rwrun, rrs, rrbout, rr,
    rrwd, rrwdeq, rsteq, rlist, rlisteq, rgas, rbouteq⟩
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj (lb.result.symm.trans rb.result))
  cases (eq_of_heq beacon)
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj (lh.result.symm.trans rh.result))
  cases (eq_of_heq history)
  cases (Except.ok.inj (ldecode.symm.trans rdecode))
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj (ltrun.symm.trans rtrun))
  cases (eq_of_heq transactions)
  rfl

/-- The modern carrier's staged view retains the exact transaction occurrences. -/
theorem StagedBodyTrace.toModern_senderOccurrences
    (trace : StagedBodyTrace benv txs ommers wds state bout)
    (covered : CoveredFork benv.stat.fork) :
    ((trace.toModern covered).toStaged covered).senderOccurrences = trace.senderOccurrences := by
  obtain ⟨beacon, history, transactions, _⟩ := trace.toModern_preserves covered
  exact StagedBodyTrace.senderOccurrences_eq_of_components _ _ beacon history transactions

/-- Modern recovery preserves every original checked sender occurrence. -/
theorem ConfiguredHistoryTraceIn.toModern_senderOccurrences
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTraceIn CoveredFork cfg checkpoint future) :
    trace.toModern.senderOccurrences = trace.senderOccurrences := by
  induction trace with
  | refl => rfl
  | step prior block ih =>
    change prior.toModern.senderOccurrences ++
      ((block.bodyTrace.toModern block.forkIn).toStaged block.forkIn).senderOccurrences =
      prior.senderOccurrences ++ block.bodyTrace.senderOccurrences
    rw [ih]
    exact congrArg (fun entries => prior.senderOccurrences ++ entries)
      (block.bodyTrace.toModern_senderOccurrences block.forkIn)

/-- Modern recovery keeps the original complete sender-query population. -/
theorem ConfiguredHistoryTraceIn.toModern_senderQueries
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTraceIn CoveredFork cfg checkpoint future) :
    trace.toModern.senderQueries = trace.senderQueries := by
  change trace.toModern.senderOccurrences.map SenderOccurrence.query =
    trace.senderOccurrences.map SenderOccurrence.query
  rw [trace.toModern_senderOccurrences]

end Blanc.ExecutionTrace
