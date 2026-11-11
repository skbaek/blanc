import Blanc.ExecutionHistory
import Blanc.ExecutionStagedFrames
import Blanc.ExecutionStagedAdmission
import Blanc.ExecutionNoDelSafeHistory
import Blanc.ExecutionHistoricalAdmission
import Blanc.HistoricalFork
import Blanc.ExecutionHistoryInAppend

/-!
# Concatenation of selected-domain (`In`) configured histories

`ConfiguredHistoryTraceIn.append` joins two `In`-histories end to end
(D to P and P to B into D to B) by induction on the second history's
`.step` spine. Frame lists (`rawFrames`, `settledFrames`) concatenate in
order, and the per-block conjunction predicates (`NoDelScheduled`,
`RewardCreditsFunded`, `FrameAdmitted`) split across the join.

`ConfiguredHistoryTraceIn.map` re-predicates a history across fork
domains; `toHistFork` specializes it along `CoveredFork.histFork`, so a
modern `ConfiguredHistoryTrace` reaches the historical domain through the
existing `ConfiguredHistoryTrace.toIn`.

Contract-neutral: no contract name in any statement. Every proof premise
is discharged on `HistFork` membership or `BodyStageCapabilities`; nothing
assumes delegation, EIP-2929 access, or enabled optional passes. The only
`CoveredFork` occurrence is the explicitly bridged source domain.
-/

namespace Blanc

namespace ExecutionTrace

open Jaune

/-- The settlement-retained roots of a join are in order. -/
theorem ConfiguredHistoryTraceIn.settledFrames_append {F : Fork → Prop}
    {cfg : ChainConfig} {a b c : BlockChain}
    (first : ConfiguredHistoryTraceIn F cfg a b)
    (second : ConfiguredHistoryTraceIn F cfg b c) :
    (append first second).settledFrames =
      first.settledFrames ++ second.settledFrames := by
  induction second with
  | refl =>
      simp only [ConfiguredHistoryTraceIn.append,
        ConfiguredHistoryTraceIn.settledFrames, List.append_nil]
  | step prior block ih =>
      simp only [ConfiguredHistoryTraceIn.append,
        ConfiguredHistoryTraceIn.settledFrames, ih, List.append_assoc]

end ExecutionTrace

end Blanc
