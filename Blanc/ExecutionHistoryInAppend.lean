import Blanc.ExecutionHistory
import Blanc.ExecutionStagedFrames
import Blanc.ExecutionStagedAdmission
import Blanc.ExecutionNoDelSafeHistory
import Blanc.ExecutionHistoricalAdmission
import Blanc.HistoricalFork

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

/-- Re-predicate one retained block across fork domains. Only the `forkIn`
membership proof changes; the retained body is untouched. -/
def ConfiguredBlockTraceIn.map {F G : Fork → Prop} {cfg : ChainConfig}
    {pre post : BlockChain} (trace : ConfiguredBlockTraceIn F cfg pre post)
    (h : ∀ f, F f → G f) : ConfiguredBlockTraceIn G cfg pre post :=
  { trace with forkIn := h _ trace.forkIn }

/-- Re-predicate a retained `In`-history across fork domains. -/
def ConfiguredHistoryTraceIn.map {F G : Fork → Prop} {cfg : ChainConfig}
    {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (h : ∀ f, F f → G f) : ConfiguredHistoryTraceIn G cfg checkpoint future :=
  match history with
  | .refl hcfg hctx hid => .refl hcfg hctx hid
  | .step prior block => .step (prior.map h) (block.map h)

/-- View a covered-domain block in the historical domain. -/
def ConfiguredBlockTraceIn.toHistFork {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTraceIn CoveredFork cfg pre post) :
    ConfiguredBlockTraceIn HistFork cfg pre post :=
  trace.map fun _ hf => hf.histFork

/-- View a covered-domain `In`-history in the historical domain. -/
def ConfiguredHistoryTraceIn.toHistFork {cfg : ChainConfig}
    {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn CoveredFork cfg checkpoint future) :
    ConfiguredHistoryTraceIn HistFork cfg checkpoint future :=
  history.map fun _ hf => hf.histFork

/-- View a modern configured history as a historical-domain `In`-history. -/
def ConfiguredHistoryTrace.toHistForkIn {cfg : ChainConfig}
    {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTrace cfg checkpoint future) :
    ConfiguredHistoryTraceIn HistFork cfg checkpoint future :=
  history.toIn.toHistFork

/-- Concatenate two `In`-histories end to end, by induction on the second. -/
def ConfiguredHistoryTraceIn.append {F : Fork → Prop} {cfg : ChainConfig}
    {a b c : BlockChain} (first : ConfiguredHistoryTraceIn F cfg a b)
    (second : ConfiguredHistoryTraceIn F cfg b c) :
    ConfiguredHistoryTraceIn F cfg a c :=
  match second with
  | .refl _ _ _ => first
  | .step prior block => .step (append first prior) block

/-- The raw roots of a join are the two histories' raw roots in order. -/
theorem ConfiguredHistoryTraceIn.rawFrames_append {F : Fork → Prop}
    {cfg : ChainConfig} {a b c : BlockChain}
    (first : ConfiguredHistoryTraceIn F cfg a b)
    (second : ConfiguredHistoryTraceIn F cfg b c) :
    (append first second).rawFrames = first.rawFrames ++ second.rawFrames := by
  induction second with
  | refl =>
      simp only [ConfiguredHistoryTraceIn.append,
        ConfiguredHistoryTraceIn.rawFrames, List.append_nil]
  | step prior block ih =>
      simp only [ConfiguredHistoryTraceIn.append,
        ConfiguredHistoryTraceIn.rawFrames, ih, List.append_assoc]

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

/-- No-deletion scheduling splits across a join. -/
theorem ConfiguredHistoryTraceIn.NoDelScheduled_append {F : Fork → Prop}
    {cfg : ChainConfig} {a b c : BlockChain}
    (first : ConfiguredHistoryTraceIn F cfg a b)
    (second : ConfiguredHistoryTraceIn F cfg b c) (wa : Adr) :
    (append first second).NoDelScheduled wa ↔
      first.NoDelScheduled wa ∧ second.NoDelScheduled wa := by
  induction second with
  | refl =>
      simp only [ConfiguredHistoryTraceIn.append,
        ConfiguredHistoryTraceIn.NoDelScheduled, and_true]
  | step prior block ih =>
      simp only [ConfiguredHistoryTraceIn.append,
        ConfiguredHistoryTraceIn.NoDelScheduled, ih, and_assoc]

/-- Reward-funding splits across a join. -/
theorem ConfiguredHistoryTraceIn.RewardCreditsFunded_append {F : Fork → Prop}
    {cfg : ChainConfig} {a b c : BlockChain}
    (first : ConfiguredHistoryTraceIn F cfg a b)
    (second : ConfiguredHistoryTraceIn F cfg b c) :
    (append first second).RewardCreditsFunded ↔
      first.RewardCreditsFunded ∧ second.RewardCreditsFunded := by
  induction second with
  | refl =>
      simp only [ConfiguredHistoryTraceIn.append,
        ConfiguredHistoryTraceIn.RewardCreditsFunded, and_true]
  | step prior block ih =>
      simp only [ConfiguredHistoryTraceIn.append,
        ConfiguredHistoryTraceIn.RewardCreditsFunded, ih, and_assoc]

/-- Entry admission splits across a join. -/
theorem ConfiguredHistoryTraceIn.FrameAdmitted_append {F : Fork → Prop}
    {cfg : ChainConfig} {a b c : BlockChain}
    (first : ConfiguredHistoryTraceIn F cfg a b)
    (second : ConfiguredHistoryTraceIn F cfg b c) (ca : Adr)
    (entry : Sevm → Devm → Prop) :
    (append first second).FrameAdmitted ca entry ↔
      first.FrameAdmitted ca entry ∧ second.FrameAdmitted ca entry := by
  induction second with
  | refl =>
      simp only [ConfiguredHistoryTraceIn.append,
        ConfiguredHistoryTraceIn.FrameAdmitted, and_true]
  | step prior block ih =>
      simp only [ConfiguredHistoryTraceIn.append,
        ConfiguredHistoryTraceIn.FrameAdmitted, ih, and_assoc]

/-- Re-predication of one block keeps its raw roots: only the `forkIn`
membership proof changes. -/
theorem ConfiguredBlockTraceIn.map_rawFrames {F G : Fork → Prop}
    {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTraceIn F cfg pre post)
    (h : ∀ f, F f → G f) :
    (trace.map h).rawFrames = trace.rawFrames := rfl

/-- Re-predication of one block keeps its settlement-retained roots. -/
theorem ConfiguredBlockTraceIn.map_settledFrames {F G : Fork → Prop}
    {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTraceIn F cfg pre post)
    (h : ∀ f, F f → G f) :
    (trace.map h).settledFrames = trace.settledFrames := rfl

/-- Re-predication keeps the raw roots. -/
theorem ConfiguredHistoryTraceIn.map_rawFrames {F G : Fork → Prop}
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (h : ∀ f, F f → G f) :
    (history.map h).rawFrames = history.rawFrames := by
  induction history with
  | refl =>
      simp only [ConfiguredHistoryTraceIn.map,
        ConfiguredHistoryTraceIn.rawFrames]
  | step prior block ih =>
      simp only [ConfiguredHistoryTraceIn.map,
        ConfiguredHistoryTraceIn.rawFrames, ih,
        ConfiguredBlockTraceIn.map_rawFrames]

/-- Re-predication keeps the settlement-retained roots. -/
theorem ConfiguredHistoryTraceIn.map_settledFrames {F G : Fork → Prop}
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (h : ∀ f, F f → G f) :
    (history.map h).settledFrames = history.settledFrames := by
  induction history with
  | refl =>
      simp only [ConfiguredHistoryTraceIn.map,
        ConfiguredHistoryTraceIn.settledFrames]
  | step prior block ih =>
      simp only [ConfiguredHistoryTraceIn.map,
        ConfiguredHistoryTraceIn.settledFrames, ih,
        ConfiguredBlockTraceIn.map_settledFrames]

/-- The historical-domain view keeps the raw roots. -/
theorem ConfiguredHistoryTraceIn.toHistFork_rawFrames {cfg : ChainConfig}
    {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn CoveredFork cfg checkpoint future) :
    history.toHistFork.rawFrames = history.rawFrames :=
  history.map_rawFrames _

/-- The historical-domain view keeps the settlement-retained roots. -/
theorem ConfiguredHistoryTraceIn.toHistFork_settledFrames {cfg : ChainConfig}
    {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn CoveredFork cfg checkpoint future) :
    history.toHistFork.settledFrames = history.settledFrames :=
  history.map_settledFrames _

/-- A modern history viewed historically keeps its raw roots. -/
theorem ConfiguredHistoryTrace.toHistForkIn_rawFrames {cfg : ChainConfig}
    {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTrace cfg checkpoint future) :
    history.toHistForkIn.rawFrames = history.rawFrames := by
  unfold ConfiguredHistoryTrace.toHistForkIn ConfiguredHistoryTraceIn.toHistFork
  rw [ConfiguredHistoryTraceIn.map_rawFrames,
    ConfiguredHistoryTrace.toIn_rawFrames]

/-- A modern history viewed historically keeps its settlement-retained roots. -/
theorem ConfiguredHistoryTrace.toHistForkIn_settledFrames {cfg : ChainConfig}
    {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTrace cfg checkpoint future) :
    history.toHistForkIn.settledFrames = history.settledFrames := by
  unfold ConfiguredHistoryTrace.toHistForkIn ConfiguredHistoryTraceIn.toHistFork
  rw [ConfiguredHistoryTraceIn.map_settledFrames,
    ConfiguredHistoryTrace.toIn_settledFrames]

end ExecutionTrace

end Blanc
