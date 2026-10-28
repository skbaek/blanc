import Blanc.ExecutionHistoryInAppend
import Blanc.ExecutionMidHistoryIn

/-! Structural reassociation preserves the actual configured history witnesses. -/
namespace Blanc.ExecutionTrace

open Jaune

/-- Reassociation changes only parentheses, preserving every original block witness. -/
theorem ConfiguredHistoryTraceIn.append_assoc
    {F : Fork → Prop} {cfg : ChainConfig} {a b c d : BlockChain}
    (first : ConfiguredHistoryTraceIn F cfg a b)
    (middle : ConfiguredHistoryTraceIn F cfg b c)
    (last : ConfiguredHistoryTraceIn F cfg c d) :
    (first.append middle).append last = first.append (middle.append last) := by
  induction last with
  | refl => rfl
  | step prior block ih =>
      simp only [ConfiguredHistoryTraceIn.append, ih]

/-- A selected-cut history follows the same original whole-block reassociation. -/
theorem MidHistoryTraceIn.append_assoc
    {F : Fork → Prop} {cfg : ChainConfig} {start : Benv} {a b c : BlockChain}
    (first : MidHistoryTraceIn F cfg start a)
    (middle : ConfiguredHistoryTraceIn F cfg a b)
    (last : ConfiguredHistoryTraceIn F cfg b c) :
    (first.append middle).append last = first.append (middle.append last) := by
  induction last with
  | refl => rfl
  | step prior block ih =>
      simp only [ConfiguredHistoryTraceIn.append, MidHistoryTraceIn.append, ih]

end Blanc.ExecutionTrace
