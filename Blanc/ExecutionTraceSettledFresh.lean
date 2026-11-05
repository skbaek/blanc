import Blanc.ExecutionHistoryFrameTime
import Blanc.ExecutionTraceEntered

/-!
# Fresh settlement-retained history frames

Every settlement-retained configured-history frame comes from an actual raw
entry and therefore starts with an empty stack and memory. Block membership
uses the existing shared configured-block transport.
-/

namespace Blanc.ExecutionTrace

open Jaune Blanc

variable {cfg : ChainConfig}

/-- A settled history frame's root derivation is a raw frame of the history. -/
theorem ConfiguredHistoryTrace.mem_rawFrames_of_mem_settledFrames {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future) (frame : Exec.Frame)
    (member : frame ∈ trace.settledFrames) :
    (Blanc.Exec.Frame.rootDeriv (frame := frame)) ∈ trace.rawFrames := by
  induction trace with
  | refl => simp only [ConfiguredHistoryTrace.settledFrames, List.not_mem_nil] at member
  | step prior block ih =>
      simp only [ConfiguredHistoryTrace.settledFrames, List.mem_append] at member
      simp only [ConfiguredHistoryTrace.rawFrames, List.mem_append]
      rcases member with member | member
      · exact Or.inl (ih member)
      · exact Or.inr (block.mem_rawFrames_of_settled frame member)

/-- **Every settled frame of a configured history is entered fresh** (empty stack and memory). -/
theorem ConfiguredHistoryTrace.settledFrames_fresh {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future) :
    ∀ f ∈ trace.settledFrames, Exec.FreshEntry f.sevm f.pre :=
  fun f member => trace.rawFrames_entered enteredCondition_fresh _
    (trace.mem_rawFrames_of_mem_settledFrames f member)


end Blanc.ExecutionTrace
