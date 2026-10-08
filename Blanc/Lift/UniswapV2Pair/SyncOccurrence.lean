import Blanc.Lift.CursorOccurrence
import Blanc.Lift.UniswapV2Pair.SyncCanonical

/-! The canonical Sync calls as actual same-frame occurrence steps. -/

namespace Blanc.Lift.UniswapV2Pair

open Jaune

/-- The first carrier reuses the canonical occurrence, slot and returned state. -/
def SyncCanonicalResult.firstOccurrenceStep {K : WriterKey → Prop}
    {current : Checkpoint} {invocation : List Nat} {root : Exec.Deriv} {b post : Devm}
    (result : SyncCanonicalResult K current invocation root b post) :
    CallOccurrenceStep root .staticcall where
  occurrence := result.first
  returned := result.returned0
  instruction := by
    rcases result.order with ⟨_, _, _, instruction, _⟩
    exact instruction
  sameFrame := result.order.1.1
  edge := by
    rcases result.order with ⟨_, _, _, _, edge, _⟩
    exact edge
  result := by
    rcases result.order with ⟨_, _, _, _, _, returned, _⟩
    exact returned

/-- The second carrier reuses the second canonical occurrence and continuation. -/
def SyncCanonicalResult.secondOccurrenceStep {K : WriterKey → Prop}
    {current : Checkpoint} {invocation : List Nat} {root : Exec.Deriv} {b post : Devm}
    (result : SyncCanonicalResult K current invocation root b post) :
    CallOccurrenceStep root .staticcall where
  occurrence := result.second
  returned := result.returned1
  instruction := by
    rcases result.order with ⟨_, _, _, _, _, _, _, _, _, _, _, instruction, _⟩
    exact instruction
  sameFrame := by
    rcases result.order with ⟨_, _, _, _, _, _, _, path, _⟩
    exact path
  edge := by
    rcases result.order with ⟨_, _, _, _, _, _, _, _, _, _, _, _, edge, _⟩
    exact edge
  result := by
    rcases result.order with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, returned, _⟩
    exact returned

/-- Both projected steps retain the canonical call-free predecessor gaps.
Their occurrences and returned states are definitionally the original fields,
so the canonical exact-slot child queues need no transport or re-selection. -/
theorem SyncCanonicalResult.occurrenceSteps_ordered {K : WriterKey → Prop}
    {current : Checkpoint} {invocation : List Nat} {root : Exec.Deriv} {b post : Devm}
    (result : SyncCanonicalResult K current invocation root b post) :
    Exec.Deriv.ExecFreeUntil root result.firstOccurrenceStep.occurrence.node ∧
      Exec.Deriv.ExecFreeUntil result.firstOccurrenceStep.returned
        result.secondOccurrenceStep.occurrence.node := by
  rcases result.order with ⟨firstFree, _, _, _, _, _, secondFree, _⟩
  exact ⟨firstFree, secondFree⟩

end Blanc.Lift.UniswapV2Pair
