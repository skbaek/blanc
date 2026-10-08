import Blanc.Lift.UniswapV2Pair.SourceOccurrence

namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- The original slot and spawning equation determine one complete queue at
the supplied parent index, including settlement pruning and full paths. -/
theorem SourceSlotQueue.paths_unique {root : Exec.Deriv} {x : Xinst}
    {call : CallOccurrenceStep root x} {pair : Adr} {index : Nat}
    {left right : List Exec.LocatedFrame}
    (a : SourceSlotQueue call pair index left)
    (b : SourceSlotQueue call pair index right) : left = right := by
  rcases a with ⟨none, empty⟩ |
    ⟨evm, raw, callee, resume, pc, child, next, spawn, enter, resumed, slot, run, paths⟩
  · rcases b with ⟨_, empty'⟩ |
      ⟨evm', raw', callee', resume', pc', child', next', spawn', enter', resumed',
        some, run', paths'⟩
    · exact empty.trans empty'.symm
    · rw [none] at some
      cases some
  · rcases b with ⟨none, _⟩ |
      ⟨evm', raw', callee', resume', pc', child', next', spawn', enter', resumed',
        slot', run', paths'⟩
    · rw [none] at slot
      cases slot
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (slot.symm.trans slot'))
      obtain ⟨rfl, rfl, rfl⟩ := Step.spawn.inj (spawn.symm.trans spawn')
      have same := Exec.unique child child'
      subst child'
      exact paths.trans paths'.symm

end Blanc.Lift.UniswapV2Pair
