import Blanc.ExecutionHistory

/-!
Downstream identification of the literal block retained by a configured
transition trace. This does not rebuild the transition's body evidence.
-/

namespace Blanc

open Jaune

namespace ExecutionTrace

/-- A successful transition to the same post-world identifies the retained
block, because both append it as the last block of the post-world. -/
theorem ConfiguredBlockTrace.block_eq_of_transition
    {cfg : ChainConfig} {pre post : BlockChain} {block : Block}
    (trace : ConfiguredBlockTrace cfg pre post)
    (h : stateTransitionUsing cfg pre block = .ok post) :
    trace.block = block := by
  obtain ⟨_, -, hs⟩ := stateTransitionUsing_scheduled_ok h
  obtain ⟨-, hblocks, -⟩ := stateTransitionCoreE_eq_ok (stateTransitionScheduledE_eq_ok_iff.mp hs)
  have executed : post.blocks.getLast? = some block := by
    rw [hblocks]
    exact appendBlock_getLast? _ _
  have retained : post.blocks.getLast? = some trace.block :=
    (congrArg (fun chain : BlockChain => chain.blocks.getLast?) trace.postEq).trans
      (appendBlock_getLast? _ _)
  exact Option.some.inj (retained.symm.trans executed)

end ExecutionTrace

end Blanc
