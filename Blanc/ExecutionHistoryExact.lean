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
  have hId := stateTransitionUsing_success_chainId_eq h
  have selected := h
  rw [stateTransitionUsing_eq_of_chainId_eq hId] at selected
  obtain ⟨rules, _, core⟩ := Except.bind_eq_ok selected
  rw [stateTransitionAt_eq_ok_iff, stateTransitionE] at core
  obtain ⟨_, _, core⟩ := Except.bind_eq_ok core
  obtain ⟨_, _, core⟩ := Except.bind_eq_ok core
  dsimp only at core
  obtain ⟨⟨bodyState, blockOutput⟩, _, core⟩ := Except.bind_eq_ok core
  dsimp only at core
  obtain ⟨_, _, final⟩ := Except.bind_eq_ok core
  obtain ⟨_, _, final⟩ := Except.bind_eq_ok final
  have executed : post.blocks.getLast? = some block := by
    have blocks := congrArg (fun chain : BlockChain => chain.blocks.getLast?)
      (Except.ok.inj final)
    simpa only [appendBlock_getLast?] using blocks.symm
  have retained : post.blocks.getLast? = some trace.block :=
    (congrArg (fun chain : BlockChain => chain.blocks.getLast?) trace.postEq).trans
      (appendBlock_getLast? _ _)
  exact Option.some.inj (retained.symm.trans executed)

end ExecutionTrace

end Blanc
