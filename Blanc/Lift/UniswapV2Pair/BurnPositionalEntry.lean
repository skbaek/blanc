import Blanc.Lift.UniswapV2Pair.BurnPositionalInitialSource
import Blanc.Lift.UniswapV2Pair.BurnPositionalInv

namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- Original successful entry guards and the incoming representation select
this exact typed first suspension, without extra source-entry premises. -/
theorem burn_start_segment_of_success {sevm : Sevm} {b post : Devm} {G : Nat}
    {K : WriterKey → Prop} {current : Checkpoint} (invocation : List Nat)
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x89afcb44)
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    startTyped current (writerContext sevm invocation) (.burn (Sevm.dataWord sevm 4).toAdr) =
      .suspended (burnSourceLockedFrame current (writerContext sevm invocation)
        (Sevm.dataWord sevm 4).toAdr)
        (requestFor .burnInitialBalance0 current.state.token0 (.balanceOf sevm.currentTarget))
        (.burnInitialBalance0 ⟨(Sevm.dataWord sevm 4).toAdr, current.state.cachedReserves,
          current.state.token0, current.state.token1⟩) := by
  obtain ⟨value, _, _, unlocked, nonstatic, _⟩ :=
    burn_prefix_guards_of_success codeEq fork selector run
  rcases rep.fixed with ⟨_, _, _, _, _, _, _, _, _, _, _, represented⟩
  have entryUnlocked : current.state.unlocked = 1 := represented.symm.trans unlocked
  exact burn_startTyped_suspended value nonstatic entryUnlocked

end Blanc.Lift.UniswapV2Pair
