import Blanc.Lift.UniswapV2Pair.SwapPositionalCanonical

namespace Blanc.Lift.UniswapV2Pair

open Jaune

/-- The original successful-run premises produce one recursively admitted Swap result. -/
theorem swap_bytecode_exact_consumes {K : WriterKey → Prop} {current : Checkpoint}
    {sevm : Sevm} {b post : Devm} {G : Nat}
    (invocation : List Nat)
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (b.getCode sevm.currentTarget).toList = sem.image)
    (freshOutput : b.output = [])
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x022c0d9f)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post))
    (hashTInj : WriterInj (WriterExtend K
      (swapTraceKeys ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩)))
    (hashTApart : WriterApart (WriterExtend K
      (swapTraceKeys ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩))) :
    Nonempty (SwapPositionalCanonicalResult K current invocation
      ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ b post) :=
  swap_positional_canonical invocation rep sem image installed freshOutput codeEq fork selector run
    hashTInj hashTApart

/-- Foreign-storage guarantees are fields of the same selected admitted canonical result. -/
theorem swap_bytecode_exact_consumes_own {K : WriterKey → Prop} {current : Checkpoint}
    {sevm : Sevm} {b post : Devm} {G : Nat}
    (invocation : List Nat)
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (b.getCode sevm.currentTarget).toList = sem.image)
    (freshOutput : b.output = [])
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x022c0d9f)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post))
    (hashTInj : WriterInj (WriterExtend K
      (swapTraceKeys ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩)))
    (hashTApart : WriterApart (WriterExtend K
      (swapTraceKeys ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩))) :
    Nonempty (SwapPositionalCanonicalResult K current invocation
      ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ b post) :=
  swap_bytecode_exact_consumes invocation rep sem image installed freshOutput codeEq fork selector run
    hashTInj hashTApart

end Blanc.Lift.UniswapV2Pair
