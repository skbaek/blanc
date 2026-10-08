import Blanc.Lift.UniswapV2Pair.BurnPositionalCanonical

namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- The original raw Burn caller assumptions produce one same-root admitted
canonical result with exact output, full mutable queues and log correspondence. -/
theorem burnRaw_source_authentic {U K : WriterKey → Prop} {current : Checkpoint}
    {sevm : Sevm} {b publicPost : Devm} {G : Nat}
    (invocation : List Nat) (codeEq : sevm.code = code)
    (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x89afcb44)
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (tracked : K (.balance sevm.currentTarget))
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok publicPost))
    (inj : WriterInj U) (apart : WriterApart U) (sub : ∀ k, K k → U k)
    (trace : ∀ k ∈ mintTraceKeys ⟨0, sevm, St b [] Mem.empty G, .ok publicPost, run⟩, U k)
    (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (b.getCode sevm.currentTarget).toList = sem.image)
    (good : ∀ F ∈ Exec.rawFrameRoots run,
      F.sevm.currentTarget = sevm.currentTarget → LockedGood U F)
    (staticGood : ∀ F ∈ Exec.rawFrameRoots run, F.sevm.currentTarget = sevm.currentTarget →
      ∀ k ∈ staticViewDecodedKeys F.sevm, U k) :
    Nonempty (BurnPositionalCanonicalResult U K current invocation
      ⟨0, sevm, St b [] Mem.empty G, .ok publicPost, run⟩ b publicPost) :=
  burn_positional_canonical invocation codeEq fork selector rep tracked run inj apart sub trace
    sem image installed good staticGood

end Blanc.Lift.UniswapV2Pair
