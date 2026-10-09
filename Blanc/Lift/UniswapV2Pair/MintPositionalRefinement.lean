import Blanc.Lift.UniswapV2Pair.MintPositionalLogs
import Blanc.Lift.UniswapV2Pair.MintCanonicalOwn

namespace Blanc.Lift.UniswapV2Pair

open Jaune

/-- One admitted canonical Mint result with its complete raw/source log image. -/
structure MintPositionalResult (K : WriterKey → Prop) (current : Checkpoint)
    (invocation : List Nat) (root : Exec.Deriv) (b post : Devm) where
  canonical : MintPositionalCanonicalResult K current invocation root b post
  added : List PendingLog
  raw : List Log
  sourceLogs : canonical.final.current.logs = current.logs ++ added
  rawLogs : post.logs = b.logs ++ raw
  images : added.map (PendingLog.rawWith (mintOwnedRaw root.sevm.currentTarget)) = raw.map some

/-- The original caller premises retain the same admitted result and complete log image. -/
theorem mint_bytecode_exact_consumes {K : WriterKey → Prop} {current : Checkpoint}
    {sevm : Sevm} {b post : Devm} {G : Nat}
    (invocation : List Nat)
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (b.getCode sevm.currentTarget).toList = sem.image)
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x6a627842)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post))
    (inj : WriterInj
      (WriterExtend K (mintTraceKeys ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩)))
    (apart : WriterApart
      (WriterExtend K (mintTraceKeys ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩))) :
    Nonempty (MintPositionalResult K current invocation
      ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ b post) := by
  obtain ⟨canonical⟩ := mint_positional_canonical invocation rep sem image installed
    codeEq fork selector run inj apart
  obtain ⟨added, raw, sourceLogs, rawLogs, images⟩ := canonical.log_image rep
  exact ⟨{
    canonical := canonical, added := added, raw := raw,
    sourceLogs := sourceLogs, rawLogs := rawLogs, images := images}⟩

/-- Foreign storage is unchanged by the same original Mint execution. -/
structure MintPositionalOwnResult (K : WriterKey → Prop) (current : Checkpoint)
    (invocation : List Nat) (root : Exec.Deriv) (b post : Devm) where
  result : MintPositionalResult K current invocation root b post
  foreign : ∀ a, a ≠ root.sevm.currentTarget → post.getStor a = b.getStor a

/-- The original caller premises retain the same admitted result and complete log image. -/
theorem mint_bytecode_exact_consumes_own {K : WriterKey → Prop} {current : Checkpoint}
    {sevm : Sevm} {b post : Devm} {G : Nat}
    (invocation : List Nat)
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (b.getCode sevm.currentTarget).toList = sem.image)
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x6a627842)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post))
    (inj : WriterInj
      (WriterExtend K (mintTraceKeys ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩)))
    (apart : WriterApart
      (WriterExtend K (mintTraceKeys ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩))) :
    Nonempty (MintPositionalOwnResult K current invocation
      ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ b post) := by
  obtain ⟨result⟩ := mint_bytecode_exact_consumes invocation rep sem image installed
    codeEq fork selector run inj apart
  exact ⟨{result := result, foreign := mint_bytecode_foreign_storage codeEq fork selector run}⟩

end Blanc.Lift.UniswapV2Pair
