import Blanc.Lift.UniswapV2Pair.SkimPositionalCanonical

namespace Blanc.Lift.UniswapV2Pair
open Jaune

/-- The strong original-name Skim refinement retains the same raw run, source
result, original indexed slot queues and recursively admitted child outputs. -/
theorem skim_bytecode_exact_consumes {K : WriterKey → Prop} {current : Checkpoint}
    {sevm : Sevm} {b post : Devm} {G : Nat}
    (invocation : List Nat)
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (b.getCode sevm.currentTarget).toList = sem.image)
    (freshOutput : b.output = [])
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xbc25cf77)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post))
    (hashTInj : WriterInj (WriterExtend K
      (skimTraceKeys ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩)))
    (hashTApart : WriterApart (WriterExtend K
      (skimTraceKeys ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩))) :
    Nonempty (SkimPositionalCanonicalResult K current invocation
      ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ b post) :=
  skim_positional_canonical invocation rep sem image installed freshOutput codeEq fork selector run
    hashTInj hashTApart

/-- Foreign-storage silence is attached to that same selected canonical result,
including the actual worlds returned by its two ordinary transfer calls. -/
structure SkimPositionalOwnResult (K : WriterKey → Prop) (current : Checkpoint)
    (invocation : List Nat) (root : Exec.Deriv) (b post : Devm) where
  canonical : SkimPositionalCanonicalResult K current invocation root b post
  initialForeign : ∀ a, a ≠ root.sevm.currentTarget →
    (temporalAccountAccessBase (skimCachedWorld root.sevm b)
      (skimToken0 root.sevm b).toAdr).getStor a = b.getStor a
  secondQuery : ∀ a,
    (temporalAccountAccessBase
      (afterSload root.sevm canonical.positions.two.transfer.call.returned.devm 8)
      (skimToken1 root.sevm b &&& 0xffffffffffffffffffffffffffffffffffffffff).toAdr).getStor a =
        canonical.positions.two.transfer.call.returned.devm.getStor a
  finalForeign : ∀ a, a ≠ root.sevm.currentTarget →
    post.getStor a = canonical.positions.transfer.call.returned.devm.getStor a

/-- The original own-storage caller assumptions produce one strong canonical
result with its own-code foreign-storage guarantees; no old true-bit transcript
or detached model result is selected. -/
theorem skim_bytecode_exact_consumes_own {K : WriterKey → Prop} {current : Checkpoint}
    {sevm : Sevm} {b post : Devm} {G : Nat}
    (invocation : List Nat)
    (rep : WriterRep K (b.getStor sevm.currentTarget) current.state)
    (sem : CodeSem) (image : sem.image = some code.toList)
    (installed : some (b.getCode sevm.currentTarget).toList = sem.image)
    (freshOutput : b.output = [])
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0xbc25cf77)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post))
    (hashTInj : WriterInj (WriterExtend K
      (skimTraceKeys ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩)))
    (hashTApart : WriterApart (WriterExtend K
      (skimTraceKeys ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩))) :
    Nonempty (SkimPositionalOwnResult K current invocation
      ⟨0, sevm, St b [] Mem.empty G, .ok post, run⟩ b post) := by
  obtain ⟨canonical⟩ := skim_bytecode_exact_consumes invocation rep sem image installed freshOutput
    codeEq fork selector run hashTInj hashTApart
  refine ⟨{canonical := canonical, initialForeign := ?_, secondQuery := ?_, finalForeign := ?_}⟩
  · intro a foreign
    simp only [Devm.getStor, Devm.getAcct, temporalAccountAccessBase_state]
    change (skimCachedWorld sevm b).getStor a = b.getStor a
    unfold skimCachedWorld syncLockedWorld
    rw [afterSload_getStor, afterSload_getStor, afterSload_getStor,
      afterSstore_getStor_ne _ _ _ _ _ (Ne.symm foreign), afterSload_getStor]
  · intro a
    simp only [Devm.getStor, Devm.getAcct, temporalAccountAccessBase_state]
    exact afterSload_getStor _ _ _ _
  · intro a foreign
    obtain ⟨M, gas, postEq⟩ := canonical.positions.post_image (post := post) rfl fork
    have projected := congrArg (fun d : Devm => d.getStor a) postEq
    change post.getStor a = (afterSstore sevm canonical.positions.transfer.call.returned.devm 12 1).getStor a
      at projected
    exact projected.trans (afterSstore_getStor_ne _ _ _ _ _ (Ne.symm foreign))

/-- The same admitted Skim result preserves the original source liquidity core.
This projects the existing source invariant without selecting another result. -/
theorem SkimPositionalCanonicalResult.liquidityCore {K : WriterKey → Prop}
    {current : Checkpoint} {invocation : List Nat} {root : Exec.Deriv} {b post : Devm}
    (result : SkimPositionalCanonicalResult K current invocation root b post) :
    (skimPositionalResult result.balance0 result.transfer0 result.balance1 result.transfer1).frame.current.state.liquidityCore =
      current.state.liquidityCore :=
  skim_source_liquidity result.admitted.positional.forget rfl

end Blanc.Lift.UniswapV2Pair
