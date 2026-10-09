import Blanc.Lift.UniswapV2Pair.MintCanonical
import Blanc.Lift.LocalStorage

/-!
# Canonical mint frame: foreign storage

The mint callee (certificate entry 41) and every entry it reaches are storage-local (the only
external call is `STATICCALL`, no `SELFDESTRUCT`), so a successful raw mint run leaves the
complete storage of every account other than the Pair unchanged.
-/

namespace Blanc.Lift.UniswapV2Pair

open Jaune

/-- The mint callee entry and every certificate entry it reaches. -/
def mintCalleeEntries : List Nat :=
  [9, 11, 12, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 41, 56, 58, 59, 60, 62, 65, 66, 68, 69,
    70, 72, 74]

theorem mintCalleeEntries_storLocal : Blanc.Lift.StorLocalSet cert.prog mintCalleeEntries = true := by
  decide +kernel

/-- Every successful raw mint run keeps the complete storage of every foreign account. -/
theorem mint_bytecode_foreign_storage {sevm : Sevm} {b post : Devm} {G : Nat}
    (codeEq : sevm.code = code) (fork : CoveredFork sevm.benvStat.fork)
    (selector : Blanc.Sevm.selector sevm = 0x6a627842)
    (run : Exec 0 sevm (St b [] Mem.empty G) (.ok post)) :
    ∀ a, a ≠ sevm.currentTarget → post.getStor a = b.getStor a := by
  intro a foreign
  obtain ⟨f, entry, derived⟩ := lift_sound_in cert_check codeEq fork run
  rw [show cert.prog[0]? = some t_0000_c0 from rfl] at entry
  cases entry
  obtain ⟨_, calleePost, publicPost, _, callee, _, _, halted, _, stor, _⟩ :=
    mintPc0_return_inv fork selector derived
  have postEq := Outcome.halted.inj halted
  subst postEq
  rw [stor a]
  exact Blanc.Lift.SFunc.Run.foreignStor_of_storLocal mintCalleeEntries_storLocal fork
    (by decide +kernel) (by decide +kernel) (callee.mono Blanc.Lift.StepIn.toRun) (Ne.symm foreign)

/-- The canonical mint frame together with the foreign-storage silence of the same run. -/
theorem mint_bytecode_exact_consumes_own_legacy {K : WriterKey → Prop} {current : Checkpoint}
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
    (∀ a, a ≠ sevm.currentTarget → post.getStor a = b.getStor a) ∧
      MintCanonicalResult K current invocation run := by
  exact ⟨mint_bytecode_foreign_storage codeEq fork selector run,
    mint_bytecode_exact_consumes_legacy invocation rep sem image installed codeEq fork selector run
      inj apart⟩

end Blanc.Lift.UniswapV2Pair
