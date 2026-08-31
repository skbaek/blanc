import Blanc.BeaconDepositConstructorStorageEffects

/-!
# Beacon deposit constructor effects

Public compiled-program and bytecode-execution wrappers for the exact
constructor chronology proved by `BeaconDepositConstructorStorageEffects`.
-/

namespace Blanc.BeaconDeposit

open Jaune
open Jaune.Ninst Blanc.Ninst

/-- Exact main-body budget: nonpayability, scratch initialization, and all
thirty-one zero-hash iterations including the runtime return. -/
def constructorMainGas : Nat := constructorLoopGas 0 31 + 52

/-- Exact constructor program budget including the compiled entry JUMPDEST. -/
def constructorProgramGas : Nat := constructorMainGas + gJumpdest

/-- Successful common `nonpayable` entry is storage-neutral and costs 19 gas. -/
private theorem constructorNonpayable_zero_storageEffectRun
    {fs : List Func} {sevm : Sevm} {base : Devm} {body : Func}
    {K : Nat} {ex : Execution}
    {effects : List (Adr × B256 × B256)}
    (hvalue : sevm.value = 0)
    (tail : Func.StorageEffectRun fs sevm
      (base.setMach ⟨[], Mem.empty, K⟩) body ex effects) :
  Func.StorageEffectRun fs sevm
      (base.setMach ⟨[], Mem.empty, K + 19⟩)
      (nonpayable body) ex effects := by
  unfold nonpayable
  storage_effect_run (3) [1]
  · rw [hvalue]
    rfl
  · simpa only [Devm.setMach_setMach, Devm.memory_setMach,
      show K + 19 - 19 = K by omega] using tail

/-- The compiled constructor main returns the exact runtime, establishes the
canonical final storage, and retains exactly the thirty-one model writes. -/
theorem constructorMain_storageEffectRun
    {sevm : Sevm} {base : Devm}
    (hvalue : sevm.value = 0)
    (world : ConstructorLoopWorld sevm base 0)
    (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hcode : sevm.code.toList = creationCode) :
    ∃ post,
      post.output = code ∧
      post.error = none ∧
      Devm.getStor post sevm.currentTarget = constructorFinalStorage ∧
      Func.StorageEffectRun
        (constructorProgram.main :: constructorProgram.aux) sevm
        (base.setMach ⟨[], Mem.empty, constructorMainGas⟩)
        constructorProgram.main (.ok post)
        (constructorStorageEffectTriples sevm.currentTarget) := by
  obtain ⟨post, postOutput, postError, postStorage, loopRun⟩ :=
    constructorZeroHashLoop_storageEffectRun
      (fs := constructorProgram.main :: constructorProgram.aux)
      (sevm := sevm) (base := base) world hstatic hdepth hpre
      (by rfl) (by rfl) hcode
  have startRun := constructorStart_storageEffectRun
    (K := constructorLoopGas 0 31) (hloop := by rfl) loopRun
  have mainRun := constructorNonpayable_zero_storageEffectRun
    (K := constructorLoopGas 0 31 + 33) hvalue startRun
  refine ⟨post, postOutput, postError, postStorage, ?_⟩
  simpa only [constructorMainGas, constructorProgram, constructorProgramAt]
    using mainRun

/-- Constructor C5/C6 flagship: the compiled creation prefix executes against
the full initcode image, commits exactly the public thirty-one-write chronology,
returns the appended runtime, and establishes the empty-history artifact
invariant from empty target storage. -/
theorem constructor_success_retainedStorageEffectTriples
    {sevm : Sevm} {base : Devm}
    (hvalue : sevm.value = 0)
    (hstorage : Devm.getStor base sevm.currentTarget = Stor.empty)
    (hshaCode : getDelegatedCodeAddress (base.getCode 2) = none)
    (hshaWarm : (2 : Adr) ∈ base.accessedAddresses)
    (herror : base.error = none)
    (hstatic : sevm.isStatic = false)
    (hdepth : sevm.depth ≠ 0)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hcode : sevm.code.toList = creationCode) :
    ∃ post,
    ∃ execution : Exec 0 sevm
        (base.setMach ⟨[], Mem.empty, constructorProgramGas⟩) (.ok post),
      post.output = code ∧
      post.error = none ∧
      Devm.getStor post sevm.currentTarget = constructorFinalStorage ∧
      ArtifactInv (Devm.getStor post sevm.currentTarget) [] ∧
      Prog.RunCompiledTo sevm
        (base.setMach ⟨[], Mem.empty, constructorProgramGas⟩)
        constructorProgram (.ok post) ∧
      Exec.retainedStorageEffectTriples execution =
        constructorStorageEffectTriples sevm.currentTarget := by
  have world : ConstructorLoopWorld sevm base 0 := by
    exact ⟨by simpa only [constructorZeroHashStorage] using hstorage,
      hshaCode, hshaWarm, herror⟩
  obtain ⟨post, postOutput, postError, postStorage, mainRun⟩ :=
    constructorMain_storageEffectRun hvalue world hstatic hdepth hpre hcode
  let mid := base.setMach ⟨[], Mem.empty, constructorMainGas⟩
  have entryBurn : Devm.BurnBy gJumpdest
      (base.setMach ⟨[], Mem.empty, constructorProgramGas⟩) mid := by
    dsimp only [mid]
    apply Devm.burnBy_setMach_gas
    simp only [constructorProgramGas, Devm.gasLeft_setMach]
  have programRun : Prog.RunCompiledTo sevm
      (base.setMach ⟨[], Mem.empty, constructorProgramGas⟩)
      constructorProgram (.ok post) := by
    exact ⟨mid, entryBurn, mainRun.run⟩
  have committed : Execution.commits (.ok post) = true := by
    simp only [Execution.commits, postError, Option.isNone_none]
  obtain ⟨execution, executionEffects⟩ :=
    Prog.exists_exec_retainedStorageEffectTriples_appended
      entryBurn mainRun.path committed constructorInitPrefix_compile.symm
      (by simpa only [creationCode] using hcode)
  have invariant : ArtifactInv
      (Devm.getStor post sevm.currentTarget) [] := by
    rw [postStorage]
    exact constructorFinalStorage_artifactInv
  exact ⟨post, execution, postOutput, postError, postStorage, invariant,
    programRun, executionEffects⟩

end Blanc.BeaconDeposit
