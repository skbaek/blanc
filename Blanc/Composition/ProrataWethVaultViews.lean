import Blanc.ProrataWethVaultViews
import Blanc.Composition.ProrataWethVaultStaging

/-!
# WETH-backed compiled views of the PRORATA vault

The contract-family view module proves only vault-local reads.  This
composition owner connects `totalAssets()` to the actual configured WETH
`balanceOf(vault)` child and then lifts that exact child effect through the
compiled vault selector.
-/

namespace Blanc.Composition.ProrataWethVault

open Jaune
open Jaune.Ninst Ninst
open scoped LogOutputHinv
open Source

private instance : PopBurn.Inv Devm.logs := ⟨fun run => run.logs⟩
private instance : Burn.Inv Devm.logs := ⟨fun run => run.logs⟩

private instance : Rinst.Hinv Devm.logs Rinst.retdatasize := by
  refine ⟨?_⟩
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  exact (Devm.pushBurn_of_pushItem run).logs

private instance : Rinst.Hinv Devm.logs Rinst.mload := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  rcases Except.bind_eq_ok run with ⟨⟨offset, popped⟩, pop, run⟩
  rcases Except.bind_eq_ok run with ⟨burned, burn, pushed⟩
  rcases Devm.pop_of_popToNat pop with ⟨actual, popDiff⟩
  have burnDiff := Devm.burn_of_chargeGas burn
  have pushDiff := Devm.push_of_push pushed
  exact ((popDiff.logs.trans burnDiff.logs).trans rfl).trans pushDiff.logs⟩

private instance : Linst.Hinv Devm.logs Devm.logs Linst.rev := by
  constructor
  intro sevm pre post run
  simp only [Linst.Run, Linst.run] at run
  rcases Except.bind_eq_ok run with ⟨s1, h1, run⟩
  rcases Except.bind_eq_ok run with ⟨s2, h2, run⟩
  rcases Except.bind_eq_ok run with ⟨s3, h3, impossible⟩
  contradiction

/-- Resources required by the exact WETH child reached from one
`totalAssets` body entry.  The gas premise is restricted to the call state
actually produced by the fixed staging line; it is not a universal gas claim. -/
def TotalAssetsResources (sevm : Sevm) (entry : Devm) : Prop :=
  sevm.depth ≠ 0 ∧
    ∀ callPre,
      Line.Run sevm entry balanceOfStaging callPre →
      StaticGasAvailable callPre 36

/-- The body-entry resource package for one exact compiled endpoint run. -/
def TotalAssetsCompiledResources (sevm : Sevm) (post : Devm) : Prop :=
  ∀ bodyPre,
    Func.RunCompiledTo
        (Blanc.ProrataWethVault.vault.main ::
          Blanc.ProrataWethVault.vault.aux)
        sevm bodyPre Blanc.ProrataWethVault.totalAssets (.ok post) →
      TotalAssetsResources sevm bodyPre

/-- Exact body effect of `totalAssets`: the configured WETH program is read at
the vault address, every account's storage and the parent log frame are
preserved, and the returned ABI word is that pre-call WETH balance. -/
theorem totalAssets_body_effect
    {fs : List Func} {sevm : Sevm} {entry post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm entry)
    (memoryWf : Mem.Wf entry.memory)
    (resources : TotalAssetsResources sevm entry)
    (run : Func.RunCompiledTo fs sevm entry
      Blanc.ProrataWethVault.totalAssets (.ok post)) :
    Blanc.ProrataWethVault.WordViewEffect
      ((entry.state.getStor wethAccount).get sevm.currentTarget.toB256)
      entry post := by
  have memory : MemoryImage entry entry.memory.data.toList := by
    refine ⟨memoryWf, ?_⟩
    intro index
    simp
  unfold Blanc.ProrataWethVault.totalAssets at run
  obtain ⟨callPre, callPost, staging, crossing, suffix⟩ :=
    readTotalAssets_trace run
  have stagingCode : Devm.getCode entry = Devm.getCode callPre :=
    Line.of_inv Devm.getCode (by
      unfold balanceOfStaging mstoreAt pushList
      simp only [List.map, List.cons_append, List.nil_append]
      line_inv) staging
  have callConfig :
      DirectWethConfiguration sevm.currentTarget sevm callPre := by
    refine ⟨config.distinct, config.nonprecompile, ?_⟩
    rw [← congrFun stagingCode wethAccount]
    exact config.code
  obtain ⟨word, returnPre, callStorage, callLogs, returnedWord,
      wordPrefix, returnRun⟩ :=
    readTotalAssets_exactEffect callConfig memory staging resources.1
      (resources.2 callPre staging) crossing suffix
  have suffixSource : Func.Run fs sevm callPost
      (iszero :::
        (Func.rev <?>
          (pushB256 32 ::: retdatasize ::: eq ::: iszero :::
            (Func.rev <?>
              (pushB256 0 ::: mload :::
                Blanc.ProrataWethVault.returnWord))))) post :=
    Func.Run.of_runCompiled
      (Func.RunCompiled.of_runCompiledTo_ok suffix)
  have suffixStorage : Devm.getStor callPost = Devm.getStor post :=
    Func.of_inv Devm.getStor Devm.getStor (by
      unfold Blanc.ProrataWethVault.returnWord
      func_inv) suffixSource
  have suffixLogs : callPost.logs = post.logs :=
    Func.of_inv Devm.logs Devm.logs (by
      unfold Blanc.ProrataWethVault.returnWord
      func_inv) suffixSource
  have stagingStorage : Devm.getStor entry = Devm.getStor callPre :=
    Line.of_inv Devm.getStor (by line_inv) staging
  have stagingLogs : entry.logs = callPre.logs :=
    Line.of_inv Devm.logs (by line_inv) staging
  have returnSource : Func.Run fs sevm returnPre
      Blanc.ProrataWethVault.returnWord post :=
    Func.Run.of_runCompiled
      (Func.RunCompiled.of_runCompiledTo_ok returnRun)
  have output : ReturnsWord word post := by
    simpa only [Blanc.ProrataWethVault.returnWord] using
      (returnsWord_of_storeReturn wordPrefix (by
        simpa only [Blanc.ProrataWethVault.returnWord] using returnSource)).1
  have wordEq : word =
      (callPre.state.getStor wethAccount).get
        sevm.currentTarget.toB256 := by
    have bytesEq := congrArg Bytes.toB256 returnedWord
    simpa only [B256.toB256_toBytes] using bytesEq
  have entryWord : word =
      (entry.state.getStor wethAccount).get
        sevm.currentTarget.toB256 := by
    rw [wordEq]
    exact (congrArg
      (fun storage : Stor => storage.get sevm.currentTarget.toB256)
      (congrFun stagingStorage wethAccount)).symm
  rw [entryWord] at output
  exact ⟨output,
    stagingStorage.trans (callStorage.symm.trans suffixStorage),
    stagingLogs.trans (callLogs.symm.trans suffixLogs)⟩

/-- Compiled `totalAssets()` returns the exact pre-state WETH balance booked
to the vault.  Direct code identity, non-precompile routing, distinct accounts,
depth, and the actual staged-call gas obligation are explicit premises; the
WETH behavior itself is derived from the inherited compiled program. -/
theorem totalAssets_compiled_effect
    {sevm : Sevm} {pre post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (memoryWf : Mem.Wf pre.memory)
    (resources : TotalAssetsCompiledResources sevm post)
    (run : Prog.RunCompiled sevm pre Blanc.ProrataWethVault.vault post)
    (hselector : Sevm.selector sevm = selector "totalAssets" []) :
    sevm.value = 0 ∧
      Blanc.ProrataWethVault.WordViewEffect
        ((pre.state.getStor wethAccount).get sevm.currentTarget.toB256)
        pre post := by
  have hmember :
      (selector "totalAssets" [],
        Blanc.ProrataWethVault.routed 0
          Blanc.ProrataWethVault.totalAssets) ∈
        Blanc.ProrataWethVault.vaultFuncs := by
    simp [Blanc.ProrataWethVault.vaultFuncs]
  rcases Blanc.ProrataWethVault.runCompiled_enters_body_compiled_logs
      run hselector hmember with
    ⟨bodyPre, hvalue, -, entryState, entryMemory, entryLogs, -, bodyRun⟩
  have bodyConfig :
      DirectWethConfiguration sevm.currentTarget sevm bodyPre := by
    refine ⟨config.distinct, config.nonprecompile, ?_⟩
    rw [← getCode_eq_of_state_eq entryState wethAccount]
    exact config.code
  have bodyMemoryWf : Mem.Wf bodyPre.memory := by
    rw [← entryMemory]
    exact memoryWf
  have bodyEffect := totalAssets_body_effect bodyConfig bodyMemoryWf
    (resources bodyPre bodyRun) bodyRun
  rcases bodyEffect with ⟨output, storage, logs⟩
  have entryStorage : Devm.getStor pre = Devm.getStor bodyPre :=
    funext (getStor_eq_of_state_eq entryState)
  have output' : ReturnsWord
      ((pre.state.getStor wethAccount).get sevm.currentTarget.toB256) post := by
    change ReturnsWord
      ((Devm.getStor pre wethAccount).get sevm.currentTarget.toB256) post
    change ReturnsWord
      ((Devm.getStor bodyPre wethAccount).get sevm.currentTarget.toB256) post
      at output
    rw [entryStorage]
    exact output
  exact ⟨hvalue, output', entryStorage.trans storage,
    entryLogs.trans logs⟩

end Blanc.Composition.ProrataWethVault
