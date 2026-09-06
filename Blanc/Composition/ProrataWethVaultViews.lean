import Blanc.ProrataWethVaultViews
import Blanc.CompiledFixedInvariance
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

/-- Resources required by the exact WETH child reached from one
`totalAssets` body entry.  The gas premise is restricted to the call state
actually produced by the fixed staging line; it is not a universal gas claim. -/
def TotalAssetsResources (sevm : Sevm) (entry : Devm) : Prop :=
  sevm.depth ≠ 0 ∧
    ∀ callPre,
      Line.Run sevm entry balanceOfStaging callPre →
      StaticGasAvailable callPre 36

/-- The body-entry resource package for a selected compiled endpoint whose
body contains one `totalAssets` crossing.  Quantifying over the body here
keeps the gas premise tied to the exact selector occurrence rather than to a
universal source function. -/
def TotalAssetsCompiledResourcesFor
    (sevm : Sevm) (post : Devm) (body : Func) : Prop :=
  ∀ bodyPre,
    Func.RunCompiledTo
        (Blanc.ProrataWethVault.vault.main ::
          Blanc.ProrataWethVault.vault.aux)
        sevm bodyPre body (.ok post) →
      TotalAssetsResources sevm bodyPre

/-- Existing specialization for the public `totalAssets()` endpoint. -/
def TotalAssetsCompiledResources (sevm : Sevm) (post : Devm) : Prop :=
  TotalAssetsCompiledResourcesFor sevm post
    Blanc.ProrataWethVault.totalAssets

/-- A successful vault balance query had room to enter its STATICCALL child.
The depth fact comes from the actual crossing and the executed zero-status
guard, independently of the configured asset and any call-gas premise. -/
private theorem readTotalAssets_depth_ne_zero
    {fs : List Func} {sevm : Sevm} {entry final : Devm} {body : Func}
    (memoryWf : Mem.Wf entry.memory)
    (run : Func.RunCompiledTo fs sevm entry
      (Blanc.ProrataWethVault.readTotalAssets body) (.ok final)) :
    sevm.depth ≠ 0 := by
  have memory : MemoryImage entry entry.memory.data.toList := by
    refine ⟨memoryWf, ?_⟩
    intro index
    simp
  obtain ⟨callPre, callPost, staging, crossing, suffix⟩ :=
    readTotalAssets_trace run
  obtain ⟨gasWord, rest, stack, -, -⟩ :=
    balanceOfStaging_boundary memory staging
  have operands :
      gasWord :: wethAccount.toB256 :: 28 :: 36 :: 0 :: 32 :: rest <<+
        callPre.stack := by
    rw [stack]
    exact ⟨[], by simp [Split]⟩
  obtain ⟨status, tail, _, statusStack, statusNonzero, _⟩ :=
    checkedCall_status_nonzero suffix
  rcases of_run_staticcall_val_with_depth operands
      (Ninst.Run.of_runCompiled crossing) with failure | success
  · obtain ⟨zeroPrefix, -, -⟩ := failure
    have statusPrefix : status :: [] <<+ callPost.stack := by
      rw [statusStack]
      exact pref_append [status] tail
    exact (statusNonzero (pref_head_unique zeroPrefix statusPrefix).symm).elim
  · obtain ⟨_, _, _, _, _, _, _, positiveDepth, _⟩ := success
    exact Nat.ne_of_gt positiveDepth

/-- The actual configured WETH crossing paid its parent-side gas charge. -/
private theorem staticGasAvailable_of_runCompiled
    {sevm : Sevm} {pre post : Devm} {inputSize : B256}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (run : Ninst.RunCompiled sevm pre staticcall post) :
    StaticGasAvailable pre inputSize := by
  intro gasWord rest stack
  obtain ⟨xl, _, steps⟩ := run
  have execution := steps 0
  rw [Ninst.StepRun, Ninst.step_exec, XStep.run_toStep] at execution
  let popped := pre.setMach ⟨rest, pre.memory, pre.gasLeft⟩
  let base := addAccessedAddress popped wethAccount
  have address : wethAccount.toB256.toAdr = wethAccount :=
    toAdr_toB256 wethAccount
  have code : base.state.getCode wethAccount = pre.getCode wethAccount := rfl
  have nondelegated : getDelegatedCodeAddress (pre.getCode wethAccount) = none := by
    unfold getDelegatedCodeAddress
    rw [if_neg config.notDelegated]
  have delegation : accessDelegation base wethAccount =
      ⟨false, wethAccount, pre.getCode wethAccount, 0, base⟩ := by
    simp only [accessDelegation, code, nondelegated]
  dsimp only [base, popped] at delegation
  simp only [Xinst.step, Devm.pop_eq_ok stack, bind, Except.bind] at execution
  rw [Devm.popToAdr_eq_ok
    (devm := pre.setMach ⟨wethAccount.toB256 :: 28 :: inputSize :: 0 :: 32 :: rest,
      pre.memory, pre.gasLeft⟩) rfl] at execution
  simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach] at execution
  rw [Devm.popToNat_eq_ok
    (devm := pre.setMach ⟨28 :: inputSize :: 0 :: 32 :: rest,
      pre.memory, pre.gasLeft⟩) rfl] at execution
  simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach] at execution
  rw [Devm.popToNat_eq_ok
    (devm := pre.setMach ⟨inputSize :: 0 :: 32 :: rest,
      pre.memory, pre.gasLeft⟩) rfl] at execution
  simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach] at execution
  rw [Devm.popToNat_eq_ok
    (devm := pre.setMach ⟨0 :: 32 :: rest, pre.memory, pre.gasLeft⟩) rfl] at execution
  simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach] at execution
  rw [Devm.popToNat_eq_ok
    (devm := pre.setMach ⟨32 :: rest, pre.memory, pre.gasLeft⟩) rfl] at execution
  simp only [Devm.setMach_setMach, Devm.memory_setMach, Devm.gasLeft_setMach,
    address, delegation, Nat.add_zero] at execution
  split at execution
  · cases XStep.run_ofExcept_error execution
  · rename_i charged charge
    exact chargeGas_le charge

-- Retain the resource argument for existing callers; the proof derives its
-- needed depth and gas facts from successful execution.
set_option linter.unusedVariables false in
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
  have depth := readTotalAssets_depth_ne_zero memoryWf run
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
  obtain ⟨word, returnPre, -, -, bodyStorage, bodyLogs, returnedWord,
      wordPrefix, -, -, -, returnRun⟩ :=
    readTotalAssets_exactEffect callConfig memory staging depth
      (staticGasAvailable_of_runCompiled callConfig crossing) crossing suffix
  have stagingStorage : Devm.getStor entry = Devm.getStor callPre :=
    Line.of_inv Devm.getStor (by line_inv) staging
  have stagingLogs : entry.logs = callPre.logs :=
    Line.of_inv Devm.logs (by line_inv) staging
  have returnSource : Func.Run fs sevm returnPre
      Blanc.ProrataWethVault.returnWord post :=
    Func.Run.of_runCompiled
      (Func.RunCompiled.of_runCompiledTo_ok returnRun)
  have returnStorage : Devm.getStor returnPre = Devm.getStor post :=
    Func.of_inv Devm.getStor Devm.getStor (by
      unfold Blanc.ProrataWethVault.returnWord
      func_inv) returnSource
  have returnLogs : returnPre.logs = post.logs :=
    Func.of_inv Devm.logs Devm.logs (by
      unfold Blanc.ProrataWethVault.returnWord
      func_inv) returnSource
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
    stagingStorage.trans (bodyStorage.symm.trans returnStorage),
    stagingLogs.trans (bodyLogs.symm.trans returnLogs)⟩

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
