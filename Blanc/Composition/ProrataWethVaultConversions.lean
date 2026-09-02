import Blanc.ProrataWethVaultConversions
import Blanc.Composition.ProrataWethVaultViews

/-!
# WETH-backed compiled conversions of the PRORATA vault

The family conversion module proves the four distinct full-width arithmetic
bodies after a booked asset word has reached the stack.  This composition
owner connects that word to the actual configured WETH `balanceOf(vault)`
child, then lifts the shared result through all six public conversion and
preview selectors.
-/

namespace Blanc.Composition.ProrataWethVault

open Jaune
open Jaune.Ninst Ninst
open Blanc.ProrataWethVault
open Source
open scoped LogOutputHinv

private def sharesFloorBody : Func :=
  mstoreAt assetsWord +++
  pushSupplySlot +++ sload ::: mstoreAt supplyWord +++
  guardStableSupply
    (loadWord assetsWord +++ isMax +++
      (productOverTwoPow256 (arg 0) stagedDenominator .down
          returnWordSlot <?>
        mulDiv (arg 0) stagedDenominator stagedAssetFactor .down
          returnWordSlot))

private def assetsFloorBody : Func :=
  mstoreAt assetsWord +++
  pushSupplySlot +++ sload ::: mstoreAt supplyWord +++
  guardStableSupply
    (loadWord assetsWord +++ isMax +++
      (shiftedDiv (arg 0) stagedDenominator .down returnWordSlot <?>
        mulDiv (arg 0) stagedAssetFactor stagedDenominator .down
          returnWordSlot))

private def assetsCeilBody : Func :=
  mstoreAt assetsWord +++
  pushSupplySlot +++ sload ::: mstoreAt supplyWord +++
  guardStableSupply
    (loadWord assetsWord +++ isMax +++
      (shiftedDiv (arg 0) stagedDenominator .up returnWordSlot <?>
        mulDiv (arg 0) stagedAssetFactor stagedDenominator .up
          returnWordSlot))

private def sharesCeilBody : Func :=
  mstoreAt assetsWord +++
  pushSupplySlot +++ sload ::: mstoreAt supplyWord +++
  guardStableSupply
    (loadWord assetsWord +++ isMax +++
      (productOverTwoPow256 (arg 0) stagedDenominator .up
          returnWordSlot <?>
        mulDiv (arg 0) stagedDenominator stagedAssetFactor .up
          returnWordSlot))

/-- Join one proved post-`totalAssets` conversion body to the exact configured
WETH child.  The exact child seam carries the checked suffix's storage, log,
and well-formed-memory frame, so this theorem does not re-walk the arithmetic
body merely to recover those observations. -/
theorem readTotalAssets_conversion_body_effect
    {fs : List Func} {sevm : Sevm} {entry post : Devm} {body : Func}
    {calculate : Nat → Nat → Nat → Nat}
    (config : DirectWethConfiguration sevm.currentTarget sevm entry)
    (memoryWf : Mem.Wf entry.memory)
    (resources : TotalAssetsResources sevm entry)
    (localEffect : ∀ {bodyPre : Devm} {image : Bytes} {assets : B256},
      Mem.Wf bodyPre.memory →
      Mem.Reads bodyPre.memory image →
      assets :: [] <<+ bodyPre.stack →
      Func.RunCompiledTo fs sevm bodyPre body (.ok post) →
      ∃ supply,
        supply = Devm.getStorVal bodyPre sevm.currentTarget supplySlot ∧
        supply.toNat ≤ maxSupplyN ∧
        WordViewEffect
          (Nat.toB256 (calculate (Sevm.argWord sevm 0).toNat
            assets.toNat supply.toNat)) bodyPre post)
    (run : Func.RunCompiledTo fs sevm entry
      (readTotalAssets body) (.ok post)) :
    ∃ supply,
      supply = Devm.getStorVal entry sevm.currentTarget supplySlot ∧
      supply.toNat ≤ maxSupplyN ∧
      WordViewEffect
        (Nat.toB256 (calculate (Sevm.argWord sevm 0).toNat
          ((entry.state.getStor wethAccount).get
            sevm.currentTarget.toB256).toNat supply.toNat)) entry post := by
  have memory : MemoryImage entry entry.memory.data.toList := by
    refine ⟨memoryWf, ?_⟩
    intro index
    simp
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
  obtain ⟨word, bodyPre, -, -, bodyStorage, bodyLogs,
      returnedWord, wordPrefix, bodyWf, bodyRun⟩ :=
    readTotalAssets_exactEffect callConfig memory staging resources.1
      (resources.2 callPre staging) crossing suffix
  have bodyReads :
      Mem.Reads bodyPre.memory bodyPre.memory.data.toList := by
    intro index
    simp
  obtain ⟨supply, supplyEq, stable, result, resultStorage, resultLogs⟩ :=
    localEffect bodyWf bodyReads wordPrefix bodyRun
  have stagingStorage : Devm.getStor entry = Devm.getStor callPre :=
    Line.of_inv Devm.getStor (by line_inv) staging
  have stagingLogs : entry.logs = callPre.logs :=
    Line.of_inv Devm.logs (by line_inv) staging
  have entryStorage : Devm.getStor entry = Devm.getStor bodyPre :=
    stagingStorage.trans bodyStorage.symm
  have entryLogs : entry.logs = bodyPre.logs :=
    stagingLogs.trans bodyLogs.symm
  have callWord : word =
      (callPre.state.getStor wethAccount).get
        sevm.currentTarget.toB256 := by
    have bytes := congrArg Bytes.toB256 returnedWord
    simpa only [B256.toB256_toBytes] using bytes
  have entryWord : word =
      (entry.state.getStor wethAccount).get
        sevm.currentTarget.toB256 := by
    rw [callWord]
    exact (congrArg
      (fun storage : Stor => storage.get sevm.currentTarget.toB256)
      (congrFun stagingStorage wethAccount)).symm
  have entrySupply :
      supply = Devm.getStorVal entry sevm.currentTarget supplySlot := by
    rw [supplyEq]
    exact (congrArg
      (fun storage : Stor => storage.get supplySlot)
      (congrFun entryStorage sevm.currentTarget)).symm
  rw [entryWord] at result
  exact ⟨supply, entrySupply, stable, result,
    entryStorage.trans resultStorage, entryLogs.trans resultLogs⟩

/-! ## Four distinct composed arithmetic bodies -/

/-- `convertToShares` joins the exact WETH balance read to the full-width
floor share conversion. -/
theorem convertToShares_body_effect
    {fs : List Func} {sevm : Sevm} {entry post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm entry)
    (memoryWf : Mem.Wf entry.memory)
    (resources : TotalAssetsResources sevm entry)
    (lookup : fs[returnWordSlot]? = some returnWord)
    (run : Func.RunCompiledTo fs sevm entry convertToShares (.ok post)) :
    ∃ supply,
      supply = Devm.getStorVal entry sevm.currentTarget supplySlot ∧
      supply.toNat ≤ maxSupplyN ∧
      WordViewEffect
        (Nat.toB256 (convertToSharesN (Sevm.argWord sevm 0).toNat
          ((entry.state.getStor wethAccount).get
            sevm.currentTarget.toB256).toNat supply.toNat)) entry post := by
  have run' : Func.RunCompiledTo fs sevm entry
      (readTotalAssets sharesFloorBody) (.ok post) := by
    simpa only [convertToShares, sharesFloorBody] using run
  apply readTotalAssets_conversion_body_effect config memoryWf resources _ run'
  intro bodyPre image assets bodyWf bodyReads bodyStack bodyRun
  apply Blanc.ProrataWethVault.convertToShares_body_effect bodyWf bodyReads
    bodyStack lookup
  simpa only [sharesFloorBody] using bodyRun

/-- `convertToAssets` joins the exact WETH balance read to the full-width
floor asset conversion. -/
theorem convertToAssets_body_effect
    {fs : List Func} {sevm : Sevm} {entry post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm entry)
    (memoryWf : Mem.Wf entry.memory)
    (resources : TotalAssetsResources sevm entry)
    (lookup : fs[returnWordSlot]? = some returnWord)
    (run : Func.RunCompiledTo fs sevm entry convertToAssets (.ok post)) :
    ∃ supply,
      supply = Devm.getStorVal entry sevm.currentTarget supplySlot ∧
      supply.toNat ≤ maxSupplyN ∧
      WordViewEffect
        (Nat.toB256 (convertToAssetsN (Sevm.argWord sevm 0).toNat
          ((entry.state.getStor wethAccount).get
            sevm.currentTarget.toB256).toNat supply.toNat)) entry post := by
  have run' : Func.RunCompiledTo fs sevm entry
      (readTotalAssets assetsFloorBody) (.ok post) := by
    simpa only [convertToAssets, assetsFloorBody] using run
  apply readTotalAssets_conversion_body_effect config memoryWf resources _ run'
  intro bodyPre image assets bodyWf bodyReads bodyStack bodyRun
  apply Blanc.ProrataWethVault.convertToAssets_body_effect bodyWf bodyReads
    bodyStack lookup
  simpa only [assetsFloorBody] using bodyRun

/-- `previewMint` joins the exact WETH balance read to the full-width ceiling
asset quote. -/
theorem previewMint_body_effect
    {fs : List Func} {sevm : Sevm} {entry post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm entry)
    (memoryWf : Mem.Wf entry.memory)
    (resources : TotalAssetsResources sevm entry)
    (lookup : fs[returnWordSlot]? = some returnWord)
    (run : Func.RunCompiledTo fs sevm entry previewMint (.ok post)) :
    ∃ supply,
      supply = Devm.getStorVal entry sevm.currentTarget supplySlot ∧
      supply.toNat ≤ maxSupplyN ∧
      WordViewEffect
        (Nat.toB256 (previewMintN (Sevm.argWord sevm 0).toNat
          ((entry.state.getStor wethAccount).get
            sevm.currentTarget.toB256).toNat supply.toNat)) entry post := by
  have run' : Func.RunCompiledTo fs sevm entry
      (readTotalAssets assetsCeilBody) (.ok post) := by
    simpa only [previewMint, assetsCeilBody] using run
  apply readTotalAssets_conversion_body_effect config memoryWf resources _ run'
  intro bodyPre image assets bodyWf bodyReads bodyStack bodyRun
  apply Blanc.ProrataWethVault.previewMint_body_effect bodyWf bodyReads
    bodyStack lookup
  simpa only [assetsCeilBody] using bodyRun

/-- `previewWithdraw` joins the exact WETH balance read to the full-width
ceiling share quote. -/
theorem previewWithdraw_body_effect
    {fs : List Func} {sevm : Sevm} {entry post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm entry)
    (memoryWf : Mem.Wf entry.memory)
    (resources : TotalAssetsResources sevm entry)
    (lookup : fs[returnWordSlot]? = some returnWord)
    (run : Func.RunCompiledTo fs sevm entry previewWithdraw (.ok post)) :
    ∃ supply,
      supply = Devm.getStorVal entry sevm.currentTarget supplySlot ∧
      supply.toNat ≤ maxSupplyN ∧
      WordViewEffect
        (Nat.toB256 (previewWithdrawN (Sevm.argWord sevm 0).toNat
          ((entry.state.getStor wethAccount).get
            sevm.currentTarget.toB256).toNat supply.toNat)) entry post := by
  have run' : Func.RunCompiledTo fs sevm entry
      (readTotalAssets sharesCeilBody) (.ok post) := by
    simpa only [previewWithdraw, sharesCeilBody] using run
  apply readTotalAssets_conversion_body_effect config memoryWf resources _ run'
  intro bodyPre image assets bodyWf bodyReads bodyStack bodyRun
  apply Blanc.ProrataWethVault.previewWithdraw_body_effect bodyWf bodyReads
    bodyStack lookup
  simpa only [sharesCeilBody] using bodyRun

/-! ## Shared compiled-selector lift -/

private theorem conversion_compiled_effect
    {sevm : Sevm} {pre post : Devm} {sig : B256} {body : Func}
    {calculate : Nat → Nat → Nat → Nat}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (memoryWf : Mem.Wf pre.memory)
    (resources : TotalAssetsCompiledResourcesFor sevm post body)
    (member : (sig, routed 1 body) ∈ vaultFuncs)
    (bodyEffect : ∀ {entry : Devm},
      DirectWethConfiguration sevm.currentTarget sevm entry →
      Mem.Wf entry.memory →
      TotalAssetsResources sevm entry →
      Func.RunCompiledTo (vault.main :: vault.aux) sevm entry body
        (.ok post) →
      ∃ supply,
        supply = Devm.getStorVal entry sevm.currentTarget supplySlot ∧
        supply.toNat ≤ maxSupplyN ∧
        WordViewEffect
          (Nat.toB256 (calculate (Sevm.argWord sevm 0).toNat
            ((entry.state.getStor wethAccount).get
              sevm.currentTarget.toB256).toNat supply.toNat)) entry post)
    (run : Prog.RunCompiled sevm pre vault post)
    (selectorEq : Sevm.selector sevm = sig) :
    sevm.value = 0 ∧
      (Devm.getStorVal pre sevm.currentTarget supplySlot).toNat ≤
        maxSupplyN ∧
      WordViewEffect
        (Nat.toB256 (calculate (Sevm.argWord sevm 0).toNat
          ((pre.state.getStor wethAccount).get
            sevm.currentTarget.toB256).toNat
          (Devm.getStorVal pre sevm.currentTarget supplySlot).toNat))
        pre post := by
  rcases Blanc.ProrataWethVault.runCompiled_enters_body_compiled_logs
      run selectorEq member with
    ⟨bodyPre, valueZero, -, entryState, entryMemory, entryLogs, -,
      bodyRun⟩
  have bodyConfig :
      DirectWethConfiguration sevm.currentTarget sevm bodyPre := by
    refine ⟨config.distinct, config.nonprecompile, ?_⟩
    rw [← getCode_eq_of_state_eq entryState wethAccount]
    exact config.code
  have bodyMemoryWf : Mem.Wf bodyPre.memory := by
    rw [← entryMemory]
    exact memoryWf
  obtain ⟨supply, supplyEq, stable, result⟩ :=
    bodyEffect bodyConfig bodyMemoryWf (resources bodyPre bodyRun) bodyRun
  rcases result with ⟨output, bodyStorage, bodyLogs⟩
  have entryStorage : Devm.getStor pre = Devm.getStor bodyPre :=
    funext (getStor_eq_of_state_eq entryState)
  have entrySupply :
      supply = Devm.getStorVal pre sevm.currentTarget supplySlot := by
    rw [supplyEq]
    exact (congrArg
      (fun storage : Stor => storage.get supplySlot)
      (congrFun entryStorage sevm.currentTarget)).symm
  have stable' :
      (Devm.getStorVal pre sevm.currentTarget supplySlot).toNat ≤
        maxSupplyN := by
    simpa only [entrySupply] using stable
  have output' : ReturnsWord
      (Nat.toB256 (calculate (Sevm.argWord sevm 0).toNat
        ((pre.state.getStor wethAccount).get
          sevm.currentTarget.toB256).toNat
        (Devm.getStorVal pre sevm.currentTarget supplySlot).toNat)) post := by
    simpa only [entryState, entrySupply] using output
  exact ⟨valueZero, stable', output',
    entryStorage.trans bodyStorage, entryLogs.trans bodyLogs⟩

private theorem returnWord_lookup :
    (vault.main :: vault.aux)[returnWordSlot]? = some returnWord := by
  simp [vault, vaultAux, returnWordSlot]

/-! ## Six public compiled endpoints -/

/-- Compiled `convertToShares` returns the exact floor share conversion of the
pre-state booked WETH balance and share supply. -/
theorem convertToShares_compiled_effect
    {sevm : Sevm} {pre post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (memoryWf : Mem.Wf pre.memory)
    (resources : TotalAssetsCompiledResourcesFor sevm post convertToShares)
    (run : Prog.RunCompiled sevm pre vault post)
    (selectorEq : Sevm.selector sevm =
      selector "convertToShares" [.uint256]) :
    sevm.value = 0 ∧
      (Devm.getStorVal pre sevm.currentTarget supplySlot).toNat ≤
        maxSupplyN ∧
      WordViewEffect
        (Nat.toB256 (convertToSharesN (Sevm.argWord sevm 0).toNat
          ((pre.state.getStor wethAccount).get
            sevm.currentTarget.toB256).toNat
          (Devm.getStorVal pre sevm.currentTarget supplySlot).toNat))
        pre post := by
  apply conversion_compiled_effect (body := convertToShares)
    (calculate := convertToSharesN) config memoryWf resources (by
    simp [vaultFuncs]) _ run selectorEq
  intro entry bodyConfig bodyMemory bodyResources bodyRun
  exact convertToShares_body_effect bodyConfig bodyMemory bodyResources
    returnWord_lookup bodyRun

/-- Compiled `convertToAssets` returns the exact floor asset conversion of the
pre-state booked WETH balance and share supply. -/
theorem convertToAssets_compiled_effect
    {sevm : Sevm} {pre post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (memoryWf : Mem.Wf pre.memory)
    (resources : TotalAssetsCompiledResourcesFor sevm post convertToAssets)
    (run : Prog.RunCompiled sevm pre vault post)
    (selectorEq : Sevm.selector sevm =
      selector "convertToAssets" [.uint256]) :
    sevm.value = 0 ∧
      (Devm.getStorVal pre sevm.currentTarget supplySlot).toNat ≤
        maxSupplyN ∧
      WordViewEffect
        (Nat.toB256 (convertToAssetsN (Sevm.argWord sevm 0).toNat
          ((pre.state.getStor wethAccount).get
            sevm.currentTarget.toB256).toNat
          (Devm.getStorVal pre sevm.currentTarget supplySlot).toNat))
        pre post := by
  apply conversion_compiled_effect (body := convertToAssets)
    (calculate := convertToAssetsN) config memoryWf resources (by
    simp [vaultFuncs]) _ run selectorEq
  intro entry bodyConfig bodyMemory bodyResources bodyRun
  exact convertToAssets_body_effect bodyConfig bodyMemory bodyResources
    returnWord_lookup bodyRun

/-- Compiled `previewDeposit` is the exact `convertToShares` arithmetic alias. -/
theorem previewDeposit_compiled_effect
    {sevm : Sevm} {pre post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (memoryWf : Mem.Wf pre.memory)
    (resources : TotalAssetsCompiledResourcesFor sevm post previewDeposit)
    (run : Prog.RunCompiled sevm pre vault post)
    (selectorEq : Sevm.selector sevm =
      selector "previewDeposit" [.uint256]) :
    sevm.value = 0 ∧
      (Devm.getStorVal pre sevm.currentTarget supplySlot).toNat ≤
        maxSupplyN ∧
      WordViewEffect
        (Nat.toB256 (previewDepositN (Sevm.argWord sevm 0).toNat
          ((pre.state.getStor wethAccount).get
            sevm.currentTarget.toB256).toNat
          (Devm.getStorVal pre sevm.currentTarget supplySlot).toNat))
        pre post := by
  apply conversion_compiled_effect (body := previewDeposit)
    (calculate := previewDepositN) config memoryWf resources (by
    simp [vaultFuncs]) _ run selectorEq
  intro entry bodyConfig bodyMemory bodyResources bodyRun
  have effect := convertToShares_body_effect bodyConfig bodyMemory
    bodyResources returnWord_lookup (by
      simpa only [previewDeposit] using bodyRun)
  simpa only [previewDepositN] using effect

/-- Compiled `previewRedeem` is the exact `convertToAssets` arithmetic alias. -/
theorem previewRedeem_compiled_effect
    {sevm : Sevm} {pre post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (memoryWf : Mem.Wf pre.memory)
    (resources : TotalAssetsCompiledResourcesFor sevm post previewRedeem)
    (run : Prog.RunCompiled sevm pre vault post)
    (selectorEq : Sevm.selector sevm =
      selector "previewRedeem" [.uint256]) :
    sevm.value = 0 ∧
      (Devm.getStorVal pre sevm.currentTarget supplySlot).toNat ≤
        maxSupplyN ∧
      WordViewEffect
        (Nat.toB256 (previewRedeemN (Sevm.argWord sevm 0).toNat
          ((pre.state.getStor wethAccount).get
            sevm.currentTarget.toB256).toNat
          (Devm.getStorVal pre sevm.currentTarget supplySlot).toNat))
        pre post := by
  apply conversion_compiled_effect (body := previewRedeem)
    (calculate := previewRedeemN) config memoryWf resources (by
    simp [vaultFuncs]) _ run selectorEq
  intro entry bodyConfig bodyMemory bodyResources bodyRun
  have effect := convertToAssets_body_effect bodyConfig bodyMemory
    bodyResources returnWord_lookup (by
      simpa only [previewRedeem] using bodyRun)
  simpa only [previewRedeemN] using effect

/-- Compiled `previewMint` returns the exact ceiling asset input. -/
theorem previewMint_compiled_effect
    {sevm : Sevm} {pre post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (memoryWf : Mem.Wf pre.memory)
    (resources : TotalAssetsCompiledResourcesFor sevm post previewMint)
    (run : Prog.RunCompiled sevm pre vault post)
    (selectorEq : Sevm.selector sevm = selector "previewMint" [.uint256]) :
    sevm.value = 0 ∧
      (Devm.getStorVal pre sevm.currentTarget supplySlot).toNat ≤
        maxSupplyN ∧
      WordViewEffect
        (Nat.toB256 (previewMintN (Sevm.argWord sevm 0).toNat
          ((pre.state.getStor wethAccount).get
            sevm.currentTarget.toB256).toNat
          (Devm.getStorVal pre sevm.currentTarget supplySlot).toNat))
        pre post := by
  apply conversion_compiled_effect (body := previewMint)
    (calculate := previewMintN) config memoryWf resources (by
    simp [vaultFuncs]) _ run selectorEq
  intro entry bodyConfig bodyMemory bodyResources bodyRun
  exact previewMint_body_effect bodyConfig bodyMemory bodyResources
    returnWord_lookup bodyRun

/-- Compiled `previewWithdraw` returns the exact ceiling share input. -/
theorem previewWithdraw_compiled_effect
    {sevm : Sevm} {pre post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (memoryWf : Mem.Wf pre.memory)
    (resources : TotalAssetsCompiledResourcesFor sevm post previewWithdraw)
    (run : Prog.RunCompiled sevm pre vault post)
    (selectorEq : Sevm.selector sevm =
      selector "previewWithdraw" [.uint256]) :
    sevm.value = 0 ∧
      (Devm.getStorVal pre sevm.currentTarget supplySlot).toNat ≤
        maxSupplyN ∧
      WordViewEffect
        (Nat.toB256 (previewWithdrawN (Sevm.argWord sevm 0).toNat
          ((pre.state.getStor wethAccount).get
            sevm.currentTarget.toB256).toNat
          (Devm.getStorVal pre sevm.currentTarget supplySlot).toNat))
        pre post := by
  apply conversion_compiled_effect (body := previewWithdraw)
    (calculate := previewWithdrawN) config memoryWf resources (by
    simp [vaultFuncs]) _ run selectorEq
  intro entry bodyConfig bodyMemory bodyResources bodyRun
  exact previewWithdraw_body_effect bodyConfig bodyMemory bodyResources
    returnWord_lookup bodyRun

end Blanc.Composition.ProrataWethVault
