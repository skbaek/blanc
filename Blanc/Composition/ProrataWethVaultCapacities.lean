import Blanc.ProrataWethVaultCapacities
import Blanc.Composition.ProrataWethVaultConversions

/-!
# WETH-backed compiled capacities of the PRORATA vault

The family owner proves the exact full-width arithmetic after a booked asset
word reaches the stack.  This composition owner carries the supply and owner
balance windows across the actual configured WETH `balanceOf(vault)` child,
then lifts the stable, unstable, and zero-receiver routes through the public
selectors.
-/

namespace Blanc.Composition.ProrataWethVault

open Jaune
open Jaune.Ninst Ninst
open Blanc.ProrataWethVault
open Source
open scoped LogOutputHinv

private def maxMintReadBody : Func :=
  mstoreAt assetsWord +++
  loadWord assetsWord +++ isMax +++
  (productOverTwoPow256 [pushB256 B256.max] stagedDenominator .down
      maxMintAfterAssetCapSlot <?>
    mulDiv [pushB256 B256.max] stagedDenominator stagedAssetFactor
      .capDown maxMintAfterAssetCapSlot)

private def maxDepositReadBody : Func :=
  mstoreAt assetsWord +++
  loadWord assetsWord +++ isMax +++
  (shiftedDiv shareRoomPlusOne stagedDenominator .capCeilPred
      returnWordSlot <?>
    mulDiv shareRoomPlusOne stagedAssetFactor stagedDenominator
      .capCeilPred returnWordSlot)

private def maxWithdrawReadBody : Func :=
  mstoreAt assetsWord +++
  loadWord assetsWord +++ isMax +++
  (shiftedDiv (loadWord amountWord) stagedDenominator .capDown
      returnWordSlot <?>
    mulDiv (loadWord amountWord) stagedAssetFactor stagedDenominator
      .capDown returnWordSlot)

private def stableCapacityBody (readBody : Func) : Func :=
  loadWord supplyWord +++ pushB256 maxSupply ::: lt :::
  (returnConstant 0 <?> readTotalAssets readBody)

private def stagedSupplyCapacityBody (readBody : Func) : Func :=
  pushSupplySlot +++ sload ::: mstoreAt supplyWord +++
  stableCapacityBody readBody

private def receiverCapacityBody (readBody : Func) : Func :=
  arg 0 +++ iszero :::
  (returnConstant 0 <?> stagedSupplyCapacityBody readBody)

/-- Gas/depth resources are tied to the exact stable `readTotalAssets`
occurrence.  Zero-receiver and unstable-supply routes do not demand a WETH
call resource they never execute. -/
def CapacityTotalAssetsResourcesFor
    (sevm : Sevm) (post : Devm) (readBody : Func) : Prop :=
  ∀ entry,
    Func.RunCompiledTo
        (vault.main :: vault.aux) sevm entry
        (readTotalAssets readBody) (.ok post) →
      TotalAssetsResources sevm entry

def MaxMintResources (sevm : Sevm) (post : Devm) : Prop :=
  CapacityTotalAssetsResourcesFor sevm post maxMintReadBody

def MaxDepositResources (sevm : Sevm) (post : Devm) : Prop :=
  CapacityTotalAssetsResourcesFor sevm post maxDepositReadBody

def MaxWithdrawResources (sevm : Sevm) (post : Devm) : Prop :=
  CapacityTotalAssetsResourcesFor sevm post maxWithdrawReadBody

/-- Join one window-carrying stable capacity body to the exact configured
WETH child.  The callback also receives the general high-window transport so
`maxWithdraw` can carry its separately staged owner balance. -/
theorem readTotalAssets_capacity_body_effect
    {fs : List Func} {sevm : Sevm} {entry post : Devm} {body : Func}
    {supply : B256} {calculate : Nat → Nat → Nat}
    (config : DirectWethConfiguration sevm.currentTarget sevm entry)
    (memoryWf : Mem.Wf entry.memory)
    (resources : TotalAssetsResources sevm entry)
    (supplyWindow : MemWordAt entry (supplyWord * 32).toNat supply)
    (localEffect : ∀ {bodyPre : Devm} {image : Bytes} {assets : B256},
      Mem.Wf bodyPre.memory →
      Mem.Reads bodyPre.memory image →
      assets :: [] <<+ bodyPre.stack →
      MemWordAt bodyPre (supplyWord * 32).toNat supply →
      (∀ {offset : Nat} {w : B256}, 64 ≤ offset →
        MemWordAt entry offset w → MemWordAt bodyPre offset w) →
      Func.RunCompiledTo fs sevm bodyPre body (.ok post) →
      calculate assets.toNat supply.toNat < wordModulusN ∧
        WordViewEffect
          (Nat.toB256 (calculate assets.toNat supply.toNat)) bodyPre post)
    (run : Func.RunCompiledTo fs sevm entry
      (readTotalAssets body) (.ok post)) :
    calculate
        ((entry.state.getStor wethAccount).get
          sevm.currentTarget.toB256).toNat supply.toNat < wordModulusN ∧
      WordViewEffect
        (Nat.toB256 (calculate
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
  obtain ⟨word, bodyPre, -, -, bodyStorage, bodyLogs, returnedWord,
      wordPrefix, bodyWf, -, preservesWindow, bodyRun⟩ :=
    readTotalAssets_exactEffect callConfig memory staging resources.1
      (resources.2 callPre staging) crossing suffix
  have bodyReads :
      Mem.Reads bodyPre.memory bodyPre.memory.data.toList := by
    intro index
    simp
  have bodySupplyWindow := preservesWindow
    (by decide +kernel : 64 ≤ (supplyWord * 32).toNat) supplyWindow
  obtain ⟨resultFits, result⟩ :=
    localEffect bodyWf bodyReads wordPrefix bodySupplyWindow
      preservesWindow bodyRun
  rcases result with ⟨output, resultStorage, resultLogs⟩
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
  rw [entryWord] at resultFits output
  exact ⟨resultFits, output, entryStorage.trans resultStorage,
    entryLogs.trans resultLogs⟩

/-! ## Capacity endpoint bodies -/

/-- Exact compiled body effect of `maxMint`, including the zero-receiver and
unstable-supply routes that deliberately avoid the WETH child. -/
theorem maxMint_body_effect
    {sevm : Sevm} {entry post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm entry)
    (memoryWf : Mem.Wf entry.memory)
    (resources : CapacityTotalAssetsResourcesFor sevm post maxMintReadBody)
    (returnLookup :
      (vault.main :: vault.aux)[returnWordSlot]? = some returnWord)
    (capLookup : (vault.main :: vault.aux)[maxMintAfterAssetCapSlot]? =
      some maxMintAfterAssetCap)
    (run : Func.RunCompiledTo (vault.main :: vault.aux) sevm entry
      maxMint (.ok post)) :
    ValidAdr (Sevm.argWord sevm 0) ∧
      maxMintViewN (Sevm.argWord sevm 0).toNat
          ((entry.state.getStor wethAccount).get
            sevm.currentTarget.toB256).toNat
          (Devm.getStorVal entry sevm.currentTarget supplySlot).toNat <
        wordModulusN ∧
      WordViewEffect
        (Nat.toB256 (maxMintViewN (Sevm.argWord sevm 0).toNat
          ((entry.state.getStor wethAccount).get
            sevm.currentTarget.toB256).toNat
          (Devm.getStorVal entry sevm.currentTarget supplySlot).toNat))
        entry post := by
  have routedRun : Func.RunCompiledTo (vault.main :: vault.aux) sevm entry
      (canonicalAddressArg 0 (receiverCapacityBody maxMintReadBody))
      (.ok post) := by
    simpa [maxMint, receiverCapacityBody, stagedSupplyCapacityBody,
      stableCapacityBody, maxMintReadBody] using run
  obtain ⟨receiverPre, receiverValid, receiverRun, receiverStack,
      entryState, entryMemory, entryLogs⟩ :=
    canonicalAddressArg_body_of_ok (R := Func.RunOk) nil_pref routedRun
  have receiverWf : Mem.Wf receiverPre.memory := by
    rw [← entryMemory]
    exact memoryWf
  have receiverRoute : Func.RunCompiledTo (vault.main :: vault.aux) sevm
      receiverPre
      (arg 0 +++ iszero :::
        (returnConstant 0 <?> stagedSupplyCapacityBody maxMintReadBody))
      (.ok post) := by
    simpa only [receiverCapacityBody] using receiverRun
  rcases zeroArgCapacityBranch_trace (R := Func.RunOk) receiverWf receiverStack receiverRoute
    with zeroReceiver | nonzeroReceiver
  · rcases zeroReceiver with ⟨receiverZero, effect⟩
    have lifted := lift_word_view entryState entryLogs effect
    have receiverNatZero : (Sevm.argWord sevm 0).toNat = 0 := by
      simp only [receiverZero, B256.toNat_zero]
    have zeroWord : Nat.toB256 0 = (0 : B256) := by decide +kernel
    refine ⟨receiverValid, ?_, ?_⟩
    · simpa only [maxMintViewN, receiverNatZero, if_pos] using
        wordModulusN_pos
    · simpa only [maxMintViewN, receiverNatZero, if_pos, zeroWord] using
        lifted
  · rcases nonzeroReceiver with
      ⟨receiverNonzero, supplyEntry, supplyStack, supplyWf,
        receiverState, receiverLogs, supplyRun⟩
    have supplyStageRun :
        Func.RunCompiledTo (vault.main :: vault.aux) sevm supplyEntry
          (pushSupplySlot +++ sload ::: mstoreAt supplyWord +++
            stableCapacityBody maxMintReadBody) (.ok post) := by
      simpa only [stagedSupplyCapacityBody] using supplyRun
    obtain ⟨supply, branchEntry, supplyEq, branchStack, supplyWindow,
        -, supplyState, supplyLogs, branchRun⟩ :=
      capacitySupplyStaging_trace (R := Func.RunOk) supplyWf supplyStack supplyStageRun
    have stableRun :
        Func.RunCompiledTo (vault.main :: vault.aux) sevm branchEntry
          (loadWord supplyWord +++ pushB256 maxSupply ::: lt :::
            (returnConstant 0 <?> readTotalAssets maxMintReadBody))
          (.ok post) := by
      simpa only [stableCapacityBody] using branchRun
    rcases stableCapacityBranch_trace (R := Func.RunOk) supplyWindow branchStack stableRun with
      unstableSupply | stableSupply
    · rcases unstableSupply with ⟨unstable, effect⟩
      have entryToBranchState :=
        entryState.trans (receiverState.trans supplyState)
      have entryToBranchLogs :=
        entryLogs.trans (receiverLogs.trans supplyLogs)
      have lifted := lift_word_view entryToBranchState entryToBranchLogs effect
      have supplyAtEntry : supply =
          Devm.getStorVal entry sevm.currentTarget supplySlot := by
        rw [supplyEq]
        change
          (Devm.getStor supplyEntry sevm.currentTarget).get supplySlot =
            (Devm.getStor entry sevm.currentTarget).get supplySlot
        rw [funext (getStor_eq_of_state_eq
          (entryState.trans receiverState))]
      have receiverNatNonzero : (Sevm.argWord sevm 0).toNat ≠ 0 := by
        intro naturalZero
        apply receiverNonzero
        apply B256.toNat_inj
        simp only [naturalZero, B256.toNat_zero]
      have unstableAtEntry : maxSupplyN <
          (Devm.getStorVal entry sevm.currentTarget supplySlot).toNat := by
        rw [← supplyAtEntry]
        exact unstable
      have zeroWord : Nat.toB256 0 = (0 : B256) := by decide +kernel
      refine ⟨receiverValid, ?_, ?_⟩
      · simpa only [maxMintViewN, if_neg receiverNatNonzero,
          if_pos unstableAtEntry] using wordModulusN_pos
      · simpa only [maxMintViewN, if_neg receiverNatNonzero,
          if_pos unstableAtEntry, zeroWord] using lifted
    · rcases stableSupply with
        ⟨readEntry, stable, readStack, readSupplyWindow, -, stableState,
          stableLogs, readRun⟩
      have entryToReadState := entryState.trans
        (receiverState.trans (supplyState.trans stableState))
      have entryToReadLogs := entryLogs.trans
        (receiverLogs.trans (supplyLogs.trans stableLogs))
      have readConfig :
          DirectWethConfiguration sevm.currentTarget sevm readEntry := by
        refine ⟨config.distinct, config.nonprecompile, ?_⟩
        rw [← getCode_eq_of_state_eq entryToReadState wethAccount]
        exact config.code
      have readWf : Mem.Wf readEntry.memory := readSupplyWindow.1
      obtain ⟨resultFits, result⟩ :=
        readTotalAssets_capacity_body_effect readConfig readWf
          (resources readEntry readRun) readSupplyWindow
          (calculate := maxMintN)
          (by
            intro bodyPre image assets bodyWf bodyReads bodyStack
              bodySupplyWindow preserves bodyRun
            apply Blanc.ProrataWethVault.maxMint_postTotalAssets_body_effect
              bodyWf bodyReads bodySupplyWindow stable bodyStack
              returnLookup capLookup
            simpa only [maxMintReadBody] using bodyRun)
          readRun
      have lifted := lift_word_view entryToReadState entryToReadLogs result
      have supplyAtEntry : supply =
          Devm.getStorVal entry sevm.currentTarget supplySlot := by
        rw [supplyEq]
        change
          (Devm.getStor supplyEntry sevm.currentTarget).get supplySlot =
            (Devm.getStor entry sevm.currentTarget).get supplySlot
        rw [funext (getStor_eq_of_state_eq
          (entryState.trans receiverState))]
      have receiverNatNonzero : (Sevm.argWord sevm 0).toNat ≠ 0 := by
        intro naturalZero
        apply receiverNonzero
        apply B256.toNat_inj
        simp only [naturalZero, B256.toNat_zero]
      have stableAtEntry :
          (Devm.getStorVal entry sevm.currentTarget supplySlot).toNat ≤
            maxSupplyN := by
        rw [← supplyAtEntry]
        exact stable
      rw [← entryToReadState, supplyAtEntry] at resultFits lifted
      exact ⟨receiverValid,
        by simpa only [maxMintViewN, if_neg receiverNatNonzero,
          if_neg (Nat.not_lt_of_ge stableAtEntry)] using resultFits,
        by simpa only [maxMintViewN, if_neg receiverNatNonzero,
          if_neg (Nat.not_lt_of_ge stableAtEntry)] using lifted⟩

/-- Exact compiled body effect of `maxDeposit`, with the same receiver and
supply-domain routing as `maxMint` but its own ceiling-predecessor capacity
formula. -/
theorem maxDeposit_body_effect
    {sevm : Sevm} {entry post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm entry)
    (memoryWf : Mem.Wf entry.memory)
    (resources :
      CapacityTotalAssetsResourcesFor sevm post maxDepositReadBody)
    (returnLookup :
      (vault.main :: vault.aux)[returnWordSlot]? = some returnWord)
    (run : Func.RunCompiledTo (vault.main :: vault.aux) sevm entry
      maxDeposit (.ok post)) :
    ValidAdr (Sevm.argWord sevm 0) ∧
      maxDepositViewN (Sevm.argWord sevm 0).toNat
          ((entry.state.getStor wethAccount).get
            sevm.currentTarget.toB256).toNat
          (Devm.getStorVal entry sevm.currentTarget supplySlot).toNat <
        wordModulusN ∧
      WordViewEffect
        (Nat.toB256 (maxDepositViewN (Sevm.argWord sevm 0).toNat
          ((entry.state.getStor wethAccount).get
            sevm.currentTarget.toB256).toNat
          (Devm.getStorVal entry sevm.currentTarget supplySlot).toNat))
        entry post := by
  have routedRun : Func.RunCompiledTo (vault.main :: vault.aux) sevm entry
      (canonicalAddressArg 0 (receiverCapacityBody maxDepositReadBody))
      (.ok post) := by
    simpa [maxDeposit, receiverCapacityBody, stagedSupplyCapacityBody,
      stableCapacityBody, maxDepositReadBody] using run
  obtain ⟨receiverPre, receiverValid, receiverRun, receiverStack,
      entryState, entryMemory, entryLogs⟩ :=
    canonicalAddressArg_body_of_ok (R := Func.RunOk) nil_pref routedRun
  have receiverWf : Mem.Wf receiverPre.memory := by
    rw [← entryMemory]
    exact memoryWf
  have receiverRoute : Func.RunCompiledTo (vault.main :: vault.aux) sevm
      receiverPre
      (arg 0 +++ iszero :::
        (returnConstant 0 <?> stagedSupplyCapacityBody maxDepositReadBody))
      (.ok post) := by
    simpa only [receiverCapacityBody] using receiverRun
  rcases zeroArgCapacityBranch_trace (R := Func.RunOk) receiverWf receiverStack receiverRoute
    with zeroReceiver | nonzeroReceiver
  · rcases zeroReceiver with ⟨receiverZero, effect⟩
    have lifted := lift_word_view entryState entryLogs effect
    have receiverNatZero : (Sevm.argWord sevm 0).toNat = 0 := by
      simp only [receiverZero, B256.toNat_zero]
    have zeroWord : Nat.toB256 0 = (0 : B256) := by decide +kernel
    refine ⟨receiverValid, ?_, ?_⟩
    · simpa only [maxDepositViewN, receiverNatZero, if_pos] using
        wordModulusN_pos
    · simpa only [maxDepositViewN, receiverNatZero, if_pos, zeroWord] using
        lifted
  · rcases nonzeroReceiver with
      ⟨receiverNonzero, supplyEntry, supplyStack, supplyWf,
        receiverState, receiverLogs, supplyRun⟩
    have supplyStageRun :
        Func.RunCompiledTo (vault.main :: vault.aux) sevm supplyEntry
          (pushSupplySlot +++ sload ::: mstoreAt supplyWord +++
            stableCapacityBody maxDepositReadBody) (.ok post) := by
      simpa only [stagedSupplyCapacityBody] using supplyRun
    obtain ⟨supply, branchEntry, supplyEq, branchStack, supplyWindow,
        -, supplyState, supplyLogs, branchRun⟩ :=
      capacitySupplyStaging_trace (R := Func.RunOk) supplyWf supplyStack supplyStageRun
    have stableRun :
        Func.RunCompiledTo (vault.main :: vault.aux) sevm branchEntry
          (loadWord supplyWord +++ pushB256 maxSupply ::: lt :::
            (returnConstant 0 <?> readTotalAssets maxDepositReadBody))
          (.ok post) := by
      simpa only [stableCapacityBody] using branchRun
    rcases stableCapacityBranch_trace (R := Func.RunOk) supplyWindow branchStack stableRun with
      unstableSupply | stableSupply
    · rcases unstableSupply with ⟨unstable, effect⟩
      have entryToBranchState :=
        entryState.trans (receiverState.trans supplyState)
      have entryToBranchLogs :=
        entryLogs.trans (receiverLogs.trans supplyLogs)
      have lifted := lift_word_view entryToBranchState entryToBranchLogs effect
      have supplyAtEntry : supply =
          Devm.getStorVal entry sevm.currentTarget supplySlot := by
        rw [supplyEq]
        change
          (Devm.getStor supplyEntry sevm.currentTarget).get supplySlot =
            (Devm.getStor entry sevm.currentTarget).get supplySlot
        rw [funext (getStor_eq_of_state_eq
          (entryState.trans receiverState))]
      have receiverNatNonzero : (Sevm.argWord sevm 0).toNat ≠ 0 := by
        intro naturalZero
        apply receiverNonzero
        apply B256.toNat_inj
        simp only [naturalZero, B256.toNat_zero]
      have unstableAtEntry : maxSupplyN <
          (Devm.getStorVal entry sevm.currentTarget supplySlot).toNat := by
        rw [← supplyAtEntry]
        exact unstable
      have zeroWord : Nat.toB256 0 = (0 : B256) := by decide +kernel
      refine ⟨receiverValid, ?_, ?_⟩
      · simpa only [maxDepositViewN, if_neg receiverNatNonzero,
          if_pos unstableAtEntry] using wordModulusN_pos
      · simpa only [maxDepositViewN, if_neg receiverNatNonzero,
          if_pos unstableAtEntry, zeroWord] using lifted
    · rcases stableSupply with
        ⟨readEntry, stable, readStack, readSupplyWindow, -, stableState,
          stableLogs, readRun⟩
      have entryToReadState := entryState.trans
        (receiverState.trans (supplyState.trans stableState))
      have entryToReadLogs := entryLogs.trans
        (receiverLogs.trans (supplyLogs.trans stableLogs))
      have readConfig :
          DirectWethConfiguration sevm.currentTarget sevm readEntry := by
        refine ⟨config.distinct, config.nonprecompile, ?_⟩
        rw [← getCode_eq_of_state_eq entryToReadState wethAccount]
        exact config.code
      have readWf : Mem.Wf readEntry.memory := readSupplyWindow.1
      obtain ⟨resultFits, result⟩ :=
        readTotalAssets_capacity_body_effect readConfig readWf
          (resources readEntry readRun) readSupplyWindow
          (calculate := maxDepositN)
          (by
            intro bodyPre image assets bodyWf bodyReads bodyStack
              bodySupplyWindow preserves bodyRun
            apply
              Blanc.ProrataWethVault.maxDeposit_postTotalAssets_body_effect
                bodyWf bodyReads bodySupplyWindow stable bodyStack
                returnLookup
            simpa only [maxDepositReadBody] using bodyRun)
          readRun
      have lifted := lift_word_view entryToReadState entryToReadLogs result
      have supplyAtEntry : supply =
          Devm.getStorVal entry sevm.currentTarget supplySlot := by
        rw [supplyEq]
        change
          (Devm.getStor supplyEntry sevm.currentTarget).get supplySlot =
            (Devm.getStor entry sevm.currentTarget).get supplySlot
        rw [funext (getStor_eq_of_state_eq
          (entryState.trans receiverState))]
      have receiverNatNonzero : (Sevm.argWord sevm 0).toNat ≠ 0 := by
        intro naturalZero
        apply receiverNonzero
        apply B256.toNat_inj
        simp only [naturalZero, B256.toNat_zero]
      have stableAtEntry :
          (Devm.getStorVal entry sevm.currentTarget supplySlot).toNat ≤
            maxSupplyN := by
        rw [← supplyAtEntry]
        exact stable
      rw [← entryToReadState, supplyAtEntry] at resultFits lifted
      exact ⟨receiverValid,
        by simpa only [maxDepositViewN, if_neg receiverNatNonzero,
          if_neg (Nat.not_lt_of_ge stableAtEntry)] using resultFits,
        by simpa only [maxDepositViewN, if_neg receiverNatNonzero,
          if_neg (Nat.not_lt_of_ge stableAtEntry)] using lifted⟩

/-- Exact compiled body effect of `maxWithdraw`.  The owner's staged balance
is carried through supply staging, the domain branch, the WETH child, and the
full-width arithmetic suffix. -/
theorem maxWithdraw_body_effect
    {sevm : Sevm} {entry post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm entry)
    (memoryWf : Mem.Wf entry.memory)
    (resources :
      CapacityTotalAssetsResourcesFor sevm post maxWithdrawReadBody)
    (returnLookup :
      (vault.main :: vault.aux)[returnWordSlot]? = some returnWord)
    (run : Func.RunCompiledTo (vault.main :: vault.aux) sevm entry
      maxWithdraw (.ok post)) :
    ValidAdr (Sevm.argWord sevm 0) ∧
      maxWithdrawViewN
          (Devm.getStorVal entry sevm.currentTarget
            (Sevm.argWord sevm 0)).toNat
          ((entry.state.getStor wethAccount).get
            sevm.currentTarget.toB256).toNat
          (Devm.getStorVal entry sevm.currentTarget supplySlot).toNat <
        wordModulusN ∧
      WordViewEffect
        (Nat.toB256 (maxWithdrawViewN
          (Devm.getStorVal entry sevm.currentTarget
            (Sevm.argWord sevm 0)).toNat
          ((entry.state.getStor wethAccount).get
            sevm.currentTarget.toB256).toNat
          (Devm.getStorVal entry sevm.currentTarget supplySlot).toNat))
        entry post := by
  have routedRun : Func.RunCompiledTo (vault.main :: vault.aux) sevm entry
      (canonicalAddressArg 0
        (arg 0 +++ sload ::: mstoreAt amountWord +++
          stagedSupplyCapacityBody maxWithdrawReadBody)) (.ok post) := by
    simpa [maxWithdraw, stagedSupplyCapacityBody, stableCapacityBody,
      maxWithdrawReadBody] using run
  obtain ⟨ownerPre, ownerValid, ownerRun, ownerStack, entryState,
      entryMemory, entryLogs⟩ :=
    canonicalAddressArg_body_of_ok (R := Func.RunOk) nil_pref routedRun
  have ownerWf : Mem.Wf ownerPre.memory := by
    rw [← entryMemory]
    exact memoryWf
  have amountStageRun :
      Func.RunCompiledTo (vault.main :: vault.aux) sevm ownerPre
        (arg 0 +++ sload ::: mstoreAt amountWord +++
          stagedSupplyCapacityBody maxWithdrawReadBody) (.ok post) :=
    ownerRun
  obtain ⟨amount, supplyEntry, amountEq, supplyStack, amountWindow,
      amountState, amountLogs, supplyRun⟩ :=
    capacityAmountStaging_trace (R := Func.RunOk) ownerWf ownerStack amountStageRun
  have supplyWf : Mem.Wf supplyEntry.memory := amountWindow.1
  have supplyStageRun :
      Func.RunCompiledTo (vault.main :: vault.aux) sevm supplyEntry
        (pushSupplySlot +++ sload ::: mstoreAt supplyWord +++
          stableCapacityBody maxWithdrawReadBody) (.ok post) := by
    simpa only [stagedSupplyCapacityBody] using supplyRun
  obtain ⟨supply, branchEntry, supplyEq, branchStack, supplyWindow,
      supplyPreserves, supplyState, supplyLogs, branchRun⟩ :=
    capacitySupplyStaging_trace (R := Func.RunOk) supplyWf supplyStack supplyStageRun
  have branchAmountWindow :
      MemWordAt branchEntry (amountWord * 32).toNat amount :=
    supplyPreserves (Or.inl (by decide +kernel)) amountWindow
  have stableRun :
      Func.RunCompiledTo (vault.main :: vault.aux) sevm branchEntry
        (loadWord supplyWord +++ pushB256 maxSupply ::: lt :::
          (returnConstant 0 <?> readTotalAssets maxWithdrawReadBody))
        (.ok post) := by
    simpa only [stableCapacityBody] using branchRun
  rcases stableCapacityBranch_trace (R := Func.RunOk) supplyWindow branchStack stableRun with
    unstableSupply | stableSupply
  · rcases unstableSupply with ⟨unstable, effect⟩
    have entryToBranchState :=
      entryState.trans (amountState.trans supplyState)
    have entryToBranchLogs :=
      entryLogs.trans (amountLogs.trans supplyLogs)
    have lifted := lift_word_view entryToBranchState entryToBranchLogs effect
    have amountAtEntry : amount = Devm.getStorVal entry sevm.currentTarget
        (Sevm.argWord sevm 0) := by
      rw [amountEq]
      change
        (Devm.getStor ownerPre sevm.currentTarget).get
            (Sevm.argWord sevm 0) =
          (Devm.getStor entry sevm.currentTarget).get
            (Sevm.argWord sevm 0)
      rw [funext (getStor_eq_of_state_eq entryState)]
    have supplyAtEntry : supply =
        Devm.getStorVal entry sevm.currentTarget supplySlot := by
      rw [supplyEq]
      change
        (Devm.getStor supplyEntry sevm.currentTarget).get supplySlot =
          (Devm.getStor entry sevm.currentTarget).get supplySlot
      rw [funext (getStor_eq_of_state_eq
        (entryState.trans amountState))]
    have unstableAtEntry : maxSupplyN <
        (Devm.getStorVal entry sevm.currentTarget supplySlot).toNat := by
      rw [← supplyAtEntry]
      exact unstable
    have zeroWord : Nat.toB256 0 = (0 : B256) := by decide +kernel
    refine ⟨ownerValid, ?_, ?_⟩
    · simpa only [maxWithdrawViewN, if_pos unstableAtEntry] using
        wordModulusN_pos
    · simpa only [maxWithdrawViewN, if_pos unstableAtEntry, zeroWord] using
        lifted
  · rcases stableSupply with
      ⟨readEntry, stable, readStack, readSupplyWindow, branchPreserves,
        stableState, stableLogs, readRun⟩
    have readAmountWindow :
        MemWordAt readEntry (amountWord * 32).toNat amount :=
      branchPreserves branchAmountWindow
    have entryToReadState := entryState.trans
      (amountState.trans (supplyState.trans stableState))
    have entryToReadLogs := entryLogs.trans
      (amountLogs.trans (supplyLogs.trans stableLogs))
    have readConfig :
        DirectWethConfiguration sevm.currentTarget sevm readEntry := by
      refine ⟨config.distinct, config.nonprecompile, ?_⟩
      rw [← getCode_eq_of_state_eq entryToReadState wethAccount]
      exact config.code
    have readWf : Mem.Wf readEntry.memory := readSupplyWindow.1
    obtain ⟨resultFits, result⟩ :=
      readTotalAssets_capacity_body_effect readConfig readWf
        (resources readEntry readRun) readSupplyWindow
        (calculate := fun assets supply =>
          min maxWordN (maxWithdrawN amount.toNat assets supply))
        (by
          intro bodyPre image assets bodyWf bodyReads bodyStack
            bodySupplyWindow preserves bodyRun
          have bodyAmountWindow := preserves
            (by decide +kernel : 64 ≤ (amountWord * 32).toNat)
            readAmountWindow
          apply
            Blanc.ProrataWethVault.maxWithdraw_postTotalAssets_body_effect
              bodyWf bodyReads bodyAmountWindow bodySupplyWindow stable
              bodyStack returnLookup
          simpa only [maxWithdrawReadBody] using bodyRun)
        readRun
    have lifted := lift_word_view entryToReadState entryToReadLogs result
    have amountAtEntry : amount = Devm.getStorVal entry sevm.currentTarget
        (Sevm.argWord sevm 0) := by
      rw [amountEq]
      change
        (Devm.getStor ownerPre sevm.currentTarget).get
            (Sevm.argWord sevm 0) =
          (Devm.getStor entry sevm.currentTarget).get
            (Sevm.argWord sevm 0)
      rw [funext (getStor_eq_of_state_eq entryState)]
    have supplyAtEntry : supply =
        Devm.getStorVal entry sevm.currentTarget supplySlot := by
      rw [supplyEq]
      change
        (Devm.getStor supplyEntry sevm.currentTarget).get supplySlot =
          (Devm.getStor entry sevm.currentTarget).get supplySlot
      rw [funext (getStor_eq_of_state_eq
        (entryState.trans amountState))]
    have stableAtEntry :
        (Devm.getStorVal entry sevm.currentTarget supplySlot).toNat ≤
          maxSupplyN := by
      rw [← supplyAtEntry]
      exact stable
    rw [← entryToReadState, amountAtEntry, supplyAtEntry] at resultFits lifted
    exact ⟨ownerValid,
      by simpa only [maxWithdrawViewN,
        if_neg (Nat.not_lt_of_ge stableAtEntry)] using resultFits,
      by simpa only [maxWithdrawViewN,
        if_neg (Nat.not_lt_of_ge stableAtEntry)] using lifted⟩

/-! ## Public compiled selectors -/

private theorem returnWord_lookup :
    (vault.main :: vault.aux)[returnWordSlot]? = some returnWord := by
  simp [vault, vaultAux, returnWordSlot]

private theorem maxMintAfterAssetCap_lookup :
    (vault.main :: vault.aux)[maxMintAfterAssetCapSlot]? =
      some maxMintAfterAssetCap := by
  simp [vault, vaultAux, maxMintAfterAssetCapSlot]

/-- Positional membership avoids reducing selector hashes or comparing the
large compiled capacity bodies. -/
private theorem maxDeposit_mem_vaultFuncs :
    (selector "maxDeposit" [.address], routed 1 maxDeposit) ∈ vaultFuncs := by
  simp only [vaultFuncs]
  apply List.Mem.tail
  apply List.Mem.tail
  apply List.Mem.tail
  apply List.Mem.tail
  apply List.Mem.tail
  apply List.Mem.tail
  apply List.Mem.tail
  apply List.Mem.tail
  apply List.Mem.tail
  exact List.Mem.head _

private theorem maxMint_mem_vaultFuncs :
    (selector "maxMint" [.address], routed 1 maxMint) ∈ vaultFuncs := by
  simp only [vaultFuncs]
  apply List.Mem.tail
  apply List.Mem.tail
  apply List.Mem.tail
  apply List.Mem.tail
  apply List.Mem.tail
  apply List.Mem.tail
  apply List.Mem.tail
  apply List.Mem.tail
  apply List.Mem.tail
  apply List.Mem.tail
  apply List.Mem.tail
  apply List.Mem.tail
  apply List.Mem.tail
  apply List.Mem.tail
  apply List.Mem.tail
  apply List.Mem.tail
  apply List.Mem.tail
  apply List.Mem.tail
  apply List.Mem.tail
  exact List.Mem.head _

private theorem maxWithdraw_mem_vaultFuncs :
    (selector "maxWithdraw" [.address], routed 1 maxWithdraw) ∈
      vaultFuncs := by
  simp only [vaultFuncs]
  apply List.Mem.tail
  apply List.Mem.tail
  apply List.Mem.tail
  apply List.Mem.tail
  apply List.Mem.tail
  apply List.Mem.tail
  apply List.Mem.tail
  apply List.Mem.tail
  apply List.Mem.tail
  apply List.Mem.tail
  apply List.Mem.tail
  apply List.Mem.tail
  apply List.Mem.tail
  apply List.Mem.tail
  apply List.Mem.tail
  apply List.Mem.tail
  apply List.Mem.tail
  apply List.Mem.tail
  apply List.Mem.tail
  apply List.Mem.tail
  apply List.Mem.tail
  exact List.Mem.head _

/-- Lift a compiled capacity body whose result depends only on persistent
state through the shared selector-entry boundary.  Keeping the result
abstract prevents each public endpoint from re-elaborating the concrete
capacity body during the dispatch proof. -/
private theorem capacity_compiled_effect
    {sevm : Sevm} {pre post : Devm} {sig : B256} {body : Func}
    {result : State → Nat}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (memoryWf : Mem.Wf pre.memory)
    (member : (sig, routed 1 body) ∈ vaultFuncs)
    (bodyEffect : ∀ {entry : Devm},
      DirectWethConfiguration sevm.currentTarget sevm entry →
      Mem.Wf entry.memory →
      Func.RunCompiledTo (vault.main :: vault.aux) sevm entry body
          (.ok post) →
        ValidAdr (Sevm.argWord sevm 0) ∧
          result entry.state < wordModulusN ∧
          WordViewEffect (Nat.toB256 (result entry.state)) entry post)
    (run : Prog.RunCompiled sevm pre vault post)
    (selectorEq : Sevm.selector sevm = sig) :
    sevm.value = 0 ∧
      ValidAdr (Sevm.argWord sevm 0) ∧
      result pre.state < wordModulusN ∧
      WordViewEffect (Nat.toB256 (result pre.state)) pre post := by
  rcases Blanc.ProrataWethVault.runCompiled_enters_body_compiled_logs
      run selectorEq member with
    ⟨bodyPre, valueZero, -, entryState, entryMemory, entryLogs, -, bodyRun⟩
  have bodyConfig :
      DirectWethConfiguration sevm.currentTarget sevm bodyPre := by
    refine ⟨config.distinct, config.nonprecompile, ?_⟩
    rw [← getCode_eq_of_state_eq entryState wethAccount]
    exact config.code
  have bodyWf : Mem.Wf bodyPre.memory := by
    rw [← entryMemory]
    exact memoryWf
  obtain ⟨valid, fits, effect⟩ := bodyEffect bodyConfig bodyWf bodyRun
  have lifted := lift_word_view entryState entryLogs effect
  rw [← entryState] at fits lifted
  exact ⟨valueZero, valid, fits, lifted⟩

/-- Public compiled `maxMint(receiver)` returns the exact frozen capacity
policy against the pre-state WETH balance and share supply. -/
theorem maxMint_compiled_effect
    {sevm : Sevm} {pre post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (memoryWf : Mem.Wf pre.memory)
    (resources : MaxMintResources sevm post)
    (run : Prog.RunCompiled sevm pre vault post)
    (selectorEq :
      Sevm.selector sevm = selector "maxMint" [.address]) :
    sevm.value = 0 ∧
      ValidAdr (Sevm.argWord sevm 0) ∧
      maxMintViewN (Sevm.argWord sevm 0).toNat
          ((pre.state.getStor wethAccount).get
            sevm.currentTarget.toB256).toNat
          (Devm.getStorVal pre sevm.currentTarget supplySlot).toNat <
        wordModulusN ∧
      WordViewEffect
        (Nat.toB256 (maxMintViewN (Sevm.argWord sevm 0).toNat
          ((pre.state.getStor wethAccount).get
            sevm.currentTarget.toB256).toNat
          (Devm.getStorVal pre sevm.currentTarget supplySlot).toNat))
        pre post := by
  refine capacity_compiled_effect
    (result := fun state =>
      maxMintViewN (Sevm.argWord sevm 0).toNat
        ((state.get wethAccount).stor.get
          sevm.currentTarget.toB256).toNat
        ((state.get sevm.currentTarget).stor.get supplySlot).toNat)
    config memoryWf maxMint_mem_vaultFuncs ?_ run selectorEq
  intro bodyPre bodyConfig bodyWf bodyRun
  exact maxMint_body_effect bodyConfig bodyWf resources returnWord_lookup
    maxMintAfterAssetCap_lookup bodyRun

/-- Public compiled `maxDeposit(receiver)` returns the exact frozen capacity
policy. -/
theorem maxDeposit_compiled_effect
    {sevm : Sevm} {pre post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (memoryWf : Mem.Wf pre.memory)
    (resources : MaxDepositResources sevm post)
    (run : Prog.RunCompiled sevm pre vault post)
    (selectorEq :
      Sevm.selector sevm = selector "maxDeposit" [.address]) :
    sevm.value = 0 ∧
      ValidAdr (Sevm.argWord sevm 0) ∧
      maxDepositViewN (Sevm.argWord sevm 0).toNat
          ((pre.state.getStor wethAccount).get
            sevm.currentTarget.toB256).toNat
          (Devm.getStorVal pre sevm.currentTarget supplySlot).toNat <
        wordModulusN ∧
      WordViewEffect
        (Nat.toB256 (maxDepositViewN (Sevm.argWord sevm 0).toNat
          ((pre.state.getStor wethAccount).get
            sevm.currentTarget.toB256).toNat
          (Devm.getStorVal pre sevm.currentTarget supplySlot).toNat))
        pre post := by
  refine capacity_compiled_effect
    (result := fun state =>
      maxDepositViewN (Sevm.argWord sevm 0).toNat
        ((state.get wethAccount).stor.get
          sevm.currentTarget.toB256).toNat
        ((state.get sevm.currentTarget).stor.get supplySlot).toNat)
    config memoryWf maxDeposit_mem_vaultFuncs ?_ run selectorEq
  intro bodyPre bodyConfig bodyWf bodyRun
  exact maxDeposit_body_effect bodyConfig bodyWf resources returnWord_lookup
    bodyRun

/-- Public compiled `maxWithdraw(owner)` returns the exact saturated capacity
policy. -/
theorem maxWithdraw_compiled_effect
    {sevm : Sevm} {pre post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (memoryWf : Mem.Wf pre.memory)
    (resources : MaxWithdrawResources sevm post)
    (run : Prog.RunCompiled sevm pre vault post)
    (selectorEq :
      Sevm.selector sevm = selector "maxWithdraw" [.address]) :
    sevm.value = 0 ∧
      ValidAdr (Sevm.argWord sevm 0) ∧
      maxWithdrawViewN
          (Devm.getStorVal pre sevm.currentTarget
            (Sevm.argWord sevm 0)).toNat
          ((pre.state.getStor wethAccount).get
            sevm.currentTarget.toB256).toNat
          (Devm.getStorVal pre sevm.currentTarget supplySlot).toNat <
        wordModulusN ∧
      WordViewEffect
        (Nat.toB256 (maxWithdrawViewN
          (Devm.getStorVal pre sevm.currentTarget
            (Sevm.argWord sevm 0)).toNat
          ((pre.state.getStor wethAccount).get
            sevm.currentTarget.toB256).toNat
          (Devm.getStorVal pre sevm.currentTarget supplySlot).toNat))
        pre post := by
  refine capacity_compiled_effect
    (result := fun state =>
      maxWithdrawViewN
        ((state.get sevm.currentTarget).stor.get
          (Sevm.argWord sevm 0)).toNat
        ((state.get wethAccount).stor.get
          sevm.currentTarget.toB256).toNat
        ((state.get sevm.currentTarget).stor.get supplySlot).toNat)
    config memoryWf maxWithdraw_mem_vaultFuncs ?_ run selectorEq
  intro bodyPre bodyConfig bodyWf bodyRun
  exact maxWithdraw_body_effect bodyConfig bodyWf resources returnWord_lookup
    bodyRun

/-- On the admitted nonzero-receiver, stable-supply domain, the `maxMint`
policy reduces to the mathematical capacity formula itself. -/
theorem maxMint_compiled_effect_stable
    {sevm : Sevm} {pre post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (memoryWf : Mem.Wf pre.memory)
    (resources : MaxMintResources sevm post)
    (receiverNonzero : (Sevm.argWord sevm 0).toNat ≠ 0)
    (stable :
      (Devm.getStorVal pre sevm.currentTarget supplySlot).toNat ≤
        maxSupplyN)
    (run : Prog.RunCompiled sevm pre vault post)
    (selectorEq :
      Sevm.selector sevm = selector "maxMint" [.address]) :
    sevm.value = 0 ∧
      ValidAdr (Sevm.argWord sevm 0) ∧
      maxMintN
          ((pre.state.getStor wethAccount).get
            sevm.currentTarget.toB256).toNat
          (Devm.getStorVal pre sevm.currentTarget supplySlot).toNat <
        wordModulusN ∧
      WordViewEffect
        (Nat.toB256 (maxMintN
          ((pre.state.getStor wethAccount).get
            sevm.currentTarget.toB256).toNat
          (Devm.getStorVal pre sevm.currentTarget supplySlot).toNat))
        pre post := by
  obtain ⟨valueZero, valid, fits, effect⟩ :=
    maxMint_compiled_effect config memoryWf resources run selectorEq
  simpa [maxMintViewN, receiverNonzero, Nat.not_lt_of_ge stable] using
    And.intro valueZero (And.intro valid (And.intro fits effect))

/-- Stable nonzero-receiver specialization of `maxDeposit`. -/
theorem maxDeposit_compiled_effect_stable
    {sevm : Sevm} {pre post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (memoryWf : Mem.Wf pre.memory)
    (resources : MaxDepositResources sevm post)
    (receiverNonzero : (Sevm.argWord sevm 0).toNat ≠ 0)
    (stable :
      (Devm.getStorVal pre sevm.currentTarget supplySlot).toNat ≤
        maxSupplyN)
    (run : Prog.RunCompiled sevm pre vault post)
    (selectorEq :
      Sevm.selector sevm = selector "maxDeposit" [.address]) :
    sevm.value = 0 ∧
      ValidAdr (Sevm.argWord sevm 0) ∧
      maxDepositN
          ((pre.state.getStor wethAccount).get
            sevm.currentTarget.toB256).toNat
          (Devm.getStorVal pre sevm.currentTarget supplySlot).toNat <
        wordModulusN ∧
      WordViewEffect
        (Nat.toB256 (maxDepositN
          ((pre.state.getStor wethAccount).get
            sevm.currentTarget.toB256).toNat
          (Devm.getStorVal pre sevm.currentTarget supplySlot).toNat))
        pre post := by
  obtain ⟨valueZero, valid, fits, effect⟩ :=
    maxDeposit_compiled_effect config memoryWf resources run selectorEq
  simpa [maxDepositViewN, receiverNonzero, Nat.not_lt_of_ge stable] using
    And.intro valueZero (And.intro valid (And.intro fits effect))

/-- In a stable conserved share ledger, an owner's balance is bounded by
supply, so the saturated `maxWithdraw` result is exactly the unsaturated
ERC-4626 asset claim. -/
theorem maxWithdraw_compiled_effect_exact
    {sevm : Sevm} {pre post : Devm}
    (config : DirectWethConfiguration sevm.currentTarget sevm pre)
    (memoryWf : Mem.Wf pre.memory)
    (resources : MaxWithdrawResources sevm post)
    (stable :
      (Devm.getStorVal pre sevm.currentTarget supplySlot).toNat ≤
        maxSupplyN)
    (balanceLe :
      (Devm.getStorVal pre sevm.currentTarget
          (Sevm.argWord sevm 0)).toNat ≤
        (Devm.getStorVal pre sevm.currentTarget supplySlot).toNat)
    (run : Prog.RunCompiled sevm pre vault post)
    (selectorEq :
      Sevm.selector sevm = selector "maxWithdraw" [.address]) :
    sevm.value = 0 ∧
      ValidAdr (Sevm.argWord sevm 0) ∧
      maxWithdrawN
          (Devm.getStorVal pre sevm.currentTarget
            (Sevm.argWord sevm 0)).toNat
          ((pre.state.getStor wethAccount).get
            sevm.currentTarget.toB256).toNat
          (Devm.getStorVal pre sevm.currentTarget supplySlot).toNat <
        wordModulusN ∧
      WordViewEffect
        (Nat.toB256 (maxWithdrawN
          (Devm.getStorVal pre sevm.currentTarget
            (Sevm.argWord sevm 0)).toNat
          ((pre.state.getStor wethAccount).get
            sevm.currentTarget.toB256).toNat
          (Devm.getStorVal pre sevm.currentTarget supplySlot).toNat))
        pre post := by
  obtain ⟨valueZero, valid, fits, effect⟩ :=
    maxWithdraw_compiled_effect config memoryWf resources run selectorEq
  let balance := (Devm.getStorVal pre sevm.currentTarget
    (Sevm.argWord sevm 0)).toNat
  let assets := ((pre.state.getStor wethAccount).get
    sevm.currentTarget.toB256).toNat
  let supply := (Devm.getStorVal pre sevm.currentTarget supplySlot).toNat
  have claimLeAssets : maxWithdrawN balance assets supply ≤ assets := by
    exact maxWithdrawN_le_assets (by simpa [balance, supply] using balanceLe)
  have assetsLeMax : assets ≤ maxWordN := by
    have assetsLt : assets < wordModulusN := by
      simpa [assets, wordModulusN] using
        B256.toNat_lt
          ((pre.state.getStor wethAccount).get sevm.currentTarget.toB256)
    unfold maxWordN
    omega
  have uncapped : min maxWordN (maxWithdrawN balance assets supply) =
      maxWithdrawN balance assets supply :=
    Nat.min_eq_right (claimLeAssets.trans assetsLeMax)
  have exactFits : maxWithdrawN balance assets supply < wordModulusN :=
    (claimLeAssets.trans assetsLeMax).trans_lt maxWordN_lt_wordModulusN
  refine ⟨valueZero, valid, by simpa [balance, assets, supply] using exactFits,
    ?_⟩
  simpa [maxWithdrawViewN, balance, assets, supply,
    Nat.not_lt_of_ge stable, uncapped] using effect

end Blanc.Composition.ProrataWethVault
