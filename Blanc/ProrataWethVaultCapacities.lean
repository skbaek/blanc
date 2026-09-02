-- ProrataWethVaultCapacities.lean : exact local ERC-4626 capacity seams.

import Blanc.ProrataWethVaultConversions

namespace Blanc

open Jaune
open Jaune.Ninst Ninst
open scoped LogOutputHinv

namespace ProrataWethVault

/-!
# Compiled capacity seams

Capacity endpoints differ from ordinary conversions in two ways.  They stage
the supply before the WETH balance query, and `maxMint` must carry that staged
word through full-width scratch arithmetic into a second internal
continuation.  `MemWordAt` and the arithmetic trace frames make that memory
dependency explicit without exposing the complete scratch image.
-/

/-! ## The final `maxMint` minimum -/

/-- `maxMintAfterAssetCap` stores the arithmetic asset cap, compares it with
the exact remaining share room, and returns their natural-number minimum.
The supply word sits immediately after the quote word and is preserved by the
quote store's half-open write interval. -/
theorem maxMintAfterAssetCap_trace
    {fs : List Func} {sevm : Sevm} {pre final : Devm}
    {supply cap : B256} {tail : Stack}
    (supplyWindow : MemWordAt pre (supplyWord * 32).toNat supply)
    (stable : supply.toNat ≤ maxSupplyN)
    (stack : cap :: tail <<+ pre.stack)
    (returnLookup : fs[returnWordSlot]? = some returnWord)
    (run : Func.RunCompiledTo fs sevm pre maxMintAfterAssetCap (.ok final)) :
    ReturnsWord
      (Nat.toB256 (min (shareRoomN supply.toNat) cap.toNat)) final := by
  unfold maxMintAfterAssetCap at run
  obtain ⟨quotePre, quoteStoreRun, run⟩ :=
    runCompiledTo_prepend_inv run
  obtain ⟨quoteStack, quoteMemory⟩ :=
    of_run_mstoreAt_val quoteStoreRun stack
  obtain ⟨sourceImage, sourceMemImage⟩ := supplyWindow.memImage
  have quoteWindow :
      MemWordAt quotePre (quoteWord * 32).toNat cap :=
    MemWordAt.of_write sourceMemImage quoteMemory
  have supplyWindow' :
      MemWordAt quotePre (supplyWord * 32).toNat supply := by
    apply supplyWindow.acrossMstoreAt
      (k := quoteWord) (Or.inr (by decide +kernel)) quoteStoreRun
  obtain ⟨image, imageMem⟩ := supplyWindow'.memImage
  have quoteAt : Bytes.toB256
      (image.sliceD (quoteWord * 32).toNat 32 0) = cap := by
    rw [quoteWindow.slice_eq imageMem.2, B256.toB256_toBytes]
  have supplyAt : Bytes.toB256
      (image.sliceD (supplyWord * 32).toNat 32 0) = supply := by
    rw [supplyWindow'.slice_eq imageMem.2, B256.toB256_toBytes]

  obtain ⟨roomPre, quoteRun, run⟩ :=
    runCompiledTo_prepend_inv run
  obtain ⟨quotePrefix, quoteWf, quoteReads, -⟩ :=
    (ProducesWord.loadWord (sevm := sevm) quoteAt)
      imageMem.1 imageMem.2 quoteStack quoteRun
  obtain ⟨testPre, roomRun, run⟩ :=
    runCompiledTo_prepend_inv run
  obtain ⟨roomPrefix, roomWf, roomReads, -⟩ :=
    (ProducesWord.shareRoom (sevm := sevm) supplyAt stable)
      quoteWf quoteReads quotePrefix roomRun
  obtain ⟨branchPre, testRun, branchRun⟩ :=
    runCompiledTo_next_inv run
  have testSource := Ninst.Run.of_runCompiled testRun
  have testPrefix := prefix_of_lt testSource roomPrefix
  have testMemory : testPre.memory = branchPre.memory :=
    Ninst.Hinv.inv (f := Devm.memory) testSource
  have branchWf : Mem.Wf branchPre.memory := by
    rw [← testMemory]
    exact roomWf
  have branchReads : Mem.Reads branchPre.memory image := by
    rw [← testMemory]
    exact roomReads
  let room := shareRoomN supply.toNat
  have roomFits : room < wordModulusN :=
    shareRoomN_lt_wordModulusN supply.toNat

  by_cases roomLt : Nat.toB256 room < cap
  · have onePrefix : (1 : B256) :: tail <<+ branchPre.stack := by
      simpa [room, B256.ltCheck, roomLt] using testPrefix
    obtain ⟨bodyPre, branchWord, branchWordNe, bodyPop, bodyRun,
        bodyPrefix⟩ :=
      Func.RunCompiledTo.succ_branch_of_prefix
        (by decide : (1 : B256) ≠ 0) onePrefix branchRun
    have bodyWf : Mem.Wf bodyPre.memory := by
      rw [← bodyPop.memory]
      exact branchWf
    have bodyReads : Mem.Reads bodyPre.memory image := by
      rw [← bodyPop.memory]
      exact branchReads
    obtain ⟨callPre, roomRun, callRun⟩ :=
      runCompiledTo_prepend_inv bodyRun
    obtain ⟨selectedPrefix, -, -, -⟩ :=
      (ProducesWord.shareRoom (sevm := sevm) supplyAt stable)
        bodyWf bodyReads bodyPrefix roomRun
    obtain ⟨returnPre, callBurn, returnRun⟩ :=
      runCompiledTo_call_inv returnLookup callRun
    have returnPrefix : Nat.toB256 room :: tail <<+ returnPre.stack := by
      rw [← callBurn.stack]
      exact selectedPrefix
    have returned := returnWord_trace returnPrefix returnRun
    have selected := minWord_eq_toB256_min roomFits cap
    rw [if_pos roomLt] at selected
    rw [← selected]
    exact returned
  · have zeroPrefix : (0 : B256) :: tail <<+ branchPre.stack := by
      simpa [room, B256.ltCheck, roomLt] using testPrefix
    obtain ⟨bodyPre, bodyPop, bodyRun, bodyPrefix⟩ :=
      Func.RunCompiledTo.zero_branch_of_prefix zeroPrefix branchRun
    have bodyWf : Mem.Wf bodyPre.memory := by
      rw [← bodyPop.memory]
      exact branchWf
    have bodyReads : Mem.Reads bodyPre.memory image := by
      rw [← bodyPop.memory]
      exact branchReads
    obtain ⟨callPre, quoteRun, callRun⟩ :=
      runCompiledTo_prepend_inv bodyRun
    obtain ⟨selectedPrefix, -, -, -⟩ :=
      (ProducesWord.loadWord (sevm := sevm) quoteAt)
        bodyWf bodyReads bodyPrefix quoteRun
    obtain ⟨returnPre, callBurn, returnRun⟩ :=
      runCompiledTo_call_inv returnLookup callRun
    have returnPrefix : cap :: tail <<+ returnPre.stack := by
      rw [← callBurn.stack]
      exact selectedPrefix
    have returned := returnWord_trace returnPrefix returnRun
    have selected := minWord_eq_toB256_min roomFits cap
    rw [if_neg roomLt] at selected
    rw [← selected]
    exact returned

/-! ## Full-width capacity arithmetic -/

/-- The post-staging `maxMint` suffix computes the full-width asset cap,
carries the supply word across arithmetic scratch memory, and returns the
minimum of that cap and the exact share room. -/
theorem maxMint_arithmetic_trace
    {fs : List Func} {sevm : Sevm} {pre final : Devm}
    {image : Bytes} {assets supply : B256} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (assetsAt : Bytes.toB256
      (image.sliceD (assetsWord * 32).toNat 32 0) = assets)
    (supplyAt : Bytes.toB256
      (image.sliceD (supplyWord * 32).toNat 32 0) = supply)
    (supplyWindow : MemWordAt pre (supplyWord * 32).toNat supply)
    (stable : supply.toNat ≤ maxSupplyN)
    (stack : tail <<+ pre.stack)
    (returnLookup : fs[returnWordSlot]? = some returnWord)
    (capLookup :
      fs[maxMintAfterAssetCapSlot]? = some maxMintAfterAssetCap)
    (run : Func.RunCompiledTo fs sevm pre
      (loadWord assetsWord +++ isMax +++
        (productOverTwoPow256 [pushB256 B256.max] stagedDenominator .down
            maxMintAfterAssetCapSlot <?>
          mulDiv [pushB256 B256.max] stagedDenominator stagedAssetFactor
            .capDown maxMintAfterAssetCapSlot)) (.ok final)) :
    ReturnsWord
      (Nat.toB256 (maxMintN assets.toNat supply.toNat)) final := by
  have supplySlice :
      image.sliceD (supplyWord * 32).toNat 32 0 = supply.toBytes :=
    supplyWindow.slice_eq memoryReads
  rcases ProducesWord.isMax_arm_trace
      (ProducesWord.loadWord assetsAt) memoryWf memoryReads stack run with
    maxArm | ordinaryArm
  · rcases maxArm with
      ⟨assetsMax, bodyPre, bodyStack, bodyWf, bodyReads, bodyRun⟩
    let denominator := Nat.toB256 (denominatorN supply.toNat)
    obtain ⟨quotientFits, capPre, capStack, capImage, capRun⟩ :=
      productOverTwoPow256_down_image_trace bodyWf bodyReads
        (ProducesWord.pushB256 sevm image B256.max)
        (ProducesWord.stagedDenominator_after_productScratch supplyAt)
        bodyStack capLookup bodyRun
    have bodySupplyWindow :
        MemWordAt bodyPre (supplyWord * 32).toNat supply :=
      MemWordAt.of_memImage ⟨bodyWf, bodyReads⟩ supplySlice
    have capSupplyWindow :
        MemWordAt capPre (supplyWord * 32).toNat supply :=
      bodySupplyWindow.of_wordFrame bodyReads capImage
        (productOverTwoPow256TraceImage_wordFrame
          image B256.max denominator)
        (by decide +kernel)
    have returned := maxMintAfterAssetCap_trace capSupplyWindow stable
      capStack returnLookup capRun
    have denominatorNat : denominator.toNat = denominatorN supply.toNat := by
      dsimp [denominator]
      exact stagedDenominator_toNat stable
    have quotientNat :
        (Nat.toB256
          (B256.max.toNat * denominator.toNat / wordModulusN)).toNat =
            B256.max.toNat * denominator.toNat / wordModulusN :=
      B256.toNat_toB256_of_lt quotientFits
    rw [quotientNat, denominatorNat, maxWord_toNat] at returned
    unfold maxMintN
    rw [assetsMax, maxWord_toNat, assetFactorN_maxWord]
    exact returned
  · rcases ordinaryArm with
      ⟨assetsNotMax, bodyPre, bodyStack, bodyWf, bodyReads, bodyRun⟩
    let factor := Nat.toB256 (assetFactorN assets.toNat)
    let denominator := Nat.toB256 (denominatorN supply.toNat)
    obtain ⟨capPre, capImage, capStack, capMemImage, capFrame, capRun⟩ :=
      mulDiv_capDown_image_trace bodyWf bodyReads
        (ProducesWord.stagedAssetFactor assetsAt)
        (ProducesWord.pushB256 sevm
          (Bytes.writeAt image (denominatorWord * 32).toNat
            factor.toBytes) B256.max)
        (ProducesWord.stagedDenominator_after_mulDivScratch supplyAt)
        bodyStack capLookup bodyRun
    have bodySupplyWindow :
        MemWordAt bodyPre (supplyWord * 32).toNat supply :=
      MemWordAt.of_memImage ⟨bodyWf, bodyReads⟩ supplySlice
    have capSupplyWindow :
        MemWordAt capPre (supplyWord * 32).toNat supply :=
      bodySupplyWindow.of_wordFrame bodyReads capMemImage capFrame
        (by decide +kernel)
    have returned := maxMintAfterAssetCap_trace capSupplyWindow stable
      capStack returnLookup capRun
    simpa [maxMintN, factor, denominator, maxWord_toNat,
      stagedDenominator_toNat stable,
      stagedAssetFactor_toNat_of_ne_max assetsNotMax,
      toNat_toB256_min_maxWord, min_shareRoomN_min_maxWord] using returned

/-- The share-room successor producer remains valid after `mulDiv` stages its
denominator in the lower arithmetic scratch region. -/
theorem ProducesWord.shareRoomPlusOne_after_denominatorScratch
    {sevm : Sevm} {image : Bytes} {supply denominator : B256}
    (supplyAt : Bytes.toB256
      (image.sliceD (supplyWord * 32).toNat 32 0) = supply)
    (stable : supply.toNat ≤ maxSupplyN) :
    ProducesWord sevm ProrataWethVault.shareRoomPlusOne
      (Bytes.writeAt image (denominatorWord * 32).toNat
        denominator.toBytes)
      (Nat.toB256 (shareRoomN supply.toNat + 1)) := by
  apply ProducesWord.shareRoomPlusOne
  rw [Bytes.readWord_writeAt_of_disjoint]
  · exact supplyAt
  · right
    decide +kernel
  exact stable

/-- The staged owner balance remains readable after `mulDiv` stages its
denominator below the operation-word region. -/
theorem ProducesWord.amount_after_denominatorScratch
    {sevm : Sevm} {image : Bytes} {amount denominator : B256}
    (amountAt : Bytes.toB256
      (image.sliceD (amountWord * 32).toNat 32 0) = amount) :
    ProducesWord sevm (ProrataWethVault.loadWord amountWord)
      (Bytes.writeAt image (denominatorWord * 32).toNat
        denominator.toBytes) amount := by
  apply ProducesWord.loadWord
  rw [Bytes.readWord_writeAt_of_disjoint]
  · exact amountAt
  · right
    decide +kernel

/-- `maxDeposit` returns the greatest word-sized asset amount whose floor
share conversion still fits the remaining supply room.  The
ceiling-predecessor arithmetic is exact in both the `2^256` asset-factor arm
and the ordinary full-width product arm. -/
theorem maxDeposit_arithmetic_trace
    {fs : List Func} {sevm : Sevm} {pre final : Devm}
    {image : Bytes} {assets supply : B256} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (assetsAt : Bytes.toB256
      (image.sliceD (assetsWord * 32).toNat 32 0) = assets)
    (supplyAt : Bytes.toB256
      (image.sliceD (supplyWord * 32).toNat 32 0) = supply)
    (stable : supply.toNat ≤ maxSupplyN)
    (stack : tail <<+ pre.stack)
    (returnLookup : fs[returnWordSlot]? = some returnWord)
    (run : Func.RunCompiledTo fs sevm pre
      (loadWord assetsWord +++ isMax +++
        (shiftedDiv shareRoomPlusOne stagedDenominator .capCeilPred
            returnWordSlot <?>
          mulDiv shareRoomPlusOne stagedAssetFactor stagedDenominator
            .capCeilPred returnWordSlot)) (.ok final)) :
    ReturnsWord
      (Nat.toB256 (maxDepositN assets.toNat supply.toNat)) final := by
  rcases ProducesWord.isMax_arm_trace
      (ProducesWord.loadWord assetsAt) memoryWf memoryReads stack run with
    maxArm | ordinaryArm
  · rcases maxArm with
      ⟨assetsMax, bodyPre, bodyStack, bodyWf, bodyReads, bodyRun⟩
    let high := Nat.toB256 (shareRoomN supply.toNat + 1)
    let denominator := Nat.toB256 (denominatorN supply.toNat)
    have highPositive : 0 < high.toNat := by
      rw [show high.toNat = shareRoomN supply.toNat + 1 by
        unfold high
        apply B256.toNat_toB256_of_lt
        exact shareRoomN_add_one_lt_wordModulusN supply.toNat]
      omega
    obtain ⟨returnPre, quotientStack, returnRun⟩ :=
      shiftedDiv_capCeilPred_trace bodyWf bodyReads
        (ProducesWord.shareRoomPlusOne supplyAt stable)
        (ProducesWord.stagedDenominator_after_shiftedScratch supplyAt)
        highPositive bodyStack returnLookup bodyRun
    have returned := returnWord_trace quotientStack returnRun
    simpa [maxDepositN, assetsMax, high, denominator, maxWord_toNat,
      assetFactorN_maxWord, stagedDenominator_toNat stable,
      B256.toNat_toB256_of_lt
        (shareRoomN_add_one_lt_wordModulusN supply.toNat)] using returned
  · rcases ordinaryArm with
      ⟨assetsNotMax, bodyPre, bodyStack, bodyWf, bodyReads, bodyRun⟩
    let high := Nat.toB256 (shareRoomN supply.toNat + 1)
    let denominator := Nat.toB256 (denominatorN supply.toNat)
    let factor := Nat.toB256 (assetFactorN assets.toNat)
    have productPositive : 0 < high.toNat * factor.toNat := by
      rw [show high.toNat = shareRoomN supply.toNat + 1 by
        unfold high
        apply B256.toNat_toB256_of_lt
        exact shareRoomN_add_one_lt_wordModulusN supply.toNat,
        show factor.toNat = assetFactorN assets.toNat by
          unfold factor
          exact stagedAssetFactor_toNat_of_ne_max assetsNotMax]
      exact Nat.mul_pos (by omega) (assetFactorN_pos assets.toNat)
    obtain ⟨returnPre, quotientStack, returnRun⟩ :=
      mulDiv_capCeilPred_trace bodyWf bodyReads
        (ProducesWord.stagedDenominator supplyAt)
        (ProducesWord.shareRoomPlusOne_after_denominatorScratch
          supplyAt stable)
        (ProducesWord.stagedAssetFactor_after_mulDivScratch assetsAt)
        productPositive bodyStack returnLookup bodyRun
    have returned := returnWord_trace quotientStack returnRun
    simpa [maxDepositN, high, denominator, factor,
      stagedDenominator_toNat stable,
      stagedAssetFactor_toNat_of_ne_max assetsNotMax,
      B256.toNat_toB256_of_lt
        (shareRoomN_add_one_lt_wordModulusN supply.toNat)] using returned

/-- `maxWithdraw` computes the owner's entire asset claim and saturates it at
the largest return word.  A later exact corollary removes the saturation from
reachable share-ledger states where the owner balance is bounded by supply. -/
theorem maxWithdraw_arithmetic_trace
    {fs : List Func} {sevm : Sevm} {pre final : Devm}
    {image : Bytes} {amount assets supply : B256} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (amountAt : Bytes.toB256
      (image.sliceD (amountWord * 32).toNat 32 0) = amount)
    (assetsAt : Bytes.toB256
      (image.sliceD (assetsWord * 32).toNat 32 0) = assets)
    (supplyAt : Bytes.toB256
      (image.sliceD (supplyWord * 32).toNat 32 0) = supply)
    (stable : supply.toNat ≤ maxSupplyN)
    (stack : tail <<+ pre.stack)
    (returnLookup : fs[returnWordSlot]? = some returnWord)
    (run : Func.RunCompiledTo fs sevm pre
      (loadWord assetsWord +++ isMax +++
        (shiftedDiv (loadWord amountWord) stagedDenominator .capDown
            returnWordSlot <?>
          mulDiv (loadWord amountWord) stagedAssetFactor stagedDenominator
            .capDown returnWordSlot)) (.ok final)) :
    ReturnsWord
      (Nat.toB256 (min maxWordN
        (maxWithdrawN amount.toNat assets.toNat supply.toNat))) final := by
  rcases ProducesWord.isMax_arm_trace
      (ProducesWord.loadWord assetsAt) memoryWf memoryReads stack run with
    maxArm | ordinaryArm
  · rcases maxArm with
      ⟨assetsMax, bodyPre, bodyStack, bodyWf, bodyReads, bodyRun⟩
    let denominator := Nat.toB256 (denominatorN supply.toNat)
    obtain ⟨returnPre, quotientStack, returnRun⟩ :=
      shiftedDiv_capDown_trace bodyWf bodyReads
        (ProducesWord.loadWord amountAt)
        (ProducesWord.stagedDenominator_after_shiftedScratch supplyAt)
        bodyStack returnLookup bodyRun
    have returned := returnWord_trace quotientStack returnRun
    simpa [maxWithdrawN, convertToAssetsN, assetsMax, denominator,
      maxWord_toNat, assetFactorN_maxWord,
      stagedDenominator_toNat stable] using returned
  · rcases ordinaryArm with
      ⟨assetsNotMax, bodyPre, bodyStack, bodyWf, bodyReads, bodyRun⟩
    let denominator := Nat.toB256 (denominatorN supply.toNat)
    let factor := Nat.toB256 (assetFactorN assets.toNat)
    obtain ⟨returnPre, quotientStack, returnRun⟩ :=
      mulDiv_capDown_trace bodyWf bodyReads
        (ProducesWord.stagedDenominator supplyAt)
        (ProducesWord.amount_after_denominatorScratch amountAt)
        (ProducesWord.stagedAssetFactor_after_mulDivScratch assetsAt)
        bodyStack returnLookup bodyRun
    have returned := returnWord_trace quotientStack returnRun
    simpa [maxWithdrawN, convertToAssetsN, denominator, factor,
      stagedDenominator_toNat stable,
      stagedAssetFactor_toNat_of_ne_max assetsNotMax] using returned

/-! ## Post-`totalAssets` body effects -/

def capacityAssetsImage (image : Bytes) (assets : B256) : Bytes :=
  Bytes.writeAt image (assetsWord * 32).toNat assets.toBytes

theorem capacityAssetsImage_assets (image : Bytes) (assets : B256) :
    Bytes.toB256
        ((capacityAssetsImage image assets).sliceD
          (assetsWord * 32).toNat 32 0) = assets := by
  unfold capacityAssetsImage
  exact Bytes.readWord_writeAt_self _ _ _

theorem maxMintAfterAssetCap_storage_inv
    {fs : List Func}
    (returnLookup : fs[returnWordSlot]? = some returnWord) :
    Func.CompiledInv fs Devm.getStor Devm.getStor
      maxMintAfterAssetCap := by
  have returnCall :
      Func.CompiledInv fs Devm.getStor Devm.getStor
        (.call returnWordSlot) :=
    returnWord_call_storage_inv returnLookup
  unfold maxMintAfterAssetCap
  compiled_inv

theorem maxMintAfterAssetCap_logs_inv
    {fs : List Func}
    (returnLookup : fs[returnWordSlot]? = some returnWord) :
    Func.CompiledInv fs Devm.logs Devm.logs maxMintAfterAssetCap := by
  have returnCall : Func.CompiledInv fs Devm.logs Devm.logs
      (.call returnWordSlot) :=
    returnWord_call_logs_inv returnLookup
  unfold maxMintAfterAssetCap
  compiled_inv

/-- Once `readTotalAssets` has supplied the booked WETH balance, the local
`maxMint` body stores it and returns the exact natural capacity. -/
theorem maxMint_postTotalAssets_body_effect
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    {image : Bytes} {assets supply : B256} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (supplyWindow : MemWordAt pre (supplyWord * 32).toNat supply)
    (stable : supply.toNat ≤ maxSupplyN)
    (stack : assets :: tail <<+ pre.stack)
    (returnLookup : fs[returnWordSlot]? = some returnWord)
    (capLookup :
      fs[maxMintAfterAssetCapSlot]? = some maxMintAfterAssetCap)
    (run : Func.RunCompiledTo fs sevm pre
      (mstoreAt assetsWord +++
        loadWord assetsWord +++ isMax +++
        (productOverTwoPow256 [pushB256 B256.max] stagedDenominator .down
            maxMintAfterAssetCapSlot <?>
          mulDiv [pushB256 B256.max] stagedDenominator stagedAssetFactor
            .capDown maxMintAfterAssetCapSlot)) (.ok post)) :
    maxMintN assets.toNat supply.toNat < wordModulusN ∧
      WordViewEffect
        (Nat.toB256 (maxMintN assets.toNat supply.toNat)) pre post := by
  have capStorage : Func.CompiledInv fs Devm.getStor Devm.getStor
      maxMintAfterAssetCap :=
    maxMintAfterAssetCap_storage_inv returnLookup
  have capCall :
      Func.CompiledInv fs Devm.getStor Devm.getStor
        (.call maxMintAfterAssetCapSlot) :=
    Func.CompiledInv.call capLookup capStorage
  have storageInv : Func.CompiledInv fs Devm.getStor Devm.getStor
      (mstoreAt assetsWord +++
        loadWord assetsWord +++ isMax +++
        (productOverTwoPow256 [pushB256 B256.max] stagedDenominator .down
            maxMintAfterAssetCapSlot <?>
          mulDiv [pushB256 B256.max] stagedDenominator stagedAssetFactor
            .capDown maxMintAfterAssetCapSlot)) := by
    compiled_inv
  have capLogs : Func.CompiledInv fs Devm.logs Devm.logs
      maxMintAfterAssetCap :=
    maxMintAfterAssetCap_logs_inv returnLookup
  have capLogsCall : Func.CompiledInv fs Devm.logs Devm.logs
      (.call maxMintAfterAssetCapSlot) :=
    Func.CompiledInv.call capLookup capLogs
  have logsInv : Func.CompiledInv fs Devm.logs Devm.logs
      (mstoreAt assetsWord +++
        loadWord assetsWord +++ isMax +++
        (productOverTwoPow256 [pushB256 B256.max] stagedDenominator .down
            maxMintAfterAssetCapSlot <?>
          mulDiv [pushB256 B256.max] stagedDenominator stagedAssetFactor
            .capDown maxMintAfterAssetCapSlot)) := by
    compiled_inv
  obtain ⟨arithmeticPre, assetsStoreRun, arithmeticRun⟩ :=
    runCompiledTo_prepend_inv run
  obtain ⟨arithmeticStack, arithmeticWf, arithmeticReads, -⟩ :=
    of_run_mstoreAt_image stack memoryWf memoryReads assetsStoreRun
  have arithmeticSupplyWindow :
      MemWordAt arithmeticPre (supplyWord * 32).toNat supply :=
    supplyWindow.acrossMstoreAt (Or.inl (by decide +kernel))
      assetsStoreRun
  let assetImage := capacityAssetsImage image assets
  change Mem.Reads arithmeticPre.memory assetImage at arithmeticReads
  have returned := maxMint_arithmetic_trace arithmeticWf arithmeticReads
    (capacityAssetsImage_assets image assets)
    (by
      rw [arithmeticSupplyWindow.slice_eq arithmeticReads,
        B256.toB256_toBytes])
    arithmeticSupplyWindow stable arithmeticStack returnLookup capLookup
    arithmeticRun
  have fits : maxMintN assets.toNat supply.toNat < wordModulusN :=
    (maxMintN_le_shareRoom assets.toNat supply.toNat).trans_lt
      (shareRoomN_lt_wordModulusN supply.toNat)
  exact ⟨fits, returned, storageInv run, logsInv run⟩

/-- Post-WETH local body effect for `maxDeposit`. -/
theorem maxDeposit_postTotalAssets_body_effect
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    {image : Bytes} {assets supply : B256} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (supplyWindow : MemWordAt pre (supplyWord * 32).toNat supply)
    (stable : supply.toNat ≤ maxSupplyN)
    (stack : assets :: tail <<+ pre.stack)
    (returnLookup : fs[returnWordSlot]? = some returnWord)
    (run : Func.RunCompiledTo fs sevm pre
      (mstoreAt assetsWord +++
        loadWord assetsWord +++ isMax +++
        (shiftedDiv shareRoomPlusOne stagedDenominator .capCeilPred
            returnWordSlot <?>
          mulDiv shareRoomPlusOne stagedAssetFactor stagedDenominator
            .capCeilPred returnWordSlot)) (.ok post)) :
    maxDepositN assets.toNat supply.toNat < wordModulusN ∧
      WordViewEffect
        (Nat.toB256 (maxDepositN assets.toNat supply.toNat)) pre post := by
  have returnStorageCall :
      Func.CompiledInv fs Devm.getStor Devm.getStor
        (.call returnWordSlot) :=
    returnWord_call_storage_inv returnLookup
  have storageInv : Func.CompiledInv fs Devm.getStor Devm.getStor
      (mstoreAt assetsWord +++
        loadWord assetsWord +++ isMax +++
        (shiftedDiv shareRoomPlusOne stagedDenominator .capCeilPred
            returnWordSlot <?>
          mulDiv shareRoomPlusOne stagedAssetFactor stagedDenominator
            .capCeilPred returnWordSlot)) := by
    compiled_inv
  have returnLogsCall : Func.CompiledInv fs Devm.logs Devm.logs
      (.call returnWordSlot) :=
    returnWord_call_logs_inv returnLookup
  have logsInv : Func.CompiledInv fs Devm.logs Devm.logs
      (mstoreAt assetsWord +++
        loadWord assetsWord +++ isMax +++
        (shiftedDiv shareRoomPlusOne stagedDenominator .capCeilPred
            returnWordSlot <?>
          mulDiv shareRoomPlusOne stagedAssetFactor stagedDenominator
            .capCeilPred returnWordSlot)) := by
    compiled_inv
  obtain ⟨arithmeticPre, assetsStoreRun, arithmeticRun⟩ :=
    runCompiledTo_prepend_inv run
  obtain ⟨arithmeticStack, arithmeticWf, arithmeticReads, -⟩ :=
    of_run_mstoreAt_image stack memoryWf memoryReads assetsStoreRun
  have arithmeticSupplyWindow :
      MemWordAt arithmeticPre (supplyWord * 32).toNat supply :=
    supplyWindow.acrossMstoreAt (Or.inl (by decide +kernel))
      assetsStoreRun
  let assetImage := capacityAssetsImage image assets
  change Mem.Reads arithmeticPre.memory assetImage at arithmeticReads
  have returned := maxDeposit_arithmetic_trace arithmeticWf arithmeticReads
    (capacityAssetsImage_assets image assets)
    (by
      rw [arithmeticSupplyWindow.slice_eq arithmeticReads,
        B256.toB256_toBytes])
    stable arithmeticStack returnLookup arithmeticRun
  have fits : maxDepositN assets.toNat supply.toNat < wordModulusN :=
    (maxDepositN_le_maxWord assets.toNat supply.toNat).trans_lt
      maxWordN_lt_wordModulusN
  exact ⟨fits, returned, storageInv run, logsInv run⟩

/-- Post-WETH local body effect for the saturated `maxWithdraw` result. -/
theorem maxWithdraw_postTotalAssets_body_effect
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    {image : Bytes} {amount assets supply : B256} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (amountWindow : MemWordAt pre (amountWord * 32).toNat amount)
    (supplyWindow : MemWordAt pre (supplyWord * 32).toNat supply)
    (stable : supply.toNat ≤ maxSupplyN)
    (stack : assets :: tail <<+ pre.stack)
    (returnLookup : fs[returnWordSlot]? = some returnWord)
    (run : Func.RunCompiledTo fs sevm pre
      (mstoreAt assetsWord +++
        loadWord assetsWord +++ isMax +++
        (shiftedDiv (loadWord amountWord) stagedDenominator .capDown
            returnWordSlot <?>
          mulDiv (loadWord amountWord) stagedAssetFactor stagedDenominator
            .capDown returnWordSlot)) (.ok post)) :
    min maxWordN (maxWithdrawN amount.toNat assets.toNat supply.toNat) <
        wordModulusN ∧
      WordViewEffect
        (Nat.toB256 (min maxWordN
          (maxWithdrawN amount.toNat assets.toNat supply.toNat))) pre post := by
  have returnStorageCall :
      Func.CompiledInv fs Devm.getStor Devm.getStor
        (.call returnWordSlot) :=
    returnWord_call_storage_inv returnLookup
  have storageInv : Func.CompiledInv fs Devm.getStor Devm.getStor
      (mstoreAt assetsWord +++
        loadWord assetsWord +++ isMax +++
        (shiftedDiv (loadWord amountWord) stagedDenominator .capDown
            returnWordSlot <?>
          mulDiv (loadWord amountWord) stagedAssetFactor stagedDenominator
            .capDown returnWordSlot)) := by
    compiled_inv
  have returnLogsCall : Func.CompiledInv fs Devm.logs Devm.logs
      (.call returnWordSlot) :=
    returnWord_call_logs_inv returnLookup
  have logsInv : Func.CompiledInv fs Devm.logs Devm.logs
      (mstoreAt assetsWord +++
        loadWord assetsWord +++ isMax +++
        (shiftedDiv (loadWord amountWord) stagedDenominator .capDown
            returnWordSlot <?>
          mulDiv (loadWord amountWord) stagedAssetFactor stagedDenominator
            .capDown returnWordSlot)) := by
    compiled_inv
  obtain ⟨arithmeticPre, assetsStoreRun, arithmeticRun⟩ :=
    runCompiledTo_prepend_inv run
  obtain ⟨arithmeticStack, arithmeticWf, arithmeticReads, -⟩ :=
    of_run_mstoreAt_image stack memoryWf memoryReads assetsStoreRun
  have arithmeticAmountWindow :
      MemWordAt arithmeticPre (amountWord * 32).toNat amount :=
    amountWindow.acrossMstoreAt (Or.inl (by decide +kernel))
      assetsStoreRun
  have arithmeticSupplyWindow :
      MemWordAt arithmeticPre (supplyWord * 32).toNat supply :=
    supplyWindow.acrossMstoreAt (Or.inl (by decide +kernel))
      assetsStoreRun
  let assetImage := capacityAssetsImage image assets
  change Mem.Reads arithmeticPre.memory assetImage at arithmeticReads
  have returned := maxWithdraw_arithmetic_trace arithmeticWf arithmeticReads
    (by
      rw [arithmeticAmountWindow.slice_eq arithmeticReads,
        B256.toB256_toBytes])
    (capacityAssetsImage_assets image assets)
    (by
      rw [arithmeticSupplyWindow.slice_eq arithmeticReads,
        B256.toB256_toBytes])
    stable arithmeticStack returnLookup arithmeticRun
  have fits : min maxWordN
      (maxWithdrawN amount.toNat assets.toNat supply.toNat) <
        wordModulusN :=
    (Nat.min_le_left maxWordN
      (maxWithdrawN amount.toNat assets.toNat supply.toNat)).trans_lt
      maxWordN_lt_wordModulusN
  exact ⟨fits, returned, storageInv run, logsInv run⟩

/-! ## Capacity-entry staging and domain routing -/

/-- Stage the exact share supply and expose a selected-word frame for every
disjoint pre-existing operation word. -/
theorem capacitySupplyStaging_trace
    {fs : List Func} {sevm : Sevm} {pre final : Devm}
    {body : Func} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (stack : tail <<+ pre.stack)
    (run : Func.RunCompiledTo fs sevm pre
      (pushSupplySlot +++ sload ::: mstoreAt supplyWord +++ body)
      (.ok final)) :
    ∃ supply bodyPre,
      supply = Devm.getStorVal pre sevm.currentTarget supplySlot ∧
      tail <<+ bodyPre.stack ∧
      MemWordAt bodyPre (supplyWord * 32).toNat supply ∧
      (∀ {offset : Nat} {w : B256},
        (offset + 32 ≤ (supplyWord * 32).toNat ∨
          (supplyWord * 32).toNat + 32 ≤ offset) →
        MemWordAt pre offset w → MemWordAt bodyPre offset w) ∧
      pre.state = bodyPre.state ∧
      pre.logs = bodyPre.logs ∧
      Func.RunCompiledTo fs sevm bodyPre body (.ok final) := by
  obtain ⟨sloadPre, slotRun, run⟩ := runCompiledTo_prepend_inv run
  simp only [pushSupplySlot] at slotRun
  rcases Line.of_run_cons slotRun with ⟨notPre, zeroRun, slotRun⟩
  rcases Line.of_run_cons slotRun with ⟨sloadPre', notRun, slotRun⟩
  cases slotRun
  have zeroPrefix : (0 : B256) :: tail <<+ notPre.stack :=
    prefix_of_push (of_run_pushB256 zeroRun) stack
  have slotPrefix : supplySlot :: tail <<+ sloadPre.stack := by
    have rawPrefix := prefix_of_not notRun zeroPrefix
    have notZero : ~~~(0 : B256) = B256.max := by decide +kernel
    unfold supplySlot
    rw [← notZero]
    exact rawPrefix
  have slotState : pre.state = sloadPre.state :=
    Line.of_inv Devm.state (by line_inv)
      (Line.Run.cons zeroRun (Line.Run.cons notRun Line.Run.nil))
  have slotMemory : pre.memory = sloadPre.memory :=
    Line.of_inv Devm.memory (by line_inv)
      (Line.Run.cons zeroRun (Line.Run.cons notRun Line.Run.nil))
  have slotLogs : pre.logs = sloadPre.logs :=
    Line.of_inv Devm.logs (by line_inv)
      (Line.Run.cons zeroRun (Line.Run.cons notRun Line.Run.nil))
  have sloadWf : Mem.Wf sloadPre.memory := by
    rw [← slotMemory]
    exact memoryWf

  obtain ⟨storePre, sloadRun, run⟩ := runCompiledTo_next_inv run
  have sloadSource := Ninst.Run.of_runCompiled sloadRun
  obtain ⟨supply, supplyPrefix, supplyEq⟩ :=
    prefix_of_sload sloadSource slotPrefix
  have sloadState : sloadPre.state = storePre.state :=
    of_run_sload_state sloadSource
  have sloadMemory : sloadPre.memory = storePre.memory :=
    Ninst.Hinv.inv (f := Devm.memory) sloadSource
  have sloadLogs : sloadPre.logs = storePre.logs :=
    of_run_sload_logs sloadSource
  have storeWf : Mem.Wf storePre.memory := by
    rw [← sloadMemory]
    exact sloadWf
  have storeImage : MemImage storePre storePre.memory.data.toList := by
    refine ⟨storeWf, ?_⟩
    intro index
    simp

  obtain ⟨bodyPre, storeRun, bodyRun⟩ :=
    runCompiledTo_prepend_inv run
  obtain ⟨bodyPrefix, storeMemory⟩ :=
    of_run_mstoreAt_val storeRun supplyPrefix
  have supplyWindow :
      MemWordAt bodyPre (supplyWord * 32).toNat supply :=
    MemWordAt.of_write storeImage storeMemory
  have storeState : storePre.state = bodyPre.state :=
    Line.of_inv Devm.state (by line_inv) storeRun
  have storeLogs : storePre.logs = bodyPre.logs :=
    Line.of_inv Devm.logs (by line_inv) storeRun
  have supplyAtEntry :
      supply = Devm.getStorVal pre sevm.currentTarget supplySlot := by
    rw [supplyEq]
    change
      (Devm.getStor sloadPre sevm.currentTarget).get supplySlot =
        (Devm.getStor pre sevm.currentTarget).get supplySlot
    rw [funext (getStor_eq_of_state_eq slotState)]
  have preserves : ∀ {offset : Nat} {w : B256},
      (offset + 32 ≤ (supplyWord * 32).toNat ∨
        (supplyWord * 32).toNat + 32 ≤ offset) →
      MemWordAt pre offset w → MemWordAt bodyPre offset w := by
    intro offset w miss window
    exact ((window.acrossLine (by line_inv)
      (Line.Run.cons zeroRun (Line.Run.cons notRun Line.Run.nil))).acrossNinst
        sloadSource).acrossMstoreAt miss storeRun
  exact ⟨supply, bodyPre, supplyAtEntry, bodyPrefix, supplyWindow,
    preserves, slotState.trans (sloadState.trans storeState),
    slotLogs.trans (sloadLogs.trans storeLogs), bodyRun⟩

/-- Stage the exact owner share balance selected by ABI argument zero. -/
theorem capacityAmountStaging_trace
    {fs : List Func} {sevm : Sevm} {pre final : Devm}
    {body : Func} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (stack : tail <<+ pre.stack)
    (run : Func.RunCompiledTo fs sevm pre
      (arg 0 +++ sload ::: mstoreAt amountWord +++ body) (.ok final)) :
    ∃ amount bodyPre,
      amount = Devm.getStorVal pre sevm.currentTarget
        (Sevm.argWord sevm 0) ∧
      tail <<+ bodyPre.stack ∧
      MemWordAt bodyPre (amountWord * 32).toNat amount ∧
      pre.state = bodyPre.state ∧
      pre.logs = bodyPre.logs ∧
      Func.RunCompiledTo fs sevm bodyPre body (.ok final) := by
  obtain ⟨sloadPre, argRun, run⟩ := runCompiledTo_prepend_inv run
  have argPrefix : Sevm.argWord sevm 0 :: tail <<+ sloadPre.stack :=
    prefix_of_arg stack argRun
  have argState : pre.state = sloadPre.state :=
    Line.of_inv Devm.state (by unfold Blanc.arg cdl; line_inv) argRun
  have argMemory : pre.memory = sloadPre.memory :=
    Line.of_inv Devm.memory (by unfold Blanc.arg cdl; line_inv) argRun
  have argLogs : pre.logs = sloadPre.logs :=
    Line.of_inv Devm.logs (by unfold Blanc.arg cdl; line_inv) argRun
  have sloadWf : Mem.Wf sloadPre.memory := by
    rw [← argMemory]
    exact memoryWf
  obtain ⟨storePre, sloadRun, run⟩ := runCompiledTo_next_inv run
  have sloadSource := Ninst.Run.of_runCompiled sloadRun
  obtain ⟨amount, amountPrefix, amountEq⟩ :=
    prefix_of_sload sloadSource argPrefix
  have sloadState : sloadPre.state = storePre.state :=
    of_run_sload_state sloadSource
  have sloadMemory : sloadPre.memory = storePre.memory :=
    Ninst.Hinv.inv (f := Devm.memory) sloadSource
  have sloadLogs : sloadPre.logs = storePre.logs :=
    of_run_sload_logs sloadSource
  have storeWf : Mem.Wf storePre.memory := by
    rw [← sloadMemory]
    exact sloadWf
  have storeImage : MemImage storePre storePre.memory.data.toList := by
    refine ⟨storeWf, ?_⟩
    intro index
    simp
  obtain ⟨bodyPre, storeRun, bodyRun⟩ :=
    runCompiledTo_prepend_inv run
  obtain ⟨bodyPrefix, storeMemory⟩ :=
    of_run_mstoreAt_val storeRun amountPrefix
  have amountWindow :
      MemWordAt bodyPre (amountWord * 32).toNat amount :=
    MemWordAt.of_write storeImage storeMemory
  have storeState : storePre.state = bodyPre.state :=
    Line.of_inv Devm.state (by line_inv) storeRun
  have storeLogs : storePre.logs = bodyPre.logs :=
    Line.of_inv Devm.logs (by line_inv) storeRun
  have amountAtEntry : amount = Devm.getStorVal pre sevm.currentTarget
      (Sevm.argWord sevm 0) := by
    rw [amountEq]
    change
      (Devm.getStor sloadPre sevm.currentTarget).get
          (Sevm.argWord sevm 0) =
        (Devm.getStor pre sevm.currentTarget).get
          (Sevm.argWord sevm 0)
    rw [funext (getStor_eq_of_state_eq argState)]
  exact ⟨amount, bodyPre, amountAtEntry, bodyPrefix, amountWindow,
    argState.trans (sloadState.trans storeState),
    argLogs.trans (sloadLogs.trans storeLogs), bodyRun⟩

/-- Route the shared capacity domain check.  An unstable supply returns zero;
otherwise the continuation receives the same operation-word windows and an
exact stable-supply proof. -/
theorem stableCapacityBranch_trace
    {fs : List Func} {sevm : Sevm} {pre final : Devm}
    {supply : B256} {body : Func} {tail : Stack}
    (supplyWindow : MemWordAt pre (supplyWord * 32).toNat supply)
    (stack : tail <<+ pre.stack)
    (run : Func.RunCompiledTo fs sevm pre
      (loadWord supplyWord +++ pushB256 maxSupply ::: lt :::
        (returnConstant 0 <?> body)) (.ok final)) :
    (maxSupplyN < supply.toNat ∧ WordViewEffect 0 pre final) ∨
      (∃ bodyPre,
        supply.toNat ≤ maxSupplyN ∧
        tail <<+ bodyPre.stack ∧
        MemWordAt bodyPre (supplyWord * 32).toNat supply ∧
        (∀ {offset : Nat} {w : B256}, MemWordAt pre offset w →
          MemWordAt bodyPre offset w) ∧
        pre.state = bodyPre.state ∧
        pre.logs = bodyPre.logs ∧
        Func.RunCompiledTo fs sevm bodyPre body (.ok final)) := by
  obtain ⟨maxPre, supplyRun, run⟩ := runCompiledTo_prepend_inv run
  have supplyPrefix := prefix_of_loadWord_window supplyWindow stack supplyRun
  have supplyWindow' := supplyWindow.acrossLoadWord supplyRun
  have supplyState : pre.state = maxPre.state :=
    Line.of_inv Devm.state (by unfold loadWord; line_inv) supplyRun
  have supplyLogs : pre.logs = maxPre.logs :=
    of_run_loadWordAt_logs supplyRun
  obtain ⟨testPre, maxRun, run⟩ := runCompiledTo_next_inv run
  have maxSource := Ninst.Run.of_runCompiled maxRun
  have maxPrefix := prefix_of_push (of_run_pushB256 maxSource) supplyPrefix
  have supplyWindow'' := supplyWindow'.acrossNinst maxSource
  obtain ⟨branchPre, testRun, branchRun⟩ := runCompiledTo_next_inv run
  have testSource := Ninst.Run.of_runCompiled testRun
  have testPrefix := prefix_of_lt testSource maxPrefix
  have supplyWindow''' := supplyWindow''.acrossNinst testSource
  have suffixState : maxPre.state = branchPre.state :=
    (Ninst.Hinv.inv (f := Devm.state) maxSource).trans
      (Ninst.Hinv.inv (f := Devm.state) testSource)
  have suffixLogs : maxPre.logs = branchPre.logs :=
    (Ninst.Hinv.inv (f := Devm.logs) maxSource).trans
      (Ninst.Hinv.inv (f := Devm.logs) testSource)
  by_cases unstable : maxSupply < supply
  · have onePrefix : (1 : B256) :: tail <<+ branchPre.stack := by
      simpa [B256.ltCheck, unstable] using testPrefix
    obtain ⟨zeroPre, branchWord, branchWordNe, zeroPop, zeroRun,
        zeroPrefix⟩ :=
      Func.RunCompiledTo.succ_branch_of_prefix
        (by decide : (1 : B256) ≠ 0) onePrefix branchRun
    have effect := returnConstant_effect zeroRun
    have unstableNat : maxSupplyN < supply.toNat := by
      rw [B256.lt_iff_toNat_lt_toNat, maxSupply_toNat] at unstable
      exact unstable
    exact Or.inl ⟨unstableNat,
      lift_word_view
        (supplyState.trans (suffixState.trans zeroPop.state))
        (supplyLogs.trans (suffixLogs.trans zeroPop.logs)) effect⟩
  · have zeroPrefix : (0 : B256) :: tail <<+ branchPre.stack := by
      simpa [B256.ltCheck, unstable] using testPrefix
    obtain ⟨bodyPre, bodyPop, bodyRun, bodyPrefix⟩ :=
      Func.RunCompiledTo.zero_branch_of_prefix zeroPrefix branchRun
    have stableWord : supply ≤ maxSupply := B256.not_lt.mp unstable
    have stable : supply.toNat ≤ maxSupplyN := by
      rw [B256.le_iff_toNat_le_toNat, maxSupply_toNat] at stableWord
      exact stableWord
    have bodySupplyWindow :
        MemWordAt bodyPre (supplyWord * 32).toNat supply :=
      MemWordAt.of_memory_eq bodyPop.memory.symm supplyWindow'''
    have preserves : ∀ {offset : Nat} {w : B256},
        MemWordAt pre offset w → MemWordAt bodyPre offset w := by
      intro offset w window
      exact MemWordAt.of_memory_eq bodyPop.memory.symm
        (((window.acrossLoadWord supplyRun).acrossNinst maxSource).acrossNinst
          testSource)
    exact Or.inr ⟨bodyPre, stable, bodyPrefix, bodySupplyWindow,
      preserves, supplyState.trans (suffixState.trans bodyPop.state),
      supplyLogs.trans (suffixLogs.trans bodyPop.logs), bodyRun⟩

/-- Route the zero-address policy shared by `maxMint` and `maxDeposit` after
the outer canonical-address guard. -/
theorem zeroArgCapacityBranch_trace
    {fs : List Func} {sevm : Sevm} {pre final : Devm}
    {body : Func} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (stack : tail <<+ pre.stack)
    (run : Func.RunCompiledTo fs sevm pre
      (arg 0 +++ iszero ::: (returnConstant 0 <?> body)) (.ok final)) :
    (Sevm.argWord sevm 0 = 0 ∧ WordViewEffect 0 pre final) ∨
      (Sevm.argWord sevm 0 ≠ 0 ∧
        ∃ bodyPre,
          tail <<+ bodyPre.stack ∧
          Mem.Wf bodyPre.memory ∧
          pre.state = bodyPre.state ∧
          pre.logs = bodyPre.logs ∧
          Func.RunCompiledTo fs sevm bodyPre body (.ok final)) := by
  obtain ⟨testPre, argRun, run⟩ := runCompiledTo_prepend_inv run
  have argPrefix : Sevm.argWord sevm 0 :: tail <<+ testPre.stack :=
    prefix_of_arg stack argRun
  have argState : pre.state = testPre.state :=
    Line.of_inv Devm.state (by unfold Blanc.arg cdl; line_inv) argRun
  have argMemory : pre.memory = testPre.memory :=
    Line.of_inv Devm.memory (by unfold Blanc.arg cdl; line_inv) argRun
  have argLogs : pre.logs = testPre.logs :=
    Line.of_inv Devm.logs (by unfold Blanc.arg cdl; line_inv) argRun
  obtain ⟨branchPre, zeroRun, branchRun⟩ := runCompiledTo_next_inv run
  have zeroSource := Ninst.Run.of_runCompiled zeroRun
  have testPrefix := prefix_of_iszero zeroSource argPrefix
  have zeroState : testPre.state = branchPre.state :=
    Ninst.Hinv.inv (f := Devm.state) zeroSource
  have zeroMemory : testPre.memory = branchPre.memory :=
    Ninst.Hinv.inv (f := Devm.memory) zeroSource
  have zeroLogs : testPre.logs = branchPre.logs :=
    Ninst.Hinv.inv (f := Devm.logs) zeroSource
  by_cases argZero : Sevm.argWord sevm 0 = 0
  · have onePrefix : (1 : B256) :: tail <<+ branchPre.stack := by
      simpa [B256.eqCheck, argZero] using testPrefix
    obtain ⟨zeroPre, branchWord, branchWordNe, zeroPop, zeroRun,
        zeroPrefix⟩ :=
      Func.RunCompiledTo.succ_branch_of_prefix
        (by decide : (1 : B256) ≠ 0) onePrefix branchRun
    have effect := returnConstant_effect zeroRun
    exact Or.inl ⟨argZero,
      lift_word_view
        (argState.trans (zeroState.trans zeroPop.state))
        (argLogs.trans (zeroLogs.trans zeroPop.logs)) effect⟩
  · have zeroPrefix : (0 : B256) :: tail <<+ branchPre.stack := by
      simpa [B256.eqCheck, argZero] using testPrefix
    obtain ⟨bodyPre, bodyPop, bodyRun, bodyPrefix⟩ :=
      Func.RunCompiledTo.zero_branch_of_prefix zeroPrefix branchRun
    have bodyWf : Mem.Wf bodyPre.memory := by
      rw [← bodyPop.memory, ← zeroMemory, ← argMemory]
      exact memoryWf
    exact Or.inr ⟨argZero, bodyPre, bodyPrefix, bodyWf,
      argState.trans (zeroState.trans bodyPop.state),
      argLogs.trans (zeroLogs.trans bodyPop.logs), bodyRun⟩

end ProrataWethVault

end Blanc
