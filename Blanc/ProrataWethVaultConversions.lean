-- ProrataWethVaultConversions.lean : compiled ERC-4626 conversion seams.

import Blanc.ProrataWethVaultArithmeticExec
import Blanc.ProrataWethVaultViews
import Blanc.CompiledFixedInvariance

namespace Blanc

open Jaune
open Jaune.Ninst Ninst
open scoped LogOutputHinv

namespace ProrataWethVault

/-!
# Compiled conversion seams

The public conversions, previews, and mutable quote paths all enter the same
compiled shape after `totalAssets`: stage the booked asset word, read and
stage total supply, discharge the stable-supply guard, select the exact
`2^256` asset arm, and invoke one of the full-width arithmetic helpers.

This module owns that shared family-local walk.  The configured WETH crossing
remains downstream in the composition stratum.
-/

/-! ## Reusable producer and guard composition -/

/-- Select the exact-max or ordinary continuation after any proved word
producer followed by the shared `isMax` line.  Both arms retain the producer's
proof-carrying memory image and surrounding stack. -/
theorem ProducesWord.isMax_arm_trace
    {R : List Func → Sevm → Devm → Func → Devm → Prop} [Func.WalkInv R]
    {fs : List Func} {sevm : Sevm} {pre final : Devm}
    {line : Line} {image : Bytes} {value : B256}
    {maxBody ordinaryBody : Func} {tail : Stack}
    (produces : ProducesWord sevm line image value)
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (stack : tail <<+ pre.stack)
    (run : R fs sevm pre
      (line +++ isMax +++ (maxBody <?> ordinaryBody)) final) :
    (value = B256.max ∧
      ∃ bodyPre,
        tail <<+ bodyPre.stack ∧
        Mem.Wf bodyPre.memory ∧
        Mem.Reads bodyPre.memory image ∧
        Devm.QuietFrame pre bodyPre ∧
        R fs sevm bodyPre maxBody final) ∨
    (value ≠ B256.max ∧
      ∃ bodyPre,
        tail <<+ bodyPre.stack ∧
        Mem.Wf bodyPre.memory ∧
        Mem.Reads bodyPre.memory image ∧
        Devm.QuietFrame pre bodyPre ∧
        R fs sevm bodyPre ordinaryBody final) := by
  obtain ⟨valuePre, valueRun, run⟩ := Func.WalkInv.prepend run
  obtain ⟨valuePrefix, valueWf, valueReads, valueState⟩ :=
    produces memoryWf memoryReads stack valueRun
  obtain ⟨testPre, testRun, branchRun⟩ :=
    Func.WalkInv.prepend run
  simp only [isMax] at testRun
  rcases Line.of_run_cons testRun with
    ⟨notPre, notRun, testRun⟩
  rcases Line.of_run_cons testRun with
    ⟨testPre', zeroRun, testRun⟩
  cases testRun
  have notPrefix := prefix_of_not notRun valuePrefix
  have testPrefix := prefix_of_iszero zeroRun notPrefix
  have testMemory : valuePre.memory = testPre.memory :=
    Line.of_inv Devm.memory (by line_inv)
      (Line.Run.cons notRun (Line.Run.cons zeroRun Line.Run.nil))
  have testWf : Mem.Wf testPre.memory := by
    rw [← testMemory]
    exact valueWf
  have testReads : Mem.Reads testPre.memory image := by
    rw [← testMemory]
    exact valueReads
  have testState : Devm.QuietFrame pre testPre :=
    valueState.trans
      (Devm.QuietFrame.ofLine (by line_inv) (by line_inv)
        (Line.Run.cons notRun (Line.Run.cons zeroRun Line.Run.nil)))
  by_cases valueMax : value = B256.max
  · have onePrefix : (1 : B256) :: tail <<+ testPre.stack := by
      simpa [valueMax, B256.not_max, B256.eqCheck] using testPrefix
    obtain ⟨bodyPre, bodyPop, bodyRun, bodyPrefix⟩ :=
      Func.WalkInv.succ_branch_of_prefix
        (by decide : (1 : B256) ≠ 0) onePrefix branchRun
    have bodyWf : Mem.Wf bodyPre.memory := by
      rw [← bodyPop.memory]
      exact testWf
    have bodyReads : Mem.Reads bodyPre.memory image := by
      rw [← bodyPop.memory]
      exact testReads
    exact Or.inl ⟨valueMax, bodyPre, bodyPrefix, bodyWf, bodyReads,
      testState.trans (Devm.QuietFrame.ofPopBurn bodyPop), bodyRun⟩
  · have notNonzero : (~~~ value) ≠ 0 := by
      intro notZero
      exact valueMax (B256.eq_max_of_not_eq_zero notZero)
    have zeroPrefix : (0 : B256) :: tail <<+ testPre.stack := by
      simpa [B256.eqCheck, notNonzero] using testPrefix
    obtain ⟨bodyPre, bodyPop, bodyRun, bodyPrefix⟩ :=
      Func.WalkInv.zero_branch_of_prefix zeroPrefix branchRun
    have bodyWf : Mem.Wf bodyPre.memory := by
      rw [← bodyPop.memory]
      exact testWf
    have bodyReads : Mem.Reads bodyPre.memory image := by
      rw [← bodyPop.memory]
      exact testReads
    exact Or.inr ⟨valueMax, bodyPre, bodyPrefix, bodyWf, bodyReads,
      testState.trans (Devm.QuietFrame.ofPopBurn bodyPop), bodyRun⟩

/-- A successful stable-supply guard proves the staged word is within the
declared supply cap and exposes the guarded body without changing the
proof-carrying memory image, surrounding stack, or persistent state. -/
theorem guardStableSupply_trace
    {fs : List Func} {sevm : Sevm} {pre final : Devm}
    {image : Bytes} {supply : B256} {body : Func} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (supplyAt : Bytes.toB256
      (image.sliceD (supplyWord * 32).toNat 32 0) = supply)
    (stack : tail <<+ pre.stack)
    (run : Func.RunCompiledTo fs sevm pre
      (guardStableSupply body) (.ok final)) :
    ∃ bodyPre,
      supply.toNat ≤ maxSupplyN ∧
      tail <<+ bodyPre.stack ∧
      Mem.Wf bodyPre.memory ∧
      Mem.Reads bodyPre.memory image ∧
      pre.state = bodyPre.state ∧
      pre.logs = bodyPre.logs ∧
      Func.RunCompiledTo fs sevm bodyPre body (.ok final) := by
  unfold guardStableSupply at run
  obtain ⟨supplyPre, supplyRun, run⟩ :=
    runCompiledTo_prepend_inv run
  obtain ⟨supplyPrefix, supplyWf, supplyReads, supplyState⟩ :=
    of_run_loadWordAt_image stack memoryWf memoryReads supplyAt supplyRun
  obtain ⟨maxPre, maxRun, run⟩ := runCompiledTo_next_inv run
  have maxSource := Ninst.Run.of_runCompiled maxRun
  have maxPrefix := prefix_of_push (of_run_pushB256 maxSource) supplyPrefix
  obtain ⟨testPre, testRun, branchRun⟩ := runCompiledTo_next_inv run
  have testSource := Ninst.Run.of_runCompiled testRun
  have testPrefix := prefix_of_lt testSource maxPrefix
  have suffixState : supplyPre.state = testPre.state :=
    (Ninst.Hinv.inv (f := Devm.state) maxSource).trans
      (Ninst.Hinv.inv (f := Devm.state) testSource)
  have suffixMemory : supplyPre.memory = testPre.memory :=
    (Ninst.Hinv.inv (f := Devm.memory) maxSource).trans
      (Ninst.Hinv.inv (f := Devm.memory) testSource)
  have suffixLogs : supplyPre.logs = testPre.logs :=
    (Ninst.Hinv.inv (f := Devm.logs) maxSource).trans
      (Ninst.Hinv.inv (f := Devm.logs) testSource)
  have entryLogs : pre.logs = supplyPre.logs := by
    refine Line.of_inv Devm.logs ?_ supplyRun
    unfold ProrataWethVault.loadWord
    line_inv
  have testWf : Mem.Wf testPre.memory := by
    rw [← suffixMemory]
    exact supplyWf
  have testReads : Mem.Reads testPre.memory image := by
    rw [← suffixMemory]
    exact supplyReads
  by_cases overflow : maxSupply < supply
  · have onePrefix : (1 : B256) :: tail <<+ testPre.stack := by
      simpa [B256.ltCheck, overflow] using testPrefix
    obtain ⟨revertPre, branchWord, branchWordNe, revertPop, revertRun,
        revertPrefix⟩ :=
      Func.RunCompiledTo.succ_branch_of_prefix
        (by decide : (1 : B256) ≠ 0) onePrefix branchRun
    obtain ⟨revertPost, impossible, -⟩ :=
      runCompiledTo_revert_inv revertRun
    cases impossible
  · have zeroPrefix : (0 : B256) :: tail <<+ testPre.stack := by
      simpa [B256.ltCheck, overflow] using testPrefix
    obtain ⟨bodyPre, bodyPop, bodyRun, bodyPrefix⟩ :=
      Func.RunCompiledTo.zero_branch_of_prefix zeroPrefix branchRun
    have stableWord : supply ≤ maxSupply := B256.not_lt.mp overflow
    have stable : supply.toNat ≤ maxSupplyN := by
      rw [B256.le_iff_toNat_le_toNat, maxSupply_toNat] at stableWord
      exact stableWord
    have bodyWf : Mem.Wf bodyPre.memory := by
      rw [← bodyPop.memory]
      exact testWf
    have bodyReads : Mem.Reads bodyPre.memory image := by
      rw [← bodyPop.memory]
      exact testReads
    exact ⟨bodyPre, stable, bodyPrefix, bodyWf, bodyReads,
      supplyState.trans (suffixState.trans bodyPop.state),
      entryLogs.trans (suffixLogs.trans bodyPop.logs), bodyRun⟩

/-! ## Shared post-`totalAssets` staging -/

/-- Memory image after staging the booked asset balance and share supply. -/
def conversionStagingImage
    (image : Bytes) (assets supply : B256) : Bytes :=
  Bytes.writeAt
    (Bytes.writeAt image (assetsWord * 32).toNat assets.toBytes)
    (supplyWord * 32).toNat supply.toBytes

theorem conversionStagingImage_assets
    (image : Bytes) (assets supply : B256) :
    Bytes.toB256
        ((conversionStagingImage image assets supply).sliceD
          (assetsWord * 32).toNat 32 0) = assets := by
  unfold conversionStagingImage
  rw [Bytes.readWord_writeAt_of_disjoint]
  · exact Bytes.readWord_writeAt_self _ _ _
  · right
    decide +kernel

theorem conversionStagingImage_supply
    (image : Bytes) (assets supply : B256) :
    Bytes.toB256
        ((conversionStagingImage image assets supply).sliceD
          (supplyWord * 32).toNat 32 0) = supply := by
  unfold conversionStagingImage
  exact Bytes.readWord_writeAt_self _ _ _

/-- Stage the booked asset word supplied by `readTotalAssets`, read and stage
the exact share supply, and discharge the common stable-supply guard. -/
theorem conversionStaging_trace
    {fs : List Func} {sevm : Sevm} {pre final : Devm}
    {image : Bytes} {assets : B256} {body : Func} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (stack : assets :: tail <<+ pre.stack)
    (run : Func.RunCompiledTo fs sevm pre
      (mstoreAt assetsWord +++
        pushSupplySlot +++ sload ::: mstoreAt supplyWord +++
        guardStableSupply body) (.ok final)) :
    ∃ supply bodyPre,
      supply = Devm.getStorVal pre sevm.currentTarget supplySlot ∧
      supply.toNat ≤ maxSupplyN ∧
      tail <<+ bodyPre.stack ∧
      Mem.Wf bodyPre.memory ∧
      Mem.Reads bodyPre.memory
        (conversionStagingImage image assets supply) ∧
      Devm.getStor pre = Devm.getStor bodyPre ∧
      Devm.getCode pre = Devm.getCode bodyPre ∧
      pre.logs = bodyPre.logs ∧
      Func.RunCompiledTo fs sevm bodyPre body (.ok final) := by
  obtain ⟨slotPre, assetsStoreRun, run⟩ :=
    runCompiledTo_prepend_inv run
  obtain ⟨slotPrefix, slotWf, slotReads, assetsState⟩ :=
    of_run_mstoreAt_image stack memoryWf memoryReads assetsStoreRun
  let image1 := Bytes.writeAt image (assetsWord * 32).toNat assets.toBytes
  change Mem.Reads slotPre.memory image1 at slotReads

  obtain ⟨sloadPre, slotRun, run⟩ :=
    runCompiledTo_prepend_inv run
  simp only [pushSupplySlot] at slotRun
  rcases Line.of_run_cons slotRun with
    ⟨notPre, zeroRun, slotRun⟩
  rcases Line.of_run_cons slotRun with
    ⟨sloadPre', notRun, slotRun⟩
  cases slotRun
  have zeroPrefix : (0 : B256) :: tail <<+ notPre.stack :=
    prefix_of_push (of_run_pushB256 zeroRun) slotPrefix
  have supplySlotPrefix : supplySlot :: tail <<+ sloadPre.stack := by
    have rawPrefix := prefix_of_not notRun zeroPrefix
    have notZero : ~~~(0 : B256) = B256.max := by decide +kernel
    unfold supplySlot
    rw [← notZero]
    exact rawPrefix
  have slotState : slotPre.state = sloadPre.state :=
    Line.of_inv Devm.state (by line_inv)
      (Line.Run.cons zeroRun (Line.Run.cons notRun Line.Run.nil))
  have slotMemory : slotPre.memory = sloadPre.memory :=
    Line.of_inv Devm.memory (by line_inv)
      (Line.Run.cons zeroRun (Line.Run.cons notRun Line.Run.nil))
  have sloadWf : Mem.Wf sloadPre.memory := by
    rw [← slotMemory]
    exact slotWf
  have sloadReads : Mem.Reads sloadPre.memory image1 := by
    rw [← slotMemory]
    exact slotReads

  obtain ⟨supplyStorePre, sloadRun, run⟩ :=
    runCompiledTo_next_inv run
  have sloadSource := Ninst.Run.of_runCompiled sloadRun
  obtain ⟨supply, supplyPrefix, supplyEq⟩ :=
    prefix_of_sload sloadSource supplySlotPrefix
  have sloadStorage :
      Devm.getStor sloadPre = Devm.getStor supplyStorePre :=
    Ninst.Hinv.inv (f := Devm.getStor) sloadSource
  have sloadMemory : sloadPre.memory = supplyStorePre.memory :=
    Ninst.Hinv.inv (f := Devm.memory) sloadSource
  have supplyStoreWf : Mem.Wf supplyStorePre.memory := by
    rw [← sloadMemory]
    exact sloadWf
  have supplyStoreReads : Mem.Reads supplyStorePre.memory image1 := by
    rw [← sloadMemory]
    exact sloadReads

  obtain ⟨guardPre, supplyStoreRun, guardRun⟩ :=
    runCompiledTo_prepend_inv run
  obtain ⟨guardPrefix, guardWf, guardReads, supplyStoreState⟩ :=
    of_run_mstoreAt_image supplyPrefix supplyStoreWf supplyStoreReads
      supplyStoreRun
  let image2 := Bytes.writeAt image1
    (supplyWord * 32).toNat supply.toBytes
  change Mem.Reads guardPre.memory image2 at guardReads
  have supplyAt : Bytes.toB256
      (image2.sliceD (supplyWord * 32).toNat 32 0) = supply := by
    unfold image2
    exact Bytes.readWord_writeAt_self _ _ _
  obtain ⟨bodyPre, stable, bodyPrefix, bodyWf, bodyReads,
      guardState, guardLogs, bodyRun⟩ :=
    guardStableSupply_trace guardWf guardReads supplyAt guardPrefix guardRun

  have supplyAtEntry :
      supply = Devm.getStorVal pre sevm.currentTarget supplySlot := by
    rw [supplyEq]
    change
      (Devm.getStor sloadPre sevm.currentTarget).get supplySlot =
        (Devm.getStor pre sevm.currentTarget).get supplySlot
    have storage : Devm.getStor pre = Devm.getStor sloadPre :=
      funext (getStor_eq_of_state_eq (assetsState.trans slotState))
    rw [storage]
  have sloadCode : Devm.getCode sloadPre = Devm.getCode supplyStorePre :=
    Ninst.Hinv.inv (f := Devm.getCode) sloadSource
  have sloadLogs : sloadPre.logs = supplyStorePre.logs :=
    Ninst.Hinv.inv (f := Devm.logs) sloadSource
  have assetsLogs : pre.logs = slotPre.logs := by
    refine Line.of_inv Devm.logs ?_ assetsStoreRun
    unfold mstoreAt
    line_inv
  have slotLogs : slotPre.logs = sloadPre.logs :=
    Line.of_inv Devm.logs (by line_inv)
      (Line.Run.cons zeroRun (Line.Run.cons notRun Line.Run.nil))
  have supplyStoreLogs : supplyStorePre.logs = guardPre.logs := by
    refine Line.of_inv Devm.logs ?_ supplyStoreRun
    unfold mstoreAt
    line_inv
  refine ⟨supply, bodyPre, supplyAtEntry, stable, bodyPrefix, bodyWf, ?_,
    ?_, ?_, ?_, bodyRun⟩
  · simpa [conversionStagingImage, image2, image1] using bodyReads
  · exact (funext (getStor_eq_of_state_eq assetsState)).trans
      ((funext (getStor_eq_of_state_eq slotState)).trans
        (sloadStorage.trans
          ((funext (getStor_eq_of_state_eq supplyStoreState)).trans
            (funext (getStor_eq_of_state_eq guardState)))))
  · exact (funext (getCode_eq_of_state_eq assetsState)).trans
      ((funext (getCode_eq_of_state_eq slotState)).trans
        (sloadCode.trans
          ((funext (getCode_eq_of_state_eq supplyStoreState)).trans
            (funext (getCode_eq_of_state_eq guardState)))))
  · exact assetsLogs.trans
      (slotLogs.trans (sloadLogs.trans (supplyStoreLogs.trans guardLogs)))

/-! ## Exact ABI-word return -/

/-- The vault's shared return continuation ABI-encodes the known stack head. -/
theorem returnWord_trace
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    {word : B256} {tail : Stack}
    (stack : word :: tail <<+ pre.stack)
    (run : Func.RunCompiledTo fs sevm pre returnWord (.ok post)) :
    ReturnsWord word post := by
  have sourceRun : Func.Run fs sevm pre returnWord post :=
    Func.Run.of_runCompiled (Func.RunCompiled.of_runCompiledTo_ok run)
  simpa only [returnWord] using
    (returnsWord_of_storeReturn stack (by
      simpa only [returnWord] using sourceRun)).1

/-! ## Exact conversion arithmetic -/

/-- The stable-supply guard makes the staged denominator an exact natural
word, rather than merely its modular embedding. -/
theorem stagedDenominator_toNat
    {supply : B256} (stable : supply.toNat ≤ maxSupplyN) :
    (Nat.toB256 (denominatorN supply.toNat)).toNat =
      denominatorN supply.toNat := by
  apply B256.toNat_toB256_of_lt
  exact (denominatorN_le_maxWord stable).trans_lt
    maxWordN_lt_wordModulusN

/-- Away from the exact all-ones case selected by `isMax`, the staged asset
factor is an exact natural word. -/
theorem stagedAssetFactor_toNat_of_ne_max
    {assets : B256} (notMax : assets ≠ B256.max) :
    (Nat.toB256 (assetFactorN assets.toNat)).toNat =
      assetFactorN assets.toNat := by
  have assetsLtModulus : assets.toNat < wordModulusN := by
    simpa only [wordModulusN] using B256.toNat_lt assets
  have assetsLeMax : assets.toNat ≤ maxWordN := by
    unfold maxWordN
    omega
  have assetsNeMax : assets.toNat ≠ maxWordN := by
    intro assetsEq
    apply notMax
    apply B256.toNat_inj
    rw [assetsEq, maxWord_toNat]
  have assetsLtMax : assets.toNat < maxWordN :=
    lt_of_le_of_ne assetsLeMax assetsNeMax
  apply B256.toNat_toB256_of_lt
  exact (Nat.succ_le_of_lt assetsLtMax).trans_lt
    maxWordN_lt_wordModulusN

/-! The arithmetic scratch region lies strictly below the two conversion
staging words.  These producer adapters make that memory separation reusable
by every floor and ceiling endpoint. -/

theorem ProducesWord.stagedDenominator_after_productScratch
    {sevm : Sevm} {image : Bytes} {supply x : B256}
    (supplyAt : Bytes.toB256
      (image.sliceD (supplyWord * 32).toNat 32 0) = supply) :
    ProducesWord sevm ProrataWethVault.stagedDenominator
      (Bytes.writeAt image (xWord * 32).toNat x.toBytes)
      (Nat.toB256 (denominatorN supply.toNat)) := by
  apply ProducesWord.stagedDenominator
  rw [Bytes.readWord_writeAt_of_disjoint]
  · exact supplyAt
  · right
    decide +kernel

theorem ProducesWord.stagedDenominator_after_shiftedScratch
    {sevm : Sevm} {image : Bytes} {supply high : B256}
    (supplyAt : Bytes.toB256
      (image.sliceD (supplyWord * 32).toNat 32 0) = supply) :
    ProducesWord sevm ProrataWethVault.stagedDenominator
      (Bytes.writeAt
        (Bytes.writeAt image (highWord * 32).toNat high.toBytes)
        (lowWord * 32).toNat (0 : B256).toBytes)
      (Nat.toB256 (denominatorN supply.toNat)) := by
  apply ProducesWord.stagedDenominator
  rw [Bytes.readWord_writeAt_of_disjoint]
  · rw [Bytes.readWord_writeAt_of_disjoint]
    · exact supplyAt
    · right
      decide +kernel
  · right
    decide +kernel

theorem ProducesWord.stagedDenominator_after_mulDivScratch
    {sevm : Sevm} {image : Bytes} {supply denominator x : B256}
    (supplyAt : Bytes.toB256
      (image.sliceD (supplyWord * 32).toNat 32 0) = supply) :
    ProducesWord sevm ProrataWethVault.stagedDenominator
      (Bytes.writeAt
        (Bytes.writeAt image (denominatorWord * 32).toNat
          denominator.toBytes)
        (xWord * 32).toNat x.toBytes)
      (Nat.toB256 (denominatorN supply.toNat)) := by
  apply ProducesWord.stagedDenominator
  rw [Bytes.readWord_writeAt_of_disjoint]
  · rw [Bytes.readWord_writeAt_of_disjoint]
    · exact supplyAt
    · right
      decide +kernel
  · right
    decide +kernel

theorem ProducesWord.stagedAssetFactor_after_mulDivScratch
    {sevm : Sevm} {image : Bytes} {assets denominator x : B256}
    (assetsAt : Bytes.toB256
      (image.sliceD (assetsWord * 32).toNat 32 0) = assets) :
    ProducesWord sevm ProrataWethVault.stagedAssetFactor
      (Bytes.writeAt
        (Bytes.writeAt image (denominatorWord * 32).toNat
          denominator.toBytes)
        (xWord * 32).toNat x.toBytes)
      (Nat.toB256 (assetFactorN assets.toNat)) := by
  apply ProducesWord.stagedAssetFactor
  rw [Bytes.readWord_writeAt_of_disjoint]
  · rw [Bytes.readWord_writeAt_of_disjoint]
    · exact assetsAt
    · right
      decide +kernel
  · right
    decide +kernel

/-- The conversion-to-shares arithmetic suffix returns exactly the G1
full-width natural formula in either the exact-`2^256` or ordinary arm. -/
theorem convertToShares_arithmetic_trace
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
    (lookup : fs[returnWordSlot]? = some returnWord)
    (run : Func.RunCompiledTo fs sevm pre
      (loadWord assetsWord +++ isMax +++
        (productOverTwoPow256 (arg 0) stagedDenominator .down
            returnWordSlot <?>
          mulDiv (arg 0) stagedDenominator stagedAssetFactor .down
            returnWordSlot)) (.ok final)) :
    convertToSharesN
        (Sevm.argWord sevm 0).toNat assets.toNat supply.toNat <
        wordModulusN ∧
      ReturnsWord
        (Nat.toB256 (convertToSharesN
          (Sevm.argWord sevm 0).toNat assets.toNat supply.toNat)) final := by
  rcases ProducesWord.isMax_arm_trace (R := Func.RunOk)
      (ProducesWord.loadWord assetsAt) memoryWf memoryReads stack run with
    maxArm | ordinaryArm
  · rcases maxArm with
      ⟨assetsMax, bodyPre, bodyStack, bodyWf, bodyReads, -, bodyRun⟩
    obtain ⟨quotientFits, returnPre, quotientStack, returnRun⟩ :=
      productOverTwoPow256_down_trace bodyWf bodyReads
        (ProducesWord.arg sevm image 0)
        (ProducesWord.stagedDenominator_after_productScratch supplyAt)
        bodyStack lookup bodyRun
    have returned := returnWord_trace quotientStack returnRun
    constructor
    · simpa [convertToSharesN, assetsMax, maxWord_toNat,
        assetFactorN_maxWord, stagedDenominator_toNat stable] using quotientFits
    · simpa [convertToSharesN, assetsMax, maxWord_toNat,
        assetFactorN_maxWord, stagedDenominator_toNat stable] using returned
  · rcases ordinaryArm with
      ⟨assetsNotMax, bodyPre, bodyStack, bodyWf, bodyReads, -, bodyRun⟩
    let factor := Nat.toB256 (assetFactorN assets.toNat)
    let amount := Sevm.argWord sevm 0
    obtain ⟨quotientFits, returnPre, quotientStack, returnRun⟩ :=
      mulDiv_down_trace bodyWf bodyReads
        (ProducesWord.stagedAssetFactor assetsAt)
        (ProducesWord.arg sevm
          (Bytes.writeAt image (denominatorWord * 32).toNat
            factor.toBytes) 0)
        (ProducesWord.stagedDenominator_after_mulDivScratch supplyAt)
        bodyStack lookup bodyRun
    have returned := returnWord_trace quotientStack returnRun
    constructor
    · simpa [convertToSharesN, factor, amount,
        stagedDenominator_toNat stable,
        stagedAssetFactor_toNat_of_ne_max assetsNotMax] using quotientFits
    · simpa [convertToSharesN, factor, amount,
        stagedDenominator_toNat stable,
        stagedAssetFactor_toNat_of_ne_max assetsNotMax] using returned

/-- The conversion-to-assets arithmetic suffix returns exactly the G1
full-width natural formula in either asset arm. -/
theorem convertToAssets_arithmetic_trace
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
    (lookup : fs[returnWordSlot]? = some returnWord)
    (run : Func.RunCompiledTo fs sevm pre
      (loadWord assetsWord +++ isMax +++
        (shiftedDiv (arg 0) stagedDenominator .down returnWordSlot <?>
          mulDiv (arg 0) stagedAssetFactor stagedDenominator .down
            returnWordSlot)) (.ok final)) :
    convertToAssetsN
        (Sevm.argWord sevm 0).toNat assets.toNat supply.toNat <
        wordModulusN ∧
      ReturnsWord
        (Nat.toB256 (convertToAssetsN
          (Sevm.argWord sevm 0).toNat assets.toNat supply.toNat)) final := by
  rcases ProducesWord.isMax_arm_trace (R := Func.RunOk)
      (ProducesWord.loadWord assetsAt) memoryWf memoryReads stack run with
    maxArm | ordinaryArm
  · rcases maxArm with
      ⟨assetsMax, bodyPre, bodyStack, bodyWf, bodyReads, -, bodyRun⟩
    obtain ⟨quotientFits, returnPre, quotientStack, returnRun⟩ :=
      shiftedDiv_down_trace bodyWf bodyReads
        (ProducesWord.arg sevm image 0)
        (ProducesWord.stagedDenominator_after_shiftedScratch supplyAt)
        bodyStack lookup bodyRun
    have returned := returnWord_trace quotientStack returnRun
    constructor
    · simpa [convertToAssetsN, assetsMax, maxWord_toNat,
        assetFactorN_maxWord, stagedDenominator_toNat stable] using quotientFits
    · simpa [convertToAssetsN, assetsMax, maxWord_toNat,
        assetFactorN_maxWord, stagedDenominator_toNat stable] using returned
  · rcases ordinaryArm with
      ⟨assetsNotMax, bodyPre, bodyStack, bodyWf, bodyReads, -, bodyRun⟩
    let denominator := Nat.toB256 (denominatorN supply.toNat)
    let amount := Sevm.argWord sevm 0
    obtain ⟨quotientFits, returnPre, quotientStack, returnRun⟩ :=
      mulDiv_down_trace bodyWf bodyReads
        (ProducesWord.stagedDenominator supplyAt)
        (ProducesWord.arg sevm
          (Bytes.writeAt image (denominatorWord * 32).toNat
            denominator.toBytes) 0)
        (ProducesWord.stagedAssetFactor_after_mulDivScratch assetsAt)
        bodyStack lookup bodyRun
    have returned := returnWord_trace quotientStack returnRun
    constructor
    · simpa [convertToAssetsN, denominator, amount,
        stagedDenominator_toNat stable,
        stagedAssetFactor_toNat_of_ne_max assetsNotMax] using quotientFits
    · simpa [convertToAssetsN, denominator, amount,
        stagedDenominator_toNat stable,
        stagedAssetFactor_toNat_of_ne_max assetsNotMax] using returned

/-- `previewMint` uses the same full-width asset ratio as
`convertToAssets`, with exact ceiling division. -/
theorem previewMint_arithmetic_trace
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
    (lookup : fs[returnWordSlot]? = some returnWord)
    (run : Func.RunCompiledTo fs sevm pre
      (loadWord assetsWord +++ isMax +++
        (shiftedDiv (arg 0) stagedDenominator .up returnWordSlot <?>
          mulDiv (arg 0) stagedAssetFactor stagedDenominator .up
            returnWordSlot)) (.ok final)) :
    previewMintN
        (Sevm.argWord sevm 0).toNat assets.toNat supply.toNat <
        wordModulusN ∧
      ReturnsWord
        (Nat.toB256 (previewMintN
          (Sevm.argWord sevm 0).toNat assets.toNat supply.toNat)) final := by
  rcases ProducesWord.isMax_arm_trace (R := Func.RunOk)
      (ProducesWord.loadWord assetsAt) memoryWf memoryReads stack run with
    maxArm | ordinaryArm
  · rcases maxArm with
      ⟨assetsMax, bodyPre, bodyStack, bodyWf, bodyReads, -, bodyRun⟩
    obtain ⟨quotientFits, returnPre, quotientStack, returnRun⟩ :=
      shiftedDiv_up_trace bodyWf bodyReads
        (ProducesWord.arg sevm image 0)
        (ProducesWord.stagedDenominator_after_shiftedScratch supplyAt)
        bodyStack lookup bodyRun
    have returned := returnWord_trace quotientStack returnRun
    constructor
    · simpa [previewMintN, assetsMax, maxWord_toNat,
        assetFactorN_maxWord, stagedDenominator_toNat stable] using quotientFits
    · simpa [previewMintN, assetsMax, maxWord_toNat,
        assetFactorN_maxWord, stagedDenominator_toNat stable] using returned
  · rcases ordinaryArm with
      ⟨assetsNotMax, bodyPre, bodyStack, bodyWf, bodyReads, -, bodyRun⟩
    let denominator := Nat.toB256 (denominatorN supply.toNat)
    let amount := Sevm.argWord sevm 0
    obtain ⟨quotientFits, returnPre, quotientStack, returnRun⟩ :=
      mulDiv_up_trace bodyWf bodyReads
        (ProducesWord.stagedDenominator supplyAt)
        (ProducesWord.arg sevm
          (Bytes.writeAt image (denominatorWord * 32).toNat
            denominator.toBytes) 0)
        (ProducesWord.stagedAssetFactor_after_mulDivScratch assetsAt)
        bodyStack lookup bodyRun
    have returned := returnWord_trace quotientStack returnRun
    constructor
    · simpa [previewMintN, denominator, amount,
        stagedDenominator_toNat stable,
        stagedAssetFactor_toNat_of_ne_max assetsNotMax] using quotientFits
    · simpa [previewMintN, denominator, amount,
        stagedDenominator_toNat stable,
        stagedAssetFactor_toNat_of_ne_max assetsNotMax] using returned

/-- `previewWithdraw` uses the same full-width share ratio as
`convertToShares`, with exact ceiling division. -/
theorem previewWithdraw_arithmetic_trace
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
    (lookup : fs[returnWordSlot]? = some returnWord)
    (run : Func.RunCompiledTo fs sevm pre
      (loadWord assetsWord +++ isMax +++
        (productOverTwoPow256 (arg 0) stagedDenominator .up
            returnWordSlot <?>
          mulDiv (arg 0) stagedDenominator stagedAssetFactor .up
            returnWordSlot)) (.ok final)) :
    previewWithdrawN
        (Sevm.argWord sevm 0).toNat assets.toNat supply.toNat <
        wordModulusN ∧
      ReturnsWord
        (Nat.toB256 (previewWithdrawN
          (Sevm.argWord sevm 0).toNat assets.toNat supply.toNat)) final := by
  rcases ProducesWord.isMax_arm_trace (R := Func.RunOk)
      (ProducesWord.loadWord assetsAt) memoryWf memoryReads stack run with
    maxArm | ordinaryArm
  · rcases maxArm with
      ⟨assetsMax, bodyPre, bodyStack, bodyWf, bodyReads, -, bodyRun⟩
    obtain ⟨quotientFits, returnPre, quotientStack, returnRun⟩ :=
      productOverTwoPow256_up_trace bodyWf bodyReads
        (ProducesWord.arg sevm image 0)
        (ProducesWord.stagedDenominator_after_productScratch supplyAt)
        bodyStack lookup bodyRun
    have returned := returnWord_trace quotientStack returnRun
    constructor
    · simpa [previewWithdrawN, assetsMax, maxWord_toNat,
        assetFactorN_maxWord, stagedDenominator_toNat stable] using quotientFits
    · simpa [previewWithdrawN, assetsMax, maxWord_toNat,
        assetFactorN_maxWord, stagedDenominator_toNat stable] using returned
  · rcases ordinaryArm with
      ⟨assetsNotMax, bodyPre, bodyStack, bodyWf, bodyReads, -, bodyRun⟩
    let factor := Nat.toB256 (assetFactorN assets.toNat)
    let amount := Sevm.argWord sevm 0
    obtain ⟨quotientFits, returnPre, quotientStack, returnRun⟩ :=
      mulDiv_up_trace bodyWf bodyReads
        (ProducesWord.stagedAssetFactor assetsAt)
        (ProducesWord.arg sevm
          (Bytes.writeAt image (denominatorWord * 32).toNat
            factor.toBytes) 0)
        (ProducesWord.stagedDenominator_after_mulDivScratch supplyAt)
        bodyStack lookup bodyRun
    have returned := returnWord_trace quotientStack returnRun
    constructor
    · simpa [previewWithdrawN, factor, amount,
        stagedDenominator_toNat stable,
        stagedAssetFactor_toNat_of_ne_max assetsNotMax] using quotientFits
    · simpa [previewWithdrawN, factor, amount,
        stagedDenominator_toNat stable,
        stagedAssetFactor_toNat_of_ne_max assetsNotMax] using returned

/-! ## Staged endpoint-body effects -/

theorem returnWord_call_storage_inv
    {fs : List Func} (lookup : fs[returnWordSlot]? = some returnWord) :
    Func.CompiledInv fs Devm.getStor Devm.getStor
      (.call returnWordSlot) :=
  Func.CompiledInv.call lookup (by
    unfold returnWord
    compiled_inv)

theorem returnWord_call_logs_inv
    {fs : List Func} (lookup : fs[returnWordSlot]? = some returnWord) :
    Func.CompiledInv fs Devm.logs Devm.logs (.call returnWordSlot) :=
  Func.CompiledInv.call lookup (by
    unfold returnWord
    compiled_inv)

/-- Lift any proved arithmetic suffix across the shared booked-assets/supply
staging prefix.  Fixed-table invariants account for internal continuations
without weakening the exact returned word. -/
theorem stagedConversion_body_effect
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    {image : Bytes} {assets : B256} {tail : Stack}
    {arithmetic : Func} {calculate : B256 → Nat}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (stack : assets :: tail <<+ pre.stack)
    (storageInv : Func.CompiledInv fs Devm.getStor Devm.getStor
      (mstoreAt assetsWord +++
        pushSupplySlot +++ sload ::: mstoreAt supplyWord +++
        guardStableSupply arithmetic))
    (logsInv : Func.CompiledInv fs Devm.logs Devm.logs
      (mstoreAt assetsWord +++
        pushSupplySlot +++ sload ::: mstoreAt supplyWord +++
        guardStableSupply arithmetic))
    (arithmeticEffect : ∀ {supply : B256} {bodyPre : Devm},
      supply.toNat ≤ maxSupplyN →
      Mem.Wf bodyPre.memory →
      Mem.Reads bodyPre.memory
        (conversionStagingImage image assets supply) →
      tail <<+ bodyPre.stack →
      Func.RunCompiledTo fs sevm bodyPre arithmetic (.ok post) →
      calculate supply < wordModulusN ∧
        ReturnsWord (Nat.toB256 (calculate supply)) post)
    (run : Func.RunCompiledTo fs sevm pre
      (mstoreAt assetsWord +++
        pushSupplySlot +++ sload ::: mstoreAt supplyWord +++
        guardStableSupply arithmetic) (.ok post)) :
    ∃ supply,
      supply = Devm.getStorVal pre sevm.currentTarget supplySlot ∧
      supply.toNat ≤ maxSupplyN ∧
      calculate supply < wordModulusN ∧
      WordViewEffect (Nat.toB256 (calculate supply)) pre post := by
  obtain ⟨supply, bodyPre, supplyEq, stable, bodyStack, bodyWf,
      bodyReads, -, -, -, bodyRun⟩ :=
    conversionStaging_trace memoryWf memoryReads stack run
  obtain ⟨resultFits, returned⟩ :=
    arithmeticEffect stable bodyWf bodyReads bodyStack bodyRun
  exact ⟨supply, supplyEq, stable, resultFits, returned,
    storageInv run, logsInv run⟩

/-- After the exact WETH balance word has been booked on the stack,
`convertToShares` stages that balance and supply, proves the configured supply
domain, and returns the exact floor conversion without changing storage or
logs. -/
theorem convertToShares_body_effect
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    {image : Bytes} {assets : B256} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (stack : assets :: tail <<+ pre.stack)
    (lookup : fs[returnWordSlot]? = some returnWord)
    (run : Func.RunCompiledTo fs sevm pre
      (mstoreAt assetsWord +++
        pushSupplySlot +++ sload ::: mstoreAt supplyWord +++
        guardStableSupply
          (loadWord assetsWord +++ isMax +++
            (productOverTwoPow256 (arg 0) stagedDenominator .down
                returnWordSlot <?>
              mulDiv (arg 0) stagedDenominator stagedAssetFactor .down
                returnWordSlot))) (.ok post)) :
    ∃ supply,
      supply = Devm.getStorVal pre sevm.currentTarget supplySlot ∧
      supply.toNat ≤ maxSupplyN ∧
      convertToSharesN
          (Sevm.argWord sevm 0).toNat assets.toNat supply.toNat <
        wordModulusN ∧
      WordViewEffect
        (Nat.toB256 (convertToSharesN
          (Sevm.argWord sevm 0).toNat assets.toNat supply.toNat)) pre post := by
  have returnStorageCall :
      Func.CompiledInv fs Devm.getStor Devm.getStor (.call returnWordSlot) :=
    returnWord_call_storage_inv lookup
  have storageInv : Func.CompiledInv fs Devm.getStor Devm.getStor
      (mstoreAt assetsWord +++
        pushSupplySlot +++ sload ::: mstoreAt supplyWord +++
        guardStableSupply
          (loadWord assetsWord +++ isMax +++
            (productOverTwoPow256 (arg 0) stagedDenominator .down
                returnWordSlot <?>
              mulDiv (arg 0) stagedDenominator stagedAssetFactor .down
                returnWordSlot))) := by
    compiled_inv
  have returnLogsCall :
      Func.CompiledInv fs Devm.logs Devm.logs (.call returnWordSlot) :=
    returnWord_call_logs_inv lookup
  have logsInv : Func.CompiledInv fs Devm.logs Devm.logs
      (mstoreAt assetsWord +++
        pushSupplySlot +++ sload ::: mstoreAt supplyWord +++
        guardStableSupply
          (loadWord assetsWord +++ isMax +++
            (productOverTwoPow256 (arg 0) stagedDenominator .down
                returnWordSlot <?>
              mulDiv (arg 0) stagedDenominator stagedAssetFactor .down
                returnWordSlot))) := by
    compiled_inv
  apply stagedConversion_body_effect memoryWf memoryReads stack
    storageInv logsInv _ run
  intro supply bodyPre stable bodyWf bodyReads bodyStack bodyRun
  exact convertToShares_arithmetic_trace bodyWf bodyReads
    (conversionStagingImage_assets image assets supply)
    (conversionStagingImage_supply image assets supply)
    stable bodyStack lookup bodyRun

/-- Post-WETH body effect for `convertToAssets` and its identical
`previewRedeem` source. -/
theorem convertToAssets_body_effect
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    {image : Bytes} {assets : B256} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (stack : assets :: tail <<+ pre.stack)
    (lookup : fs[returnWordSlot]? = some returnWord)
    (run : Func.RunCompiledTo fs sevm pre
      (mstoreAt assetsWord +++
        pushSupplySlot +++ sload ::: mstoreAt supplyWord +++
        guardStableSupply
          (loadWord assetsWord +++ isMax +++
            (shiftedDiv (arg 0) stagedDenominator .down returnWordSlot <?>
              mulDiv (arg 0) stagedAssetFactor stagedDenominator .down
                returnWordSlot))) (.ok post)) :
    ∃ supply,
      supply = Devm.getStorVal pre sevm.currentTarget supplySlot ∧
      supply.toNat ≤ maxSupplyN ∧
      convertToAssetsN
          (Sevm.argWord sevm 0).toNat assets.toNat supply.toNat <
        wordModulusN ∧
      WordViewEffect
        (Nat.toB256 (convertToAssetsN
          (Sevm.argWord sevm 0).toNat assets.toNat supply.toNat)) pre post := by
  have returnStorageCall :
      Func.CompiledInv fs Devm.getStor Devm.getStor (.call returnWordSlot) :=
    returnWord_call_storage_inv lookup
  have storageInv : Func.CompiledInv fs Devm.getStor Devm.getStor
      (mstoreAt assetsWord +++
        pushSupplySlot +++ sload ::: mstoreAt supplyWord +++
        guardStableSupply
          (loadWord assetsWord +++ isMax +++
            (shiftedDiv (arg 0) stagedDenominator .down returnWordSlot <?>
              mulDiv (arg 0) stagedAssetFactor stagedDenominator .down
                returnWordSlot))) := by
    compiled_inv
  have returnLogsCall :
      Func.CompiledInv fs Devm.logs Devm.logs (.call returnWordSlot) :=
    returnWord_call_logs_inv lookup
  have logsInv : Func.CompiledInv fs Devm.logs Devm.logs
      (mstoreAt assetsWord +++
        pushSupplySlot +++ sload ::: mstoreAt supplyWord +++
        guardStableSupply
          (loadWord assetsWord +++ isMax +++
            (shiftedDiv (arg 0) stagedDenominator .down returnWordSlot <?>
              mulDiv (arg 0) stagedAssetFactor stagedDenominator .down
                returnWordSlot))) := by
    compiled_inv
  apply stagedConversion_body_effect memoryWf memoryReads stack
    storageInv logsInv _ run
  intro supply bodyPre stable bodyWf bodyReads bodyStack bodyRun
  exact convertToAssets_arithmetic_trace bodyWf bodyReads
    (conversionStagingImage_assets image assets supply)
    (conversionStagingImage_supply image assets supply)
    stable bodyStack lookup bodyRun

/-- Post-WETH body effect for the ceiling-input `previewMint` endpoint. -/
theorem previewMint_body_effect
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    {image : Bytes} {assets : B256} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (stack : assets :: tail <<+ pre.stack)
    (lookup : fs[returnWordSlot]? = some returnWord)
    (run : Func.RunCompiledTo fs sevm pre
      (mstoreAt assetsWord +++
        pushSupplySlot +++ sload ::: mstoreAt supplyWord +++
        guardStableSupply
          (loadWord assetsWord +++ isMax +++
            (shiftedDiv (arg 0) stagedDenominator .up returnWordSlot <?>
              mulDiv (arg 0) stagedAssetFactor stagedDenominator .up
                returnWordSlot))) (.ok post)) :
    ∃ supply,
      supply = Devm.getStorVal pre sevm.currentTarget supplySlot ∧
      supply.toNat ≤ maxSupplyN ∧
      previewMintN
          (Sevm.argWord sevm 0).toNat assets.toNat supply.toNat <
        wordModulusN ∧
      WordViewEffect
        (Nat.toB256 (previewMintN
          (Sevm.argWord sevm 0).toNat assets.toNat supply.toNat)) pre post := by
  have returnStorageCall :
      Func.CompiledInv fs Devm.getStor Devm.getStor (.call returnWordSlot) :=
    returnWord_call_storage_inv lookup
  have storageInv : Func.CompiledInv fs Devm.getStor Devm.getStor
      (mstoreAt assetsWord +++
        pushSupplySlot +++ sload ::: mstoreAt supplyWord +++
        guardStableSupply
          (loadWord assetsWord +++ isMax +++
            (shiftedDiv (arg 0) stagedDenominator .up returnWordSlot <?>
              mulDiv (arg 0) stagedAssetFactor stagedDenominator .up
                returnWordSlot))) := by
    compiled_inv
  have returnLogsCall :
      Func.CompiledInv fs Devm.logs Devm.logs (.call returnWordSlot) :=
    returnWord_call_logs_inv lookup
  have logsInv : Func.CompiledInv fs Devm.logs Devm.logs
      (mstoreAt assetsWord +++
        pushSupplySlot +++ sload ::: mstoreAt supplyWord +++
        guardStableSupply
          (loadWord assetsWord +++ isMax +++
            (shiftedDiv (arg 0) stagedDenominator .up returnWordSlot <?>
              mulDiv (arg 0) stagedAssetFactor stagedDenominator .up
                returnWordSlot))) := by
    compiled_inv
  apply stagedConversion_body_effect memoryWf memoryReads stack
    storageInv logsInv _ run
  intro supply bodyPre stable bodyWf bodyReads bodyStack bodyRun
  exact previewMint_arithmetic_trace bodyWf bodyReads
    (conversionStagingImage_assets image assets supply)
    (conversionStagingImage_supply image assets supply)
    stable bodyStack lookup bodyRun

/-- Post-WETH body effect for the ceiling-output `previewWithdraw` endpoint. -/
theorem previewWithdraw_body_effect
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    {image : Bytes} {assets : B256} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (stack : assets :: tail <<+ pre.stack)
    (lookup : fs[returnWordSlot]? = some returnWord)
    (run : Func.RunCompiledTo fs sevm pre
      (mstoreAt assetsWord +++
        pushSupplySlot +++ sload ::: mstoreAt supplyWord +++
        guardStableSupply
          (loadWord assetsWord +++ isMax +++
            (productOverTwoPow256 (arg 0) stagedDenominator .up
                returnWordSlot <?>
              mulDiv (arg 0) stagedDenominator stagedAssetFactor .up
                returnWordSlot))) (.ok post)) :
    ∃ supply,
      supply = Devm.getStorVal pre sevm.currentTarget supplySlot ∧
      supply.toNat ≤ maxSupplyN ∧
      previewWithdrawN
          (Sevm.argWord sevm 0).toNat assets.toNat supply.toNat <
        wordModulusN ∧
      WordViewEffect
        (Nat.toB256 (previewWithdrawN
          (Sevm.argWord sevm 0).toNat assets.toNat supply.toNat)) pre post := by
  have returnStorageCall :
      Func.CompiledInv fs Devm.getStor Devm.getStor (.call returnWordSlot) :=
    returnWord_call_storage_inv lookup
  have storageInv : Func.CompiledInv fs Devm.getStor Devm.getStor
      (mstoreAt assetsWord +++
        pushSupplySlot +++ sload ::: mstoreAt supplyWord +++
        guardStableSupply
          (loadWord assetsWord +++ isMax +++
            (productOverTwoPow256 (arg 0) stagedDenominator .up
                returnWordSlot <?>
              mulDiv (arg 0) stagedDenominator stagedAssetFactor .up
                returnWordSlot))) := by
    compiled_inv
  have returnLogsCall :
      Func.CompiledInv fs Devm.logs Devm.logs (.call returnWordSlot) :=
    returnWord_call_logs_inv lookup
  have logsInv : Func.CompiledInv fs Devm.logs Devm.logs
      (mstoreAt assetsWord +++
        pushSupplySlot +++ sload ::: mstoreAt supplyWord +++
        guardStableSupply
          (loadWord assetsWord +++ isMax +++
            (productOverTwoPow256 (arg 0) stagedDenominator .up
                returnWordSlot <?>
              mulDiv (arg 0) stagedDenominator stagedAssetFactor .up
                returnWordSlot))) := by
    compiled_inv
  apply stagedConversion_body_effect memoryWf memoryReads stack
    storageInv logsInv _ run
  intro supply bodyPre stable bodyWf bodyReads bodyStack bodyRun
  exact previewWithdraw_arithmetic_trace bodyWf bodyReads
    (conversionStagingImage_assets image assets supply)
    (conversionStagingImage_supply image assets supply)
    stable bodyStack lookup bodyRun

end ProrataWethVault

end Blanc
