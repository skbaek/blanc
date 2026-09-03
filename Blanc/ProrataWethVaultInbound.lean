-- ProrataWethVaultInbound.lean : exact local seams for `deposit` and `mint`.

import Blanc.ProrataWethVaultCapacities

namespace Blanc

open Jaune
open Jaune.Ninst Ninst
open scoped LogOutputHinv

namespace ProrataWethVault

/-!
# Compiled inbound seams

`deposit` and `mint` stage their ABI arguments, quote against the booked
WETH balance *before* the inbound transfer, and only then execute the exact
configured WETH `transferFrom` child.  This module owns the family-local half
of that walk: argument staging, the exact quote reaching the auxiliary
continuation, and the local guards inside `depositAfterQuote` and
`mintAfterQuote`.  The WETH child itself and the public compiled selectors
belong to the composition stratum.

Every theorem here carries the long-lived operation words through arithmetic
scratch memory with `MemWordAt`, so the continuation's reads of `amountWord`,
`receiverWord`, `supplyWord`, and `quoteWord` are justified rather than
assumed.
-/

/-! ## Inbound argument staging -/

/-- Memory image after the two inbound ABI arguments are staged. -/
def inboundArgImage (image : Bytes) (amount receiver : B256) : Bytes :=
  Bytes.writeAt
    (Bytes.writeAt image (amountWord * 32).toNat amount.toBytes)
    (receiverWord * 32).toNat receiver.toBytes

theorem inboundArgImage_amount
    (image : Bytes) (amount receiver : B256) :
    Bytes.toB256
        ((inboundArgImage image amount receiver).sliceD
          (amountWord * 32).toNat 32 0) = amount := by
  unfold inboundArgImage
  rw [Bytes.readWord_writeAt_of_disjoint]
  · exact Bytes.readWord_writeAt_self _ _ _
  · left
    decide +kernel

theorem inboundArgImage_receiver
    (image : Bytes) (amount receiver : B256) :
    Bytes.toB256
        ((inboundArgImage image amount receiver).sliceD
          (receiverWord * 32).toNat 32 0) = receiver := by
  unfold inboundArgImage
  exact Bytes.readWord_writeAt_self _ _ _

/-- Both inbound flows begin by staging ABI arguments zero and one into the
long-lived operation words, leaving persistent state untouched. -/
theorem inboundArgs_trace
    {fs : List Func} {sevm : Sevm} {pre final : Devm}
    {image : Bytes} {body : Func} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (stack : tail <<+ pre.stack)
    (run : Func.RunCompiledTo fs sevm pre
      (arg 0 +++ mstoreAt amountWord +++
        arg 1 +++ mstoreAt receiverWord +++ body) (.ok final)) :
    ∃ bodyPre,
      tail <<+ bodyPre.stack ∧
      Mem.Wf bodyPre.memory ∧
      Mem.Reads bodyPre.memory
        (inboundArgImage image (Sevm.argWord sevm 0)
          (Sevm.argWord sevm 1)) ∧
      pre.state = bodyPre.state ∧
      pre.logs = bodyPre.logs ∧
      Func.RunCompiledTo fs sevm bodyPre body (.ok final) := by
  obtain ⟨amountStorePre, amountRun, run⟩ := runCompiledTo_prepend_inv run
  have amountPrefix := prefix_of_arg stack amountRun
  have amountMemory : pre.memory = amountStorePre.memory := by
    refine Line.of_inv Devm.memory ?_ amountRun
    unfold Blanc.arg cdl
    line_inv
  have amountState : pre.state = amountStorePre.state := by
    refine Line.of_inv Devm.state ?_ amountRun
    unfold Blanc.arg cdl
    line_inv
  have amountLogs : pre.logs = amountStorePre.logs := by
    refine Line.of_inv Devm.logs ?_ amountRun
    unfold Blanc.arg cdl
    line_inv
  have amountStoreWf : Mem.Wf amountStorePre.memory := by
    rw [← amountMemory]; exact memoryWf
  have amountStoreReads : Mem.Reads amountStorePre.memory image := by
    rw [← amountMemory]; exact memoryReads
  obtain ⟨receiverPre, amountStoreRun, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨receiverStack, receiverWf, receiverReads, amountStoreState⟩ :=
    of_run_mstoreAt_image amountPrefix amountStoreWf amountStoreReads
      amountStoreRun
  have amountStoreLogs : amountStorePre.logs = receiverPre.logs := by
    refine Line.of_inv Devm.logs ?_ amountStoreRun
    unfold mstoreAt
    line_inv
  obtain ⟨receiverStorePre, receiverRun, run⟩ := runCompiledTo_prepend_inv run
  have receiverPrefix := prefix_of_arg receiverStack receiverRun
  have receiverMemory : receiverPre.memory = receiverStorePre.memory := by
    refine Line.of_inv Devm.memory ?_ receiverRun
    unfold Blanc.arg cdl
    line_inv
  have receiverState : receiverPre.state = receiverStorePre.state := by
    refine Line.of_inv Devm.state ?_ receiverRun
    unfold Blanc.arg cdl
    line_inv
  have receiverLogs : receiverPre.logs = receiverStorePre.logs := by
    refine Line.of_inv Devm.logs ?_ receiverRun
    unfold Blanc.arg cdl
    line_inv
  have receiverStoreWf : Mem.Wf receiverStorePre.memory := by
    rw [← receiverMemory]; exact receiverWf
  have receiverStoreReads : Mem.Reads receiverStorePre.memory
      (Bytes.writeAt image (amountWord * 32).toNat
        (Sevm.argWord sevm 0).toBytes) := by
    rw [← receiverMemory]; exact receiverReads
  obtain ⟨bodyPre, receiverStoreRun, bodyRun⟩ := runCompiledTo_prepend_inv run
  obtain ⟨bodyStack, bodyWf, bodyReads, receiverStoreState⟩ :=
    of_run_mstoreAt_image receiverPrefix receiverStoreWf receiverStoreReads
      receiverStoreRun
  have receiverStoreLogs : receiverStorePre.logs = bodyPre.logs := by
    refine Line.of_inv Devm.logs ?_ receiverStoreRun
    unfold mstoreAt
    line_inv
  exact ⟨bodyPre, bodyStack, bodyWf, bodyReads,
    amountState.trans (amountStoreState.trans
      (receiverState.trans receiverStoreState)),
    amountLogs.trans (amountStoreLogs.trans
      (receiverLogs.trans receiverStoreLogs)),
    bodyRun⟩

/-! ## Exact inbound quotes reaching the auxiliary continuation -/

/-- The `deposit` arithmetic suffix quotes exactly `floor(amount*D/X)` from the
*pre-transfer* booked assets and supply, then calls the auxiliary
`depositAfterQuote` continuation with that word on the stack.  Both the
exact-`2^256` and ordinary asset arms are covered, and the continuation
receives a memory image agreeing with the entry image on every word at or
above the arithmetic scratch boundary. -/
theorem depositQuote_arithmetic_trace
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
    (lookup : fs[depositAfterQuoteSlot]? = some depositAfterQuote)
    (run : Func.RunCompiledTo fs sevm pre
      (loadWord assetsWord +++ isMax +++
        (productOverTwoPow256 (loadWord amountWord) stagedDenominator .down
            depositAfterQuoteSlot <?>
          mulDiv (loadWord amountWord) stagedDenominator stagedAssetFactor
            .down depositAfterQuoteSlot)) (.ok final)) :
    convertToSharesN amount.toNat assets.toNat supply.toNat < wordModulusN ∧
      ∃ bodyPre bodyImage,
        Nat.toB256
            (convertToSharesN amount.toNat assets.toNat supply.toNat) ::
          tail <<+ bodyPre.stack ∧
        MemImage bodyPre bodyImage ∧
        Bytes.WordFrameFrom image bodyImage arithmeticScratchEnd ∧
        Devm.QuietFrame pre bodyPre ∧
        Func.RunCompiledTo fs sevm bodyPre depositAfterQuote (.ok final) := by
  rcases ProducesWord.isMax_arm_trace
      (ProducesWord.loadWord assetsAt) memoryWf memoryReads stack run with
    maxArm | ordinaryArm
  · rcases maxArm with
      ⟨assetsMax, bodyPre, bodyStack, bodyWf, bodyReads, bodyState,
        bodyRun⟩
    let denominator := Nat.toB256 (denominatorN supply.toNat)
    obtain ⟨quotientFits, quotePre, quoteStack, quoteImage, quoteState,
        quoteRun⟩ :=
      productOverTwoPow256_down_image_trace bodyWf bodyReads
        (ProducesWord.loadWord amountAt)
        (ProducesWord.stagedDenominator_after_productScratch supplyAt)
        bodyStack lookup bodyRun
    refine ⟨?_, quotePre,
      productOverTwoPow256TraceImage image amount denominator, ?_, quoteImage,
      productOverTwoPow256TraceImage_wordFrame image amount denominator,
      bodyState.trans quoteState, quoteRun⟩
    · simpa [convertToSharesN, denominator, assetsMax, maxWord_toNat,
        assetFactorN_maxWord, stagedDenominator_toNat stable] using
        quotientFits
    · simpa [convertToSharesN, denominator, assetsMax, maxWord_toNat,
        assetFactorN_maxWord, stagedDenominator_toNat stable] using
        quoteStack
  · rcases ordinaryArm with
      ⟨assetsNotMax, bodyPre, bodyStack, bodyWf, bodyReads, bodyState,
        bodyRun⟩
    obtain ⟨quotientFits, quotePre, quoteImage, quoteStack, quoteMemImage,
        quoteFrame, quoteState, quoteRun⟩ :=
      mulDiv_down_image_trace bodyWf bodyReads
        (ProducesWord.stagedAssetFactor assetsAt)
        (ProducesWord.amount_after_denominatorScratch amountAt)
        (ProducesWord.stagedDenominator_after_mulDivScratch supplyAt)
        bodyStack lookup bodyRun
    refine ⟨?_, quotePre, quoteImage, ?_, quoteMemImage, quoteFrame,
      bodyState.trans quoteState, quoteRun⟩
    · simpa [convertToSharesN, stagedDenominator_toNat stable,
        stagedAssetFactor_toNat_of_ne_max assetsNotMax] using quotientFits
    · simpa [convertToSharesN, stagedDenominator_toNat stable,
        stagedAssetFactor_toNat_of_ne_max assetsNotMax] using quoteStack

/-- The `mint` arithmetic suffix quotes exactly `ceil(shares*X/D)` from the
pre-transfer booked assets and supply and calls `mintAfterQuote`. -/
theorem mintQuote_arithmetic_trace
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
    (lookup : fs[mintAfterQuoteSlot]? = some mintAfterQuote)
    (run : Func.RunCompiledTo fs sevm pre
      (loadWord assetsWord +++ isMax +++
        (shiftedDiv (loadWord amountWord) stagedDenominator .up
            mintAfterQuoteSlot <?>
          mulDiv (loadWord amountWord) stagedAssetFactor stagedDenominator
            .up mintAfterQuoteSlot)) (.ok final)) :
    previewMintN amount.toNat assets.toNat supply.toNat < wordModulusN ∧
      ∃ bodyPre bodyImage,
        Nat.toB256 (previewMintN amount.toNat assets.toNat supply.toNat) ::
          tail <<+ bodyPre.stack ∧
        MemImage bodyPre bodyImage ∧
        Bytes.WordFrameFrom image bodyImage arithmeticScratchEnd ∧
        Devm.QuietFrame pre bodyPre ∧
        Func.RunCompiledTo fs sevm bodyPre mintAfterQuote (.ok final) := by
  rcases ProducesWord.isMax_arm_trace
      (ProducesWord.loadWord assetsAt) memoryWf memoryReads stack run with
    maxArm | ordinaryArm
  · rcases maxArm with
      ⟨assetsMax, bodyPre, bodyStack, bodyWf, bodyReads, bodyState,
        bodyRun⟩
    obtain ⟨ceilingFits, quotePre, quoteImage, quoteStack, quoteMemImage,
        quoteFrame, quoteState, quoteRun⟩ :=
      shiftedDiv_up_image_trace bodyWf bodyReads
        (ProducesWord.loadWord amountAt)
        (ProducesWord.stagedDenominator_after_shiftedScratch supplyAt)
        bodyStack lookup bodyRun
    refine ⟨?_, quotePre, quoteImage, ?_, quoteMemImage, quoteFrame,
      bodyState.trans quoteState, quoteRun⟩
    · simpa [previewMintN, assetsMax, maxWord_toNat, assetFactorN_maxWord,
        stagedDenominator_toNat stable] using ceilingFits
    · simpa [previewMintN, assetsMax, maxWord_toNat, assetFactorN_maxWord,
        stagedDenominator_toNat stable] using quoteStack
  · rcases ordinaryArm with
      ⟨assetsNotMax, bodyPre, bodyStack, bodyWf, bodyReads, bodyState,
        bodyRun⟩
    obtain ⟨ceilingFits, quotePre, quoteImage, quoteStack, quoteMemImage,
        quoteFrame, quoteState, quoteRun⟩ :=
      mulDiv_up_image_trace bodyWf bodyReads
        (ProducesWord.stagedDenominator supplyAt)
        (ProducesWord.amount_after_denominatorScratch amountAt)
        (ProducesWord.stagedAssetFactor_after_mulDivScratch assetsAt)
        bodyStack lookup bodyRun
    refine ⟨?_, quotePre, quoteImage, ?_, quoteMemImage, quoteFrame,
      bodyState.trans quoteState, quoteRun⟩
    · simpa [previewMintN, stagedDenominator_toNat stable,
        stagedAssetFactor_toNat_of_ne_max assetsNotMax] using ceilingFits
    · simpa [previewMintN, stagedDenominator_toNat stable,
        stagedAssetFactor_toNat_of_ne_max assetsNotMax] using quoteStack

/-- A successful staged-address guard proves the selected operation word is a
canonical nonzero address and leaves memory, state, and logs untouched. -/
theorem nonzeroStagedAddress_trace
    {fs : List Func} {sevm : Sevm} {pre final : Devm}
    {image : Bytes} {word value : B256} {body : Func} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (valueAt : Bytes.toB256
      (image.sliceD (word * 32).toNat 32 0) = value)
    (stack : tail <<+ pre.stack)
    (run : Func.RunCompiledTo fs sevm pre
      (nonzeroStagedAddress word body) (.ok final)) :
    ∃ bodyPre,
      ValidAdr value ∧
      value ≠ 0 ∧
      tail <<+ bodyPre.stack ∧
      Mem.Wf bodyPre.memory ∧
      Mem.Reads bodyPre.memory image ∧
      pre.state = bodyPre.state ∧
      pre.logs = bodyPre.logs ∧
      Func.RunCompiledTo fs sevm bodyPre body (.ok final) := by
  unfold nonzeroStagedAddress at run
  obtain ⟨checkPre, valueRun, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨valuePrefix, checkWf, checkReads, valueState⟩ :=
    of_run_loadWordAt_image stack memoryWf memoryReads valueAt valueRun
  have valueLogs : pre.logs = checkPre.logs :=
    Line.of_inv Devm.logs (by unfold ProrataWethVault.loadWord; line_inv)
      valueRun
  obtain ⟨dupPre, dupRun, run⟩ := runCompiledTo_next_inv run
  have dupSource := Ninst.Run.of_runCompiled dupRun
  have dupPrefix : value :: value :: tail <<+ dupPre.stack :=
    prefix_of_dup_val dupSource (by show_nth) valuePrefix
  obtain ⟨checkPost, checkRun, branchRun⟩ := runCompiledTo_prepend_inv run
  obtain ⟨flag, flagPrefix, flagValid⟩ := of_check_non_address dupPrefix checkRun
  have checkMemory : checkPre.memory = checkPost.memory :=
    (Ninst.Hinv.inv (f := Devm.memory) dupSource).trans
      (Line.of_inv Devm.memory (by unfold checkNonAddress; line_inv) checkRun)
  have checkState : checkPre.state = checkPost.state :=
    (Ninst.Hinv.inv (f := Devm.state) dupSource).trans
      (Line.of_inv Devm.state (by unfold checkNonAddress; line_inv) checkRun)
  have checkLogs : checkPre.logs = checkPost.logs :=
    (Ninst.Hinv.inv (f := Devm.logs) dupSource).trans
      (Line.of_inv Devm.logs (by unfold checkNonAddress; line_inv) checkRun)
  rcases runCompiledTo_branch_inv branchRun with zeroRoute | revertRoute
  · rcases zeroRoute with ⟨zeroPre, flagStack, flagPop, zeroRun⟩
    have zeroFlagPrefix : (0 : B256) :: [] <<+ checkPost.stack :=
      ⟨zeroPre.stack, by simpa [Split] using flagStack⟩
    have flagZero : flag = 0 := pref_head_unique flagPrefix zeroFlagPrefix
    have zeroPrefix : value :: tail <<+ zeroPre.stack :=
      (popBurn_pref (Devm.PopBurn.of_popBurnBy flagPop) flagPrefix).2
    have zeroWf : Mem.Wf zeroPre.memory := by
      rw [← flagPop.memory, ← checkMemory]
      exact checkWf
    have zeroReads : Mem.Reads zeroPre.memory image := by
      rw [← flagPop.memory, ← checkMemory]
      exact checkReads
    obtain ⟨testPre, testRun, testBranchRun⟩ := runCompiledTo_next_inv zeroRun
    have testSource := Ninst.Run.of_runCompiled testRun
    have testPrefix := prefix_of_iszero testSource zeroPrefix
    have testMemory : zeroPre.memory = testPre.memory :=
      Ninst.Hinv.inv (f := Devm.memory) testSource
    have testState : zeroPre.state = testPre.state :=
      Ninst.Hinv.inv (f := Devm.state) testSource
    have testLogs : zeroPre.logs = testPre.logs :=
      Ninst.Hinv.inv (f := Devm.logs) testSource
    have valueNonzero : value ≠ 0 := by
      intro valueZero
      have onePrefix : (1 : B256) :: tail <<+ testPre.stack := by
        simpa [B256.eqCheck, valueZero] using testPrefix
      obtain ⟨revertPre, branchWord, branchWordNe, revertPop, revertRun, -⟩ :=
        Func.RunCompiledTo.succ_branch_of_prefix
          (by decide : (1 : B256) ≠ 0) onePrefix testBranchRun
      obtain ⟨revertPost, impossible, -⟩ := runCompiledTo_revert_inv revertRun
      cases impossible
    have testZeroPrefix : (0 : B256) :: tail <<+ testPre.stack := by
      simpa [B256.eqCheck, valueNonzero] using testPrefix
    obtain ⟨bodyPre, bodyPop, bodyRun, bodyPrefix⟩ :=
      Func.RunCompiledTo.zero_branch_of_prefix testZeroPrefix testBranchRun
    have bodyWf : Mem.Wf bodyPre.memory := by
      rw [← bodyPop.memory, ← testMemory]
      exact zeroWf
    have bodyReads : Mem.Reads bodyPre.memory image := by
      rw [← bodyPop.memory, ← testMemory]
      exact zeroReads
    refine ⟨bodyPre, flagValid.mp flagZero, valueNonzero, bodyPrefix, bodyWf,
      bodyReads, ?_, ?_, bodyRun⟩
    · exact valueState.trans
        (checkState.trans
          (flagPop.state.trans (testState.trans bodyPop.state)))
    · exact valueLogs.trans
        (checkLogs.trans
          (flagPop.logs.trans (testLogs.trans bodyPop.logs)))
  · rcases revertRoute with ⟨_, revertPre, -, -, -, revertRun⟩
    obtain ⟨revertPost, impossible, -⟩ := runCompiledTo_revert_inv revertRun
    cases impossible

/-! ## Local inbound guards -/

/-- The shared inbound guard prefix stages the quote, rejects the zero EVM
caller, and rejects a dirty or zero staged receiver.  Persistent state, logs,
and every operation word other than `quoteWord` are untouched. -/
theorem inboundGuards_trace
    {fs : List Func} {sevm : Sevm} {pre final : Devm}
    {image : Bytes} {quote receiver : B256} {body : Func} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (receiverAt : Bytes.toB256
      (image.sliceD (receiverWord * 32).toNat 32 0) = receiver)
    (stack : quote :: tail <<+ pre.stack)
    (run : Func.RunCompiledTo fs sevm pre
      (mstoreAt quoteWord +++
        nonzeroCaller (nonzeroStagedAddress receiverWord body)) (.ok final)) :
    ∃ bodyPre,
      sevm.caller.toB256 ≠ 0 ∧
      ValidAdr receiver ∧
      receiver ≠ 0 ∧
      tail <<+ bodyPre.stack ∧
      Mem.Wf bodyPre.memory ∧
      Mem.Reads bodyPre.memory
        (Bytes.writeAt image (quoteWord * 32).toNat quote.toBytes) ∧
      pre.state = bodyPre.state ∧
      pre.logs = bodyPre.logs ∧
      Func.RunCompiledTo fs sevm bodyPre body (.ok final) := by
  obtain ⟨callerPre, quoteStoreRun, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨callerStack, callerWf, callerReads, quoteState⟩ :=
    of_run_mstoreAt_image stack memoryWf memoryReads quoteStoreRun
  have quoteLogs : pre.logs = callerPre.logs :=
    Line.of_inv Devm.logs (by line_inv) quoteStoreRun
  let quoteImage := Bytes.writeAt image (quoteWord * 32).toNat quote.toBytes
  change Mem.Reads callerPre.memory quoteImage at callerReads
  have receiverAtQuote : Bytes.toB256
      (quoteImage.sliceD (receiverWord * 32).toNat 32 0) = receiver := by
    unfold quoteImage
    rw [Bytes.readWord_writeAt_of_disjoint]
    · exact receiverAt
    · left
      decide +kernel

  -- Reject the zero caller.
  unfold nonzeroCaller at run
  obtain ⟨callerTest, callerRun, run⟩ := runCompiledTo_next_inv run
  have callerSource := Ninst.Run.of_runCompiled callerRun
  have callerPrefix : sevm.caller.toB256 :: tail <<+ callerTest.stack :=
    prefix_of_push (of_run_caller callerSource) callerStack
  obtain ⟨zeroTest, callerZeroRun, callerBranchRun⟩ :=
    runCompiledTo_next_inv run
  have callerZeroSource := Ninst.Run.of_runCompiled callerZeroRun
  have zeroTestPrefix := prefix_of_iszero callerZeroSource callerPrefix
  have callerPush := of_run_caller callerSource
  have callerMemory : callerPre.memory = zeroTest.memory :=
    callerPush.memory.trans
      (Ninst.Hinv.inv (f := Devm.memory) callerZeroSource)
  have callerState : callerPre.state = zeroTest.state :=
    callerPush.state.trans
      (Ninst.Hinv.inv (f := Devm.state) callerZeroSource)
  have callerLogs : callerPre.logs = zeroTest.logs :=
    callerPush.logs.trans
      (Ninst.Hinv.inv (f := Devm.logs) callerZeroSource)
  have callerNonzero : sevm.caller.toB256 ≠ 0 := by
    intro callerZero
    have onePrefix : (1 : B256) :: tail <<+ zeroTest.stack := by
      simpa [B256.eqCheck, callerZero] using zeroTestPrefix
    obtain ⟨revertPre, branchWord, branchWordNe, revertPop, revertRun, -⟩ :=
      Func.RunCompiledTo.succ_branch_of_prefix
        (by decide : (1 : B256) ≠ 0) onePrefix callerBranchRun
    obtain ⟨revertPost, impossible, -⟩ := runCompiledTo_revert_inv revertRun
    cases impossible
  have callerZeroPrefix : (0 : B256) :: tail <<+ zeroTest.stack := by
    simpa [B256.eqCheck, callerNonzero] using zeroTestPrefix
  obtain ⟨addressPre, callerPop, run, addressStack⟩ :=
    Func.RunCompiledTo.zero_branch_of_prefix callerZeroPrefix callerBranchRun
  have addressWf : Mem.Wf addressPre.memory := by
    rw [← callerPop.memory, ← callerMemory]
    exact callerWf
  have addressReads : Mem.Reads addressPre.memory quoteImage := by
    rw [← callerPop.memory, ← callerMemory]
    exact callerReads

  -- Reject a dirty or zero staged receiver.
  obtain ⟨bodyPre, receiverValid, receiverNonzero, bodyStack, bodyWf,
      bodyReads, addressState, addressLogs, bodyRun⟩ :=
    nonzeroStagedAddress_trace addressWf addressReads receiverAtQuote
      addressStack run
  refine ⟨bodyPre, callerNonzero, receiverValid, receiverNonzero, bodyStack,
    bodyWf, bodyReads, ?_, ?_, bodyRun⟩
  · exact quoteState.trans
      (callerState.trans (callerPop.state.trans addressState))
  · exact quoteLogs.trans
      (callerLogs.trans (callerPop.logs.trans addressLogs))

/-! ## Supply-room guard -/

/-- The inbound supply-room guard runs *before* the WETH child.  A successful
walk proves the quoted share amount fits the exact remaining room and leaves
memory, persistent state, and logs untouched. -/
theorem shareRoomGuard_trace
    {fs : List Func} {sevm : Sevm} {pre final : Devm}
    {image : Bytes} {sharesWord shares supply : B256}
    {body : Func} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (sharesAt : Bytes.toB256
      (image.sliceD (sharesWord * 32).toNat 32 0) = shares)
    (supplyAt : Bytes.toB256
      (image.sliceD (supplyWord * 32).toNat 32 0) = supply)
    (stable : supply.toNat ≤ maxSupplyN)
    (stack : tail <<+ pre.stack)
    (run : Func.RunCompiledTo fs sevm pre
      (loadWord sharesWord +++ shareRoom +++ lt ::: (Func.revert <?> body))
      (.ok final)) :
    ∃ bodyPre,
      shares.toNat ≤ shareRoomN supply.toNat ∧
      tail <<+ bodyPre.stack ∧
      Mem.Wf bodyPre.memory ∧
      Mem.Reads bodyPre.memory image ∧
      pre.state = bodyPre.state ∧
      pre.logs = bodyPre.logs ∧
      Func.RunCompiledTo fs sevm bodyPre body (.ok final) := by
  obtain ⟨roomPre, sharesRun, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨sharesPrefix, sharesMemWf, sharesReads, sharesState⟩ :=
    of_run_loadWordAt_image stack memoryWf memoryReads sharesAt sharesRun
  have sharesLogs : pre.logs = roomPre.logs := by
    refine Line.of_inv Devm.logs ?_ sharesRun
    unfold ProrataWethVault.loadWord
    line_inv
  obtain ⟨testPre, roomRun, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨roomPrefix, roomWf, roomReads, roomState⟩ :=
    (ProducesWord.shareRoom (sevm := sevm) supplyAt stable)
      sharesMemWf sharesReads sharesPrefix roomRun
  have roomLogs : roomPre.logs = testPre.logs := by
    refine Line.of_inv Devm.logs ?_ roomRun
    unfold ProrataWethVault.shareRoom ProrataWethVault.loadWord
    line_inv
  obtain ⟨branchPre, testRun, branchRun⟩ := runCompiledTo_next_inv run
  have testSource := Ninst.Run.of_runCompiled testRun
  have testPrefix := prefix_of_lt testSource roomPrefix
  have testMemory : testPre.memory = branchPre.memory :=
    Ninst.Hinv.inv (f := Devm.memory) testSource
  have testState : testPre.state = branchPre.state :=
    Ninst.Hinv.inv (f := Devm.state) testSource
  have testLogs : testPre.logs = branchPre.logs :=
    Ninst.Hinv.inv (f := Devm.logs) testSource
  have roomFits : shareRoomN supply.toNat < wordModulusN :=
    shareRoomN_lt_wordModulusN supply.toNat
  have roomNat :
      (Nat.toB256 (shareRoomN supply.toNat)).toNat =
        shareRoomN supply.toNat :=
    B256.toNat_toB256_of_lt roomFits
  have roomLarge : ¬ Nat.toB256 (shareRoomN supply.toNat) < shares := by
    intro roomLt
    have onePrefix : (1 : B256) :: tail <<+ branchPre.stack := by
      simpa [B256.ltCheck, roomLt] using testPrefix
    obtain ⟨revertPre, branchWord, branchWordNe, revertPop, revertRun, -⟩ :=
      Func.RunCompiledTo.succ_branch_of_prefix
        (by decide : (1 : B256) ≠ 0) onePrefix branchRun
    obtain ⟨revertPost, impossible, -⟩ := runCompiledTo_revert_inv revertRun
    cases impossible
  have zeroPrefix : (0 : B256) :: tail <<+ branchPre.stack := by
    simpa [B256.ltCheck, roomLarge] using testPrefix
  obtain ⟨bodyPre, bodyPop, bodyRun, bodyPrefix⟩ :=
    Func.RunCompiledTo.zero_branch_of_prefix zeroPrefix branchRun
  have bodyWf : Mem.Wf bodyPre.memory := by
    rw [← bodyPop.memory, ← testMemory]
    exact roomWf
  have bodyReads : Mem.Reads bodyPre.memory image := by
    rw [← bodyPop.memory, ← testMemory]
    exact roomReads
  refine ⟨bodyPre, ?_, bodyPrefix, bodyWf, bodyReads, ?_, ?_, bodyRun⟩
  · by_contra sharesLarge
    exact roomLarge
      (B256.lt_of_toNat_lt_toNat (by rw [roomNat]; omega))
  · exact sharesState.trans
      (roomState.1.trans (testState.trans bodyPop.state))
  · exact sharesLogs.trans
      (roomLogs.trans (testLogs.trans bodyPop.logs))

/-! ## Receiver credit and its overflow guard -/

/-- Memory image after the receiver's pre-state share balance and the checked
sum are staged. -/
def inboundCreditImage (image : Bytes) (balance credited : B256) : Bytes :=
  Bytes.writeAt
    (Bytes.writeAt image (balanceWord * 32).toNat balance.toBytes)
    (scratchWord * 32).toNat credited.toBytes

/-- The inbound tail reads the receiver's exact pre-state share balance,
stages the credited sum, and rejects a wrapped total.  Persistent state and
logs are still untouched: every write so far is memory-local. -/
theorem inboundCredit_trace
    {fs : List Func} {sevm : Sevm} {pre final : Devm}
    {image : Bytes} {sharesWord receiver shares : B256}
    {body : Func} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (receiverAt : Bytes.toB256
      (image.sliceD (receiverWord * 32).toNat 32 0) = receiver)
    (sharesAt : Bytes.toB256
      (image.sliceD (sharesWord * 32).toNat 32 0) = shares)
    (sharesBelow : (sharesWord * 32).toNat + 32 ≤ (balanceWord * 32).toNat)
    (stack : tail <<+ pre.stack)
    (run : Func.RunCompiledTo fs sevm pre
      (loadWord receiverWord +++ sload ::: mstoreAt balanceWord +++
        loadWord sharesWord +++ loadWord balanceWord +++ add :::
        mstoreAt scratchWord +++
        loadWord balanceWord +++ loadWord scratchWord +++ lt :::
        (Func.revert <?> body)) (.ok final)) :
    ∃ bodyPre balance,
      balance = Devm.getStorVal pre sevm.currentTarget receiver ∧
      balance.toNat + shares.toNat < wordModulusN ∧
      tail <<+ bodyPre.stack ∧
      Mem.Wf bodyPre.memory ∧
      Mem.Reads bodyPre.memory
        (inboundCreditImage image balance (balance + shares)) ∧
      Devm.getStor pre = Devm.getStor bodyPre ∧
      pre.logs = bodyPre.logs ∧
      Func.RunCompiledTo fs sevm bodyPre body (.ok final) := by
  -- Read the receiver's share row.
  obtain ⟨sloadPre, receiverRun, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨receiverPrefix, sloadWf, sloadReads, receiverState⟩ :=
    of_run_loadWordAt_image stack memoryWf memoryReads receiverAt receiverRun
  have receiverLogs : pre.logs = sloadPre.logs := by
    refine Line.of_inv Devm.logs ?_ receiverRun
    unfold ProrataWethVault.loadWord
    line_inv
  obtain ⟨balanceStorePre, sloadRun, run⟩ := runCompiledTo_next_inv run
  have sloadSource := Ninst.Run.of_runCompiled sloadRun
  obtain ⟨balance, balancePrefix, balanceEq⟩ :=
    prefix_of_sload sloadSource receiverPrefix
  have sloadStorage : Devm.getStor sloadPre = Devm.getStor balanceStorePre :=
    Ninst.Hinv.inv (f := Devm.getStor) sloadSource
  have sloadMemory : sloadPre.memory = balanceStorePre.memory :=
    Ninst.Hinv.inv (f := Devm.memory) sloadSource
  have sloadLogs : sloadPre.logs = balanceStorePre.logs :=
    Ninst.Hinv.inv (f := Devm.logs) sloadSource
  have balanceStoreWf : Mem.Wf balanceStorePre.memory := by
    rw [← sloadMemory]; exact sloadWf
  have balanceStoreReads : Mem.Reads balanceStorePre.memory image := by
    rw [← sloadMemory]; exact sloadReads

  -- Stage the balance.
  obtain ⟨sharesPre, balanceStoreRun, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨sharesStack, sharesWf, sharesReads, balanceStoreState⟩ :=
    of_run_mstoreAt_image balancePrefix balanceStoreWf balanceStoreReads
      balanceStoreRun
  have balanceStoreLogs : balanceStorePre.logs = sharesPre.logs := by
    refine Line.of_inv Devm.logs ?_ balanceStoreRun
    unfold mstoreAt
    line_inv
  let image1 := Bytes.writeAt image (balanceWord * 32).toNat balance.toBytes
  change Mem.Reads sharesPre.memory image1 at sharesReads
  have sharesAt1 : Bytes.toB256
      (image1.sliceD (sharesWord * 32).toNat 32 0) = shares := by
    unfold image1
    rw [Bytes.readWord_writeAt_of_disjoint]
    · exact sharesAt
    · left
      exact sharesBelow
  have balanceAt1 : Bytes.toB256
      (image1.sliceD (balanceWord * 32).toNat 32 0) = balance := by
    unfold image1
    exact Bytes.readWord_writeAt_self _ _ _

  -- Stage the credited sum.
  obtain ⟨balanceLoadPre, sharesRun, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨sharesPrefix, balanceLoadWf, balanceLoadReads, sharesState⟩ :=
    of_run_loadWordAt_image sharesStack sharesWf sharesReads sharesAt1
      sharesRun
  have sharesLogs : sharesPre.logs = balanceLoadPre.logs := by
    refine Line.of_inv Devm.logs ?_ sharesRun
    unfold ProrataWethVault.loadWord
    line_inv
  obtain ⟨addPre, balanceLoadRun, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨balanceLoadPrefix, addWf, addReads, balanceLoadState⟩ :=
    of_run_loadWordAt_image sharesPrefix balanceLoadWf balanceLoadReads
      balanceAt1 balanceLoadRun
  have balanceLoadLogs : balanceLoadPre.logs = addPre.logs := by
    refine Line.of_inv Devm.logs ?_ balanceLoadRun
    unfold ProrataWethVault.loadWord
    line_inv
  obtain ⟨creditStorePre, addRun, run⟩ := runCompiledTo_next_inv run
  have addSource := Ninst.Run.of_runCompiled addRun
  have creditPrefix : (balance + shares) :: tail <<+ creditStorePre.stack :=
    prefix_of_add addSource balanceLoadPrefix
  have addMemory : addPre.memory = creditStorePre.memory :=
    Ninst.Hinv.inv (f := Devm.memory) addSource
  have addState : addPre.state = creditStorePre.state :=
    Ninst.Hinv.inv (f := Devm.state) addSource
  have addLogs : addPre.logs = creditStorePre.logs :=
    Ninst.Hinv.inv (f := Devm.logs) addSource
  have creditStoreWf : Mem.Wf creditStorePre.memory := by
    rw [← addMemory]; exact addWf
  have creditStoreReads : Mem.Reads creditStorePre.memory image1 := by
    rw [← addMemory]; exact addReads
  obtain ⟨guardBalancePre, creditStoreRun, run⟩ :=
    runCompiledTo_prepend_inv run
  obtain ⟨guardStack, guardWf, guardReads, creditStoreState⟩ :=
    of_run_mstoreAt_image creditPrefix creditStoreWf creditStoreReads
      creditStoreRun
  have creditStoreLogs : creditStorePre.logs = guardBalancePre.logs := by
    refine Line.of_inv Devm.logs ?_ creditStoreRun
    unfold mstoreAt
    line_inv
  change Mem.Reads guardBalancePre.memory
    (inboundCreditImage image balance (balance + shares)) at guardReads
  have guardBalanceAt : Bytes.toB256
      ((inboundCreditImage image balance (balance + shares)).sliceD
        (balanceWord * 32).toNat 32 0) = balance := by
    unfold inboundCreditImage
    rw [Bytes.readWord_writeAt_of_disjoint]
    · exact Bytes.readWord_writeAt_self _ _ _
    · right
      decide +kernel
  have guardCreditAt : Bytes.toB256
      ((inboundCreditImage image balance (balance + shares)).sliceD
        (scratchWord * 32).toNat 32 0) = balance + shares := by
    unfold inboundCreditImage
    exact Bytes.readWord_writeAt_self _ _ _

  -- Reject a wrapped total.
  obtain ⟨guardCreditPre, guardBalanceRun, run⟩ :=
    runCompiledTo_prepend_inv run
  obtain ⟨guardBalancePrefix, guardCreditWf, guardCreditReads,
      guardBalanceState⟩ :=
    of_run_loadWordAt_image guardStack guardWf guardReads guardBalanceAt
      guardBalanceRun
  have guardBalanceLogs : guardBalancePre.logs = guardCreditPre.logs := by
    refine Line.of_inv Devm.logs ?_ guardBalanceRun
    unfold ProrataWethVault.loadWord
    line_inv
  obtain ⟨testPre, guardCreditRun, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨guardCreditPrefix, testWf, testReads, guardCreditState⟩ :=
    of_run_loadWordAt_image guardBalancePrefix guardCreditWf guardCreditReads
      guardCreditAt guardCreditRun
  have guardCreditLogs : guardCreditPre.logs = testPre.logs := by
    refine Line.of_inv Devm.logs ?_ guardCreditRun
    unfold ProrataWethVault.loadWord
    line_inv
  obtain ⟨branchPre, testRun, branchRun⟩ := runCompiledTo_next_inv run
  have testSource := Ninst.Run.of_runCompiled testRun
  have testPrefix := prefix_of_lt testSource guardCreditPrefix
  have testMemory : testPre.memory = branchPre.memory :=
    Ninst.Hinv.inv (f := Devm.memory) testSource
  have testState : testPre.state = branchPre.state :=
    Ninst.Hinv.inv (f := Devm.state) testSource
  have testLogs : testPre.logs = branchPre.logs :=
    Ninst.Hinv.inv (f := Devm.logs) testSource
  have noWrap : ¬ (balance + shares) < balance := by
    intro wrapped
    have onePrefix : (1 : B256) :: tail <<+ branchPre.stack := by
      simpa [B256.ltCheck, wrapped] using testPrefix
    obtain ⟨revertPre, branchWord, branchWordNe, revertPop, revertRun, -⟩ :=
      Func.RunCompiledTo.succ_branch_of_prefix
        (by decide : (1 : B256) ≠ 0) onePrefix branchRun
    obtain ⟨revertPost, impossible, -⟩ := runCompiledTo_revert_inv revertRun
    cases impossible
  have zeroPrefix : (0 : B256) :: tail <<+ branchPre.stack := by
    simpa [B256.ltCheck, noWrap] using testPrefix
  obtain ⟨bodyPre, bodyPop, bodyRun, bodyPrefix⟩ :=
    Func.RunCompiledTo.zero_branch_of_prefix zeroPrefix branchRun
  have bodyWf : Mem.Wf bodyPre.memory := by
    rw [← bodyPop.memory, ← testMemory]; exact testWf
  have bodyReads : Mem.Reads bodyPre.memory
      (inboundCreditImage image balance (balance + shares)) := by
    rw [← bodyPop.memory, ← testMemory]; exact testReads
  refine ⟨bodyPre, balance, ?_, ?_, bodyPrefix, bodyWf, bodyReads, ?_, ?_,
    bodyRun⟩
  · rw [balanceEq]
    change
      (Devm.getStor sloadPre sevm.currentTarget).get receiver =
        (Devm.getStor pre sevm.currentTarget).get receiver
    rw [funext (getStor_eq_of_state_eq receiverState)]
  · by_contra wrapped
    exact noWrap ((wordAdd_lt_left_iff balance shares).mpr (by omega))
  · exact (funext (getStor_eq_of_state_eq receiverState)).trans
      (sloadStorage.trans
        ((funext (getStor_eq_of_state_eq balanceStoreState)).trans
          ((funext (getStor_eq_of_state_eq sharesState)).trans
            ((funext (getStor_eq_of_state_eq balanceLoadState)).trans
              ((funext (getStor_eq_of_state_eq addState)).trans
                ((funext (getStor_eq_of_state_eq creditStoreState)).trans
                  ((funext (getStor_eq_of_state_eq guardBalanceState)).trans
                    ((funext (getStor_eq_of_state_eq guardCreditState)).trans
                      ((funext (getStor_eq_of_state_eq testState)).trans
                        (funext
                          (getStor_eq_of_state_eq bodyPop.state)))))))))))
  · exact receiverLogs.trans
      (sloadLogs.trans
        (balanceStoreLogs.trans
          (sharesLogs.trans
            (balanceLoadLogs.trans
              (addLogs.trans
                (creditStoreLogs.trans
                  (guardBalanceLogs.trans
                    (guardCreditLogs.trans
                      (testLogs.trans bodyPop.logs)))))))))

/-! ## Settlement: share credit, supply increase, events, and return -/

/-- The share `Transfer(0, receiver, shares)` entry emitted by a successful
inbound flow. -/
def mintTransferLog (sevm : Sevm) (receiver shares : B256) : Log :=
  ⟨sevm.currentTarget, [transferEvent, 0, receiver], shares.toBytes⟩

/-- The ERC-4626 `Deposit(caller, receiver, assets, shares)` entry. -/
def depositLogEntry (sevm : Sevm) (receiver assets shares : B256) : Log :=
  ⟨sevm.currentTarget, [depositEvent, sevm.caller.toB256, receiver],
    assets.toBytes ++ shares.toBytes⟩

private theorem sstore_getStor_of_ne
    {sevm : Sevm} {s s' : Devm} {account : Adr}
    (run : Ninst.Run sevm s Ninst.sstore s')
    (ne : sevm.currentTarget ≠ account) :
    Devm.getStor s' account = Devm.getStor s account := by
  obtain ⟨pc, registerRun⟩ := of_run_reg run
  exact sstore_preserves_getStor_ne registerRun ne

/-- The inbound settlement tail writes the credited receiver row and the
increased share supply, emits the share `Transfer` and ERC-4626 `Deposit`
events in that order, and returns the quoted word.  No other account's
storage moves. -/
theorem inboundSettle_trace
    {fs : List Func} {sevm : Sevm} {pre final : Devm}
    {image : Bytes} {sharesWord assetsSourceWord returnedWord : B256}
    {receiver shares assets returned supply credited : B256} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (creditedAt : Bytes.toB256
      (image.sliceD (scratchWord * 32).toNat 32 0) = credited)
    (receiverAt : Bytes.toB256
      (image.sliceD (receiverWord * 32).toNat 32 0) = receiver)
    (supplyAt : Bytes.toB256
      (image.sliceD (supplyWord * 32).toNat 32 0) = supply)
    (sharesAt : Bytes.toB256
      (image.sliceD (sharesWord * 32).toNat 32 0) = shares)
    (assetsAt : Bytes.toB256
      (image.sliceD (assetsSourceWord * 32).toNat 32 0) = assets)
    (returnedAt : Bytes.toB256
      (image.sliceD (returnedWord * 32).toNat 32 0) = returned)
    (sharesAbove : 64 ≤ (sharesWord * 32).toNat)
    (assetsAbove : 64 ≤ (assetsSourceWord * 32).toNat)
    (returnedAbove : 64 ≤ (returnedWord * 32).toNat)
    (stack : tail <<+ pre.stack)
    (run : Func.RunCompiledTo fs sevm pre
      (loadWord scratchWord +++ loadWord receiverWord +++ sstore :::
        loadWord sharesWord +++ loadWord supplyWord +++ add :::
        pushSupplySlot +++ sstore :::
        logMintTransfer (loadWord sharesWord) +++
        logDeposit (loadWord assetsSourceWord) (loadWord sharesWord) +++
        loadWord returnedWord +++ returnWord) (.ok final)) :
    ReturnsWord returned final ∧
      Devm.getStor final sevm.currentTarget =
        ((Devm.getStor pre sevm.currentTarget).set receiver credited).set
          supplySlot (supply + shares) ∧
      (∀ account, sevm.currentTarget ≠ account →
        Devm.getStor final account = Devm.getStor pre account) ∧
      final.logs = pre.logs ++
        [mintTransferLog sevm receiver shares,
          depositLogEntry sevm receiver assets shares] := by
  -- Credit the receiver's share row.
  obtain ⟨receiverPre, creditedRun, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨creditedPrefix, receiverWf, receiverReads, creditedState⟩ :=
    of_run_loadWordAt_image stack memoryWf memoryReads creditedAt creditedRun
  have creditedLogs : pre.logs = receiverPre.logs := by
    refine Line.of_inv Devm.logs ?_ creditedRun
    unfold ProrataWethVault.loadWord
    line_inv
  obtain ⟨creditStorePre, receiverRun, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨receiverPrefix, creditStoreWf, creditStoreReads, receiverState⟩ :=
    of_run_loadWordAt_image creditedPrefix receiverWf receiverReads
      receiverAt receiverRun
  have receiverLogs : receiverPre.logs = creditStorePre.logs := by
    refine Line.of_inv Devm.logs ?_ receiverRun
    unfold ProrataWethVault.loadWord
    line_inv
  obtain ⟨sharesPre, creditStoreRun, run⟩ := runCompiledTo_next_inv run
  have creditStoreSource := Ninst.Run.of_runCompiled creditStoreRun
  have creditStoreSet :
      Devm.getStor sharesPre sevm.currentTarget =
        (Devm.getStor creditStorePre sevm.currentTarget).set receiver
          credited :=
    sstore_getStor_set creditStoreSource receiverPrefix
  have sharesStack : tail <<+ sharesPre.stack :=
    prefix_of_sstore creditStoreSource receiverPrefix
  have creditStoreMemory : creditStorePre.memory = sharesPre.memory :=
    Ninst.Hinv.inv (f := Devm.memory) creditStoreSource
  have creditStoreLogs : creditStorePre.logs = sharesPre.logs :=
    Ninst.Hinv.inv (f := Devm.logs) creditStoreSource
  have sharesWf : Mem.Wf sharesPre.memory := by
    rw [← creditStoreMemory]; exact creditStoreWf
  have sharesReads : Mem.Reads sharesPre.memory image := by
    rw [← creditStoreMemory]; exact creditStoreReads

  -- Increase the share supply.
  obtain ⟨supplyPre, sharesRun, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨sharesPrefix, supplyWf, supplyReads, sharesState⟩ :=
    of_run_loadWordAt_image sharesStack sharesWf sharesReads sharesAt
      sharesRun
  have sharesLogs : sharesPre.logs = supplyPre.logs := by
    refine Line.of_inv Devm.logs ?_ sharesRun
    unfold ProrataWethVault.loadWord
    line_inv
  obtain ⟨addPre, supplyRun, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨supplyPrefix, addWf, addReads, supplyState⟩ :=
    of_run_loadWordAt_image sharesPrefix supplyWf supplyReads supplyAt
      supplyRun
  have supplyLogs : supplyPre.logs = addPre.logs := by
    refine Line.of_inv Devm.logs ?_ supplyRun
    unfold ProrataWethVault.loadWord
    line_inv
  obtain ⟨slotPre, addRun, run⟩ := runCompiledTo_next_inv run
  have addSource := Ninst.Run.of_runCompiled addRun
  have sumPrefix : (supply + shares) :: tail <<+ slotPre.stack := by
    simpa only [B256.add_comm] using prefix_of_add addSource supplyPrefix
  have addMemory : addPre.memory = slotPre.memory :=
    Ninst.Hinv.inv (f := Devm.memory) addSource
  have addState : addPre.state = slotPre.state :=
    Ninst.Hinv.inv (f := Devm.state) addSource
  have addLogs : addPre.logs = slotPre.logs :=
    Ninst.Hinv.inv (f := Devm.logs) addSource
  have slotWf : Mem.Wf slotPre.memory := by rw [← addMemory]; exact addWf
  have slotReads : Mem.Reads slotPre.memory image := by
    rw [← addMemory]; exact addReads
  obtain ⟨supplyStorePre, slotRun, run⟩ := runCompiledTo_prepend_inv run
  simp only [pushSupplySlot] at slotRun
  rcases Line.of_run_cons slotRun with ⟨notPre, zeroRun, slotRun'⟩
  rcases Line.of_run_cons slotRun' with ⟨notPost, notRun, slotNil⟩
  cases slotNil
  have zeroPrefix : (0 : B256) :: (supply + shares) :: tail <<+ notPre.stack :=
    prefix_of_push (of_run_pushB256 zeroRun) sumPrefix
  have slotPrefix :
      supplySlot :: (supply + shares) :: tail <<+ supplyStorePre.stack := by
    have rawPrefix := prefix_of_not notRun zeroPrefix
    have notZero : ~~~(0 : B256) = B256.max := by decide +kernel
    unfold supplySlot
    rw [← notZero]
    exact rawPrefix
  have slotLineRun : Line.Run sevm slotPre [pushB256 0, Ninst.not]
      supplyStorePre :=
    Line.Run.cons zeroRun (Line.Run.cons notRun Line.Run.nil)
  have slotState : slotPre.state = supplyStorePre.state :=
    Line.of_inv Devm.state (by line_inv) slotLineRun
  have slotMemory : slotPre.memory = supplyStorePre.memory :=
    Line.of_inv Devm.memory (by line_inv) slotLineRun
  have slotLogs : slotPre.logs = supplyStorePre.logs :=
    Line.of_inv Devm.logs (by line_inv) slotLineRun
  have supplyStoreWf : Mem.Wf supplyStorePre.memory := by
    rw [← slotMemory]; exact slotWf
  have supplyStoreReads : Mem.Reads supplyStorePre.memory image := by
    rw [← slotMemory]; exact slotReads
  obtain ⟨logPre, supplyStoreRun, run⟩ := runCompiledTo_next_inv run
  have supplyStoreSource := Ninst.Run.of_runCompiled supplyStoreRun
  have supplyStoreSet :
      Devm.getStor logPre sevm.currentTarget =
        (Devm.getStor supplyStorePre sevm.currentTarget).set supplySlot
          (supply + shares) :=
    sstore_getStor_set supplyStoreSource slotPrefix
  have logStack : tail <<+ logPre.stack :=
    prefix_of_sstore supplyStoreSource slotPrefix
  have supplyStoreMemory : supplyStorePre.memory = logPre.memory :=
    Ninst.Hinv.inv (f := Devm.memory) supplyStoreSource
  have supplyStoreLogs : supplyStorePre.logs = logPre.logs :=
    Ninst.Hinv.inv (f := Devm.logs) supplyStoreSource
  have logWf : Mem.Wf logPre.memory := by
    rw [← supplyStoreMemory]; exact supplyStoreWf
  have logReads : Mem.Reads logPre.memory image := by
    rw [← supplyStoreMemory]; exact supplyStoreReads

  -- Emit the share `Transfer(0, receiver, shares)` event.
  obtain ⟨depositLogPre, mintLogRun, run⟩ := runCompiledTo_prepend_inv run
  have mintLogStorage :
      Devm.getStor logPre = Devm.getStor depositLogPre := by
    refine Line.of_inv Devm.getStor ?_ mintLogRun
    unfold logMintTransfer ProrataWethVault.loadWord mstoreAt logWith
    line_inv
  simp only [logMintTransfer, List.append_assoc] at mintLogRun
  rcases of_run_append (loadWord sharesWord) mintLogRun with
    ⟨mintStorePre, mintSharesRun, mintLogRun⟩
  obtain ⟨mintSharesPrefix, mintStoreWf, mintStoreReads, -⟩ :=
    of_run_loadWordAt_image logStack logWf logReads sharesAt mintSharesRun
  have mintSharesLogs : logPre.logs = mintStorePre.logs := by
    refine Line.of_inv Devm.logs ?_ mintSharesRun
    unfold ProrataWethVault.loadWord
    line_inv
  rcases of_run_append (mstoreAt 0) mintLogRun with
    ⟨mintReceiverPre, mintStoreRun, mintLogRun⟩
  obtain ⟨mintReceiverStack, mintReceiverWf, mintReceiverReads,
      mintStoreState⟩ :=
    of_run_mstoreAt_image mintSharesPrefix mintStoreWf mintStoreReads
      mintStoreRun
  have mintStoreLogs : mintStorePre.logs = mintReceiverPre.logs := by
    refine Line.of_inv Devm.logs ?_ mintStoreRun
    unfold mstoreAt
    line_inv
  let sharesImage := Bytes.writeAt image ((0 : B256) * 32).toNat
    shares.toBytes
  change Mem.Reads mintReceiverPre.memory sharesImage at mintReceiverReads
  have receiverAtShares : Bytes.toB256
      (sharesImage.sliceD (receiverWord * 32).toNat 32 0) = receiver := by
    unfold sharesImage
    rw [Bytes.readWord_writeAt_of_disjoint]
    · exact receiverAt
    · right
      decide +kernel
  have mintData :
      (mintReceiverPre.memory.read 0 32).1 = shares.toBytes := by
    rw [Mem.Reads.read mintReceiverReads 0 32,
      show (32 : Nat) = shares.toBytes.length from
        (B256.length_toBytes shares).symm]
    exact Bytes.sliceD_writeAt image shares.toBytes 0
  rcases of_run_append (loadWord receiverWord) mintLogRun with
    ⟨mintZeroPre, mintReceiverRun, mintLogRun⟩
  obtain ⟨mintReceiverPrefix, mintZeroWf, mintZeroReads, -⟩ :=
    of_run_loadWordAt_image mintReceiverStack mintReceiverWf
      mintReceiverReads receiverAtShares mintReceiverRun
  have mintReceiverLogs : mintReceiverPre.logs = mintZeroPre.logs := by
    refine Line.of_inv Devm.logs ?_ mintReceiverRun
    unfold ProrataWethVault.loadWord
    line_inv
  rcases Line.of_run_cons mintLogRun with ⟨mintEventPre, mintZeroRun,
    mintLogRun⟩
  rcases Line.of_run_cons mintLogRun with ⟨mintEmitPre, mintEventRun,
    mintLogRun⟩
  have mintZeroPush := of_run_pushB256 mintZeroRun
  have mintEventPush := of_run_pushB256 mintEventRun
  have mintEmitPrefix :
      transferEvent :: 0 :: receiver :: tail <<+ mintEmitPre.stack :=
    prefix_of_push mintEventPush (prefix_of_push mintZeroPush
      mintReceiverPrefix)
  have mintEmitMemory : mintZeroPre.memory = mintEmitPre.memory :=
    mintZeroPush.memory.trans mintEventPush.memory
  have mintEmitLogs : mintZeroPre.logs = mintEmitPre.logs :=
    mintZeroPush.logs.trans mintEventPush.logs
  have mintEmitWf : Mem.Wf mintEmitPre.memory := by
    rw [← mintEmitMemory]
    exact mintZeroWf
  have mintEmitReads : Mem.Reads mintEmitPre.memory sharesImage := by
    rw [← mintEmitMemory]
    exact mintZeroReads
  have mintEmitData :
      (mintEmitPre.memory.read 0 32).1 = shares.toBytes := by
    rw [Mem.Reads.read mintEmitReads 0 32,
      show (32 : Nat) = shares.toBytes.length from
        (B256.length_toBytes shares).symm]
    exact Bytes.sliceD_writeAt image shares.toBytes 0
  obtain ⟨mintEmitStack, mintEmitted⟩ :=
    of_logWith201_val mintEmitPrefix mintLogRun
  obtain ⟨depositLogWf, depositLogReads⟩ :=
    of_logWith_image mintEmitWf mintEmitReads mintLogRun
  have mintLogged :
      depositLogPre.logs =
        logPre.logs ++ [mintTransferLog sevm receiver shares] := by
    rw [mintEmitted, mintEmitData, ← mintEmitLogs, ← mintReceiverLogs,
      ← mintStoreLogs, ← mintSharesLogs]
    rfl

  -- Emit the ERC-4626 `Deposit(caller, receiver, assets, shares)` event.
  obtain ⟨returnLoadPre, depositRunLine, run⟩ := runCompiledTo_prepend_inv run
  have depositLogStorage :
      Devm.getStor depositLogPre = Devm.getStor returnLoadPre := by
    refine Line.of_inv Devm.getStor ?_ depositRunLine
    unfold logDeposit ProrataWethVault.loadWord mstoreAt logWith
    line_inv
  simp only [logDeposit, List.append_assoc] at depositRunLine
  have zeroOffset : ((0 : B256) * 32).toNat = 0 := by decide +kernel
  have oneOffset : ((1 : B256) * 32).toNat = 32 := by decide +kernel
  have assetsAtShares : Bytes.toB256
      (sharesImage.sliceD (assetsSourceWord * 32).toNat 32 0) = assets := by
    unfold sharesImage
    rw [Bytes.readWord_writeAt_of_disjoint]
    · exact assetsAt
    · right
      omega
  rcases of_run_append (loadWord assetsSourceWord) depositRunLine with
    ⟨depositAssetStorePre, depositAssetsRun, depositRunLine⟩
  obtain ⟨depositAssetsPrefix, depositAssetStoreWf, depositAssetStoreReads,
      -⟩ :=
    of_run_loadWordAt_image mintEmitStack depositLogWf depositLogReads
      assetsAtShares depositAssetsRun
  have depositAssetsLogs : depositLogPre.logs = depositAssetStorePre.logs := by
    refine Line.of_inv Devm.logs ?_ depositAssetsRun
    unfold ProrataWethVault.loadWord
    line_inv
  rcases of_run_append (mstoreAt 0) depositRunLine with
    ⟨depositSharesPre, depositAssetStoreRun, depositRunLine⟩
  obtain ⟨depositSharesStack, depositSharesWf, depositSharesReads,
      depositAssetStoreState⟩ :=
    of_run_mstoreAt_image depositAssetsPrefix depositAssetStoreWf
      depositAssetStoreReads depositAssetStoreRun
  have depositAssetStoreLogs :
      depositAssetStorePre.logs = depositSharesPre.logs := by
    refine Line.of_inv Devm.logs ?_ depositAssetStoreRun
    unfold mstoreAt
    line_inv
  rw [zeroOffset] at depositSharesReads
  have sharesAtAssets : Bytes.toB256
      ((Bytes.writeAt sharesImage 0 assets.toBytes).sliceD
        (sharesWord * 32).toNat 32 0) = shares := by
    rw [Bytes.readWord_writeAt_of_disjoint]
    · unfold sharesImage
      rw [Bytes.readWord_writeAt_of_disjoint]
      · exact sharesAt
      · right
        omega
    · right
      omega
  rcases of_run_append (loadWord sharesWord) depositRunLine with
    ⟨depositShareStorePre, depositSharesRun, depositRunLine⟩
  obtain ⟨depositSharesPrefix, depositShareStoreWf, depositShareStoreReads,
      -⟩ :=
    of_run_loadWordAt_image depositSharesStack depositSharesWf
      depositSharesReads sharesAtAssets depositSharesRun
  have depositSharesLogs :
      depositSharesPre.logs = depositShareStorePre.logs := by
    refine Line.of_inv Devm.logs ?_ depositSharesRun
    unfold ProrataWethVault.loadWord
    line_inv
  rcases of_run_append (mstoreAt 1) depositRunLine with
    ⟨depositReceiverPre, depositShareStoreRun, depositRunLine⟩
  obtain ⟨depositReceiverStack, depositReceiverWf, depositReceiverReads,
      depositShareStoreState⟩ :=
    of_run_mstoreAt_image depositSharesPrefix depositShareStoreWf
      depositShareStoreReads depositShareStoreRun
  have depositShareStoreLogs :
      depositShareStorePre.logs = depositReceiverPre.logs := by
    refine Line.of_inv Devm.logs ?_ depositShareStoreRun
    unfold mstoreAt
    line_inv
  rw [oneOffset] at depositReceiverReads
  let depositImage :=
    Bytes.writeAt (Bytes.writeAt sharesImage 0 assets.toBytes) 32
      shares.toBytes
  have depositImageReads :
      Mem.Reads depositReceiverPre.memory depositImage :=
    depositReceiverReads
  have receiverAtDeposit : Bytes.toB256
      (depositImage.sliceD (receiverWord * 32).toNat 32 0) = receiver := by
    unfold depositImage
    rw [Bytes.readWord_writeAt_of_disjoint]
    · rw [Bytes.readWord_writeAt_of_disjoint]
      · exact receiverAtShares
      · right
        decide +kernel
    · right
      decide +kernel
  rcases of_run_append (loadWord receiverWord) depositRunLine with
    ⟨depositCallerPre, depositReceiverRun, depositRunLine⟩
  obtain ⟨depositReceiverPrefix, depositCallerWf, depositCallerReads, -⟩ :=
    of_run_loadWordAt_image depositReceiverStack depositReceiverWf
      depositImageReads receiverAtDeposit depositReceiverRun
  have depositReceiverLogs :
      depositReceiverPre.logs = depositCallerPre.logs := by
    refine Line.of_inv Devm.logs ?_ depositReceiverRun
    unfold ProrataWethVault.loadWord
    line_inv
  rcases Line.of_run_cons depositRunLine with
    ⟨depositEventPre, depositCallerRun, depositRunLine⟩
  rcases Line.of_run_cons depositRunLine with
    ⟨depositEmitPre, depositEventRun, depositRunLine⟩
  have depositCallerPush := of_run_caller depositCallerRun
  have depositEventPush := of_run_pushB256 depositEventRun
  have depositEmitPrefix :
      depositEvent :: sevm.caller.toB256 :: receiver :: tail <<+
        depositEmitPre.stack :=
    prefix_of_push depositEventPush
      (prefix_of_push depositCallerPush depositReceiverPrefix)
  have depositEmitMemory :
      depositCallerPre.memory = depositEmitPre.memory :=
    depositCallerPush.memory.trans depositEventPush.memory
  have depositEmitLogs : depositCallerPre.logs = depositEmitPre.logs :=
    depositCallerPush.logs.trans depositEventPush.logs
  have depositEmitReads :
      Mem.Reads depositEmitPre.memory depositImage := by
    rw [← depositEmitMemory]
    exact depositCallerReads
  have depositEmitData :
      (depositEmitPre.memory.read 0 64).1 =
        assets.toBytes ++ shares.toBytes := by
    rw [Mem.Reads.read depositEmitReads 0 64]
    exact Bytes.read_two_word_writes_at sharesImage 0 assets shares
  obtain ⟨returnLoadStack, depositEmitted⟩ :=
    of_logWith_val (k := 2) (topics := [depositEvent, sevm.caller.toB256,
      receiver]) rfl depositEmitPrefix depositRunLine
  have depositLogged :
      returnLoadPre.logs =
        depositLogPre.logs ++
          [depositLogEntry sevm receiver assets shares] := by
    rw [depositEmitted, zeroOffset, show ((2 : B256) * 32).toNat = 64 from by
        decide +kernel, depositEmitData, ← depositEmitLogs,
      ← depositReceiverLogs, ← depositShareStoreLogs, ← depositSharesLogs,
      ← depositAssetStoreLogs, ← depositAssetsLogs]
    rfl
  obtain ⟨returnLoadWf, returnLoadReads⟩ :=
    of_logWith_image (by
      rw [← depositEmitMemory]
      exact depositCallerWf) depositEmitReads depositRunLine

  -- Return the quoted word.
  have returnedAtDeposit : Bytes.toB256
      (depositImage.sliceD (returnedWord * 32).toNat 32 0) = returned := by
    unfold depositImage
    rw [Bytes.readWord_writeAt_of_disjoint]
    · unfold sharesImage
      rw [Bytes.readWord_writeAt_of_disjoint]
      · rw [Bytes.readWord_writeAt_of_disjoint]
        · exact returnedAt
        · right
          omega
      · right
        omega
    · right
      omega
  obtain ⟨returnPre, returnedRun, returnRun⟩ := runCompiledTo_prepend_inv run
  obtain ⟨returnedPrefix, -, -, -⟩ :=
    of_run_loadWordAt_image returnLoadStack returnLoadWf returnLoadReads
      returnedAtDeposit returnedRun
  have returnedLogs : returnLoadPre.logs = returnPre.logs := by
    refine Line.of_inv Devm.logs ?_ returnedRun
    unfold ProrataWethVault.loadWord
    line_inv
  have returnedStorage :
      Devm.getStor returnLoadPre = Devm.getStor returnPre := by
    refine Line.of_inv Devm.getStor ?_ returnedRun
    unfold ProrataWethVault.loadWord
    line_inv
  have returnStorage : Devm.getStor returnPre = Devm.getStor final := by
    refine (show Func.CompiledInv fs Devm.getStor Devm.getStor returnWord from
      ?_) returnRun
    unfold returnWord
    compiled_inv
  have returnLogs : returnPre.logs = final.logs := by
    refine (show Func.CompiledInv fs Devm.logs Devm.logs returnWord from
      ?_) returnRun
    unfold returnWord
    compiled_inv
  have returned := returnWord_trace returnedPrefix returnRun

  -- Assemble the exact settlement effect.
  have entryStorage : Devm.getStor pre = Devm.getStor creditStorePre :=
    (funext (getStor_eq_of_state_eq creditedState)).trans
      (funext (getStor_eq_of_state_eq receiverState))
  have middleStorage :
      Devm.getStor sharesPre = Devm.getStor supplyStorePre :=
    (funext (getStor_eq_of_state_eq sharesState)).trans
      ((funext (getStor_eq_of_state_eq supplyState)).trans
        ((funext (getStor_eq_of_state_eq addState)).trans
          (funext (getStor_eq_of_state_eq slotState))))
  have exitStorage : Devm.getStor logPre = Devm.getStor final :=
    mintLogStorage.trans
      (depositLogStorage.trans (returnedStorage.trans returnStorage))
  refine ⟨returned, ?_, ?_, ?_⟩
  · rw [← exitStorage, supplyStoreSet, ← middleStorage, creditStoreSet,
      ← entryStorage]
  · intro account accountNe
    rw [← exitStorage, sstore_getStor_of_ne supplyStoreSource accountNe,
      ← congrFun middleStorage account,
      sstore_getStor_of_ne creditStoreSource accountNe,
      ← congrFun entryStorage account]
  · have entryLogs : pre.logs = logPre.logs :=
      creditedLogs.trans
        (receiverLogs.trans
          (creditStoreLogs.trans
            (sharesLogs.trans
              (supplyLogs.trans
                (addLogs.trans (slotLogs.trans supplyStoreLogs))))))
    rw [← returnLogs, ← returnedLogs, depositLogged, mintLogged,
      List.append_assoc, ← entryLogs]
    rfl

/-! ## The complete post-child inbound tail -/

/-- Exact effect of the whole inbound tail that follows a settled WETH
`transferFrom` child.  The receiver's share row is credited by the quoted
amount without wrapping, the share supply increases by the same amount, the
share `Transfer` and ERC-4626 `Deposit` events are appended in that order, and
the quoted word is returned.  No other account's storage moves.

The three word parameters are the exact operation words each flow supplies:
`deposit` settles `(quote, amount, quote)` and `mint` settles
`(amount, quote, quote)`.  Both lie above the arithmetic scratch region and
below the staged balance word, which is what the offset premises record. -/
theorem inboundTail_effect
    {fs : List Func} {sevm : Sevm} {pre final : Devm}
    {image : Bytes} {sharesWord assetsSourceWord returnedWord : B256}
    {receiver shares assets returned supply : B256} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (receiverAt : Bytes.toB256
      (image.sliceD (receiverWord * 32).toNat 32 0) = receiver)
    (supplyAt : Bytes.toB256
      (image.sliceD (supplyWord * 32).toNat 32 0) = supply)
    (sharesAt : Bytes.toB256
      (image.sliceD (sharesWord * 32).toNat 32 0) = shares)
    (assetsAt : Bytes.toB256
      (image.sliceD (assetsSourceWord * 32).toNat 32 0) = assets)
    (returnedAt : Bytes.toB256
      (image.sliceD (returnedWord * 32).toNat 32 0) = returned)
    (sharesAbove : arithmeticScratchEnd ≤ (sharesWord * 32).toNat)
    (sharesBelow : (sharesWord * 32).toNat + 32 ≤ (balanceWord * 32).toNat)
    (assetsAbove : arithmeticScratchEnd ≤ (assetsSourceWord * 32).toNat)
    (assetsBelow :
      (assetsSourceWord * 32).toNat + 32 ≤ (balanceWord * 32).toNat)
    (returnedAbove : arithmeticScratchEnd ≤ (returnedWord * 32).toNat)
    (returnedBelow :
      (returnedWord * 32).toNat + 32 ≤ (balanceWord * 32).toNat)
    (stack : tail <<+ pre.stack)
    (run : Func.RunCompiledTo fs sevm pre
      (loadWord receiverWord +++ sload ::: mstoreAt balanceWord +++
        loadWord sharesWord +++ loadWord balanceWord +++ add :::
        mstoreAt scratchWord +++
        loadWord balanceWord +++ loadWord scratchWord +++ lt :::
        (Func.revert <?>
          (loadWord scratchWord +++ loadWord receiverWord +++ sstore :::
            loadWord sharesWord +++ loadWord supplyWord +++ add :::
            pushSupplySlot +++ sstore :::
            logMintTransfer (loadWord sharesWord) +++
            logDeposit (loadWord assetsSourceWord) (loadWord sharesWord) +++
            loadWord returnedWord +++ returnWord))) (.ok final)) :
    ∃ balance,
      balance = Devm.getStorVal pre sevm.currentTarget receiver ∧
      balance.toNat + shares.toNat < wordModulusN ∧
      ReturnsWord returned final ∧
      Devm.getStor final sevm.currentTarget =
        ((Devm.getStor pre sevm.currentTarget).set receiver
          (balance + shares)).set supplySlot (supply + shares) ∧
      (∀ account, sevm.currentTarget ≠ account →
        Devm.getStor final account = Devm.getStor pre account) ∧
      final.logs = pre.logs ++
        [mintTransferLog sevm receiver shares,
          depositLogEntry sevm receiver assets shares] := by
  have scratchEnd : arithmeticScratchEnd = (scratchWord * 32).toNat + 96 := by
    decide +kernel
  obtain ⟨settlePre, balance, balanceEq, noWrap, settleStack, settleWf,
      settleReads, creditStorage, creditLogs, settleRun⟩ :=
    inboundCredit_trace memoryWf memoryReads receiverAt sharesAt sharesBelow
      stack run
  -- Every operation word the settlement reads survives the two staging
  -- writes, which land at the balance and arithmetic scratch words.
  have transport : ∀ (word value : B256),
      Bytes.toB256 (image.sliceD (word * 32).toNat 32 0) = value →
      (scratchWord * 32).toNat + 32 ≤ (word * 32).toNat →
      (word * 32).toNat + 32 ≤ (balanceWord * 32).toNat →
      Bytes.toB256
          ((inboundCreditImage image balance (balance + shares)).sliceD
            (word * 32).toNat 32 0) = value := by
    intro word value valueAt aboveScratch belowBalance
    unfold inboundCreditImage
    rw [Bytes.readWord_writeAt_of_disjoint]
    · rw [Bytes.readWord_writeAt_of_disjoint]
      · exact valueAt
      · left
        exact belowBalance
    · right
      exact aboveScratch
  have creditedAt : Bytes.toB256
      ((inboundCreditImage image balance (balance + shares)).sliceD
        (scratchWord * 32).toNat 32 0) = balance + shares := by
    unfold inboundCreditImage
    exact Bytes.readWord_writeAt_self _ _ _
  obtain ⟨returned', storageSet, storageFrame, logged⟩ :=
    inboundSettle_trace settleWf settleReads creditedAt
      (transport receiverWord receiver receiverAt (by decide +kernel)
        (by decide +kernel))
      (transport supplyWord supply supplyAt (by decide +kernel)
        (by decide +kernel))
      (transport sharesWord shares sharesAt (by omega) sharesBelow)
      (transport assetsSourceWord assets assetsAt (by omega) assetsBelow)
      (transport returnedWord returned returnedAt (by omega) returnedBelow)
      (by omega) (by omega) (by omega) settleStack settleRun
  refine ⟨balance, balanceEq, noWrap, returned', ?_, ?_, ?_⟩
  · rw [storageSet, ← congrFun creditStorage sevm.currentTarget]
  · intro account accountNe
    rw [storageFrame account accountNe, ← congrFun creditStorage account]
  · rw [logged, ← creditLogs]

/-! ## Source shapes

These definitional pins tie the inlined program fragments used above to the
actual `Blanc/ProrataWethVault.lean` definitions, so a later edit to the
compiled surface cannot silently leave the seams above proving something the
vault no longer does. -/

theorem depositAfterQuote_shape :
    depositAfterQuote =
      mstoreAt quoteWord +++
        nonzeroCaller (nonzeroStagedAddress receiverWord
          (finishInbound (loadWord quoteWord) (loadWord amountWord)
            (loadWord quoteWord))) := rfl

theorem mintAfterQuote_shape :
    mintAfterQuote =
      mstoreAt quoteWord +++
        nonzeroCaller (nonzeroStagedAddress receiverWord
          (finishInbound (loadWord amountWord) (loadWord quoteWord)
            (loadWord quoteWord))) := rfl

theorem finishInbound_shape (sharesWord assetsSourceWord returnedWord : B256) :
    finishInbound (loadWord sharesWord) (loadWord assetsSourceWord)
        (loadWord returnedWord) =
      (loadWord sharesWord +++ shareRoom +++ lt :::
        (Func.revert <?>
          callWethTransferFrom (loadWord assetsSourceWord)
            (loadWord receiverWord +++ sload ::: mstoreAt balanceWord +++
              loadWord sharesWord +++ loadWord balanceWord +++ add :::
              mstoreAt scratchWord +++
              loadWord balanceWord +++ loadWord scratchWord +++ lt :::
              (Func.revert <?>
                (loadWord scratchWord +++ loadWord receiverWord +++
                  sstore :::
                  loadWord sharesWord +++ loadWord supplyWord +++ add :::
                  pushSupplySlot +++ sstore :::
                  logMintTransfer (loadWord sharesWord) +++
                  logDeposit (loadWord assetsSourceWord)
                    (loadWord sharesWord) +++
                  loadWord returnedWord +++ returnWord))))) := rfl

theorem deposit_shape :
    deposit =
      arg 0 +++ mstoreAt amountWord +++
        arg 1 +++ mstoreAt receiverWord +++
        (readTotalAssets <|
          mstoreAt assetsWord +++
            pushSupplySlot +++ sload ::: mstoreAt supplyWord +++
            guardStableSupply
              (loadWord assetsWord +++ isMax +++
                (productOverTwoPow256 (loadWord amountWord) stagedDenominator
                    .down depositAfterQuoteSlot <?>
                  mulDiv (loadWord amountWord) stagedDenominator
                    stagedAssetFactor .down depositAfterQuoteSlot))) := rfl

theorem mint_shape :
    mint =
      arg 0 +++ mstoreAt amountWord +++
        arg 1 +++ mstoreAt receiverWord +++
        (readTotalAssets <|
          mstoreAt assetsWord +++
            pushSupplySlot +++ sload ::: mstoreAt supplyWord +++
            guardStableSupply
              (loadWord assetsWord +++ isMax +++
                (shiftedDiv (loadWord amountWord) stagedDenominator .up
                    mintAfterQuoteSlot <?>
                  mulDiv (loadWord amountWord) stagedAssetFactor
                    stagedDenominator .up mintAfterQuoteSlot))) := rfl

/-- The three operation words each inbound flow settles with satisfy the
offset premises of `inboundTail_effect`. -/
theorem inboundSettlementWords_bounds :
    arithmeticScratchEnd ≤ (quoteWord * 32).toNat ∧
      (quoteWord * 32).toNat + 32 ≤ (balanceWord * 32).toNat ∧
      arithmeticScratchEnd ≤ (amountWord * 32).toNat ∧
      (amountWord * 32).toNat + 32 ≤ (balanceWord * 32).toNat := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

end ProrataWethVault

end Blanc
