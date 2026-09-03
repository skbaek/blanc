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
      Func.RunCompiledTo fs sevm bodyPre body (.ok final) := by
  obtain ⟨receiverPre, receiverStack, receiverWf, receiverReads,
      amountState, run⟩ :=
    ProducesWord.store_trace (ProducesWord.arg sevm image 0) memoryWf
      memoryReads stack run
  obtain ⟨bodyPre, bodyStack, bodyWf, bodyReads, receiverState, bodyRun⟩ :=
    ProducesWord.store_trace
      (ProducesWord.arg sevm
        (Bytes.writeAt image (amountWord * 32).toNat
          (Sevm.argWord sevm 0).toBytes) 1)
      receiverWf receiverReads receiverStack run
  exact ⟨bodyPre, bodyStack, bodyWf, bodyReads,
    amountState.trans receiverState, bodyRun⟩

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
        Func.RunCompiledTo fs sevm bodyPre depositAfterQuote (.ok final) := by
  rcases ProducesWord.isMax_arm_trace
      (ProducesWord.loadWord assetsAt) memoryWf memoryReads stack run with
    maxArm | ordinaryArm
  · rcases maxArm with
      ⟨assetsMax, bodyPre, bodyStack, bodyWf, bodyReads, bodyRun⟩
    let denominator := Nat.toB256 (denominatorN supply.toNat)
    obtain ⟨quotientFits, quotePre, quoteStack, quoteImage, quoteRun⟩ :=
      productOverTwoPow256_down_image_trace bodyWf bodyReads
        (ProducesWord.loadWord amountAt)
        (ProducesWord.stagedDenominator_after_productScratch supplyAt)
        bodyStack lookup bodyRun
    refine ⟨?_, quotePre,
      productOverTwoPow256TraceImage image amount denominator, ?_, quoteImage,
      productOverTwoPow256TraceImage_wordFrame image amount denominator,
      quoteRun⟩
    · simpa [convertToSharesN, denominator, assetsMax, maxWord_toNat,
        assetFactorN_maxWord, stagedDenominator_toNat stable] using
        quotientFits
    · simpa [convertToSharesN, denominator, assetsMax, maxWord_toNat,
        assetFactorN_maxWord, stagedDenominator_toNat stable] using
        quoteStack
  · rcases ordinaryArm with
      ⟨assetsNotMax, bodyPre, bodyStack, bodyWf, bodyReads, bodyRun⟩
    obtain ⟨quotientFits, quotePre, quoteImage, quoteStack, quoteMemImage,
        quoteFrame, quoteRun⟩ :=
      mulDiv_down_image_trace bodyWf bodyReads
        (ProducesWord.stagedAssetFactor assetsAt)
        (ProducesWord.amount_after_denominatorScratch amountAt)
        (ProducesWord.stagedDenominator_after_mulDivScratch supplyAt)
        bodyStack lookup bodyRun
    refine ⟨?_, quotePre, quoteImage, ?_, quoteMemImage, quoteFrame,
      quoteRun⟩
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
        Func.RunCompiledTo fs sevm bodyPre mintAfterQuote (.ok final) := by
  rcases ProducesWord.isMax_arm_trace
      (ProducesWord.loadWord assetsAt) memoryWf memoryReads stack run with
    maxArm | ordinaryArm
  · rcases maxArm with
      ⟨assetsMax, bodyPre, bodyStack, bodyWf, bodyReads, bodyRun⟩
    obtain ⟨ceilingFits, quotePre, quoteImage, quoteStack, quoteMemImage,
        quoteFrame, quoteRun⟩ :=
      shiftedDiv_up_image_trace bodyWf bodyReads
        (ProducesWord.loadWord amountAt)
        (ProducesWord.stagedDenominator_after_shiftedScratch supplyAt)
        bodyStack lookup bodyRun
    refine ⟨?_, quotePre, quoteImage, ?_, quoteMemImage, quoteFrame,
      quoteRun⟩
    · simpa [previewMintN, assetsMax, maxWord_toNat, assetFactorN_maxWord,
        stagedDenominator_toNat stable] using ceilingFits
    · simpa [previewMintN, assetsMax, maxWord_toNat, assetFactorN_maxWord,
        stagedDenominator_toNat stable] using quoteStack
  · rcases ordinaryArm with
      ⟨assetsNotMax, bodyPre, bodyStack, bodyWf, bodyReads, bodyRun⟩
    obtain ⟨ceilingFits, quotePre, quoteImage, quoteStack, quoteMemImage,
        quoteFrame, quoteRun⟩ :=
      mulDiv_up_image_trace bodyWf bodyReads
        (ProducesWord.stagedDenominator supplyAt)
        (ProducesWord.amount_after_denominatorScratch amountAt)
        (ProducesWord.stagedAssetFactor_after_mulDivScratch assetsAt)
        bodyStack lookup bodyRun
    refine ⟨?_, quotePre, quoteImage, ?_, quoteMemImage, quoteFrame,
      quoteRun⟩
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
      (roomState.trans (testState.trans bodyPop.state))
  · exact sharesLogs.trans
      (roomLogs.trans (testLogs.trans bodyPop.logs))

end ProrataWethVault

end Blanc
