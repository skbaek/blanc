-- ProrataWethVaultOutbound.lean : exact local seams for `withdraw` and `redeem`.

import Blanc.ProrataWethVaultInbound

namespace Blanc

open Jaune
open Jaune.Ninst Ninst
open scoped LogOutputHinv

namespace ProrataWethVault

/-!
# Compiled outbound seams

`withdraw` and `redeem` stage three ABI arguments, snapshot the booked WETH
balance and the share supply, quote against that snapshot, and only then burn
shares and execute the exact configured WETH `transfer` child.  This module
owns the family-local half of that walk: argument staging, the exact quote
reaching the auxiliary continuation, the local guards, and the burn/settle
tail.  The WETH child itself and the public compiled selectors belong to the
composition stratum.

The outbound direction is not the inbound one read backwards.  Its share write
happens *before* the WETH crossing rather than after, so its frozen log order
is share `Transfer(owner, 0, shares)` first, then the child's
`Transfer(vault, receiver, assets)`, then `Withdraw` -- and the owner may be
someone other than the caller, which adds an allowance path with no inbound
counterpart.
-/

/-! ## Outbound argument staging -/

/-- Memory image after the three outbound ABI arguments are staged. -/
def outboundArgImage (image : Bytes) (amount receiver owner : B256) : Bytes :=
  Bytes.writeAt
    (Bytes.writeAt
      (Bytes.writeAt image (amountWord * 32).toNat amount.toBytes)
      (receiverWord * 32).toNat receiver.toBytes)
    (ownerWord * 32).toNat owner.toBytes

theorem outboundArgImage_amount
    (image : Bytes) (amount receiver owner : B256) :
    Bytes.toB256
        ((outboundArgImage image amount receiver owner).sliceD
          (amountWord * 32).toNat 32 0) = amount := by
  unfold outboundArgImage
  rw [Bytes.readWord_writeAt_of_disjoint, Bytes.readWord_writeAt_of_disjoint]
  · exact Bytes.readWord_writeAt_self _ _ _
  · left
    decide +kernel
  · left
    decide +kernel

theorem outboundArgImage_receiver
    (image : Bytes) (amount receiver owner : B256) :
    Bytes.toB256
        ((outboundArgImage image amount receiver owner).sliceD
          (receiverWord * 32).toNat 32 0) = receiver := by
  unfold outboundArgImage
  rw [Bytes.readWord_writeAt_of_disjoint]
  · exact Bytes.readWord_writeAt_self _ _ _
  · left
    decide +kernel

theorem outboundArgImage_owner
    (image : Bytes) (amount receiver owner : B256) :
    Bytes.toB256
        ((outboundArgImage image amount receiver owner).sliceD
          (ownerWord * 32).toNat 32 0) = owner := by
  unfold outboundArgImage
  exact Bytes.readWord_writeAt_self _ _ _

/-- Both outbound flows begin by staging ABI arguments zero, one and two into
the long-lived operation words, leaving persistent state untouched. -/
theorem outboundArgs_trace
    {fs : List Func} {sevm : Sevm} {pre final : Devm}
    {image : Bytes} {body : Func} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (stack : tail <<+ pre.stack)
    (run : Func.RunCompiledTo fs sevm pre
      (arg 0 +++ mstoreAt amountWord +++
        arg 1 +++ mstoreAt receiverWord +++
        arg 2 +++ mstoreAt ownerWord +++ body) (.ok final)) :
    ∃ bodyPre,
      tail <<+ bodyPre.stack ∧
      Mem.Wf bodyPre.memory ∧
      Mem.Reads bodyPre.memory
        (outboundArgImage image (Sevm.argWord sevm 0)
          (Sevm.argWord sevm 1) (Sevm.argWord sevm 2)) ∧
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
  obtain ⟨ownerPre, receiverStoreRun, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨ownerStack, ownerWf, ownerReads, receiverStoreState⟩ :=
    of_run_mstoreAt_image receiverPrefix receiverStoreWf receiverStoreReads
      receiverStoreRun
  have receiverStoreLogs : receiverStorePre.logs = ownerPre.logs := by
    refine Line.of_inv Devm.logs ?_ receiverStoreRun
    unfold mstoreAt
    line_inv
  obtain ⟨ownerStorePre, ownerRun, run⟩ := runCompiledTo_prepend_inv run
  have ownerPrefix := prefix_of_arg ownerStack ownerRun
  have ownerMemory : ownerPre.memory = ownerStorePre.memory := by
    refine Line.of_inv Devm.memory ?_ ownerRun
    unfold Blanc.arg cdl
    line_inv
  have ownerState : ownerPre.state = ownerStorePre.state := by
    refine Line.of_inv Devm.state ?_ ownerRun
    unfold Blanc.arg cdl
    line_inv
  have ownerLogs : ownerPre.logs = ownerStorePre.logs := by
    refine Line.of_inv Devm.logs ?_ ownerRun
    unfold Blanc.arg cdl
    line_inv
  have ownerStoreWf : Mem.Wf ownerStorePre.memory := by
    rw [← ownerMemory]; exact ownerWf
  have ownerStoreReads : Mem.Reads ownerStorePre.memory
      (Bytes.writeAt
        (Bytes.writeAt image (amountWord * 32).toNat
          (Sevm.argWord sevm 0).toBytes)
        (receiverWord * 32).toNat (Sevm.argWord sevm 1).toBytes) := by
    rw [← ownerMemory]; exact ownerReads
  obtain ⟨bodyPre, ownerStoreRun, bodyRun⟩ := runCompiledTo_prepend_inv run
  obtain ⟨bodyStack, bodyWf, bodyReads, ownerStoreState⟩ :=
    of_run_mstoreAt_image ownerPrefix ownerStoreWf ownerStoreReads
      ownerStoreRun
  have ownerStoreLogs : ownerStorePre.logs = bodyPre.logs := by
    refine Line.of_inv Devm.logs ?_ ownerStoreRun
    unfold mstoreAt
    line_inv
  exact ⟨bodyPre, bodyStack, bodyWf, bodyReads,
    amountState.trans (amountStoreState.trans
      (receiverState.trans (receiverStoreState.trans
        (ownerState.trans ownerStoreState)))),
    amountLogs.trans (amountStoreLogs.trans
      (receiverLogs.trans (receiverStoreLogs.trans
        (ownerLogs.trans ownerStoreLogs)))),
    bodyRun⟩

/-! ## Exact outbound quotes reaching the auxiliary continuation -/

/-- The `withdraw` arithmetic suffix quotes exactly `ceil(amount*D/X)` from the
booked assets and supply, then calls the auxiliary `withdrawAfterQuote`
continuation with that word on the stack.  Both the exact-`2^256` and ordinary
asset arms are covered.

This is `depositQuote_arithmetic_trace` with the rounding reversed: a
withdrawal must round the shares it burns *up*, so the vault never pays out
assets it has not charged for. -/
theorem withdrawQuote_arithmetic_trace
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
    (lookup : fs[withdrawAfterQuoteSlot]? = some withdrawAfterQuote)
    (run : Func.RunCompiledTo fs sevm pre
      (loadWord assetsWord +++ isMax +++
        (productOverTwoPow256 (loadWord amountWord) stagedDenominator .up
            withdrawAfterQuoteSlot <?>
          mulDiv (loadWord amountWord) stagedDenominator stagedAssetFactor
            .up withdrawAfterQuoteSlot)) (.ok final)) :
    previewWithdrawN amount.toNat assets.toNat supply.toNat < wordModulusN ∧
      ∃ bodyPre bodyImage,
        Nat.toB256
            (previewWithdrawN amount.toNat assets.toNat supply.toNat) ::
          tail <<+ bodyPre.stack ∧
        MemImage bodyPre bodyImage ∧
        Bytes.WordFrameFrom image bodyImage arithmeticScratchEnd ∧
        Devm.QuietFrame pre bodyPre ∧
        Func.RunCompiledTo fs sevm bodyPre withdrawAfterQuote (.ok final) := by
  rcases ProducesWord.isMax_arm_trace
      (ProducesWord.loadWord assetsAt) memoryWf memoryReads stack run with
    maxArm | ordinaryArm
  · rcases maxArm with
      ⟨assetsMax, bodyPre, bodyStack, bodyWf, bodyReads, bodyState,
        bodyRun⟩
    let denominator := Nat.toB256 (denominatorN supply.toNat)
    obtain ⟨ceilingFits, quotePre, quoteStack, quoteImage, quoteState,
        quoteRun⟩ :=
      productOverTwoPow256_up_image_trace bodyWf bodyReads
        (ProducesWord.loadWord amountAt)
        (ProducesWord.stagedDenominator_after_productScratch supplyAt)
        bodyStack lookup bodyRun
    refine ⟨?_, quotePre,
      productOverTwoPow256TraceImage image amount denominator, ?_, quoteImage,
      productOverTwoPow256TraceImage_wordFrame image amount denominator,
      bodyState.trans quoteState, quoteRun⟩
    · simpa [previewWithdrawN, denominator, assetsMax, maxWord_toNat,
        assetFactorN_maxWord, stagedDenominator_toNat stable] using
        ceilingFits
    · simpa [previewWithdrawN, denominator, assetsMax, maxWord_toNat,
        assetFactorN_maxWord, stagedDenominator_toNat stable] using
        quoteStack
  · rcases ordinaryArm with
      ⟨assetsNotMax, bodyPre, bodyStack, bodyWf, bodyReads, bodyState,
        bodyRun⟩
    obtain ⟨ceilingFits, quotePre, quoteImage, quoteStack, quoteMemImage,
        quoteFrame, quoteState, quoteRun⟩ :=
      mulDiv_up_image_trace bodyWf bodyReads
        (ProducesWord.stagedAssetFactor assetsAt)
        (ProducesWord.amount_after_denominatorScratch amountAt)
        (ProducesWord.stagedDenominator_after_mulDivScratch supplyAt)
        bodyStack lookup bodyRun
    refine ⟨?_, quotePre, quoteImage, ?_, quoteMemImage, quoteFrame,
      bodyState.trans quoteState, quoteRun⟩
    · simpa [previewWithdrawN, stagedDenominator_toNat stable,
        stagedAssetFactor_toNat_of_ne_max assetsNotMax] using ceilingFits
    · simpa [previewWithdrawN, stagedDenominator_toNat stable,
        stagedAssetFactor_toNat_of_ne_max assetsNotMax] using quoteStack

/-- The `redeem` arithmetic suffix quotes exactly `floor(shares*X/D)` from the
booked assets and supply and calls `redeemAfterQuote`.

This is `mintQuote_arithmetic_trace` with the rounding reversed: a redemption
must round the assets it pays out *down*. -/
theorem redeemQuote_arithmetic_trace
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
    (lookup : fs[redeemAfterQuoteSlot]? = some redeemAfterQuote)
    (run : Func.RunCompiledTo fs sevm pre
      (loadWord assetsWord +++ isMax +++
        (shiftedDiv (loadWord amountWord) stagedDenominator .down
            redeemAfterQuoteSlot <?>
          mulDiv (loadWord amountWord) stagedAssetFactor stagedDenominator
            .down redeemAfterQuoteSlot)) (.ok final)) :
    previewRedeemN amount.toNat assets.toNat supply.toNat < wordModulusN ∧
      ∃ bodyPre bodyImage,
        Nat.toB256 (previewRedeemN amount.toNat assets.toNat supply.toNat) ::
          tail <<+ bodyPre.stack ∧
        MemImage bodyPre bodyImage ∧
        Bytes.WordFrameFrom image bodyImage arithmeticScratchEnd ∧
        Devm.QuietFrame pre bodyPre ∧
        Func.RunCompiledTo fs sevm bodyPre redeemAfterQuote (.ok final) := by
  rcases ProducesWord.isMax_arm_trace
      (ProducesWord.loadWord assetsAt) memoryWf memoryReads stack run with
    maxArm | ordinaryArm
  · rcases maxArm with
      ⟨assetsMax, bodyPre, bodyStack, bodyWf, bodyReads, bodyState,
        bodyRun⟩
    obtain ⟨quotientFits, quotePre, quoteImage, quoteStack, quoteMemImage,
        quoteFrame, quoteState, quoteRun⟩ :=
      shiftedDiv_down_image_trace bodyWf bodyReads
        (ProducesWord.loadWord amountAt)
        (ProducesWord.stagedDenominator_after_shiftedScratch supplyAt)
        bodyStack lookup bodyRun
    refine ⟨?_, quotePre, quoteImage, ?_, quoteMemImage, quoteFrame,
      bodyState.trans quoteState, quoteRun⟩
    · simpa [previewRedeemN, convertToAssetsN, assetsMax, maxWord_toNat,
        assetFactorN_maxWord, stagedDenominator_toNat stable] using
        quotientFits
    · simpa [previewRedeemN, convertToAssetsN, assetsMax, maxWord_toNat,
        assetFactorN_maxWord, stagedDenominator_toNat stable] using
        quoteStack
  · rcases ordinaryArm with
      ⟨assetsNotMax, bodyPre, bodyStack, bodyWf, bodyReads, bodyState,
        bodyRun⟩
    obtain ⟨quotientFits, quotePre, quoteImage, quoteStack, quoteMemImage,
        quoteFrame, quoteState, quoteRun⟩ :=
      mulDiv_down_image_trace bodyWf bodyReads
        (ProducesWord.stagedDenominator supplyAt)
        (ProducesWord.amount_after_denominatorScratch amountAt)
        (ProducesWord.stagedAssetFactor_after_mulDivScratch assetsAt)
        bodyStack lookup bodyRun
    refine ⟨?_, quotePre, quoteImage, ?_, quoteMemImage, quoteFrame,
      bodyState.trans quoteState, quoteRun⟩
    · simpa [previewRedeemN, convertToAssetsN, stagedDenominator_toNat stable,
        stagedAssetFactor_toNat_of_ne_max assetsNotMax] using quotientFits
    · simpa [previewRedeemN, convertToAssetsN, stagedDenominator_toNat stable,
        stagedAssetFactor_toNat_of_ne_max assetsNotMax] using quoteStack

/-! ## Outbound guards -/

/-- Both outbound continuations stage the quote, then reject the zero caller,
a dirty or zero staged receiver, and a dirty or zero staged owner.

The owner check has no inbound counterpart: `deposit` and `mint` always credit
on behalf of the caller, while `withdraw` and `redeem` may burn someone else's
shares, so the owner is a third address that must be canonical before it is
used as a storage key. -/
theorem outboundGuards_trace
    {fs : List Func} {sevm : Sevm} {pre final : Devm}
    {image : Bytes} {quote receiver owner : B256} {body : Func} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (receiverAt : Bytes.toB256
      (image.sliceD (receiverWord * 32).toNat 32 0) = receiver)
    (ownerAt : Bytes.toB256
      (image.sliceD (ownerWord * 32).toNat 32 0) = owner)
    (stack : quote :: tail <<+ pre.stack)
    (run : Func.RunCompiledTo fs sevm pre
      (mstoreAt quoteWord +++
        nonzeroCaller (nonzeroStagedAddress receiverWord
          (nonzeroStagedAddress ownerWord body))) (.ok final)) :
    ∃ bodyPre,
      sevm.caller.toB256 ≠ 0 ∧
      ValidAdr receiver ∧
      receiver ≠ 0 ∧
      ValidAdr owner ∧
      owner ≠ 0 ∧
      tail <<+ bodyPre.stack ∧
      Mem.Wf bodyPre.memory ∧
      Mem.Reads bodyPre.memory
        (Bytes.writeAt image (quoteWord * 32).toNat quote.toBytes) ∧
      pre.state = bodyPre.state ∧
      pre.logs = bodyPre.logs ∧
      Func.RunCompiledTo fs sevm bodyPre body (.ok final) := by
  obtain ⟨ownerPre, callerNonzero, receiverValid, receiverNonzero,
      ownerStack, ownerWf, ownerReads, ownerState, ownerLogs, ownerRun⟩ :=
    inboundGuards_trace memoryWf memoryReads receiverAt stack run
  have ownerAtQuote : Bytes.toB256
      ((Bytes.writeAt image (quoteWord * 32).toNat quote.toBytes).sliceD
        (ownerWord * 32).toNat 32 0) = owner := by
    rw [Bytes.readWord_writeAt_of_disjoint]
    · exact ownerAt
    · left
      decide +kernel
  obtain ⟨bodyPre, ownerValid, ownerNonzero, bodyStack, bodyWf,
      bodyReads, bodyState, bodyLogs, bodyRun⟩ :=
    nonzeroStagedAddress_trace ownerWf ownerReads ownerAtQuote ownerStack
      ownerRun
  exact ⟨bodyPre, callerNonzero, receiverValid, receiverNonzero, ownerValid,
    ownerNonzero, bodyStack, bodyWf, bodyReads,
    ownerState.trans bodyState, ownerLogs.trans bodyLogs, bodyRun⟩

/-! ## Owner share-balance guard -/

/-- The outbound share guard reads the owner's share row, stages it, and
requires the burn amount to fit it.  A successful walk proves the burn is
covered by the owner's own balance and leaves persistent storage and logs
untouched.

`SLOAD` is not state-invariant -- it touches the accessed-storage set -- so
this returns storage equality rather than whole-state equality, exactly as the
inbound credit walk does. -/
theorem ownerHasShares_trace
    {fs : List Func} {sevm : Sevm} {pre final : Devm}
    {image : Bytes} {sharesWord owner shares : B256}
    {body : Func} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (ownerAt : Bytes.toB256
      (image.sliceD (ownerWord * 32).toNat 32 0) = owner)
    (sharesAt : Bytes.toB256
      (image.sliceD (sharesWord * 32).toNat 32 0) = shares)
    (sharesBelow : (sharesWord * 32).toNat + 32 ≤ (balanceWord * 32).toNat)
    (stack : tail <<+ pre.stack)
    (run : Func.RunCompiledTo fs sevm pre
      (ownerHasShares (loadWord sharesWord) body) (.ok final)) :
    ∃ bodyPre balance,
      balance = Devm.getStorVal pre sevm.currentTarget owner ∧
      shares.toNat ≤ balance.toNat ∧
      tail <<+ bodyPre.stack ∧
      Mem.Wf bodyPre.memory ∧
      Mem.Reads bodyPre.memory
        (Bytes.writeAt image (balanceWord * 32).toNat balance.toBytes) ∧
      Devm.getStor pre = Devm.getStor bodyPre ∧
      pre.logs = bodyPre.logs ∧
      Func.RunCompiledTo fs sevm bodyPre body (.ok final) := by
  simp only [ownerHasShares] at run

  -- Read the owner's share row.
  obtain ⟨sloadPre, ownerRun, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨ownerPrefix, sloadWf, sloadReads, ownerState⟩ :=
    of_run_loadWordAt_image stack memoryWf memoryReads ownerAt ownerRun
  have ownerLogs : pre.logs = sloadPre.logs := by
    refine Line.of_inv Devm.logs ?_ ownerRun
    unfold ProrataWethVault.loadWord
    line_inv
  obtain ⟨balanceStorePre, sloadRun, run⟩ := runCompiledTo_next_inv run
  have sloadSource := Ninst.Run.of_runCompiled sloadRun
  obtain ⟨balance, balancePrefix, balanceEq⟩ :=
    prefix_of_sload sloadSource ownerPrefix
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

  -- Compare the burn amount against the staged balance.
  obtain ⟨balanceLoadPre, sharesRun, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨sharesPrefix, balanceLoadWf, balanceLoadReads, sharesState⟩ :=
    of_run_loadWordAt_image sharesStack sharesWf sharesReads sharesAt1
      sharesRun
  have sharesLogs : sharesPre.logs = balanceLoadPre.logs := by
    refine Line.of_inv Devm.logs ?_ sharesRun
    unfold ProrataWethVault.loadWord
    line_inv
  obtain ⟨testPre, balanceLoadRun, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨balanceLoadPrefix, testWf, testReads, balanceLoadState⟩ :=
    of_run_loadWordAt_image sharesPrefix balanceLoadWf balanceLoadReads
      balanceAt1 balanceLoadRun
  have balanceLoadLogs : balanceLoadPre.logs = testPre.logs := by
    refine Line.of_inv Devm.logs ?_ balanceLoadRun
    unfold ProrataWethVault.loadWord
    line_inv
  obtain ⟨branchPre, testRun, branchRun⟩ := runCompiledTo_next_inv run
  have testSource := Ninst.Run.of_runCompiled testRun
  have testPrefix := prefix_of_lt testSource balanceLoadPrefix
  have testMemory : testPre.memory = branchPre.memory :=
    Ninst.Hinv.inv (f := Devm.memory) testSource
  have testStorage : Devm.getStor testPre = Devm.getStor branchPre :=
    Ninst.Hinv.inv (f := Devm.getStor) testSource
  have testLogs : testPre.logs = branchPre.logs :=
    Ninst.Hinv.inv (f := Devm.logs) testSource
  have balanceLarge : ¬ balance < shares := by
    intro balanceLt
    have onePrefix : (1 : B256) :: tail <<+ branchPre.stack := by
      simpa [B256.ltCheck, balanceLt] using testPrefix
    obtain ⟨revertPre, branchWord, branchWordNe, revertPop, revertRun, -⟩ :=
      Func.RunCompiledTo.succ_branch_of_prefix
        (by decide : (1 : B256) ≠ 0) onePrefix branchRun
    obtain ⟨revertPost, impossible, -⟩ := runCompiledTo_revert_inv revertRun
    cases impossible
  have zeroPrefix : (0 : B256) :: tail <<+ branchPre.stack := by
    simpa [B256.ltCheck, balanceLarge] using testPrefix
  obtain ⟨bodyPre, bodyPop, bodyRun, bodyPrefix⟩ :=
    Func.RunCompiledTo.zero_branch_of_prefix zeroPrefix branchRun
  have bodyWf : Mem.Wf bodyPre.memory := by
    rw [← bodyPop.memory, ← testMemory]
    exact testWf
  have bodyReads : Mem.Reads bodyPre.memory image1 := by
    rw [← bodyPop.memory, ← testMemory]
    exact testReads
  refine ⟨bodyPre, balance, ?_, ?_, bodyPrefix, bodyWf, bodyReads, ?_, ?_,
    bodyRun⟩
  · rw [balanceEq]
    change
      (Devm.getStor sloadPre sevm.currentTarget).get owner =
        (Devm.getStor pre sevm.currentTarget).get owner
    rw [funext (getStor_eq_of_state_eq ownerState)]
  · by_contra sharesLarge
    exact balanceLarge (B256.lt_of_toNat_lt_toNat (by omega))
  · exact (funext (getStor_eq_of_state_eq ownerState)).trans
      (sloadStorage.trans
        ((funext (getStor_eq_of_state_eq balanceStoreState)).trans
          ((funext (getStor_eq_of_state_eq sharesState)).trans
            ((funext (getStor_eq_of_state_eq balanceLoadState)).trans
              (testStorage.trans
                (funext (getStor_eq_of_state_eq bodyPop.state)))))))
  · exact ownerLogs.trans (sloadLogs.trans (balanceStoreLogs.trans
      (sharesLogs.trans (balanceLoadLogs.trans
        (testLogs.trans bodyPop.logs)))))

/-! ## Outbound authorization -/

/-- Memory image after the two hashed allowance words are staged. -/
def allowanceKeyImage (image : Bytes) (owner spender : B256) : Bytes :=
  Bytes.writeAt (Bytes.writeAt image 0 owner.toBytes) 32 spender.toBytes

/-- The guarded allowance key hashes the staged owner against the frame caller
and reaches its body only when that hash aliases neither a share row nor the
reserved supply word.  Both hashed words land in the low scratch region, so
every long-lived operation word survives. -/
theorem allowanceKey_trace
    {fs : List Func} {sevm : Sevm} {pre final : Devm}
    {image : Bytes} {owner : B256} {body : Func} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (ownerAt : Bytes.toB256
      (image.sliceD (ownerWord * 32).toNat 32 0) = owner)
    (stack : tail <<+ pre.stack)
    (run : Func.RunCompiledTo fs sevm pre
      (guardedAllowanceKey (loadWord ownerWord) [caller] body) (.ok final)) :
    ∃ bodyPre,
      ¬ ValidAdr (allowanceKey owner sevm.caller.toB256) ∧
      allowanceKey owner sevm.caller.toB256 ≠ supplySlot ∧
      allowanceKey owner sevm.caller.toB256 :: tail <<+ bodyPre.stack ∧
      Mem.Wf bodyPre.memory ∧
      Mem.Reads bodyPre.memory
        (allowanceKeyImage image owner sevm.caller.toB256) ∧
      Devm.getStor pre = Devm.getStor bodyPre ∧
      pre.logs = bodyPre.logs ∧
      Func.RunCompiledTo fs sevm bodyPre body (.ok final) := by
  simp only [guardedAllowanceKey] at run

  -- Stage the owner into scratch word zero.
  obtain ⟨ownerStorePre, ownerRun, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨ownerPrefix, ownerStoreWf, ownerStoreReads, ownerState⟩ :=
    of_run_loadWordAt_image stack memoryWf memoryReads ownerAt ownerRun
  have ownerLogs : pre.logs = ownerStorePre.logs := by
    refine Line.of_inv Devm.logs ?_ ownerRun
    unfold ProrataWethVault.loadWord
    line_inv
  obtain ⟨spenderPre, ownerStoreRun, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨spenderStack, spenderWf, spenderReads, ownerStoreState⟩ :=
    of_run_mstoreAt_image ownerPrefix ownerStoreWf ownerStoreReads
      ownerStoreRun
  have ownerStoreLogs : ownerStorePre.logs = spenderPre.logs := by
    refine Line.of_inv Devm.logs ?_ ownerStoreRun
    unfold mstoreAt
    line_inv

  -- Stage the frame caller into scratch word one.
  obtain ⟨spenderStorePre, spenderRun, run⟩ := runCompiledTo_prepend_inv run
  rcases Line.of_run_cons spenderRun with ⟨_, callerRun, callerNil⟩
  cases callerNil
  have callerPush := of_run_caller callerRun
  have spenderPrefix : sevm.caller.toB256 :: tail <<+ spenderStorePre.stack :=
    prefix_of_push callerPush spenderStack
  have spenderStoreWf : Mem.Wf spenderStorePre.memory := by
    rw [← callerPush.memory]; exact spenderWf
  have spenderStoreReads : Mem.Reads spenderStorePre.memory
      (Bytes.writeAt image ((0 : B256) * 32).toNat owner.toBytes) := by
    rw [← callerPush.memory]; exact spenderReads
  obtain ⟨windowPre, spenderStoreRun, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨windowStack, windowWf, windowReads, spenderStoreState⟩ :=
    of_run_mstoreAt_image spenderPrefix spenderStoreWf spenderStoreReads
      spenderStoreRun
  have spenderStoreLogs : spenderStorePre.logs = windowPre.logs := by
    refine Line.of_inv Devm.logs ?_ spenderStoreRun
    unfold mstoreAt
    line_inv
  have windowImage : Mem.Reads windowPre.memory
      (allowanceKeyImage image owner sevm.caller.toB256) := by
    simpa only [allowanceKeyImage,
      show ((0 : B256) * 32).toNat = 0 by decide +kernel,
      show ((1 : B256) * 32).toNat = 32 by decide +kernel] using windowReads

  -- Push the hash window and hash it.
  obtain ⟨keccakPre, pushWindowRun, run⟩ := runCompiledTo_prepend_inv run
  have pushWindowLine := pushWindowRun
  simp only [pushList, List.map] at pushWindowRun
  rcases Line.of_run_cons pushWindowRun with ⟨_, push64Run, pushWindowRun⟩
  rcases Line.of_run_cons pushWindowRun with ⟨_, push0Run, pushNil⟩
  cases pushNil
  have push64 := of_run_pushB256 push64Run
  have push0 := of_run_pushB256 push0Run
  have windowPrefix : (0 : B256) :: 64 :: tail <<+ keccakPre.stack :=
    prefix_of_push push0 (prefix_of_push push64 windowStack)
  have keccakWf : Mem.Wf keccakPre.memory := by
    rw [← push0.memory, ← push64.memory]; exact windowWf
  have keccakReads : Mem.Reads keccakPre.memory
      (allowanceKeyImage image owner sevm.caller.toB256) := by
    rw [← push0.memory, ← push64.memory]; exact windowImage
  obtain ⟨collisionPre, keccakRun, run⟩ := runCompiledTo_next_inv run
  have keccakSource := Ninst.Run.of_runCompiled keccakRun
  obtain ⟨hashPrefix, keccakMemory⟩ :=
    prefix_of_keccak256_val keccakSource windowPrefix
  have windowRead :
      (keccakPre.memory.read (0 : B256).toNat (64 : B256).toNat).1 =
        owner.toBytes ++ sevm.caller.toB256.toBytes := by
    rw [show ((0 : B256)).toNat = 0 by decide +kernel,
      show ((64 : B256)).toNat = 64 by decide +kernel,
      Mem.Reads.read keccakReads]
    simpa only [allowanceKeyImage] using
      Bytes.read_two_word_writes_at image 0 owner sevm.caller.toB256
  have keyPrefix : allowanceKey owner sevm.caller.toB256 :: tail <<+
      collisionPre.stack := by
    rw [windowRead] at hashPrefix
    simpa only [allowanceKey] using hashPrefix
  have collisionWf : Mem.Wf collisionPre.memory := by
    rw [keccakMemory]
    exact keccakWf.extend _ _
  have collisionReads : Mem.Reads collisionPre.memory
      (allowanceKeyImage image owner sevm.caller.toB256) := by
    rw [keccakMemory]
    exact Mem.Reads.extend keccakReads _ _

  -- Reject a key that aliases a share row or the supply slot.
  obtain ⟨bodyPre, keyNotAddress, keyNotSupply, bodyRun, bodyPrefix,
      collisionState, collisionLogs, bodyMemory⟩ :=
    allowanceCollisionGuard_body_of_ok keyPrefix run
  refine ⟨bodyPre, keyNotAddress, keyNotSupply, bodyPrefix, ?_, ?_, ?_, ?_,
    bodyRun⟩
  · rw [← bodyMemory]; exact collisionWf
  · rw [← bodyMemory]; exact collisionReads
  · exact (funext (getStor_eq_of_state_eq ownerState)).trans
      ((funext (getStor_eq_of_state_eq ownerStoreState)).trans
        ((funext (getStor_eq_of_state_eq callerPush.state)).trans
          ((funext (getStor_eq_of_state_eq spenderStoreState)).trans
            ((Line.of_inv Devm.getStor (by
                simp only [pushList, List.map]
                line_inv) pushWindowLine).trans
              ((Ninst.Hinv.inv (f := Devm.getStor) keccakSource).trans
                (funext (getStor_eq_of_state_eq collisionState)))))))
  · exact ownerLogs.trans (ownerStoreLogs.trans
      (callerPush.logs.trans (spenderStoreLogs.trans
        ((Line.of_inv Devm.logs (by
            simp only [pushList, List.map]
            line_inv) pushWindowLine).trans
          ((Ninst.Hinv.inv (f := Devm.logs) keccakSource).trans
            collisionLogs)))))

/-- Memory image after the allowance key and the loaded allowance are staged.
All four writes land at word `0`, word `1`, the scratch word and the allowance
word, so every other long-lived operation word survives the spend. -/
def allowanceStagingImage
    (image : Bytes) (owner spender key allowance : B256) : Bytes :=
  Bytes.writeAt
    (Bytes.writeAt (allowanceKeyImage image owner spender)
      (scratchWord * 32).toNat key.toBytes)
    (allowanceWord * 32).toNat allowance.toBytes

/-- Spending a staged allowance either finds it infinite and writes nothing, or
finds it finite, proves it covers the amount, and decrements exactly that one
slot.  In both routes the key is neither address-shaped nor the reserved supply
word, so no share row and not the supply can have moved. -/
theorem spendAllowance_trace
    {fs : List Func} {sevm : Sevm} {pre final : Devm}
    {image : Bytes} {amountSel owner amount : B256} {continuation : Nat}
    {body : Func} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (ownerAt : Bytes.toB256
      (image.sliceD (ownerWord * 32).toNat 32 0) = owner)
    (amountAt : Bytes.toB256
      (image.sliceD (amountSel * 32).toNat 32 0) = amount)
    (amountAboveKeyWords : 64 ≤ (amountSel * 32).toNat)
    (amountAboveScratch :
      (scratchWord * 32).toNat + 32 ≤ (amountSel * 32).toNat)
    (amountBelowAllowance :
      (amountSel * 32).toNat + 32 ≤ (allowanceWord * 32).toNat)
    (stack : tail <<+ pre.stack)
    (lookup : fs[continuation]? = some body)
    (run : Func.RunCompiledTo fs sevm pre
      (spendAllowance (loadWord ownerWord) [caller] (loadWord amountSel)
        continuation) (.ok final)) :
    ∃ bodyPre key allowance,
      ¬ ValidAdr key ∧
      key ≠ supplySlot ∧
      allowance = Devm.getStorVal pre sevm.currentTarget key ∧
      (Devm.getStor bodyPre sevm.currentTarget =
          Devm.getStor pre sevm.currentTarget ∨
        (amount.toNat ≤ allowance.toNat ∧
          Devm.getStor bodyPre sevm.currentTarget =
            (Devm.getStor pre sevm.currentTarget).set key
              (allowance - amount))) ∧
      (∀ account, sevm.currentTarget ≠ account →
        Devm.getStor bodyPre account = Devm.getStor pre account) ∧
      pre.logs = bodyPre.logs ∧
      tail <<+ bodyPre.stack ∧
      Mem.Wf bodyPre.memory ∧
      Mem.Reads bodyPre.memory
        (allowanceStagingImage image owner sevm.caller.toB256 key
          allowance) ∧
      Func.RunCompiledTo fs sevm bodyPre body (.ok final) := by
  simp only [spendAllowance] at run

  -- Hash and guard the allowance key.
  obtain ⟨scratchStorePre, keyNotAddress, keyNotSupply, keyPrefix, keyWf,
      keyReads, keyState, keyLogs, run⟩ :=
    allowanceKey_trace memoryWf memoryReads ownerAt stack run
  set key := allowanceKey owner sevm.caller.toB256 with keyDef

  -- Stage the key.
  obtain ⟨scratchLoadPre, scratchStoreRun, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨scratchLoadStack, scratchLoadWf, scratchLoadReads,
      scratchStoreState⟩ :=
    of_run_mstoreAt_image keyPrefix keyWf keyReads scratchStoreRun
  have scratchStoreLogs : scratchStorePre.logs = scratchLoadPre.logs := by
    refine Line.of_inv Devm.logs ?_ scratchStoreRun
    unfold mstoreAt
    line_inv
  set keyImage :=
    Bytes.writeAt (allowanceKeyImage image owner sevm.caller.toB256)
      (scratchWord * 32).toNat key.toBytes with keyImageDef
  change Mem.Reads scratchLoadPre.memory keyImage at scratchLoadReads
  have scratchAt : Bytes.toB256
      (keyImage.sliceD (scratchWord * 32).toNat 32 0) = key := by
    rw [keyImageDef]
    exact Bytes.readWord_writeAt_self _ _ _

  -- Read the allowance.
  obtain ⟨sloadPre, scratchLoadRun, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨scratchPrefix, sloadWf, sloadReads, scratchLoadState⟩ :=
    of_run_loadWordAt_image scratchLoadStack scratchLoadWf scratchLoadReads
      scratchAt scratchLoadRun
  have scratchLoadLogs : scratchLoadPre.logs = sloadPre.logs := by
    refine Line.of_inv Devm.logs ?_ scratchLoadRun
    unfold ProrataWethVault.loadWord
    line_inv
  obtain ⟨allowanceStorePre, sloadRun, run⟩ := runCompiledTo_next_inv run
  have sloadSource := Ninst.Run.of_runCompiled sloadRun
  obtain ⟨allowance, allowancePrefix, allowanceEq⟩ :=
    prefix_of_sload sloadSource scratchPrefix
  have sloadStorage : Devm.getStor sloadPre = Devm.getStor allowanceStorePre :=
    Ninst.Hinv.inv (f := Devm.getStor) sloadSource
  have sloadMemory : sloadPre.memory = allowanceStorePre.memory :=
    Ninst.Hinv.inv (f := Devm.memory) sloadSource
  have sloadLogs : sloadPre.logs = allowanceStorePre.logs :=
    Ninst.Hinv.inv (f := Devm.logs) sloadSource
  have allowanceStoreWf : Mem.Wf allowanceStorePre.memory := by
    rw [← sloadMemory]; exact sloadWf
  have allowanceStoreReads : Mem.Reads allowanceStorePre.memory keyImage := by
    rw [← sloadMemory]; exact sloadReads

  -- Stage the allowance.
  obtain ⟨branchPre, allowanceStoreRun, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨branchStack, branchWf, branchReads, allowanceStoreState⟩ :=
    of_run_mstoreAt_image allowancePrefix allowanceStoreWf
      allowanceStoreReads allowanceStoreRun
  have allowanceStoreLogs : allowanceStorePre.logs = branchPre.logs := by
    refine Line.of_inv Devm.logs ?_ allowanceStoreRun
    unfold mstoreAt
    line_inv
  set stagedImage :=
    allowanceStagingImage image owner sevm.caller.toB256 key allowance
    with stagedImageDef
  change Mem.Reads branchPre.memory stagedImage at branchReads
  have allowanceAt : Bytes.toB256
      (stagedImage.sliceD (allowanceWord * 32).toNat 32 0) = allowance := by
    rw [stagedImageDef, allowanceStagingImage]
    exact Bytes.readWord_writeAt_self _ _ _
  have amountAtStaged : Bytes.toB256
      (stagedImage.sliceD (amountSel * 32).toNat 32 0) = amount := by
    rw [stagedImageDef, allowanceStagingImage, allowanceKeyImage]
    rw [Bytes.readWord_writeAt_of_disjoint, Bytes.readWord_writeAt_of_disjoint,
      Bytes.readWord_writeAt_of_disjoint, Bytes.readWord_writeAt_of_disjoint]
    · exact amountAt
    · right
      omega
    · right
      omega
    · right
      exact amountAboveScratch
    · left
      exact amountBelowAllowance

  -- The storage prefix is untouched up to the branch.
  have entryStorage : Devm.getStor pre = Devm.getStor sloadPre :=
    keyState.trans
      ((funext (getStor_eq_of_state_eq scratchStoreState)).trans
        (funext (getStor_eq_of_state_eq scratchLoadState)))
  have branchStorage : Devm.getStor pre = Devm.getStor branchPre :=
    entryStorage.trans (sloadStorage.trans
      (funext (getStor_eq_of_state_eq allowanceStoreState)))
  have branchLogs : pre.logs = branchPre.logs :=
    keyLogs.trans (scratchStoreLogs.trans (scratchLoadLogs.trans
      (sloadLogs.trans allowanceStoreLogs)))
  have allowanceValue : allowance = Devm.getStorVal pre sevm.currentTarget
      key := by
    rw [allowanceEq]
    change
      (Devm.getStor sloadPre sevm.currentTarget).get key =
        (Devm.getStor pre sevm.currentTarget).get key
    rw [entryStorage]

  -- Infinite or finite allowance.
  rcases ProducesWord.isMax_arm_trace (ProducesWord.loadWord allowanceAt)
      branchWf branchReads branchStack run with maxArm | ordinaryArm
  · obtain ⟨-, callPre, callStack, callWf, callReads, callQuiet, callRun⟩ :=
      maxArm
    obtain ⟨bodyPre, burn, bodyRun⟩ := runCompiledTo_call_inv lookup callRun
    refine ⟨bodyPre, key, allowance, keyNotAddress, keyNotSupply,
      allowanceValue, Or.inl ?_, ?_, ?_, ?_, ?_, ?_, bodyRun⟩
    · rw [← congrFun (funext (getStor_eq_of_state_eq burn.state))
          sevm.currentTarget,
        ← congrFun (funext (getStor_eq_of_state_eq callQuiet.1))
          sevm.currentTarget,
        ← congrFun branchStorage sevm.currentTarget]
    · intro account _
      rw [← congrFun (funext (getStor_eq_of_state_eq burn.state)) account,
        ← congrFun (funext (getStor_eq_of_state_eq callQuiet.1)) account,
        ← congrFun branchStorage account]
    · exact branchLogs.trans (callQuiet.2.trans burn.logs)
    · rw [← burn.stack]
      exact callStack
    · rw [← burn.memory]; exact callWf
    · rw [← burn.memory]; exact callReads
  · obtain ⟨-, testPre, testStack, testWf, testReads, testQuiet, run⟩ :=
      ordinaryArm

    -- Require the allowance to cover the amount.
    obtain ⟨coverLoadPre, coverAmountRun, run⟩ := runCompiledTo_prepend_inv run
    obtain ⟨coverAmountPrefix, coverLoadWf, coverLoadReads,
        coverAmountState⟩ :=
      of_run_loadWordAt_image testStack testWf testReads amountAtStaged
        coverAmountRun
    have coverAmountLogs : testPre.logs = coverLoadPre.logs := by
      refine Line.of_inv Devm.logs ?_ coverAmountRun
      unfold ProrataWethVault.loadWord
      line_inv
    obtain ⟨coverTestPre, coverLoadRun, run⟩ := runCompiledTo_prepend_inv run
    obtain ⟨coverLoadPrefix, coverTestWf, coverTestReads, coverLoadState⟩ :=
      of_run_loadWordAt_image coverAmountPrefix coverLoadWf coverLoadReads
        allowanceAt coverLoadRun
    have coverLoadLogs : coverLoadPre.logs = coverTestPre.logs := by
      refine Line.of_inv Devm.logs ?_ coverLoadRun
      unfold ProrataWethVault.loadWord
      line_inv
    obtain ⟨coverBranchPre, coverTestRun, coverBranchRun⟩ :=
      runCompiledTo_next_inv run
    have coverTestSource := Ninst.Run.of_runCompiled coverTestRun
    have coverTestPrefix := prefix_of_lt coverTestSource coverLoadPrefix
    have coverTestMemory : coverTestPre.memory = coverBranchPre.memory :=
      Ninst.Hinv.inv (f := Devm.memory) coverTestSource
    have coverTestStorage :
        Devm.getStor coverTestPre = Devm.getStor coverBranchPre :=
      Ninst.Hinv.inv (f := Devm.getStor) coverTestSource
    have coverTestLogs : coverTestPre.logs = coverBranchPre.logs :=
      Ninst.Hinv.inv (f := Devm.logs) coverTestSource
    have covered : ¬ allowance < amount := by
      intro allowanceLt
      have onePrefix : (1 : B256) :: tail <<+ coverBranchPre.stack := by
        simpa [B256.ltCheck, allowanceLt] using coverTestPrefix
      obtain ⟨revertPre, branchWord, branchWordNe, revertPop, revertRun, -⟩ :=
        Func.RunCompiledTo.succ_branch_of_prefix
          (by decide : (1 : B256) ≠ 0) onePrefix coverBranchRun
      obtain ⟨revertPost, impossible, -⟩ := runCompiledTo_revert_inv revertRun
      cases impossible
    have coverZeroPrefix : (0 : B256) :: tail <<+ coverBranchPre.stack := by
      simpa [B256.ltCheck, covered] using coverTestPrefix
    obtain ⟨spendPre, coverPop, run, spendStack⟩ :=
      Func.RunCompiledTo.zero_branch_of_prefix coverZeroPrefix coverBranchRun
    have spendWf : Mem.Wf spendPre.memory := by
      rw [← coverPop.memory, ← coverTestMemory]; exact coverTestWf
    have spendReads : Mem.Reads spendPre.memory stagedImage := by
      rw [← coverPop.memory, ← coverTestMemory]; exact coverTestReads

    -- Decrement exactly the allowance slot.
    obtain ⟨spendLoadPre, spendAmountRun, run⟩ := runCompiledTo_prepend_inv run
    obtain ⟨spendAmountPrefix, spendLoadWf, spendLoadReads, spendAmountState⟩ :=
      of_run_loadWordAt_image spendStack spendWf spendReads amountAtStaged
        spendAmountRun
    have spendAmountLogs : spendPre.logs = spendLoadPre.logs := by
      refine Line.of_inv Devm.logs ?_ spendAmountRun
      unfold ProrataWethVault.loadWord
      line_inv
    obtain ⟨subPre, spendLoadRun, run⟩ := runCompiledTo_prepend_inv run
    obtain ⟨spendLoadPrefix, subWf, subReads, spendLoadState⟩ :=
      of_run_loadWordAt_image spendAmountPrefix spendLoadWf spendLoadReads
        allowanceAt spendLoadRun
    have spendLoadLogs : spendLoadPre.logs = subPre.logs := by
      refine Line.of_inv Devm.logs ?_ spendLoadRun
      unfold ProrataWethVault.loadWord
      line_inv
    obtain ⟨keyLoadPre, subRun, run⟩ := runCompiledTo_next_inv run
    have subSource := Ninst.Run.of_runCompiled subRun
    have subPrefix : (allowance - amount) :: tail <<+ keyLoadPre.stack :=
      prefix_of_sub subSource spendLoadPrefix
    have subMemory : subPre.memory = keyLoadPre.memory :=
      Ninst.Hinv.inv (f := Devm.memory) subSource
    have subStorage : Devm.getStor subPre = Devm.getStor keyLoadPre :=
      Ninst.Hinv.inv (f := Devm.getStor) subSource
    have subLogs : subPre.logs = keyLoadPre.logs :=
      Ninst.Hinv.inv (f := Devm.logs) subSource
    have keyLoadWf : Mem.Wf keyLoadPre.memory := by
      rw [← subMemory]; exact subWf
    have keyLoadReads : Mem.Reads keyLoadPre.memory stagedImage := by
      rw [← subMemory]; exact subReads
    have scratchAtStaged : Bytes.toB256
        (stagedImage.sliceD (scratchWord * 32).toNat 32 0) = key := by
      rw [stagedImageDef, allowanceStagingImage]
      rw [Bytes.readWord_writeAt_of_disjoint]
      · exact Bytes.readWord_writeAt_self _ _ _
      · left
        decide +kernel
    obtain ⟨storePre, keyLoadRun, run⟩ := runCompiledTo_prepend_inv run
    obtain ⟨keyLoadPrefix, storeWf, storeReads, keyLoadState⟩ :=
      of_run_loadWordAt_image subPrefix keyLoadWf keyLoadReads scratchAtStaged
        keyLoadRun
    have keyLoadLogs : keyLoadPre.logs = storePre.logs := by
      refine Line.of_inv Devm.logs ?_ keyLoadRun
      unfold ProrataWethVault.loadWord
      line_inv
    obtain ⟨callPre, storeRun, run⟩ := runCompiledTo_next_inv run
    have storeSource := Ninst.Run.of_runCompiled storeRun
    have storeSet : Devm.getStor callPre sevm.currentTarget =
        (Devm.getStor storePre sevm.currentTarget).set key
          (allowance - amount) :=
      sstore_getStor_set storeSource keyLoadPrefix
    have storeForeign : ∀ account, sevm.currentTarget ≠ account →
        Devm.getStor callPre account = Devm.getStor storePre account := by
      intro account accountNe
      obtain ⟨pc, registerRun⟩ := of_run_reg storeSource
      exact sstore_preserves_getStor_ne registerRun accountNe
    have storeStack : tail <<+ callPre.stack :=
      prefix_of_sstore storeSource keyLoadPrefix
    have storeLogs : storePre.logs = callPre.logs :=
      Ninst.Hinv.inv (f := Devm.logs) storeSource
    obtain ⟨bodyPre, burn, bodyRun⟩ := runCompiledTo_call_inv lookup run

    have preStore : Devm.getStor pre = Devm.getStor storePre :=
      branchStorage.trans ((funext (getStor_eq_of_state_eq testQuiet.1)).trans
        ((funext (getStor_eq_of_state_eq coverAmountState)).trans
          ((funext (getStor_eq_of_state_eq coverLoadState)).trans
            (coverTestStorage.trans
              ((funext (getStor_eq_of_state_eq coverPop.state)).trans
                ((funext (getStor_eq_of_state_eq spendAmountState)).trans
                  ((funext (getStor_eq_of_state_eq spendLoadState)).trans
                    (subStorage.trans
                      (funext
                        (getStor_eq_of_state_eq keyLoadState))))))))))
    have preLogs : pre.logs = storePre.logs :=
      branchLogs.trans (testQuiet.2.trans (coverAmountLogs.trans
        (coverLoadLogs.trans (coverTestLogs.trans (coverPop.logs.trans
          (spendAmountLogs.trans (spendLoadLogs.trans
            (subLogs.trans keyLoadLogs))))))))
    refine ⟨bodyPre, key, allowance, keyNotAddress, keyNotSupply,
      allowanceValue, Or.inr ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, bodyRun⟩
    · by_contra amountLarge
      exact covered (B256.lt_of_toNat_lt_toNat (by omega))
    · rw [← congrFun (funext (getStor_eq_of_state_eq burn.state))
          sevm.currentTarget, storeSet, ← congrFun preStore sevm.currentTarget]
    · intro account accountNe
      rw [← congrFun (funext (getStor_eq_of_state_eq burn.state)) account,
        storeForeign account accountNe, ← congrFun preStore account]
    · exact preLogs.trans (storeLogs.trans burn.logs)
    · rw [← burn.stack]
      exact storeStack
    · rw [← burn.memory, ← Ninst.Hinv.inv (f := Devm.memory) storeSource]
      exact storeWf
    · rw [← burn.memory, ← Ninst.Hinv.inv (f := Devm.memory) storeSource]
      exact storeReads

/-- The image the authorization step hands to the burn tail. -/
def outboundStagedImage
    (image : Bytes) (owner spender : B256) (bodyImage : Bytes) : Prop :=
  bodyImage = image ∨
    ∃ key allowance,
      bodyImage = allowanceStagingImage image owner spender key allowance

/-- Every operation word above the allowance staging region and below the
allowance word itself reads the same through either authorization route. -/
theorem outboundStagedImage_readWord
    {image bodyImage : Bytes} {owner spender w : B256}
    (staged : outboundStagedImage image owner spender bodyImage)
    (aboveKeyWords : 64 ≤ (w * 32).toNat)
    (aboveScratch : (scratchWord * 32).toNat + 32 ≤ (w * 32).toNat)
    (belowAllowance : (w * 32).toNat + 32 ≤ (allowanceWord * 32).toNat) :
    Bytes.toB256 (bodyImage.sliceD (w * 32).toNat 32 0) =
      Bytes.toB256 (image.sliceD (w * 32).toNat 32 0) := by
  rcases staged with direct | ⟨key, allowance, spent⟩
  · rw [direct]
  · rw [spent, allowanceStagingImage, allowanceKeyImage]
    rw [Bytes.readWord_writeAt_of_disjoint, Bytes.readWord_writeAt_of_disjoint,
      Bytes.readWord_writeAt_of_disjoint, Bytes.readWord_writeAt_of_disjoint]
    · right
      omega
    · right
      omega
    · right
      exact aboveScratch
    · left
      exact belowAllowance

/-- The outbound authorization step: either the caller owns the shares, or a
staged allowance covers the burn and is decremented by exactly it.  Neither
route moves a share row or the supply, and neither emits a log. -/
theorem outboundAuthorization_trace
    {fs : List Func} {sevm : Sevm} {pre final : Devm}
    {image : Bytes} {amountSel owner amount : B256} {continuation : Nat}
    {body : Func} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (ownerAt : Bytes.toB256
      (image.sliceD (ownerWord * 32).toNat 32 0) = owner)
    (amountAt : Bytes.toB256
      (image.sliceD (amountSel * 32).toNat 32 0) = amount)
    (amountAboveKeyWords : 64 ≤ (amountSel * 32).toNat)
    (amountAboveScratch :
      (scratchWord * 32).toNat + 32 ≤ (amountSel * 32).toNat)
    (amountBelowAllowance :
      (amountSel * 32).toNat + 32 ≤ (allowanceWord * 32).toNat)
    (stack : tail <<+ pre.stack)
    (lookup : fs[continuation]? = some body)
    (run : Func.RunCompiledTo fs sevm pre
      (loadWord ownerWord +++ caller ::: eq :::
        (.call continuation <?>
          spendAllowance (loadWord ownerWord) [caller] (loadWord amountSel)
            continuation)) (.ok final)) :
    ∃ bodyPre bodyImage,
      (∀ key, ValidAdr key ∨ key = supplySlot →
        Devm.getStorVal bodyPre sevm.currentTarget key =
          Devm.getStorVal pre sevm.currentTarget key) ∧
      (∀ account, sevm.currentTarget ≠ account →
        Devm.getStor bodyPre account = Devm.getStor pre account) ∧
      pre.logs = bodyPre.logs ∧
      tail <<+ bodyPre.stack ∧
      Mem.Wf bodyPre.memory ∧
      Mem.Reads bodyPre.memory bodyImage ∧
      outboundStagedImage image owner sevm.caller.toB256 bodyImage ∧
      Func.RunCompiledTo fs sevm bodyPre body (.ok final) := by
  -- Compare the staged owner against the frame caller.
  obtain ⟨callerPre, ownerRun, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨ownerPrefix, callerWf, callerReads, ownerState⟩ :=
    of_run_loadWordAt_image stack memoryWf memoryReads ownerAt ownerRun
  have ownerLogs : pre.logs = callerPre.logs := by
    refine Line.of_inv Devm.logs ?_ ownerRun
    unfold ProrataWethVault.loadWord
    line_inv
  obtain ⟨testPre, callerRun, run⟩ := runCompiledTo_next_inv run
  have callerSource := Ninst.Run.of_runCompiled callerRun
  have callerPush := of_run_caller callerSource
  have callerPrefix : sevm.caller.toB256 :: owner :: tail <<+ testPre.stack :=
    prefix_of_push callerPush ownerPrefix
  obtain ⟨branchPre, testRun, branchRun⟩ := runCompiledTo_next_inv run
  have testSource := Ninst.Run.of_runCompiled testRun
  have testPrefix := prefix_of_eq testSource callerPrefix
  have branchWf : Mem.Wf branchPre.memory := by
    rw [← Ninst.Hinv.inv (f := Devm.memory) testSource, ← callerPush.memory]
    exact callerWf
  have branchReads : Mem.Reads branchPre.memory image := by
    rw [← Ninst.Hinv.inv (f := Devm.memory) testSource, ← callerPush.memory]
    exact callerReads
  have branchStorage : Devm.getStor pre = Devm.getStor branchPre :=
    (funext (getStor_eq_of_state_eq ownerState)).trans
      ((funext (getStor_eq_of_state_eq callerPush.state)).trans
        (Ninst.Hinv.inv (f := Devm.getStor) testSource))
  have branchLogs : pre.logs = branchPre.logs :=
    ownerLogs.trans (callerPush.logs.trans
      (Ninst.Hinv.inv (f := Devm.logs) testSource))
  by_cases ownerIsCaller : sevm.caller.toB256 = owner
  · -- The caller owns the shares: tail-call the burn directly.
    have onePrefix : (1 : B256) :: tail <<+ branchPre.stack := by
      simpa [B256.eqCheck, ownerIsCaller] using testPrefix
    obtain ⟨callPre, branchWord, branchWordNe, callPop, callRun, callStack⟩ :=
      Func.RunCompiledTo.succ_branch_of_prefix
        (by decide : (1 : B256) ≠ 0) onePrefix branchRun
    obtain ⟨bodyPre, burn, bodyRun⟩ := runCompiledTo_call_inv lookup callRun
    have bodyStorage : Devm.getStor pre = Devm.getStor bodyPre :=
      branchStorage.trans
        ((funext (getStor_eq_of_state_eq callPop.state)).trans
          (funext (getStor_eq_of_state_eq burn.state)))
    refine ⟨bodyPre, image, ?_, ?_, ?_, ?_, ?_, ?_, Or.inl rfl, bodyRun⟩
    · intro key _
      change
        (Devm.getStor bodyPre sevm.currentTarget).get key =
          (Devm.getStor pre sevm.currentTarget).get key
      rw [← congrFun bodyStorage sevm.currentTarget]
    · intro account _
      rw [← congrFun bodyStorage account]
    · exact branchLogs.trans (callPop.logs.trans burn.logs)
    · rw [← burn.stack]
      exact callStack
    · rw [← burn.memory, ← callPop.memory]
      exact branchWf
    · rw [← burn.memory, ← callPop.memory]
      exact branchReads
  · -- Otherwise a staged allowance must cover the burn.
    have zeroPrefix : (0 : B256) :: tail <<+ branchPre.stack := by
      simpa [B256.eqCheck, ownerIsCaller] using testPrefix
    obtain ⟨spendPre, spendPop, spendRun, spendStack⟩ :=
      Func.RunCompiledTo.zero_branch_of_prefix zeroPrefix branchRun
    have spendWf : Mem.Wf spendPre.memory := by
      rw [← spendPop.memory]; exact branchWf
    have spendReads : Mem.Reads spendPre.memory image := by
      rw [← spendPop.memory]; exact branchReads
    have spendOwnerAt : Bytes.toB256
        (image.sliceD (ownerWord * 32).toNat 32 0) = owner := ownerAt
    obtain ⟨bodyPre, key, allowance, keyNotAddress, keyNotSupply, -,
        allowanceRoute, foreign, logs, bodyStack, bodyWf, bodyReads,
        bodyRun⟩ :=
      spendAllowance_trace spendWf spendReads spendOwnerAt amountAt
        amountAboveKeyWords amountAboveScratch amountBelowAllowance
        spendStack lookup spendRun
    have spendStorage : Devm.getStor pre = Devm.getStor spendPre :=
      branchStorage.trans (funext (getStor_eq_of_state_eq spendPop.state))
    refine ⟨bodyPre, _, ?_, ?_, ?_, bodyStack, bodyWf, bodyReads,
      Or.inr ⟨key, allowance, rfl⟩, bodyRun⟩
    · intro slot slotShape
      change
        (Devm.getStor bodyPre sevm.currentTarget).get slot =
          (Devm.getStor pre sevm.currentTarget).get slot
      rw [congrFun spendStorage sevm.currentTarget]
      rcases allowanceRoute with unchanged | ⟨-, decremented⟩
      · rw [unchanged]
      · rw [decremented, Stor.get_set_ne]
        intro slotIsKey
        rcases slotShape with slotAddress | slotSupply
        · exact keyNotAddress (slotIsKey ▸ slotAddress)
        · exact keyNotSupply (slotIsKey.trans slotSupply)
    · intro account accountNe
      rw [foreign account accountNe, ← congrFun spendStorage account]
    · exact branchLogs.trans (spendPop.logs.trans logs)

end ProrataWethVault

end Blanc
