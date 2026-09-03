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

end ProrataWethVault

end Blanc
