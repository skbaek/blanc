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

/-! ## Code frame

The outbound flows write storage *before* their WETH child, so a configuration
premise about the WETH program cannot ride on state equality the way the
inbound ones do.  It rides on this instead: no register instruction installs
code, so every seam below can carry the installed-code world forward. -/

theorem register_getCode {sevm : Sevm} {s s' : Devm} {r : Rinst}
    (run : Ninst.Run sevm s (Ninst.reg r) s') :
    Devm.getCode s' = Devm.getCode s := by
  obtain ⟨pc, registerRun⟩ := of_run_reg run
  exact funext (Rinst.preserves_getCode registerRun)

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
      Devm.getCode pre = Devm.getCode bodyPre ∧
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
  have codeFrame : Devm.getCode pre = Devm.getCode bodyPre :=
    (Line.of_inv Devm.getCode (by
        unfold ProrataWethVault.loadWord
        line_inv) ownerRun).trans <|
      (register_getCode sloadSource).symm.trans <|
        (Line.of_inv Devm.getCode (by
            unfold mstoreAt
            line_inv) balanceStoreRun).trans <|
          (Line.of_inv Devm.getCode (by
              unfold ProrataWethVault.loadWord
              line_inv) sharesRun).trans <|
            (Line.of_inv Devm.getCode (by
                unfold ProrataWethVault.loadWord
                line_inv) balanceLoadRun).trans <|
              (register_getCode testSource).symm.trans
                (funext (getCode_eq_of_state_eq bodyPop.state))
  refine ⟨bodyPre, balance, ?_, ?_, bodyPrefix, bodyWf, bodyReads, ?_,
    codeFrame, ?_, bodyRun⟩
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
      Devm.getCode pre = Devm.getCode bodyPre ∧
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
  have codeFrame : Devm.getCode pre = Devm.getCode bodyPre :=
    (Line.of_inv Devm.getCode (by
        unfold ProrataWethVault.loadWord
        line_inv) ownerRun).trans <|
      (Line.of_inv Devm.getCode (by
          unfold mstoreAt
          line_inv) ownerStoreRun).trans <|
        (funext (getCode_eq_of_state_eq callerPush.state)).trans <|
          (Line.of_inv Devm.getCode (by
              unfold mstoreAt
              line_inv) spenderStoreRun).trans <|
            (Line.of_inv Devm.getCode (by
                simp only [pushList, List.map]
                line_inv) pushWindowLine).trans <|
              (register_getCode keccakSource).symm.trans
                (funext (getCode_eq_of_state_eq collisionState))
  refine ⟨bodyPre, keyNotAddress, keyNotSupply, bodyPrefix, ?_, ?_, ?_,
    codeFrame, ?_, bodyRun⟩
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
    ∃ bodyPre allowance,
      ¬ ValidAdr (allowanceKey owner sevm.caller.toB256) ∧
      allowanceKey owner sevm.caller.toB256 ≠ supplySlot ∧
      allowance = Devm.getStorVal pre sevm.currentTarget
        (allowanceKey owner sevm.caller.toB256) ∧
      amount.toNat ≤ allowance.toNat ∧
      ((allowance = B256.max ∧
          Devm.getStor bodyPre sevm.currentTarget =
            Devm.getStor pre sevm.currentTarget) ∨
        Devm.getStor bodyPre sevm.currentTarget =
          (Devm.getStor pre sevm.currentTarget).set
            (allowanceKey owner sevm.caller.toB256) (allowance - amount)) ∧
      (∀ account, sevm.currentTarget ≠ account →
        Devm.getStor bodyPre account = Devm.getStor pre account) ∧
      pre.logs = bodyPre.logs ∧
      Devm.getCode pre = Devm.getCode bodyPre ∧
      tail <<+ bodyPre.stack ∧
      Mem.Wf bodyPre.memory ∧
      Mem.Reads bodyPre.memory
        (allowanceStagingImage image owner sevm.caller.toB256
          (allowanceKey owner sevm.caller.toB256) allowance) ∧
      Func.RunCompiledTo fs sevm bodyPre body (.ok final) := by
  simp only [spendAllowance] at run

  -- Hash and guard the allowance key.
  obtain ⟨scratchStorePre, keyNotAddress, keyNotSupply, keyPrefix, keyWf,
      keyReads, keyState, keyCode, keyLogs, run⟩ :=
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
  have branchCode : Devm.getCode pre = Devm.getCode branchPre :=
    keyCode.trans <|
      (Line.of_inv Devm.getCode (by
          unfold mstoreAt
          line_inv) scratchStoreRun).trans <|
        (Line.of_inv Devm.getCode (by
            unfold ProrataWethVault.loadWord
            line_inv) scratchLoadRun).trans <|
          (register_getCode sloadSource).symm.trans
            (Line.of_inv Devm.getCode (by
              unfold mstoreAt
              line_inv) allowanceStoreRun)
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
  · obtain ⟨allowanceMax, callPre, callStack, callWf, callReads, callQuiet,
      callRun⟩ := maxArm
    obtain ⟨bodyPre, burn, bodyRun⟩ := runCompiledTo_call_inv lookup callRun
    have amountFits : amount.toNat ≤ allowance.toNat := by
      rw [allowanceMax, maxWord_toNat]
      have bound := B256.toNat_lt amount
      simp only [maxWordN, wordModulusN] at *
      omega
    refine ⟨bodyPre, allowance, keyNotAddress, keyNotSupply,
      allowanceValue, amountFits, Or.inl ⟨allowanceMax, ?_⟩, ?_, ?_,
      branchCode.trans ((funext (getCode_eq_of_state_eq callQuiet.1)).trans
        (funext (getCode_eq_of_state_eq burn.state))),
      ?_, ?_, ?_, bodyRun⟩
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
    have spendCode : Devm.getCode pre = Devm.getCode bodyPre :=
      branchCode.trans <|
        (funext (getCode_eq_of_state_eq testQuiet.1)).trans <|
          (Line.of_inv Devm.getCode (by
              unfold ProrataWethVault.loadWord
              line_inv) coverAmountRun).trans <|
            (Line.of_inv Devm.getCode (by
                unfold ProrataWethVault.loadWord
                line_inv) coverLoadRun).trans <|
              (register_getCode coverTestSource).symm.trans <|
                (funext (getCode_eq_of_state_eq coverPop.state)).trans <|
                  (Line.of_inv Devm.getCode (by
                      unfold ProrataWethVault.loadWord
                      line_inv) spendAmountRun).trans <|
                    (Line.of_inv Devm.getCode (by
                        unfold ProrataWethVault.loadWord
                        line_inv) spendLoadRun).trans <|
                      (register_getCode subSource).symm.trans <|
                        (Line.of_inv Devm.getCode (by
                            unfold ProrataWethVault.loadWord
                            line_inv) keyLoadRun).trans <|
                          (register_getCode storeSource).symm.trans
                            (funext (getCode_eq_of_state_eq burn.state))
    have amountFits : amount.toNat ≤ allowance.toNat := by
      by_contra amountLarge
      exact covered (B256.lt_of_toNat_lt_toNat (by omega))
    refine ⟨bodyPre, allowance, keyNotAddress, keyNotSupply,
      allowanceValue, amountFits, Or.inr ?_, ?_, ?_, spendCode, ?_, ?_, ?_,
      bodyRun⟩
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

/-- What an outbound flow did to the caller's allowance over the owner.

Either the caller owns the shares, in which case no allowance is consulted and
none is claimed about, or the caller is a third party, the hashed allowance key
aliases neither a share row nor the supply, the allowance covers the burn, and
it is either infinite and left alone or decremented by exactly the burn.

The owner branch deliberately says nothing about any allowance slot.  The
collision guard runs only on the third-party route, so on the owner route the
vault has no proof that the hashed key is distinct from the share rows the same
walk writes -- and it does not need one, because it never reads or writes an
allowance there.

This is stated pointwise at the allowance slot rather than as a whole-`Stor`
equation because the same walk also moves the owner's share row and the
supply. -/
def AllowanceSpent (sevm : Sevm) (owner shares : B256) (pre post : Devm) :
    Prop :=
  sevm.caller.toB256 = owner ∨
    (sevm.caller.toB256 ≠ owner ∧
      ¬ ValidAdr (allowanceKey owner sevm.caller.toB256) ∧
      allowanceKey owner sevm.caller.toB256 ≠ supplySlot ∧
      shares.toNat ≤ (Devm.getStorVal pre sevm.currentTarget
        (allowanceKey owner sevm.caller.toB256)).toNat ∧
      ((Devm.getStorVal pre sevm.currentTarget
              (allowanceKey owner sevm.caller.toB256) = B256.max ∧
            Devm.getStorVal post sevm.currentTarget
                (allowanceKey owner sevm.caller.toB256) =
              Devm.getStorVal pre sevm.currentTarget
                (allowanceKey owner sevm.caller.toB256)) ∨
        Devm.getStorVal post sevm.currentTarget
            (allowanceKey owner sevm.caller.toB256) =
          Devm.getStorVal pre sevm.currentTarget
              (allowanceKey owner sevm.caller.toB256) - shares))

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
      Devm.getCode pre = Devm.getCode bodyPre ∧
      AllowanceSpent sevm owner amount pre bodyPre ∧
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
  have branchCode : Devm.getCode pre = Devm.getCode branchPre :=
    (Line.of_inv Devm.getCode (by
        unfold ProrataWethVault.loadWord
        line_inv) ownerRun).trans
      ((funext (getCode_eq_of_state_eq callerPush.state)).trans
        (register_getCode testSource).symm)
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
    refine ⟨bodyPre, image, ?_, ?_, ?_,
      branchCode.trans ((funext (getCode_eq_of_state_eq callPop.state)).trans
        (funext (getCode_eq_of_state_eq burn.state))),
      Or.inl ownerIsCaller, ?_, ?_, ?_, Or.inl rfl, bodyRun⟩
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
    obtain ⟨bodyPre, allowance, keyNotAddress, keyNotSupply, allowanceValue,
        amountFits, allowanceRoute, foreign, logs, spendCode, bodyStack,
        bodyWf, bodyReads, bodyRun⟩ :=
      spendAllowance_trace spendWf spendReads spendOwnerAt amountAt
        amountAboveKeyWords amountAboveScratch amountBelowAllowance
        spendStack lookup spendRun
    have spendStorage : Devm.getStor pre = Devm.getStor spendPre :=
      branchStorage.trans (funext (getStor_eq_of_state_eq spendPop.state))
    have keyValue : Devm.getStorVal pre sevm.currentTarget
        (allowanceKey owner sevm.caller.toB256) = allowance := by
      rw [allowanceValue]
      change
        (Devm.getStor pre sevm.currentTarget).get
            (allowanceKey owner sevm.caller.toB256) =
          (Devm.getStor spendPre sevm.currentTarget).get
            (allowanceKey owner sevm.caller.toB256)
      rw [spendStorage]
    refine ⟨bodyPre, _, ?_, ?_, ?_,
      branchCode.trans ((funext (getCode_eq_of_state_eq spendPop.state)).trans
        spendCode),
      Or.inr ⟨ownerIsCaller, keyNotAddress, keyNotSupply, ?_, ?_⟩,
      bodyStack, bodyWf, bodyReads,
      Or.inr ⟨allowanceKey owner sevm.caller.toB256, allowance, rfl⟩,
      bodyRun⟩
    · intro slot slotShape
      change
        (Devm.getStor bodyPre sevm.currentTarget).get slot =
          (Devm.getStor pre sevm.currentTarget).get slot
      rw [congrFun spendStorage sevm.currentTarget]
      rcases allowanceRoute with ⟨-, unchanged⟩ | decremented
      · rw [unchanged]
      · rw [decremented, Stor.get_set_ne]
        intro slotIsKey
        rcases slotShape with slotAddress | slotSupply
        · exact keyNotAddress (slotIsKey ▸ slotAddress)
        · exact keyNotSupply (slotIsKey.trans slotSupply)
    · intro account accountNe
      rw [foreign account accountNe, ← congrFun spendStorage account]
    · exact branchLogs.trans (spendPop.logs.trans logs)
    · rw [keyValue]
      exact amountFits
    · rcases allowanceRoute with ⟨allowanceMax, unchanged⟩ | decremented
      · refine Or.inl ⟨keyValue.trans allowanceMax, ?_⟩
        change
          (Devm.getStor bodyPre sevm.currentTarget).get
              (allowanceKey owner sevm.caller.toB256) =
            (Devm.getStor pre sevm.currentTarget).get
              (allowanceKey owner sevm.caller.toB256)
        rw [unchanged, congrFun spendStorage sevm.currentTarget]
      · refine Or.inr ?_
        change
          (Devm.getStor bodyPre sevm.currentTarget).get
              (allowanceKey owner sevm.caller.toB256) =
            (Devm.getStor pre sevm.currentTarget).get
                (allowanceKey owner sevm.caller.toB256) - amount
        rw [decremented, Stor.get_set_self]
        exact congrArg (· - amount) keyValue.symm

/-! ## Burn and supply settlement -/

/-- The share `Transfer(owner, 0, shares)` entry the vault emits when it burns.
The inbound mint's `mintTransferLog` is its mirror, with the roles swapped. -/
def burnTransferLog (sevm : Sevm) (owner shares : B256) : Log :=
  ⟨sevm.currentTarget, [transferEvent, owner, 0], shares.toBytes⟩

/-- The ERC-4626 `Withdraw(caller, receiver, owner, assets, shares)` entry. -/
def withdrawLogEntry
    (sevm : Sevm) (receiver owner assets shares : B256) : Log :=
  ⟨sevm.currentTarget,
    [withdrawEvent, sevm.caller.toB256, receiver, owner],
    assets.toBytes ++ shares.toBytes⟩

/-- The outbound burn debits the owner's staged share row, requires the burn to
fit the staged supply, decreases the supply by exactly it, and emits the burn
`Transfer` -- all before the WETH child runs.  No other account's storage
moves.

This is the inbound settlement read in reverse order as well as in reverse
direction: `finishInbound` credits *after* its child, while `finishOutbound`
burns *before* its child, which is what puts the share `Transfer` first in the
outbound log order. -/
theorem outboundBurn_trace
    {fs : List Func} {sevm : Sevm} {pre final : Devm}
    {image : Bytes} {sharesSel owner balance supply shares : B256}
    {tailFunc : Func} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (sharesAt : Bytes.toB256
      (image.sliceD (sharesSel * 32).toNat 32 0) = shares)
    (ownerAt : Bytes.toB256
      (image.sliceD (ownerWord * 32).toNat 32 0) = owner)
    (balanceAt : Bytes.toB256
      (image.sliceD (balanceWord * 32).toNat 32 0) = balance)
    (supplyAt : Bytes.toB256
      (image.sliceD (supplyWord * 32).toNat 32 0) = supply)
    (stack : tail <<+ pre.stack)
    (run : Func.RunCompiledTo fs sevm pre
      (loadWord sharesSel +++ loadWord balanceWord +++ sub :::
        loadWord ownerWord +++ sstore :::
        loadWord sharesSel +++ loadWord supplyWord +++ lt :::
        (Func.revert <?>
          (loadWord sharesSel +++ loadWord supplyWord +++ sub :::
            pushSupplySlot +++ sstore :::
            logBurnTransfer (loadWord sharesSel) +++ tailFunc)))
      (.ok final)) :
    ∃ bodyPre,
      shares.toNat ≤ supply.toNat ∧
      Devm.getStor bodyPre sevm.currentTarget =
        ((Devm.getStor pre sevm.currentTarget).set owner
          (balance - shares)).set supplySlot (supply - shares) ∧
      (∀ account, sevm.currentTarget ≠ account →
        Devm.getStor bodyPre account = Devm.getStor pre account) ∧
      bodyPre.logs = pre.logs ++ [burnTransferLog sevm owner shares] ∧
      Devm.getCode pre = Devm.getCode bodyPre ∧
      tail <<+ bodyPre.stack ∧
      Mem.Wf bodyPre.memory ∧
      Mem.Reads bodyPre.memory (Bytes.writeAt image 0 shares.toBytes) ∧
      Func.RunCompiledTo fs sevm bodyPre tailFunc (.ok final) := by
  -- Debit the owner's staged share row.
  obtain ⟨balanceLoadPre, sharesRun, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨sharesPrefix, balanceLoadWf, balanceLoadReads, sharesState⟩ :=
    of_run_loadWordAt_image stack memoryWf memoryReads sharesAt sharesRun
  have sharesLogs : pre.logs = balanceLoadPre.logs :=
    of_run_loadWordAt_logs sharesRun
  obtain ⟨subPre, balanceLoadRun, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨balanceLoadPrefix, subWf, subReads, balanceLoadState⟩ :=
    of_run_loadWordAt_image sharesPrefix balanceLoadWf balanceLoadReads
      balanceAt balanceLoadRun
  have balanceLoadLogs : balanceLoadPre.logs = subPre.logs :=
    of_run_loadWordAt_logs balanceLoadRun
  obtain ⟨ownerLoadPre, subRun, run⟩ := runCompiledTo_next_inv run
  have subSource := Ninst.Run.of_runCompiled subRun
  have subPrefix : (balance - shares) :: tail <<+ ownerLoadPre.stack :=
    prefix_of_sub subSource balanceLoadPrefix
  have subMemory : subPre.memory = ownerLoadPre.memory :=
    Ninst.Hinv.inv (f := Devm.memory) subSource
  have subStorage : Devm.getStor subPre = Devm.getStor ownerLoadPre :=
    Ninst.Hinv.inv (f := Devm.getStor) subSource
  have subLogs : subPre.logs = ownerLoadPre.logs :=
    Ninst.Hinv.inv (f := Devm.logs) subSource
  have ownerLoadWf : Mem.Wf ownerLoadPre.memory := by
    rw [← subMemory]; exact subWf
  have ownerLoadReads : Mem.Reads ownerLoadPre.memory image := by
    rw [← subMemory]; exact subReads
  obtain ⟨balanceStorePre, ownerRun, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨ownerPrefix, balanceStoreWf, balanceStoreReads, ownerState⟩ :=
    of_run_loadWordAt_image subPrefix ownerLoadWf ownerLoadReads ownerAt
      ownerRun
  have ownerLogs : ownerLoadPre.logs = balanceStorePre.logs :=
    of_run_loadWordAt_logs ownerRun
  obtain ⟨supplyTestPre, balanceStoreRun, run⟩ := runCompiledTo_next_inv run
  have balanceStoreSource := Ninst.Run.of_runCompiled balanceStoreRun
  have balanceSet : Devm.getStor supplyTestPre sevm.currentTarget =
      (Devm.getStor balanceStorePre sevm.currentTarget).set owner
        (balance - shares) :=
    sstore_getStor_set balanceStoreSource ownerPrefix
  have balanceForeign : ∀ account, sevm.currentTarget ≠ account →
      Devm.getStor supplyTestPre account =
        Devm.getStor balanceStorePre account :=
    fun _ ne => sstore_getStor_of_ne balanceStoreSource ne
  have balanceStoreStack : tail <<+ supplyTestPre.stack :=
    prefix_of_sstore balanceStoreSource ownerPrefix
  have balanceStoreMemory : balanceStorePre.memory = supplyTestPre.memory :=
    Ninst.Hinv.inv (f := Devm.memory) balanceStoreSource
  have balanceStoreLogs : balanceStorePre.logs = supplyTestPre.logs :=
    Ninst.Hinv.inv (f := Devm.logs) balanceStoreSource
  have supplyTestWf : Mem.Wf supplyTestPre.memory := by
    rw [← balanceStoreMemory]; exact balanceStoreWf
  have supplyTestReads : Mem.Reads supplyTestPre.memory image := by
    rw [← balanceStoreMemory]; exact balanceStoreReads

  -- Require the burn to fit the staged supply.
  obtain ⟨supplyLoadPre, roomSharesRun, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨roomSharesPrefix, supplyLoadWf, supplyLoadReads, roomSharesState⟩ :=
    of_run_loadWordAt_image balanceStoreStack supplyTestWf supplyTestReads
      sharesAt roomSharesRun
  have roomSharesLogs : supplyTestPre.logs = supplyLoadPre.logs :=
    of_run_loadWordAt_logs roomSharesRun
  obtain ⟨roomTestPre, supplyLoadRun, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨supplyLoadPrefix, roomTestWf, roomTestReads, supplyLoadState⟩ :=
    of_run_loadWordAt_image roomSharesPrefix supplyLoadWf supplyLoadReads
      supplyAt supplyLoadRun
  have supplyLoadLogs : supplyLoadPre.logs = roomTestPre.logs :=
    of_run_loadWordAt_logs supplyLoadRun
  obtain ⟨roomBranchPre, roomTestRun, roomBranchRun⟩ :=
    runCompiledTo_next_inv run
  have roomTestSource := Ninst.Run.of_runCompiled roomTestRun
  have roomTestPrefix := prefix_of_lt roomTestSource supplyLoadPrefix
  have roomTestMemory : roomTestPre.memory = roomBranchPre.memory :=
    Ninst.Hinv.inv (f := Devm.memory) roomTestSource
  have roomTestStorage :
      Devm.getStor roomTestPre = Devm.getStor roomBranchPre :=
    Ninst.Hinv.inv (f := Devm.getStor) roomTestSource
  have roomTestLogs : roomTestPre.logs = roomBranchPre.logs :=
    Ninst.Hinv.inv (f := Devm.logs) roomTestSource
  have supplyLarge : ¬ supply < shares := by
    intro supplyLt
    have onePrefix : (1 : B256) :: tail <<+ roomBranchPre.stack := by
      simpa [B256.ltCheck, supplyLt] using roomTestPrefix
    obtain ⟨revertPre, branchWord, branchWordNe, revertPop, revertRun, -⟩ :=
      Func.RunCompiledTo.succ_branch_of_prefix
        (by decide : (1 : B256) ≠ 0) onePrefix roomBranchRun
    obtain ⟨revertPost, impossible, -⟩ := runCompiledTo_revert_inv revertRun
    cases impossible
  have roomZeroPrefix : (0 : B256) :: tail <<+ roomBranchPre.stack := by
    simpa [B256.ltCheck, supplyLarge] using roomTestPrefix
  obtain ⟨decrPre, roomPop, run, decrStack⟩ :=
    Func.RunCompiledTo.zero_branch_of_prefix roomZeroPrefix roomBranchRun
  have decrWf : Mem.Wf decrPre.memory := by
    rw [← roomPop.memory, ← roomTestMemory]; exact roomTestWf
  have decrReads : Mem.Reads decrPre.memory image := by
    rw [← roomPop.memory, ← roomTestMemory]; exact roomTestReads

  -- Decrease the supply by exactly the burn.
  obtain ⟨decrSupplyPre, decrSharesRun, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨decrSharesPrefix, decrSupplyWf, decrSupplyReads, decrSharesState⟩ :=
    of_run_loadWordAt_image decrStack decrWf decrReads sharesAt decrSharesRun
  have decrSharesLogs : decrPre.logs = decrSupplyPre.logs :=
    of_run_loadWordAt_logs decrSharesRun
  obtain ⟨decrSubPre, decrSupplyRun, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨decrSupplyPrefix, decrSubWf, decrSubReads, decrSupplyState⟩ :=
    of_run_loadWordAt_image decrSharesPrefix decrSupplyWf decrSupplyReads
      supplyAt decrSupplyRun
  have decrSupplyLogs : decrSupplyPre.logs = decrSubPre.logs :=
    of_run_loadWordAt_logs decrSupplyRun
  obtain ⟨slotPushPre, decrSubRun, run⟩ := runCompiledTo_next_inv run
  have decrSubSource := Ninst.Run.of_runCompiled decrSubRun
  have decrSubPrefix : (supply - shares) :: tail <<+ slotPushPre.stack :=
    prefix_of_sub decrSubSource decrSupplyPrefix
  have decrSubMemory : decrSubPre.memory = slotPushPre.memory :=
    Ninst.Hinv.inv (f := Devm.memory) decrSubSource
  have decrSubStorage : Devm.getStor decrSubPre = Devm.getStor slotPushPre :=
    Ninst.Hinv.inv (f := Devm.getStor) decrSubSource
  have decrSubLogs : decrSubPre.logs = slotPushPre.logs :=
    Ninst.Hinv.inv (f := Devm.logs) decrSubSource
  obtain ⟨supplyStorePre, slotPushRun, run⟩ := runCompiledTo_prepend_inv run
  simp only [pushSupplySlot] at slotPushRun
  rcases Line.of_run_cons slotPushRun with ⟨zeroPost, zeroRun, slotTailRun⟩
  rcases Line.of_run_cons slotTailRun with ⟨_, notRun, slotNil⟩
  cases slotNil
  have zeroPush := of_run_pushB256 zeroRun
  have pushedZero : (0 : B256) :: (supply - shares) :: tail <<+
      zeroPost.stack := prefix_of_push zeroPush decrSubPrefix
  have slotPrefix : supplySlot :: (supply - shares) :: tail <<+
      supplyStorePre.stack := by
    have notZero : (~~~(0 : B256)) = supplySlot := by decide +kernel
    rw [← notZero]
    exact prefix_of_not notRun pushedZero
  obtain ⟨logPre, supplyStoreRun, run⟩ := runCompiledTo_next_inv run
  have supplyStoreSource := Ninst.Run.of_runCompiled supplyStoreRun
  have supplySet : Devm.getStor logPre sevm.currentTarget =
      (Devm.getStor supplyStorePre sevm.currentTarget).set supplySlot
        (supply - shares) :=
    sstore_getStor_set supplyStoreSource slotPrefix
  have supplyForeign : ∀ account, sevm.currentTarget ≠ account →
      Devm.getStor logPre account = Devm.getStor supplyStorePre account :=
    fun _ ne => sstore_getStor_of_ne supplyStoreSource ne
  have supplyStoreStack : tail <<+ logPre.stack :=
    prefix_of_sstore supplyStoreSource slotPrefix
  have supplyStoreLogs : supplyStorePre.logs = logPre.logs :=
    Ninst.Hinv.inv (f := Devm.logs) supplyStoreSource
  have slotMemory : decrSubPre.memory = logPre.memory :=
    decrSubMemory.trans (zeroPush.memory.trans
      ((Ninst.Hinv.inv (f := Devm.memory) notRun).trans
        (Ninst.Hinv.inv (f := Devm.memory) supplyStoreSource)))
  have logWf : Mem.Wf logPre.memory := by
    rw [← slotMemory]; exact decrSubWf
  have logReads : Mem.Reads logPre.memory image := by
    rw [← slotMemory]; exact decrSubReads

  -- Emit the burn transfer.
  obtain ⟨bodyPre, logRun, bodyRun⟩ := runCompiledTo_prepend_inv run
  have logLineRun := logRun
  have logStorage : Devm.getStor logPre = Devm.getStor bodyPre := by
    refine Line.of_inv Devm.getStor ?_ logLineRun
    unfold logBurnTransfer ProrataWethVault.loadWord mstoreAt logWith
    line_inv
  simp only [logBurnTransfer, List.append_assoc] at logRun
  obtain ⟨e1, logSharesRun, logRun⟩ :=
    of_run_append (loadWord sharesSel) logRun
  obtain ⟨logSharesPrefix, e1Wf, e1Reads, -⟩ :=
    of_run_loadWordAt_image supplyStoreStack logWf logReads sharesAt
      logSharesRun
  obtain ⟨e2, logStoreRun, logRun⟩ := of_run_append (mstoreAt 0) logRun
  obtain ⟨e2Stack, e2Wf, e2Reads, -⟩ :=
    of_run_mstoreAt_image logSharesPrefix e1Wf e1Reads logStoreRun
  obtain ⟨e3, zeroTopicRun, logRun⟩ := of_run_append [pushB256 0] logRun
  rcases Line.of_run_cons zeroTopicRun with ⟨_, zeroTopic, zeroTopicNil⟩
  cases zeroTopicNil
  have zeroTopicPush := of_run_pushB256 zeroTopic
  have e3Prefix : (0 : B256) :: tail <<+ e3.stack :=
    prefix_of_push zeroTopicPush e2Stack
  have e3Wf : Mem.Wf e3.memory := by rw [← zeroTopicPush.memory]; exact e2Wf
  have e3Reads : Mem.Reads e3.memory
      (Bytes.writeAt image ((0 : B256) * 32).toNat shares.toBytes) := by
    rw [← zeroTopicPush.memory]; exact e2Reads
  have ownerAtLogged : Bytes.toB256
      ((Bytes.writeAt image ((0 : B256) * 32).toNat shares.toBytes).sliceD
        (ownerWord * 32).toNat 32 0) = owner := by
    rw [Bytes.readWord_writeAt_of_disjoint]
    · exact ownerAt
    · right
      decide +kernel
  obtain ⟨e4, logOwnerRun, logRun⟩ :=
    of_run_append (loadWord ownerWord) logRun
  obtain ⟨e4Prefix, e4Wf, e4Reads, -⟩ :=
    of_run_loadWordAt_image e3Prefix e3Wf e3Reads ownerAtLogged logOwnerRun
  obtain ⟨e5, eventRun, logRun⟩ :=
    of_run_append [pushB256 transferEvent] logRun
  rcases Line.of_run_cons eventRun with ⟨_, eventPushRun, eventNil⟩
  cases eventNil
  have eventPush := of_run_pushB256 eventPushRun
  have e5Prefix : transferEvent :: owner :: 0 :: tail <<+ e5.stack :=
    prefix_of_push eventPush e4Prefix
  have e5Wf : Mem.Wf e5.memory := by rw [← eventPush.memory]; exact e4Wf
  have e5Reads : Mem.Reads e5.memory
      (Bytes.writeAt image ((0 : B256) * 32).toNat shares.toBytes) := by
    rw [← eventPush.memory]; exact e4Reads
  obtain ⟨bodyStack, emitted⟩ :=
    of_logWith_val (topics := [transferEvent, owner, 0]) (by simp)
      (by simpa using e5Prefix) logRun
  obtain ⟨bodyWf, bodyReads⟩ := of_logWith_image e5Wf e5Reads logRun
  have logWindow : (e5.memory.read ((0 : B256) * 32).toNat
      ((1 : B256) * 32).toNat).1 = shares.toBytes := by
    have zeroOffset : ((0 : B256) * 32).toNat = 0 := by decide +kernel
    have sizeWord : ((1 : B256) * 32).toNat = 32 := by decide +kernel
    rw [zeroOffset, sizeWord, Mem.Reads.read e5Reads, zeroOffset,
      show (32 : Nat) = shares.toBytes.length from
        (B256.length_toBytes shares).symm]
    exact Bytes.sliceD_writeAt image shares.toBytes 0
  have logPrefixLogs : logPre.logs = e5.logs :=
    (of_run_loadWordAt_logs logSharesRun).trans
      ((Line.of_inv Devm.logs (by
          unfold mstoreAt
          line_inv) logStoreRun).trans
        (zeroTopicPush.logs.trans
          ((of_run_loadWordAt_logs logOwnerRun).trans eventPush.logs)))

  -- Assemble the two storage writes and the single emitted entry.
  have preToBalanceStore : Devm.getStor pre = Devm.getStor balanceStorePre :=
    (funext (getStor_eq_of_state_eq sharesState)).trans
      ((funext (getStor_eq_of_state_eq balanceLoadState)).trans
        (subStorage.trans (funext (getStor_eq_of_state_eq ownerState))))
  have supplyTestToSupplyStore :
      Devm.getStor supplyTestPre = Devm.getStor supplyStorePre :=
    (funext (getStor_eq_of_state_eq roomSharesState)).trans
      ((funext (getStor_eq_of_state_eq supplyLoadState)).trans
        (roomTestStorage.trans
          ((funext (getStor_eq_of_state_eq roomPop.state)).trans
            ((funext (getStor_eq_of_state_eq decrSharesState)).trans
              ((funext (getStor_eq_of_state_eq decrSupplyState)).trans
                (decrSubStorage.trans
                  ((funext (getStor_eq_of_state_eq zeroPush.state)).trans
                    (Ninst.Hinv.inv (f := Devm.getStor) notRun))))))))
  have preToLogPre : pre.logs = logPre.logs :=
    sharesLogs.trans <| balanceLoadLogs.trans <| subLogs.trans <|
      ownerLogs.trans <| balanceStoreLogs.trans <| roomSharesLogs.trans <|
        supplyLoadLogs.trans <| roomTestLogs.trans <| roomPop.logs.trans <|
          decrSharesLogs.trans <| decrSupplyLogs.trans <| decrSubLogs.trans <|
            zeroPush.logs.trans <|
              (Ninst.Hinv.inv (f := Devm.logs) notRun).trans supplyStoreLogs
  have codeFrame : Devm.getCode pre = Devm.getCode bodyPre :=
    (Line.of_inv Devm.getCode (by
        unfold ProrataWethVault.loadWord
        line_inv) sharesRun).trans <|
      (Line.of_inv Devm.getCode (by
          unfold ProrataWethVault.loadWord
          line_inv) balanceLoadRun).trans <|
        (register_getCode subSource).symm.trans <|
          (Line.of_inv Devm.getCode (by
              unfold ProrataWethVault.loadWord
              line_inv) ownerRun).trans <|
            (register_getCode balanceStoreSource).symm.trans <|
              (Line.of_inv Devm.getCode (by
                  unfold ProrataWethVault.loadWord
                  line_inv) roomSharesRun).trans <|
                (Line.of_inv Devm.getCode (by
                    unfold ProrataWethVault.loadWord
                    line_inv) supplyLoadRun).trans <|
                  (register_getCode roomTestSource).symm.trans <|
                    (funext (getCode_eq_of_state_eq roomPop.state)).trans <|
                      (Line.of_inv Devm.getCode (by
                          unfold ProrataWethVault.loadWord
                          line_inv) decrSharesRun).trans <|
                        (Line.of_inv Devm.getCode (by
                            unfold ProrataWethVault.loadWord
                            line_inv) decrSupplyRun).trans <|
                          (register_getCode decrSubSource).symm.trans <|
                            (funext
                                (getCode_eq_of_state_eq zeroPush.state)).trans <|
                              (register_getCode notRun).symm.trans <|
                                (register_getCode
                                    supplyStoreSource).symm.trans
                                  (Line.of_inv Devm.getCode (by
                                    unfold logBurnTransfer
                                      ProrataWethVault.loadWord mstoreAt
                                      logWith
                                    line_inv) logLineRun)
  refine ⟨bodyPre, ?_, ?_, ?_, ?_, codeFrame, bodyStack, bodyWf, ?_,
    bodyRun⟩
  · by_contra sharesLarge
    exact supplyLarge (B256.lt_of_toNat_lt_toNat (by omega))
  · rw [← congrFun logStorage sevm.currentTarget, supplySet,
      ← congrFun supplyTestToSupplyStore sevm.currentTarget, balanceSet,
      ← congrFun preToBalanceStore sevm.currentTarget]
  · intro account accountNe
    rw [← congrFun logStorage account, supplyForeign account accountNe,
      ← congrFun supplyTestToSupplyStore account,
      balanceForeign account accountNe,
      ← congrFun preToBalanceStore account]
  · rw [emitted, logWindow, ← logPrefixLogs, ← preToLogPre]
    rfl
  · have zeroOffset : ((0 : B256) * 32).toNat = 0 := by decide +kernel
    rw [← zeroOffset]
    exact bodyReads

/-- Memory image after the two `Withdraw` data words are staged. -/
def outboundSettleImage (image : Bytes) (assets shares : B256) : Bytes :=
  Bytes.writeAt (Bytes.writeAt image 0 assets.toBytes) 32 shares.toBytes

/-- The outbound settlement runs *after* the WETH child: it emits the exact
ERC-4626 `Withdraw` entry and returns the quoted word, writing no storage. -/
theorem outboundSettle_trace
    {fs : List Func} {sevm : Sevm} {pre final : Devm}
    {image : Bytes} {assetsSel sharesSel returnedSel : B256}
    {assets shares owner receiver returned : B256} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (assetsAt : Bytes.toB256
      (image.sliceD (assetsSel * 32).toNat 32 0) = assets)
    (sharesAt : Bytes.toB256
      (image.sliceD (sharesSel * 32).toNat 32 0) = shares)
    (ownerAt : Bytes.toB256
      (image.sliceD (ownerWord * 32).toNat 32 0) = owner)
    (receiverAt : Bytes.toB256
      (image.sliceD (receiverWord * 32).toNat 32 0) = receiver)
    (returnedAt : Bytes.toB256
      (image.sliceD (returnedSel * 32).toNat 32 0) = returned)
    (sharesAboveWords : 64 ≤ (sharesSel * 32).toNat)
    (returnedAboveWords : 64 ≤ (returnedSel * 32).toNat)
    (stack : tail <<+ pre.stack)
    (run : Func.RunCompiledTo fs sevm pre
      (logWithdraw (loadWord assetsSel) (loadWord sharesSel) +++
        loadWord returnedSel +++ returnWord) (.ok final)) :
    ReturnsWord returned final ∧
      Devm.getStor final = Devm.getStor pre ∧
      final.logs = pre.logs ++
        [withdrawLogEntry sevm receiver owner assets shares] := by
  obtain ⟨returnLoadPre, logRun, run⟩ := runCompiledTo_prepend_inv run
  have logLineRun := logRun
  have logStorage : Devm.getStor pre = Devm.getStor returnLoadPre := by
    refine Line.of_inv Devm.getStor ?_ logLineRun
    unfold logWithdraw ProrataWethVault.loadWord mstoreAt logWith
    line_inv
  simp only [logWithdraw, List.append_assoc] at logRun

  -- Stage the two data words.
  obtain ⟨w1, assetsRun, logRun⟩ := of_run_append (loadWord assetsSel) logRun
  obtain ⟨assetsPrefix, w1Wf, w1Reads, -⟩ :=
    of_run_loadWordAt_image stack memoryWf memoryReads assetsAt assetsRun
  obtain ⟨w2, assetsStoreRun, logRun⟩ := of_run_append (mstoreAt 0) logRun
  obtain ⟨w2Stack, w2Wf, w2Reads, -⟩ :=
    of_run_mstoreAt_image assetsPrefix w1Wf w1Reads assetsStoreRun
  have zeroOffset : ((0 : B256) * 32).toNat = 0 := by decide +kernel
  have oneOffset : ((1 : B256) * 32).toNat = 32 := by decide +kernel
  rw [zeroOffset] at w2Reads
  have sharesAtStaged : Bytes.toB256
      ((Bytes.writeAt image 0 assets.toBytes).sliceD
        (sharesSel * 32).toNat 32 0) = shares := by
    rw [Bytes.readWord_writeAt_of_disjoint]
    · exact sharesAt
    · right
      omega
  obtain ⟨w3, sharesRun, logRun⟩ := of_run_append (loadWord sharesSel) logRun
  obtain ⟨sharesPrefix, w3Wf, w3Reads, -⟩ :=
    of_run_loadWordAt_image w2Stack w2Wf w2Reads sharesAtStaged sharesRun
  obtain ⟨w4, sharesStoreRun, logRun⟩ := of_run_append (mstoreAt 1) logRun
  obtain ⟨w4Stack, w4Wf, w4Reads, -⟩ :=
    of_run_mstoreAt_image sharesPrefix w3Wf w3Reads sharesStoreRun
  rw [oneOffset] at w4Reads
  have stagedReads : Mem.Reads w4.memory
      (outboundSettleImage image assets shares) := w4Reads
  have ownerAtStaged : Bytes.toB256
      ((outboundSettleImage image assets shares).sliceD
        (ownerWord * 32).toNat 32 0) = owner := by
    unfold outboundSettleImage
    rw [Bytes.readWord_writeAt_of_disjoint,
      Bytes.readWord_writeAt_of_disjoint]
    · exact ownerAt
    · right
      decide +kernel
    · right
      decide +kernel
  have receiverAtStaged : Bytes.toB256
      ((outboundSettleImage image assets shares).sliceD
        (receiverWord * 32).toNat 32 0) = receiver := by
    unfold outboundSettleImage
    rw [Bytes.readWord_writeAt_of_disjoint,
      Bytes.readWord_writeAt_of_disjoint]
    · exact receiverAt
    · right
      decide +kernel
    · right
      decide +kernel

  -- Push the three indexed topics and the event signature.
  obtain ⟨w5, ownerRun, logRun⟩ := of_run_append (loadWord ownerWord) logRun
  obtain ⟨ownerPrefix, w5Wf, w5Reads, -⟩ :=
    of_run_loadWordAt_image w4Stack w4Wf stagedReads ownerAtStaged ownerRun
  obtain ⟨w6, receiverRun, logRun⟩ :=
    of_run_append (loadWord receiverWord) logRun
  obtain ⟨receiverPrefix, w6Wf, w6Reads, -⟩ :=
    of_run_loadWordAt_image ownerPrefix w5Wf w5Reads receiverAtStaged
      receiverRun
  obtain ⟨w7, headRun, logRun⟩ :=
    of_run_append [caller, pushB256 withdrawEvent] logRun
  rcases Line.of_run_cons headRun with ⟨w6b, callerRun, headTailRun⟩
  rcases Line.of_run_cons headTailRun with ⟨_, eventRun, headNil⟩
  cases headNil
  have callerPush := of_run_caller callerRun
  have eventPush := of_run_pushB256 eventRun
  have topicPrefix : withdrawEvent :: sevm.caller.toB256 :: receiver ::
      owner :: tail <<+ w7.stack :=
    prefix_of_push eventPush (prefix_of_push callerPush receiverPrefix)
  have w7Wf : Mem.Wf w7.memory := by
    rw [← eventPush.memory, ← callerPush.memory]; exact w6Wf
  have w7Reads : Mem.Reads w7.memory
      (outboundSettleImage image assets shares) := by
    rw [← eventPush.memory, ← callerPush.memory]; exact w6Reads
  obtain ⟨returnLoadStack, emitted⟩ :=
    of_logWith_val
      (topics := [withdrawEvent, sevm.caller.toB256, receiver, owner])
      (by simp) (by simpa using topicPrefix) logRun
  obtain ⟨returnLoadWf, returnLoadReads⟩ := of_logWith_image w7Wf w7Reads logRun
  have dataWindow : (w7.memory.read ((0 : B256) * 32).toNat
      ((2 : B256) * 32).toNat).1 = assets.toBytes ++ shares.toBytes := by
    have twoOffset : ((2 : B256) * 32).toNat = 64 := by decide +kernel
    rw [zeroOffset, twoOffset, Mem.Reads.read w7Reads]
    simpa only [outboundSettleImage] using
      Bytes.read_two_word_writes_at image 0 assets shares
  have logLogs : pre.logs = w7.logs :=
    (of_run_loadWordAt_logs assetsRun).trans <|
      (Line.of_inv Devm.logs (by unfold mstoreAt; line_inv)
          assetsStoreRun).trans <|
        (of_run_loadWordAt_logs sharesRun).trans <|
          (Line.of_inv Devm.logs (by unfold mstoreAt; line_inv)
              sharesStoreRun).trans <|
            (of_run_loadWordAt_logs ownerRun).trans <|
              (of_run_loadWordAt_logs receiverRun).trans <|
                callerPush.logs.trans eventPush.logs

  -- Return the quoted word.
  have returnedAtStaged : Bytes.toB256
      ((outboundSettleImage image assets shares).sliceD
        (returnedSel * 32).toNat 32 0) = returned := by
    unfold outboundSettleImage
    rw [Bytes.readWord_writeAt_of_disjoint,
      Bytes.readWord_writeAt_of_disjoint]
    · exact returnedAt
    · right
      omega
    · right
      omega
  obtain ⟨returnPre, returnedRun, returnRun⟩ := runCompiledTo_prepend_inv run
  obtain ⟨returnedPrefix, -, -, -⟩ :=
    of_run_loadWordAt_image returnLoadStack returnLoadWf returnLoadReads
      returnedAtStaged returnedRun
  have returnedLogs : returnLoadPre.logs = returnPre.logs :=
    of_run_loadWordAt_logs returnedRun
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
  refine ⟨returnWord_trace returnedPrefix returnRun, ?_, ?_⟩
  · rw [← returnStorage, ← returnedStorage, ← logStorage]
  · rw [← returnLogs, ← returnedLogs, emitted, dataWindow, ← logLogs]
    rfl

/-! ## Shape pins

Each `rfl` ties an inlined fragment above to the actual vault definition, so a
change to the source that the walks no longer describe fails here rather than
silently proving something about a fragment the contract no longer contains. -/

theorem withdrawAfterQuote_shape :
    withdrawAfterQuote =
      mstoreAt quoteWord +++
        nonzeroCaller (nonzeroStagedAddress receiverWord
          (nonzeroStagedAddress ownerWord
            (ownerHasShares (loadWord quoteWord)
              (loadWord ownerWord +++ caller ::: eq :::
                (.call withdrawBurnSlot <?>
                  spendAllowance (loadWord ownerWord) [caller]
                    (loadWord quoteWord) withdrawBurnSlot))))) := rfl

theorem redeemAfterQuote_shape :
    redeemAfterQuote =
      mstoreAt quoteWord +++
        nonzeroCaller (nonzeroStagedAddress receiverWord
          (nonzeroStagedAddress ownerWord
            (ownerHasShares (loadWord amountWord)
              (loadWord ownerWord +++ caller ::: eq :::
                (.call redeemBurnSlot <?>
                  spendAllowance (loadWord ownerWord) [caller]
                    (loadWord amountWord) redeemBurnSlot))))) := rfl

theorem finishOutbound_shape (sharesSel assetsSel returnedSel : B256) :
    finishOutbound (loadWord sharesSel) (loadWord assetsSel)
        (loadWord returnedSel) =
      (loadWord sharesSel +++ loadWord balanceWord +++ sub :::
        loadWord ownerWord +++ sstore :::
        loadWord sharesSel +++ loadWord supplyWord +++ lt :::
        (Func.revert <?>
          (loadWord sharesSel +++ loadWord supplyWord +++ sub :::
            pushSupplySlot +++ sstore :::
            logBurnTransfer (loadWord sharesSel) +++
            callWethTransfer (loadWord receiverWord) (loadWord assetsSel)
              (logWithdraw (loadWord assetsSel) (loadWord sharesSel) +++
                loadWord returnedSel +++ returnWord)))) := rfl

theorem withdrawBurn_shape :
    withdrawBurn =
      finishOutbound (loadWord quoteWord) (loadWord amountWord)
        (loadWord quoteWord) := rfl

theorem redeemBurn_shape :
    redeemBurn =
      finishOutbound (loadWord amountWord) (loadWord quoteWord)
        (loadWord quoteWord) := rfl

theorem withdraw_shape :
    withdraw =
      arg 0 +++ mstoreAt amountWord +++
        arg 1 +++ mstoreAt receiverWord +++
        arg 2 +++ mstoreAt ownerWord +++
        (readTotalAssets <|
          mstoreAt assetsWord +++
          pushSupplySlot +++ sload ::: mstoreAt supplyWord +++
          guardStableSupply
            (loadWord assetsWord +++ isMax +++
              (productOverTwoPow256 (loadWord amountWord) stagedDenominator
                  .up withdrawAfterQuoteSlot <?>
                mulDiv (loadWord amountWord) stagedDenominator
                  stagedAssetFactor .up withdrawAfterQuoteSlot))) := rfl

theorem redeem_shape :
    redeem =
      arg 0 +++ mstoreAt amountWord +++
        arg 1 +++ mstoreAt receiverWord +++
        arg 2 +++ mstoreAt ownerWord +++
        (readTotalAssets <|
          mstoreAt assetsWord +++
          pushSupplySlot +++ sload ::: mstoreAt supplyWord +++
          guardStableSupply
            (loadWord assetsWord +++ isMax +++
              (shiftedDiv (loadWord amountWord) stagedDenominator .down
                  redeemAfterQuoteSlot <?>
                mulDiv (loadWord amountWord) stagedAssetFactor
                  stagedDenominator .down redeemAfterQuoteSlot))) := rfl

end ProrataWethVault

end Blanc
