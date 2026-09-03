-- ProrataWethVaultShares.lean : exact local seams for the ERC-20 share ledger.

import Blanc.ProrataWethVaultOutbound

namespace Blanc

open Jaune
open Jaune.Ninst Ninst
open scoped LogOutputHinv

namespace ProrataWethVault

/-!
# Compiled share-ledger seams

`transfer`, `transferFrom` and `approve` move the vault's own ERC-20 shares.
This module owns their family-local half.

`transfer` and `transferFrom` reach the same settlement, `transferStaged`,
through the same auxiliary slot: the only difference is where the three staged
words come from and whether an allowance is spent on the way.  That settlement
is a conservative rearrangement -- one row debited, one row credited, by the
same amount -- and it never touches the supply, which is why a share transfer
cannot change how much WETH backs a share.

The debit half of `transferStaged` is literally `ownerHasShares`, and its
credit half is literally the inbound credit walk, so both are reused rather
than restated.
-/

/-- The staged settlement debits the owner's row, credits the receiver's row by
the same amount, emits the ERC-20 `Transfer`, and returns canonical true.

The receiver's row is read *after* the debit, so a self-transfer nets to zero
rather than double-counting.  The supply slot is never written. -/
theorem transferStaged_trace
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    {image : Bytes} {owner receiver amount : B256}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (ownerAt : Bytes.toB256
      (image.sliceD (ownerWord * 32).toNat 32 0) = owner)
    (receiverAt : Bytes.toB256
      (image.sliceD (receiverWord * 32).toNat 32 0) = receiver)
    (amountAt : Bytes.toB256
      (image.sliceD (amountWord * 32).toNat 32 0) = amount)
    (stack : [] <<+ pre.stack)
    (run : Func.RunCompiledTo fs sevm pre transferStaged (.ok post)) :
    ∃ ownerBalance receiverBalance,
      ownerBalance = Devm.getStorVal pre sevm.currentTarget owner ∧
      amount.toNat ≤ ownerBalance.toNat ∧
      receiverBalance =
        ((Devm.getStor pre sevm.currentTarget).set owner
          (ownerBalance - amount)).get receiver ∧
      receiverBalance.toNat + amount.toNat < wordModulusN ∧
      AbiReturnsTrue post ∧
      Devm.getStor post sevm.currentTarget =
        ((Devm.getStor pre sevm.currentTarget).set owner
          (ownerBalance - amount)).set receiver (receiverBalance + amount) ∧
      (∀ account, sevm.currentTarget ≠ account →
        Devm.getStor post account = Devm.getStor pre account) ∧
      post.logs = pre.logs ++
        [transferLogEntry sevm owner receiver amount] := by
  -- The debit guard is the outbound owner-balance guard.
  obtain ⟨debitPre, ownerBalance, ownerBalanceEq, covered, debitStack,
      debitWf, debitReads, guardStorage, guardCode, guardLogs, debitRun⟩ :=
    ownerHasShares_trace memoryWf memoryReads ownerAt amountAt
      (by decide +kernel) stack run
  set balanceImage :=
    Bytes.writeAt image (balanceWord * 32).toNat ownerBalance.toBytes
    with balanceImageDef
  change Mem.Reads debitPre.memory balanceImage at debitReads
  have amountAtBalance : Bytes.toB256
      (balanceImage.sliceD (amountWord * 32).toNat 32 0) = amount := by
    rw [balanceImageDef, Bytes.readWord_writeAt_of_disjoint]
    · exact amountAt
    · left
      decide +kernel
  have receiverAtBalance : Bytes.toB256
      (balanceImage.sliceD (receiverWord * 32).toNat 32 0) = receiver := by
    rw [balanceImageDef, Bytes.readWord_writeAt_of_disjoint]
    · exact receiverAt
    · left
      decide +kernel
  have ownerAtBalance : Bytes.toB256
      (balanceImage.sliceD (ownerWord * 32).toNat 32 0) = owner := by
    rw [balanceImageDef, Bytes.readWord_writeAt_of_disjoint]
    · exact ownerAt
    · left
      decide +kernel
  have balanceAtBalance : Bytes.toB256
      (balanceImage.sliceD (balanceWord * 32).toNat 32 0) = ownerBalance := by
    rw [balanceImageDef]
    exact Bytes.readWord_writeAt_self _ _ _

  -- Debit the owner's row.
  obtain ⟨debitLoadPre, debitAmountRun, debitRun⟩ :=
    runCompiledTo_prepend_inv debitRun
  obtain ⟨debitAmountPrefix, debitLoadWf, debitLoadReads, debitAmountState⟩ :=
    of_run_loadWordAt_image debitStack debitWf debitReads amountAtBalance
      debitAmountRun
  obtain ⟨subPre, debitLoadRun, debitRun⟩ := runCompiledTo_prepend_inv debitRun
  obtain ⟨debitLoadPrefix, subWf, subReads, debitLoadState⟩ :=
    of_run_loadWordAt_image debitAmountPrefix debitLoadWf debitLoadReads
      balanceAtBalance debitLoadRun
  obtain ⟨ownerLoadPre, subRun, debitRun⟩ := runCompiledTo_next_inv debitRun
  have subSource := Ninst.Run.of_runCompiled subRun
  have subPrefix : (ownerBalance - amount) :: [] <<+ ownerLoadPre.stack :=
    prefix_of_sub subSource debitLoadPrefix
  have subMemory : subPre.memory = ownerLoadPre.memory :=
    Ninst.Hinv.inv (f := Devm.memory) subSource
  have subStorage : Devm.getStor subPre = Devm.getStor ownerLoadPre :=
    Ninst.Hinv.inv (f := Devm.getStor) subSource
  have ownerLoadWf : Mem.Wf ownerLoadPre.memory := by
    rw [← subMemory]; exact subWf
  have ownerLoadReads : Mem.Reads ownerLoadPre.memory balanceImage := by
    rw [← subMemory]; exact subReads
  obtain ⟨debitStorePre, ownerLoadRun, debitRun⟩ :=
    runCompiledTo_prepend_inv debitRun
  obtain ⟨ownerPrefix, debitStoreWf, debitStoreReads, ownerLoadState⟩ :=
    of_run_loadWordAt_image subPrefix ownerLoadWf ownerLoadReads
      ownerAtBalance ownerLoadRun
  obtain ⟨creditPre, debitStoreRun, creditRun⟩ := runCompiledTo_next_inv debitRun
  have debitStoreSource := Ninst.Run.of_runCompiled debitStoreRun
  have debitSet : Devm.getStor creditPre sevm.currentTarget =
      (Devm.getStor debitStorePre sevm.currentTarget).set owner
        (ownerBalance - amount) :=
    sstore_getStor_set debitStoreSource ownerPrefix
  have debitForeign : ∀ account, sevm.currentTarget ≠ account →
      Devm.getStor creditPre account = Devm.getStor debitStorePre account :=
    fun _ ne => sstore_getStor_of_ne debitStoreSource ne
  have creditStack : [] <<+ creditPre.stack :=
    prefix_of_sstore debitStoreSource ownerPrefix
  have debitStoreMemory : debitStorePre.memory = creditPre.memory :=
    Ninst.Hinv.inv (f := Devm.memory) debitStoreSource
  have creditWf : Mem.Wf creditPre.memory := by
    rw [← debitStoreMemory]; exact debitStoreWf
  have creditReads : Mem.Reads creditPre.memory balanceImage := by
    rw [← debitStoreMemory]; exact debitStoreReads

  -- Credit the receiver's row, rejecting a wrapped total.
  obtain ⟨settlePre, receiverBalance, receiverBalanceEq, noWrap, settleStack,
      settleWf, settleReads, creditStorage, creditLogs, settleRun⟩ :=
    inboundCredit_trace creditWf creditReads receiverAtBalance
      amountAtBalance (by decide +kernel) creditStack creditRun
  set creditImage :=
    inboundCreditImage balanceImage receiverBalance (receiverBalance + amount)
    with creditImageDef
  change Mem.Reads settlePre.memory creditImage at settleReads
  have scratchAtCredit : Bytes.toB256
      (creditImage.sliceD (scratchWord * 32).toNat 32 0) =
      receiverBalance + amount := by
    rw [creditImageDef, inboundCreditImage]
    exact Bytes.readWord_writeAt_self _ _ _
  have receiverAtCredit : Bytes.toB256
      (creditImage.sliceD (receiverWord * 32).toNat 32 0) = receiver := by
    rw [creditImageDef, inboundCreditImage,
      Bytes.readWord_writeAt_of_disjoint, Bytes.readWord_writeAt_of_disjoint]
    · exact receiverAtBalance
    · left
      decide +kernel
    · right
      decide +kernel
  have ownerAtCredit : Bytes.toB256
      (creditImage.sliceD (ownerWord * 32).toNat 32 0) = owner := by
    rw [creditImageDef, inboundCreditImage,
      Bytes.readWord_writeAt_of_disjoint, Bytes.readWord_writeAt_of_disjoint]
    · exact ownerAtBalance
    · left
      decide +kernel
    · right
      decide +kernel
  have amountAtCredit : Bytes.toB256
      (creditImage.sliceD (amountWord * 32).toNat 32 0) = amount := by
    rw [creditImageDef, inboundCreditImage,
      Bytes.readWord_writeAt_of_disjoint, Bytes.readWord_writeAt_of_disjoint]
    · exact amountAtBalance
    · left
      decide +kernel
    · right
      decide +kernel

  -- Write the credited row.
  obtain ⟨creditLoadPre, scratchRun, settleRun⟩ :=
    runCompiledTo_prepend_inv settleRun
  obtain ⟨scratchPrefix, creditLoadWf, creditLoadReads, scratchState⟩ :=
    of_run_loadWordAt_image settleStack settleWf settleReads scratchAtCredit
      scratchRun
  obtain ⟨creditStorePre, creditReceiverRun, settleRun⟩ :=
    runCompiledTo_prepend_inv settleRun
  obtain ⟨creditReceiverPrefix, creditStoreWf, creditStoreReads,
      creditReceiverState⟩ :=
    of_run_loadWordAt_image scratchPrefix creditLoadWf creditLoadReads
      receiverAtCredit creditReceiverRun
  obtain ⟨logPre, creditStoreRun, settleRun⟩ := runCompiledTo_next_inv settleRun
  have creditStoreSource := Ninst.Run.of_runCompiled creditStoreRun
  have creditSet : Devm.getStor logPre sevm.currentTarget =
      (Devm.getStor creditStorePre sevm.currentTarget).set receiver
        (receiverBalance + amount) :=
    sstore_getStor_set creditStoreSource creditReceiverPrefix
  have creditForeign : ∀ account, sevm.currentTarget ≠ account →
      Devm.getStor logPre account = Devm.getStor creditStorePre account :=
    fun _ ne => sstore_getStor_of_ne creditStoreSource ne
  have logStack : [] <<+ logPre.stack :=
    prefix_of_sstore creditStoreSource creditReceiverPrefix
  have creditStoreMemory : creditStorePre.memory = logPre.memory :=
    Ninst.Hinv.inv (f := Devm.memory) creditStoreSource
  have logWf : Mem.Wf logPre.memory := by
    rw [← creditStoreMemory]; exact creditStoreWf
  have logReads : Mem.Reads logPre.memory creditImage := by
    rw [← creditStoreMemory]; exact creditStoreReads

  -- Emit the ERC-20 transfer and return canonical true.
  obtain ⟨truePre, logRun, trueRun⟩ := runCompiledTo_prepend_inv settleRun
  have logLineRun := logRun
  have logStorage : Devm.getStor logPre = Devm.getStor truePre := by
    refine Line.of_inv Devm.getStor ?_ logLineRun
    unfold logStagedTransfer ProrataWethVault.loadWord mstoreAt logWith
    line_inv
  simp only [logStagedTransfer, List.append_assoc] at logRun
  obtain ⟨e1, logAmountRun, logRun⟩ := of_run_append (loadWord amountWord) logRun
  obtain ⟨logAmountPrefix, e1Wf, e1Reads, -⟩ :=
    of_run_loadWordAt_image logStack logWf logReads amountAtCredit
      logAmountRun
  obtain ⟨e2, logStoreRun, logRun⟩ := of_run_append (mstoreAt 0) logRun
  obtain ⟨e2Stack, e2Wf, e2Reads, -⟩ :=
    of_run_mstoreAt_image logAmountPrefix e1Wf e1Reads logStoreRun
  have zeroOffset : ((0 : B256) * 32).toNat = 0 := by decide +kernel
  rw [zeroOffset] at e2Reads
  have receiverAtLogged : Bytes.toB256
      ((Bytes.writeAt creditImage 0 amount.toBytes).sliceD
        (receiverWord * 32).toNat 32 0) = receiver := by
    rw [Bytes.readWord_writeAt_of_disjoint]
    · exact receiverAtCredit
    · right
      decide +kernel
  have ownerAtLogged : Bytes.toB256
      ((Bytes.writeAt creditImage 0 amount.toBytes).sliceD
        (ownerWord * 32).toNat 32 0) = owner := by
    rw [Bytes.readWord_writeAt_of_disjoint]
    · exact ownerAtCredit
    · right
      decide +kernel
  obtain ⟨e3, logReceiverRun, logRun⟩ :=
    of_run_append (loadWord receiverWord) logRun
  obtain ⟨e3Prefix, e3Wf, e3Reads, -⟩ :=
    of_run_loadWordAt_image e2Stack e2Wf e2Reads receiverAtLogged
      logReceiverRun
  obtain ⟨e4, logOwnerRun, logRun⟩ := of_run_append (loadWord ownerWord) logRun
  obtain ⟨e4Prefix, e4Wf, e4Reads, -⟩ :=
    of_run_loadWordAt_image e3Prefix e3Wf e3Reads ownerAtLogged logOwnerRun
  obtain ⟨e5, eventRun, logRun⟩ :=
    of_run_append [pushB256 transferEvent] logRun
  rcases Line.of_run_cons eventRun with ⟨_, eventPushRun, eventNil⟩
  cases eventNil
  have eventPush := of_run_pushB256 eventPushRun
  have e5Prefix : transferEvent :: owner :: receiver :: [] <<+ e5.stack :=
    prefix_of_push eventPush e4Prefix
  have e5Wf : Mem.Wf e5.memory := by rw [← eventPush.memory]; exact e4Wf
  have e5Reads : Mem.Reads e5.memory
      (Bytes.writeAt creditImage 0 amount.toBytes) := by
    rw [← eventPush.memory]; exact e4Reads
  obtain ⟨trueStack, emitted⟩ :=
    of_logWith_val (topics := [transferEvent, owner, receiver]) (by simp)
      (by simpa using e5Prefix) logRun
  obtain ⟨trueWf, trueReads⟩ := of_logWith_image e5Wf e5Reads logRun
  have logWindow : (e5.memory.read ((0 : B256) * 32).toNat
      ((1 : B256) * 32).toNat).1 = amount.toBytes := by
    have sizeWord : ((1 : B256) * 32).toNat = 32 := by decide +kernel
    rw [zeroOffset, sizeWord, Mem.Reads.read e5Reads,
      show (32 : Nat) = amount.toBytes.length from
        (B256.length_toBytes amount).symm]
    exact Bytes.sliceD_writeAt creditImage amount.toBytes 0
  have logPrefixLogs : logPre.logs = e5.logs :=
    (of_run_loadWordAt_logs logAmountRun).trans <|
      (Line.of_inv Devm.logs (by unfold mstoreAt; line_inv)
          logStoreRun).trans <|
        (of_run_loadWordAt_logs logReceiverRun).trans <|
          (of_run_loadWordAt_logs logOwnerRun).trans eventPush.logs
  have trueSourceRun : Func.Run fs sevm truePre returnTrue post :=
    Func.Run.of_runCompiled (Func.RunCompiled.of_runCompiledTo_ok trueRun)
  obtain ⟨returnsTrue, -⟩ :=
    of_returnTrue_shared trueStack trueWf trueReads trueSourceRun
  have trueStorage : Devm.getStor truePre = Devm.getStor post :=
    Func.of_inv Devm.getStor Devm.getStor (by
      unfold returnTrue
      func_inv) trueSourceRun
  have trueLogs : truePre.logs = post.logs :=
    Func.of_inv Devm.logs Devm.logs (by
      unfold returnTrue
      func_inv) trueSourceRun

  -- Assemble the conservative rearrangement.
  have preToDebitStore : Devm.getStor pre = Devm.getStor debitStorePre :=
    guardStorage.trans
      ((funext (getStor_eq_of_state_eq debitAmountState)).trans
        ((funext (getStor_eq_of_state_eq debitLoadState)).trans
          (subStorage.trans
            (funext (getStor_eq_of_state_eq ownerLoadState)))))
  have creditToCreditStore :
      Devm.getStor creditPre = Devm.getStor creditStorePre :=
    creditStorage.trans
      ((funext (getStor_eq_of_state_eq scratchState)).trans
        (funext (getStor_eq_of_state_eq creditReceiverState)))
  have logToPost : Devm.getStor logPre = Devm.getStor post :=
    logStorage.trans trueStorage
  have preToLog : pre.logs = logPre.logs :=
    guardLogs.trans <|
      (of_run_loadWordAt_logs debitAmountRun).trans <|
        (of_run_loadWordAt_logs debitLoadRun).trans <|
          (Ninst.Hinv.inv (f := Devm.logs) subSource).trans <|
            (of_run_loadWordAt_logs ownerLoadRun).trans <|
              (Ninst.Hinv.inv (f := Devm.logs) debitStoreSource).trans <|
                creditLogs.trans <|
                  (of_run_loadWordAt_logs scratchRun).trans <|
                    (of_run_loadWordAt_logs creditReceiverRun).trans
                      (Ninst.Hinv.inv (f := Devm.logs) creditStoreSource)
  refine ⟨ownerBalance, receiverBalance, ownerBalanceEq, covered, ?_, noWrap,
    returnsTrue, ?_, ?_, ?_⟩
  · rw [receiverBalanceEq]
    change
      (Devm.getStor creditPre sevm.currentTarget).get receiver =
        ((Devm.getStor pre sevm.currentTarget).set owner
          (ownerBalance - amount)).get receiver
    rw [debitSet, ← congrFun preToDebitStore sevm.currentTarget]
  · rw [← congrFun logToPost sevm.currentTarget, creditSet,
      ← congrFun creditToCreditStore sevm.currentTarget, debitSet,
      ← congrFun preToDebitStore sevm.currentTarget]
  · intro account accountNe
    rw [← congrFun logToPost account, creditForeign account accountNe,
      ← congrFun creditToCreditStore account, debitForeign account accountNe,
      ← congrFun preToDebitStore account]
  · rw [← trueLogs, emitted, logWindow, ← logPrefixLogs, ← preToLog]
    rfl

end ProrataWethVault

end Blanc
