-- ProrataWethVaultShares.lean : exact local seams for the ERC-20 share ledger.

import Blanc.ProrataWethVaultOutbound
import Blanc.LedgerConservation

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

/-! ## Shared three-word staging

`approve`, `transfer` and `transferFrom` all stage an owner, a receiver and an
amount into the same three operation words.  They differ only in where those
words come from: `transfer` takes its owner from the frame caller and the other
two from ABI arguments zero and one, while `transferFrom` takes all three from
arguments zero, one and two. -/

/-- Memory image after the three share-operation words are staged. -/
def shareArgImage (image : Bytes) (owner receiver amount : B256) : Bytes :=
  Bytes.writeAt
    (Bytes.writeAt
      (Bytes.writeAt image (ownerWord * 32).toNat owner.toBytes)
      (receiverWord * 32).toNat receiver.toBytes)
    (amountWord * 32).toNat amount.toBytes

theorem shareArgs_trace
    {fs : List Func} {sevm : Sevm} {pre final : Devm}
    {image : Bytes} {ownerLine receiverLine amountLine : Line}
    {owner receiver amount : B256} {body : Func} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (ownerProduces : ProducesWord sevm ownerLine image owner)
    (receiverProduces : ProducesWord sevm receiverLine
      (Bytes.writeAt image (ownerWord * 32).toNat owner.toBytes) receiver)
    (amountProduces : ProducesWord sevm amountLine
      (Bytes.writeAt
        (Bytes.writeAt image (ownerWord * 32).toNat owner.toBytes)
        (receiverWord * 32).toNat receiver.toBytes) amount)
    (stack : tail <<+ pre.stack)
    (run : Func.RunCompiledTo fs sevm pre
      (ownerLine +++ mstoreAt ownerWord +++
        receiverLine +++ mstoreAt receiverWord +++
        amountLine +++ mstoreAt amountWord +++ body) (.ok final)) :
    ∃ bodyPre,
      tail <<+ bodyPre.stack ∧
      Mem.Wf bodyPre.memory ∧
      Mem.Reads bodyPre.memory (shareArgImage image owner receiver amount) ∧
      pre.state = bodyPre.state ∧
      pre.logs = bodyPre.logs ∧
      Func.RunCompiledTo fs sevm bodyPre body (.ok final) := by
  obtain ⟨ownerStorePre, ownerRun, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨ownerPrefix, ownerStoreWf, ownerStoreReads, ownerQuiet⟩ :=
    ownerProduces memoryWf memoryReads stack ownerRun
  obtain ⟨receiverPre, ownerStoreRun, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨receiverStack, receiverWf, receiverReads, ownerStoreState⟩ :=
    of_run_mstoreAt_image ownerPrefix ownerStoreWf ownerStoreReads
      ownerStoreRun
  have ownerStoreLogs : ownerStorePre.logs = receiverPre.logs := by
    refine Line.of_inv Devm.logs ?_ ownerStoreRun
    unfold mstoreAt
    line_inv
  obtain ⟨receiverStorePre, receiverRun, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨receiverPrefix, receiverStoreWf, receiverStoreReads,
      receiverQuiet⟩ :=
    receiverProduces receiverWf receiverReads receiverStack receiverRun
  obtain ⟨amountPre, receiverStoreRun, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨amountStack, amountWf, amountReads, receiverStoreState⟩ :=
    of_run_mstoreAt_image receiverPrefix receiverStoreWf receiverStoreReads
      receiverStoreRun
  have receiverStoreLogs : receiverStorePre.logs = amountPre.logs := by
    refine Line.of_inv Devm.logs ?_ receiverStoreRun
    unfold mstoreAt
    line_inv
  obtain ⟨amountStorePre, amountRun, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨amountPrefix, amountStoreWf, amountStoreReads, amountQuiet⟩ :=
    amountProduces amountWf amountReads amountStack amountRun
  obtain ⟨bodyPre, amountStoreRun, bodyRun⟩ := runCompiledTo_prepend_inv run
  obtain ⟨bodyStack, bodyWf, bodyReads, amountStoreState⟩ :=
    of_run_mstoreAt_image amountPrefix amountStoreWf amountStoreReads
      amountStoreRun
  have amountStoreLogs : amountStorePre.logs = bodyPre.logs := by
    refine Line.of_inv Devm.logs ?_ amountStoreRun
    unfold mstoreAt
    line_inv
  exact ⟨bodyPre, bodyStack, bodyWf, bodyReads,
    ownerQuiet.1.trans (ownerStoreState.trans
      (receiverQuiet.1.trans (receiverStoreState.trans
        (amountQuiet.1.trans amountStoreState)))),
    ownerQuiet.2.trans (ownerStoreLogs.trans
      (receiverQuiet.2.trans (receiverStoreLogs.trans
        (amountQuiet.2.trans amountStoreLogs)))),
    bodyRun⟩

/-! ## Approval -/

/-- The ERC-20 `Approval(owner, spender, amount)` entry the vault emits. -/
def approvalLogEntry (sevm : Sevm) (spender amount : B256) : Log :=
  ⟨sevm.currentTarget, [approvalEvent, sevm.caller.toB256, spender],
    amount.toBytes⟩

/-- `approve(spender, amount)` writes exactly the caller's allowance for the
spender and nothing else.

The written slot is the guarded hash, which the collision guard has proved is
neither address-shaped nor the reserved supply word.  That is what makes an
approval unable to move any economic quantity: it cannot alias a share row and
it cannot alias the supply. -/
theorem approve_body_effect
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    (memoryWf : Mem.Wf pre.memory)
    (stack : [] <<+ pre.stack)
    (run : Func.RunCompiledTo fs sevm pre approve (.ok post)) :
    sevm.caller.toB256 ≠ 0 ∧
      ValidAdr (Sevm.argWord sevm 0) ∧
      Sevm.argWord sevm 0 ≠ 0 ∧
      ¬ ValidAdr (allowanceKey sevm.caller.toB256 (Sevm.argWord sevm 0)) ∧
      allowanceKey sevm.caller.toB256 (Sevm.argWord sevm 0) ≠ supplySlot ∧
      AbiReturnsTrue post ∧
      Devm.getStor post sevm.currentTarget =
        (Devm.getStor pre sevm.currentTarget).set
          (allowanceKey sevm.caller.toB256 (Sevm.argWord sevm 0))
          (Sevm.argWord sevm 1) ∧
      (∀ account, sevm.currentTarget ≠ account →
        Devm.getStor post account = Devm.getStor pre account) ∧
      post.logs = pre.logs ++
        [approvalLogEntry sevm (Sevm.argWord sevm 0)
          (Sevm.argWord sevm 1)] := by
  unfold approve at run
  have entryReads : Mem.Reads pre.memory pre.memory.data.toList := by
    intro index
    simp
  obtain ⟨spenderPre, callerNonzero, spenderStack, callerMemory, callerState,
      callerLogs, run⟩ := nonzeroCaller_trace stack run
  have spenderWf : Mem.Wf spenderPre.memory := by
    rw [← callerMemory]; exact memoryWf
  have spenderReads :
      Mem.Reads spenderPre.memory pre.memory.data.toList := by
    rw [← callerMemory]; exact entryReads
  obtain ⟨stagePre, spenderValid, spenderNonzero, stageStack, stageWf,
      stageReads, spenderState, spenderLogs, run⟩ :=
    canonicalNonzeroAddress_trace spenderWf spenderReads
      (ProducesWord.arg sevm _ 0) spenderStack run

  -- Stage the caller, the spender and the amount.
  obtain ⟨ownerStorePre, ownerRun, run⟩ := runCompiledTo_next_inv run
  have ownerSource := Ninst.Run.of_runCompiled ownerRun
  have ownerPush := of_run_caller ownerSource
  have ownerPrefix : sevm.caller.toB256 :: [] <<+ ownerStorePre.stack :=
    prefix_of_push ownerPush stageStack
  have ownerStoreWf : Mem.Wf ownerStorePre.memory := by
    rw [← ownerPush.memory]; exact stageWf
  have ownerStoreReads :
      Mem.Reads ownerStorePre.memory pre.memory.data.toList := by
    rw [← ownerPush.memory]; exact stageReads
  obtain ⟨spenderArgPre, ownerStoreRun, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨spenderArgStack, spenderArgWf, spenderArgReads, ownerStoreState⟩ :=
    of_run_mstoreAt_image ownerPrefix ownerStoreWf ownerStoreReads
      ownerStoreRun
  obtain ⟨spenderStorePre, spenderArgRun, run⟩ := runCompiledTo_prepend_inv run
  have spenderArgPrefix := prefix_of_arg spenderArgStack spenderArgRun
  have spenderArgQuiet :=
    ProducesWord.arg sevm
      (Bytes.writeAt pre.memory.data.toList (ownerWord * 32).toNat
        sevm.caller.toB256.toBytes) 0 spenderArgWf spenderArgReads
      spenderArgStack spenderArgRun
  obtain ⟨-, spenderStoreWf, spenderStoreReads, spenderArgFrame⟩ :=
    spenderArgQuiet
  obtain ⟨amountArgPre, spenderStoreRun, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨amountArgStack, amountArgWf, amountArgReads, spenderStoreState⟩ :=
    of_run_mstoreAt_image spenderArgPrefix spenderStoreWf spenderStoreReads
      spenderStoreRun
  obtain ⟨amountStorePre, amountArgRun, run⟩ := runCompiledTo_prepend_inv run
  have amountArgPrefix := prefix_of_arg amountArgStack amountArgRun
  obtain ⟨-, amountStoreWf, amountStoreReads, amountArgFrame⟩ :=
    ProducesWord.arg sevm _ 1 amountArgWf amountArgReads amountArgStack
      amountArgRun
  obtain ⟨keyPre, amountStoreRun, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨keyStack, keyWf, keyReads, amountStoreState⟩ :=
    of_run_mstoreAt_image amountArgPrefix amountStoreWf amountStoreReads
      amountStoreRun
  set stagedImage := Bytes.writeAt
    (Bytes.writeAt
      (Bytes.writeAt pre.memory.data.toList (ownerWord * 32).toNat
        sevm.caller.toB256.toBytes)
      (receiverWord * 32).toNat (Sevm.argWord sevm 0).toBytes)
    (amountWord * 32).toNat (Sevm.argWord sevm 1).toBytes with stagedImageDef
  change Mem.Reads keyPre.memory stagedImage at keyReads
  have ownerAtStaged : Bytes.toB256
      (stagedImage.sliceD (ownerWord * 32).toNat 32 0) =
      sevm.caller.toB256 := by
    rw [stagedImageDef, Bytes.readWord_writeAt_of_disjoint,
      Bytes.readWord_writeAt_of_disjoint]
    · exact Bytes.readWord_writeAt_self _ _ _
    · right
      decide +kernel
    · right
      decide +kernel
  have receiverAtStaged : Bytes.toB256
      ((Bytes.writeAt stagedImage ((0 : B256) * 32).toNat
        sevm.caller.toB256.toBytes).sliceD
          (receiverWord * 32).toNat 32 0) = Sevm.argWord sevm 0 := by
    rw [Bytes.readWord_writeAt_of_disjoint, stagedImageDef,
      Bytes.readWord_writeAt_of_disjoint]
    · exact Bytes.readWord_writeAt_self _ _ _
    · right
      decide +kernel
    · right
      decide +kernel

  -- Hash and guard the allowance key.
  obtain ⟨storePre, keyNotAddress, keyNotSupply, keyPrefix, storeWf,
      storeReads, keyStorage, keyCode, keyLogs, run⟩ :=
    allowanceKey_trace keyWf keyReads (ProducesWord.loadWord ownerAtStaged)
      (ProducesWord.loadWord receiverAtStaged) keyStack run
  set aKey := allowanceKey sevm.caller.toB256 (Sevm.argWord sevm 0)
    with aKeyDef
  set keyImage := allowanceKeyImage stagedImage sevm.caller.toB256
    (Sevm.argWord sevm 0) with keyImageDef
  change Mem.Reads storePre.memory keyImage at storeReads
  have amountAtKey : Bytes.toB256
      (keyImage.sliceD (amountWord * 32).toNat 32 0) =
      Sevm.argWord sevm 1 := by
    rw [keyImageDef, allowanceKeyImage, Bytes.readWord_writeAt_of_disjoint,
      Bytes.readWord_writeAt_of_disjoint, stagedImageDef]
    · exact Bytes.readWord_writeAt_self _ _ _
    · right
      decide +kernel
    · right
      decide +kernel
  have receiverAtKey : Bytes.toB256
      (keyImage.sliceD (receiverWord * 32).toNat 32 0) =
      Sevm.argWord sevm 0 := by
    rw [keyImageDef, allowanceKeyImage, Bytes.readWord_writeAt_of_disjoint,
      Bytes.readWord_writeAt_of_disjoint, stagedImageDef,
      Bytes.readWord_writeAt_of_disjoint]
    · exact Bytes.readWord_writeAt_self _ _ _
    · right
      decide +kernel
    · right
      decide +kernel
    · right
      decide +kernel

  -- Write the allowance.
  obtain ⟨swapPre, amountRun, run⟩ := runCompiledTo_prepend_inv run
  obtain ⟨amountPrefix, swapWf, swapReads, amountState⟩ :=
    of_run_loadWordAt_image keyPrefix storeWf storeReads amountAtKey amountRun
  obtain ⟨sstorePre, swapRun, run⟩ := runCompiledTo_next_inv run
  have swapSource := Ninst.Run.of_runCompiled swapRun
  have swapShape : Stack.Swap (0 : Fin 16).val
      [Sevm.argWord sevm 1, aKey] [aKey, Sevm.argWord sevm 1] :=
    Stack.swapCore_zero
  have sstorePrefix : aKey :: Sevm.argWord sevm 1 :: [] <<+ sstorePre.stack :=
    Stack.prefix_of_swap swapShape (of_run_swap swapSource) amountPrefix
  have swapMemory : swapPre.memory = sstorePre.memory :=
    Ninst.Hinv.inv (f := Devm.memory) swapSource
  have sstoreWf : Mem.Wf sstorePre.memory := by
    rw [← swapMemory]; exact swapWf
  have sstoreReads : Mem.Reads sstorePre.memory keyImage := by
    rw [← swapMemory]; exact swapReads
  obtain ⟨logPre, sstoreRun, run⟩ := runCompiledTo_next_inv run
  have sstoreSource := Ninst.Run.of_runCompiled sstoreRun
  have allowanceSet : Devm.getStor logPre sevm.currentTarget =
      (Devm.getStor sstorePre sevm.currentTarget).set aKey
        (Sevm.argWord sevm 1) :=
    sstore_getStor_set sstoreSource sstorePrefix
  have allowanceForeign : ∀ account, sevm.currentTarget ≠ account →
      Devm.getStor logPre account = Devm.getStor sstorePre account :=
    fun _ ne => sstore_getStor_of_ne sstoreSource ne
  have logStack : [] <<+ logPre.stack :=
    prefix_of_sstore sstoreSource sstorePrefix
  have sstoreMemory : sstorePre.memory = logPre.memory :=
    Ninst.Hinv.inv (f := Devm.memory) sstoreSource
  have logWf : Mem.Wf logPre.memory := by
    rw [← sstoreMemory]; exact sstoreWf
  have logReads : Mem.Reads logPre.memory keyImage := by
    rw [← sstoreMemory]; exact sstoreReads

  -- Emit the approval and return canonical true.
  obtain ⟨truePre, logRun, trueRun⟩ := runCompiledTo_prepend_inv run
  have logLineRun := logRun
  have logStorage : Devm.getStor logPre = Devm.getStor truePre := by
    refine Line.of_inv Devm.getStor ?_ logLineRun
    unfold logApproval ProrataWethVault.loadWord mstoreAt logWith
    line_inv
  simp only [logApproval, List.append_assoc] at logRun
  obtain ⟨e1, logAmountRun, logRun⟩ := of_run_append (loadWord amountWord) logRun
  obtain ⟨logAmountPrefix, e1Wf, e1Reads, -⟩ :=
    of_run_loadWordAt_image logStack logWf logReads amountAtKey logAmountRun
  obtain ⟨e2, logStoreRun, logRun⟩ := of_run_append (mstoreAt 0) logRun
  obtain ⟨e2Stack, e2Wf, e2Reads, -⟩ :=
    of_run_mstoreAt_image logAmountPrefix e1Wf e1Reads logStoreRun
  have zeroOffset : ((0 : B256) * 32).toNat = 0 := by decide +kernel
  rw [zeroOffset] at e2Reads
  have receiverAtLogged : Bytes.toB256
      ((Bytes.writeAt keyImage 0 (Sevm.argWord sevm 1).toBytes).sliceD
        (receiverWord * 32).toNat 32 0) = Sevm.argWord sevm 0 := by
    rw [Bytes.readWord_writeAt_of_disjoint]
    · exact receiverAtKey
    · right
      decide +kernel
  obtain ⟨e3, logReceiverRun, logRun⟩ :=
    of_run_append (loadWord receiverWord) logRun
  obtain ⟨e3Prefix, e3Wf, e3Reads, -⟩ :=
    of_run_loadWordAt_image e2Stack e2Wf e2Reads receiverAtLogged
      logReceiverRun
  obtain ⟨e4, headRun, logRun⟩ :=
    of_run_append [caller, pushB256 approvalEvent] logRun
  rcases Line.of_run_cons headRun with ⟨e3b, logCallerRun, headTailRun⟩
  rcases Line.of_run_cons headTailRun with ⟨_, eventRun, headNil⟩
  cases headNil
  have logCallerPush := of_run_caller logCallerRun
  have eventPush := of_run_pushB256 eventRun
  have e4Prefix : approvalEvent :: sevm.caller.toB256 ::
      Sevm.argWord sevm 0 :: [] <<+ e4.stack :=
    prefix_of_push eventPush (prefix_of_push logCallerPush e3Prefix)
  have e4Wf : Mem.Wf e4.memory := by
    rw [← eventPush.memory, ← logCallerPush.memory]; exact e3Wf
  have e4Reads : Mem.Reads e4.memory
      (Bytes.writeAt keyImage 0 (Sevm.argWord sevm 1).toBytes) := by
    rw [← eventPush.memory, ← logCallerPush.memory]; exact e3Reads
  obtain ⟨trueStack, emitted⟩ :=
    of_logWith_val
      (topics := [approvalEvent, sevm.caller.toB256, Sevm.argWord sevm 0])
      (by simp) (by simpa using e4Prefix) logRun
  obtain ⟨trueWf, trueReads⟩ := of_logWith_image e4Wf e4Reads logRun
  have logWindow : (e4.memory.read ((0 : B256) * 32).toNat
      ((1 : B256) * 32).toNat).1 = (Sevm.argWord sevm 1).toBytes := by
    have sizeWord : ((1 : B256) * 32).toNat = 32 := by decide +kernel
    rw [zeroOffset, sizeWord, Mem.Reads.read e4Reads,
      show (32 : Nat) = (Sevm.argWord sevm 1).toBytes.length from
        (B256.length_toBytes (Sevm.argWord sevm 1)).symm]
    exact Bytes.sliceD_writeAt keyImage (Sevm.argWord sevm 1).toBytes 0
  have logPrefixLogs : logPre.logs = e4.logs :=
    (of_run_loadWordAt_logs logAmountRun).trans <|
      (Line.of_inv Devm.logs (by unfold mstoreAt; line_inv)
          logStoreRun).trans <|
        (of_run_loadWordAt_logs logReceiverRun).trans <|
          logCallerPush.logs.trans eventPush.logs
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

  -- Assemble the exact approval.
  have preToSstore : Devm.getStor pre = Devm.getStor sstorePre :=
    (funext (getStor_eq_of_state_eq callerState)).trans <|
      (funext (getStor_eq_of_state_eq spenderState)).trans <|
        (funext (getStor_eq_of_state_eq ownerPush.state)).trans <|
          (funext (getStor_eq_of_state_eq ownerStoreState)).trans <|
            (funext (getStor_eq_of_state_eq spenderArgFrame.1)).trans <|
              (funext (getStor_eq_of_state_eq spenderStoreState)).trans <|
                (funext (getStor_eq_of_state_eq amountArgFrame.1)).trans <|
                  (funext (getStor_eq_of_state_eq amountStoreState)).trans <|
                    keyStorage.trans <|
                      (funext (getStor_eq_of_state_eq amountState)).trans
                        (Ninst.Hinv.inv (f := Devm.getStor) swapSource)
  have preToLog : pre.logs = logPre.logs :=
    callerLogs.trans <|
      spenderLogs.trans <|
        ownerPush.logs.trans <|
          (Line.of_inv Devm.logs (by unfold mstoreAt; line_inv)
              ownerStoreRun).trans <|
            spenderArgFrame.2.trans <|
              (Line.of_inv Devm.logs (by unfold mstoreAt; line_inv)
                  spenderStoreRun).trans <|
                amountArgFrame.2.trans <|
                  (Line.of_inv Devm.logs (by unfold mstoreAt; line_inv)
                      amountStoreRun).trans <|
                    keyLogs.trans <|
                      (of_run_loadWordAt_logs amountRun).trans <|
                        (Ninst.Hinv.inv (f := Devm.logs) swapSource).trans
                          (Ninst.Hinv.inv (f := Devm.logs) sstoreSource)
  refine ⟨callerNonzero, spenderValid, spenderNonzero, keyNotAddress,
    keyNotSupply, returnsTrue, ?_, ?_, ?_⟩
  · rw [← congrFun (logStorage.trans trueStorage) sevm.currentTarget,
      allowanceSet, ← congrFun preToSstore sevm.currentTarget]
  · intro account accountNe
    rw [← congrFun (logStorage.trans trueStorage) account,
      allowanceForeign account accountNe, ← congrFun preToSstore account]
  · rw [← trueLogs, emitted, logWindow, ← logPrefixLogs, ← preToLog]
    rfl

/-! ## Share transfers -/

/-- The supply slot is not address-shaped, so it can never alias a share row.
This is what makes a share transfer unable to change the total supply. -/
theorem supplySlot_not_validAdr' :
    ¬ ValidAdr supplySlot := by
  rw [validAdr_iff]
  decide +kernel

/-- `transfer(receiver, amount)` moves the caller's own shares. -/
theorem transfer_body_effect
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    (memoryWf : Mem.Wf pre.memory)
    (lookup : fs[transferFromAfterAllowanceSlot]? = some transferStaged)
    (stack : [] <<+ pre.stack)
    (run : Func.RunCompiledTo fs sevm pre transfer (.ok post)) :
    sevm.caller.toB256 ≠ 0 ∧
      ValidAdr (Sevm.argWord sevm 0) ∧
      Sevm.argWord sevm 0 ≠ 0 ∧
      AbiReturnsTrue post ∧
      Devm.getStorVal post sevm.currentTarget supplySlot =
        Devm.getStorVal pre sevm.currentTarget supplySlot ∧
      ∃ ownerBalance receiverBalance,
        ownerBalance =
          Devm.getStorVal pre sevm.currentTarget sevm.caller.toB256 ∧
        (Sevm.argWord sevm 1).toNat ≤ ownerBalance.toNat ∧
        receiverBalance =
          ((Devm.getStor pre sevm.currentTarget).set sevm.caller.toB256
            (ownerBalance - Sevm.argWord sevm 1)).get
              (Sevm.argWord sevm 0) ∧
        receiverBalance.toNat + (Sevm.argWord sevm 1).toNat < wordModulusN ∧
        Devm.getStor post sevm.currentTarget =
          ((Devm.getStor pre sevm.currentTarget).set sevm.caller.toB256
            (ownerBalance - Sevm.argWord sevm 1)).set (Sevm.argWord sevm 0)
              (receiverBalance + Sevm.argWord sevm 1) ∧
        (∀ account, sevm.currentTarget ≠ account →
          Devm.getStor post account = Devm.getStor pre account) ∧
        post.logs = pre.logs ++
          [transferLogEntry sevm sevm.caller.toB256 (Sevm.argWord sevm 0)
            (Sevm.argWord sevm 1)] := by
  unfold transfer at run
  have entryReads : Mem.Reads pre.memory pre.memory.data.toList := by
    intro index
    simp
  obtain ⟨receiverPre, callerNonzero, receiverStack, callerMemory,
      callerState, callerLogs, run⟩ := nonzeroCaller_trace stack run
  have receiverWf : Mem.Wf receiverPre.memory := by
    rw [← callerMemory]; exact memoryWf
  have receiverReads :
      Mem.Reads receiverPre.memory pre.memory.data.toList := by
    rw [← callerMemory]; exact entryReads
  obtain ⟨stagePre, receiverValid, receiverNonzero, stageStack, stageWf,
      stageReads, receiverState, receiverLogs, run⟩ :=
    canonicalNonzeroAddress_trace receiverWf receiverReads
      (ProducesWord.arg sevm _ 0) receiverStack run
  obtain ⟨callPre, callStack, callWf, callReads, stageState, stageLogs,
      callRun⟩ :=
    shareArgs_trace stageWf stageReads ProducesWord.caller
      (ProducesWord.arg sevm _ 0) (ProducesWord.arg sevm _ 1) stageStack run
  obtain ⟨settlePre, burn, settleRun⟩ := runCompiledTo_call_inv lookup callRun
  have settleWf : Mem.Wf settlePre.memory := by
    rw [← burn.memory]; exact callWf
  have settleReads : Mem.Reads settlePre.memory
      (shareArgImage pre.memory.data.toList sevm.caller.toB256
        (Sevm.argWord sevm 0) (Sevm.argWord sevm 1)) := by
    rw [← burn.memory]; exact callReads
  have settleStack : [] <<+ settlePre.stack := by
    rw [← burn.stack]; exact callStack
  set argImage := shareArgImage pre.memory.data.toList sevm.caller.toB256
    (Sevm.argWord sevm 0) (Sevm.argWord sevm 1) with argImageDef
  change Mem.Reads settlePre.memory argImage at settleReads
  have ownerAtArgs : Bytes.toB256
      (argImage.sliceD (ownerWord * 32).toNat 32 0) =
      sevm.caller.toB256 := by
    rw [argImageDef, shareArgImage, Bytes.readWord_writeAt_of_disjoint,
      Bytes.readWord_writeAt_of_disjoint]
    · exact Bytes.readWord_writeAt_self _ _ _
    · right
      decide +kernel
    · right
      decide +kernel
  have receiverAtArgs : Bytes.toB256
      (argImage.sliceD (receiverWord * 32).toNat 32 0) =
      Sevm.argWord sevm 0 := by
    rw [argImageDef, shareArgImage, Bytes.readWord_writeAt_of_disjoint]
    · exact Bytes.readWord_writeAt_self _ _ _
    · right
      decide +kernel
  have amountAtArgs : Bytes.toB256
      (argImage.sliceD (amountWord * 32).toNat 32 0) =
      Sevm.argWord sevm 1 := by
    rw [argImageDef, shareArgImage]
    exact Bytes.readWord_writeAt_self _ _ _
  obtain ⟨ownerBalance, receiverBalance, ownerBalanceEq, covered,
      receiverBalanceEq, noWrap, returnsTrue, settleStorage, settleForeign,
      settleLogged⟩ :=
    transferStaged_trace settleWf settleReads ownerAtArgs receiverAtArgs
      amountAtArgs settleStack settleRun
  have preToSettle : Devm.getStor pre = Devm.getStor settlePre :=
    (funext (getStor_eq_of_state_eq callerState)).trans
      ((funext (getStor_eq_of_state_eq receiverState)).trans
        ((funext (getStor_eq_of_state_eq stageState)).trans
          (funext (getStor_eq_of_state_eq burn.state))))
  have preToSettleLogs : pre.logs = settlePre.logs :=
    callerLogs.trans (receiverLogs.trans (stageLogs.trans burn.logs))
  have storVal : ∀ k, Devm.getStorVal pre sevm.currentTarget k =
      Devm.getStorVal settlePre sevm.currentTarget k := by
    intro k
    change (Devm.getStor pre sevm.currentTarget).get k =
      (Devm.getStor settlePre sevm.currentTarget).get k
    rw [congrFun preToSettle sevm.currentTarget]
  have callerValid : ValidAdr sevm.caller.toB256 :=
    ⟨sevm.caller, rfl⟩
  have supplyNotOwner : supplySlot ≠ sevm.caller.toB256 := by
    intro slotEq
    exact supplySlot_not_validAdr' (slotEq ▸ callerValid)
  have supplyNotReceiver : supplySlot ≠ Sevm.argWord sevm 0 := by
    intro slotEq
    exact supplySlot_not_validAdr' (slotEq ▸ receiverValid)
  refine ⟨callerNonzero, receiverValid, receiverNonzero, returnsTrue, ?_,
    ownerBalance, receiverBalance, ownerBalanceEq.trans (storVal _).symm,
    covered,
    ?_, noWrap, ?_, ?_, ?_⟩
  · change (Devm.getStor post sevm.currentTarget).get supplySlot =
      (Devm.getStor pre sevm.currentTarget).get supplySlot
    rw [settleStorage, Stor.get_set_ne _ (Ne.symm supplyNotReceiver),
      Stor.get_set_ne _ (Ne.symm supplyNotOwner),
      ← congrFun preToSettle sevm.currentTarget]
  · rw [receiverBalanceEq, ← congrFun preToSettle sevm.currentTarget]
  · rw [settleStorage, ← congrFun preToSettle sevm.currentTarget]
  · intro account accountNe
    rw [settleForeign account accountNe, ← congrFun preToSettle account]
  · rw [settleLogged, ← preToSettleLogs]

/-- `transferFrom(owner, receiver, amount)` moves a third party's shares and
always consults the allowance.

Unlike the outbound redemptions there is no owner-is-caller shortcut in the
source: `transferFrom` reaches `spendAllowance` unconditionally, so the
allowance is always read, always proved to cover the amount, and either
infinite or decremented by exactly it.  `afterAllowance` names the share ledger
between the allowance write and the transfer, which is what lets the settlement
be stated as one exact equation without hiding the allowance step. -/
theorem transferFrom_body_effect
    {fs : List Func} {sevm : Sevm} {pre post : Devm}
    (memoryWf : Mem.Wf pre.memory)
    (lookup : fs[transferFromAfterAllowanceSlot]? = some transferStaged)
    (stack : [] <<+ pre.stack)
    (run : Func.RunCompiledTo fs sevm pre transferFrom (.ok post)) :
    sevm.caller.toB256 ≠ 0 ∧
      ValidAdr (Sevm.argWord sevm 0) ∧
      Sevm.argWord sevm 0 ≠ 0 ∧
      ValidAdr (Sevm.argWord sevm 1) ∧
      Sevm.argWord sevm 1 ≠ 0 ∧
      AbiReturnsTrue post ∧
      ¬ ValidAdr (allowanceKey (Sevm.argWord sevm 0) sevm.caller.toB256) ∧
      allowanceKey (Sevm.argWord sevm 0) sevm.caller.toB256 ≠ supplySlot ∧
      Devm.getStorVal post sevm.currentTarget supplySlot =
        Devm.getStorVal pre sevm.currentTarget supplySlot ∧
      ∃ allowance afterAllowance ownerBalance receiverBalance,
        allowance = Devm.getStorVal pre sevm.currentTarget
          (allowanceKey (Sevm.argWord sevm 0) sevm.caller.toB256) ∧
        (Sevm.argWord sevm 2).toNat ≤ allowance.toNat ∧
        ((allowance = B256.max ∧
            afterAllowance = Devm.getStor pre sevm.currentTarget) ∨
          afterAllowance = (Devm.getStor pre sevm.currentTarget).set
            (allowanceKey (Sevm.argWord sevm 0) sevm.caller.toB256)
            (allowance - Sevm.argWord sevm 2)) ∧
        ownerBalance = afterAllowance.get (Sevm.argWord sevm 0) ∧
        (Sevm.argWord sevm 2).toNat ≤ ownerBalance.toNat ∧
        receiverBalance =
          (afterAllowance.set (Sevm.argWord sevm 0)
            (ownerBalance - Sevm.argWord sevm 2)).get
              (Sevm.argWord sevm 1) ∧
        receiverBalance.toNat + (Sevm.argWord sevm 2).toNat < wordModulusN ∧
        Devm.getStor post sevm.currentTarget =
          ((afterAllowance.set (Sevm.argWord sevm 0)
            (ownerBalance - Sevm.argWord sevm 2)).set (Sevm.argWord sevm 1)
              (receiverBalance + Sevm.argWord sevm 2)) ∧
        (∀ account, sevm.currentTarget ≠ account →
          Devm.getStor post account = Devm.getStor pre account) ∧
        post.logs = pre.logs ++
          [transferLogEntry sevm (Sevm.argWord sevm 0) (Sevm.argWord sevm 1)
            (Sevm.argWord sevm 2)] := by
  unfold transferFrom at run
  have entryReads : Mem.Reads pre.memory pre.memory.data.toList := by
    intro index
    simp
  obtain ⟨ownerPre, callerNonzero, ownerStack, callerMemory, callerState,
      callerLogs, run⟩ := nonzeroCaller_trace stack run
  have ownerWf : Mem.Wf ownerPre.memory := by
    rw [← callerMemory]; exact memoryWf
  have ownerReads : Mem.Reads ownerPre.memory pre.memory.data.toList := by
    rw [← callerMemory]; exact entryReads
  obtain ⟨receiverPre, ownerValid, ownerNonzero, receiverStack, receiverWf,
      receiverReads, ownerState, ownerLogs, run⟩ :=
    canonicalNonzeroAddress_trace ownerWf ownerReads
      (ProducesWord.arg sevm _ 0) ownerStack run
  obtain ⟨stagePre, receiverValid, receiverNonzero, stageStack, stageWf,
      stageReads, receiverState, receiverLogs, run⟩ :=
    canonicalNonzeroAddress_trace receiverWf receiverReads
      (ProducesWord.arg sevm _ 1) receiverStack run
  obtain ⟨spendPre, spendStack, spendWf, spendReads, stageState, stageLogs,
      spendRun⟩ :=
    shareArgs_trace stageWf stageReads (ProducesWord.arg sevm _ 0)
      (ProducesWord.arg sevm _ 1) (ProducesWord.arg sevm _ 2) stageStack run
  set argImage := shareArgImage pre.memory.data.toList (Sevm.argWord sevm 0)
    (Sevm.argWord sevm 1) (Sevm.argWord sevm 2) with argImageDef
  change Mem.Reads spendPre.memory argImage at spendReads
  have ownerAtArgs : Bytes.toB256
      (argImage.sliceD (ownerWord * 32).toNat 32 0) =
      Sevm.argWord sevm 0 := by
    rw [argImageDef, shareArgImage, Bytes.readWord_writeAt_of_disjoint,
      Bytes.readWord_writeAt_of_disjoint]
    · exact Bytes.readWord_writeAt_self _ _ _
    · right
      decide +kernel
    · right
      decide +kernel
  have amountAtArgs : Bytes.toB256
      (argImage.sliceD (amountWord * 32).toNat 32 0) =
      Sevm.argWord sevm 2 := by
    rw [argImageDef, shareArgImage]
    exact Bytes.readWord_writeAt_self _ _ _

  -- Spend the allowance.
  obtain ⟨callPre, allowance, keyNotAddress, keyNotSupply, allowanceValue,
      amountFits, allowanceRoute, spendForeign, spendLogs, spendCode,
      callStack, callWf, callReads, callRun⟩ :=
    spendAllowance_trace spendWf spendReads ownerAtArgs amountAtArgs
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
      spendStack lookup spendRun
  set aKey := allowanceKey (Sevm.argWord sevm 0) sevm.caller.toB256
    with aKeyDef
  set spentImage := allowanceStagingImage argImage (Sevm.argWord sevm 0)
    sevm.caller.toB256 aKey allowance with spentImageDef
  change Mem.Reads callPre.memory spentImage at callReads
  have settleWf : Mem.Wf callPre.memory := callWf
  have settleReads : Mem.Reads callPre.memory spentImage := callReads
  have settleStack : [] <<+ callPre.stack := callStack
  have settleRun := callRun
  have ownerAtSpent : Bytes.toB256
      (spentImage.sliceD (ownerWord * 32).toNat 32 0) =
      Sevm.argWord sevm 0 := by
    rw [spentImageDef, allowanceStagingImage, allowanceKeyImage,
      Bytes.readWord_writeAt_of_disjoint, Bytes.readWord_writeAt_of_disjoint,
      Bytes.readWord_writeAt_of_disjoint, Bytes.readWord_writeAt_of_disjoint]
    · exact ownerAtArgs
    · right
      decide +kernel
    · right
      decide +kernel
    · right
      decide +kernel
    · left
      decide +kernel
  have receiverAtSpent : Bytes.toB256
      (spentImage.sliceD (receiverWord * 32).toNat 32 0) =
      Sevm.argWord sevm 1 := by
    rw [spentImageDef, allowanceStagingImage, allowanceKeyImage,
      Bytes.readWord_writeAt_of_disjoint, Bytes.readWord_writeAt_of_disjoint,
      Bytes.readWord_writeAt_of_disjoint, Bytes.readWord_writeAt_of_disjoint,
      argImageDef, shareArgImage, Bytes.readWord_writeAt_of_disjoint]
    · exact Bytes.readWord_writeAt_self _ _ _
    · right
      decide +kernel
    · right
      decide +kernel
    · right
      decide +kernel
    · right
      decide +kernel
    · left
      decide +kernel
  have amountAtSpent : Bytes.toB256
      (spentImage.sliceD (amountWord * 32).toNat 32 0) =
      Sevm.argWord sevm 2 := by
    rw [spentImageDef, allowanceStagingImage, allowanceKeyImage,
      Bytes.readWord_writeAt_of_disjoint, Bytes.readWord_writeAt_of_disjoint,
      Bytes.readWord_writeAt_of_disjoint, Bytes.readWord_writeAt_of_disjoint]
    · exact amountAtArgs
    · right
      decide +kernel
    · right
      decide +kernel
    · right
      decide +kernel
    · left
      decide +kernel
  obtain ⟨ownerBalance, receiverBalance, ownerBalanceEq, covered,
      receiverBalanceEq, noWrap, returnsTrue, settleStorage, settleForeign,
      settleLogged⟩ :=
    transferStaged_trace settleWf settleReads ownerAtSpent receiverAtSpent
      amountAtSpent settleStack settleRun

  -- Assemble against the endpoint entry.
  have preToSpend : Devm.getStor pre = Devm.getStor spendPre :=
    (funext (getStor_eq_of_state_eq callerState)).trans
      ((funext (getStor_eq_of_state_eq ownerState)).trans
        ((funext (getStor_eq_of_state_eq receiverState)).trans
          (funext (getStor_eq_of_state_eq stageState))))
  have preToSpendLogs : pre.logs = spendPre.logs :=
    callerLogs.trans (ownerLogs.trans (receiverLogs.trans stageLogs))
  have storVal : ∀ k, Devm.getStorVal pre sevm.currentTarget k =
      Devm.getStorVal spendPre sevm.currentTarget k := by
    intro k
    change (Devm.getStor pre sevm.currentTarget).get k =
      (Devm.getStor spendPre sevm.currentTarget).get k
    rw [congrFun preToSpend sevm.currentTarget]
  have supplyNotOwner : supplySlot ≠ Sevm.argWord sevm 0 := by
    intro slotEq
    exact supplySlot_not_validAdr' (slotEq ▸ ownerValid)
  have supplyNotReceiver : supplySlot ≠ Sevm.argWord sevm 1 := by
    intro slotEq
    exact supplySlot_not_validAdr' (slotEq ▸ receiverValid)
  refine ⟨callerNonzero, ownerValid, ownerNonzero, receiverValid,
    receiverNonzero, returnsTrue, keyNotAddress, keyNotSupply, ?_,
    allowance, Devm.getStor callPre sevm.currentTarget, ownerBalance,
    receiverBalance, allowanceValue.trans (storVal _).symm, amountFits, ?_,
    ownerBalanceEq, covered, receiverBalanceEq, noWrap, settleStorage, ?_,
    ?_⟩
  · change (Devm.getStor post sevm.currentTarget).get supplySlot =
      (Devm.getStor pre sevm.currentTarget).get supplySlot
    rw [settleStorage, Stor.get_set_ne _ (Ne.symm supplyNotReceiver),
      Stor.get_set_ne _ (Ne.symm supplyNotOwner)]
    rcases allowanceRoute with ⟨-, unchanged⟩ | decremented
    · rw [unchanged, ← congrFun preToSpend sevm.currentTarget]
    · rw [decremented, Stor.get_set_ne _ keyNotSupply,
        ← congrFun preToSpend sevm.currentTarget]
  · rcases allowanceRoute with ⟨isMax, unchanged⟩ | decremented
    · exact Or.inl ⟨isMax,
        unchanged.trans (congrFun preToSpend sevm.currentTarget).symm⟩
    · exact Or.inr (decremented.trans
        (congrArg (fun storage : Stor => storage.set aKey
          (allowance - Sevm.argWord sevm 2))
          (congrFun preToSpend sevm.currentTarget).symm))
  · intro account accountNe
    rw [settleForeign account accountNe, spendForeign account accountNe,
      ← congrFun preToSpend account]
  · rw [settleLogged, ← spendLogs, ← preToSpendLogs]

theorem transferStaged_lookup :
    (vault.main :: vault.aux)[transferFromAfterAllowanceSlot]? =
      some transferStaged := by
  simp [vault, vaultAux, transferFromAfterAllowanceSlot]

/-! ## Public compiled share operations

None of the three touches WETH, so each lifts through the vault dispatch
without a composition premise. -/

/-- Public compiled `approve(spender, amount)`. -/
theorem approve_compiled_effect
    {sevm : Sevm} {pre post : Devm}
    (memoryWf : Mem.Wf pre.memory)
    (run : Prog.RunCompiled sevm pre vault post)
    (selectorEq :
      Sevm.selector sevm = selector "approve" [.address, .uint256]) :
    sevm.value = 0 ∧
      sevm.caller.toB256 ≠ 0 ∧
      ValidAdr (Sevm.argWord sevm 0) ∧
      Sevm.argWord sevm 0 ≠ 0 ∧
      ¬ ValidAdr (allowanceKey sevm.caller.toB256 (Sevm.argWord sevm 0)) ∧
      allowanceKey sevm.caller.toB256 (Sevm.argWord sevm 0) ≠ supplySlot ∧
      AbiReturnsTrue post ∧
      Devm.getStor post sevm.currentTarget =
        (Devm.getStor pre sevm.currentTarget).set
          (allowanceKey sevm.caller.toB256 (Sevm.argWord sevm 0))
          (Sevm.argWord sevm 1) ∧
      (∀ account, sevm.currentTarget ≠ account →
        Devm.getStor post account = Devm.getStor pre account) ∧
      post.logs = pre.logs ++
        [approvalLogEntry sevm (Sevm.argWord sevm 0)
          (Sevm.argWord sevm 1)] := by
  have member :
      (selector "approve" [.address, .uint256], routed 2 approve) ∈
        vaultFuncs := by
    simp [vaultFuncs]
  rcases runCompiled_enters_body_compiled_logs run selectorEq member with
    ⟨bodyPre, valueZero, -, entryState, entryMemory, entryLogs, -, bodyRun⟩
  have bodyWf : Mem.Wf bodyPre.memory := by
    rw [← entryMemory]
    exact memoryWf
  obtain ⟨callerNonzero, spenderValid, spenderNonzero, keyNotAddress,
      keyNotSupply, returnsTrue, allowanceSet, foreign, logged⟩ :=
    approve_body_effect bodyWf nil_pref bodyRun
  have storEq : Devm.getStor pre = Devm.getStor bodyPre :=
    funext (getStor_eq_of_state_eq entryState)
  refine ⟨valueZero, callerNonzero, spenderValid, spenderNonzero,
    keyNotAddress, keyNotSupply, returnsTrue, ?_, ?_, ?_⟩
  · rw [allowanceSet, ← congrFun storEq sevm.currentTarget]
  · intro account accountNe
    rw [foreign account accountNe, ← congrFun storEq account]
  · rw [logged, ← entryLogs]

/-- Public compiled `transfer(receiver, amount)`. -/
theorem transfer_compiled_effect
    {sevm : Sevm} {pre post : Devm}
    (memoryWf : Mem.Wf pre.memory)
    (run : Prog.RunCompiled sevm pre vault post)
    (selectorEq :
      Sevm.selector sevm = selector "transfer" [.address, .uint256]) :
    sevm.value = 0 ∧
      sevm.caller.toB256 ≠ 0 ∧
      ValidAdr (Sevm.argWord sevm 0) ∧
      Sevm.argWord sevm 0 ≠ 0 ∧
      AbiReturnsTrue post ∧
      Devm.getStorVal post sevm.currentTarget supplySlot =
        Devm.getStorVal pre sevm.currentTarget supplySlot ∧
      ∃ ownerBalance receiverBalance,
        ownerBalance =
          Devm.getStorVal pre sevm.currentTarget sevm.caller.toB256 ∧
        (Sevm.argWord sevm 1).toNat ≤ ownerBalance.toNat ∧
        receiverBalance =
          ((Devm.getStor pre sevm.currentTarget).set sevm.caller.toB256
            (ownerBalance - Sevm.argWord sevm 1)).get
              (Sevm.argWord sevm 0) ∧
        receiverBalance.toNat + (Sevm.argWord sevm 1).toNat < wordModulusN ∧
        Devm.getStor post sevm.currentTarget =
          ((Devm.getStor pre sevm.currentTarget).set sevm.caller.toB256
            (ownerBalance - Sevm.argWord sevm 1)).set (Sevm.argWord sevm 0)
              (receiverBalance + Sevm.argWord sevm 1) ∧
        (∀ account, sevm.currentTarget ≠ account →
          Devm.getStor post account = Devm.getStor pre account) ∧
        post.logs = pre.logs ++
          [transferLogEntry sevm sevm.caller.toB256 (Sevm.argWord sevm 0)
            (Sevm.argWord sevm 1)] := by
  have member :
      (selector "transfer" [.address, .uint256], routed 2 transfer) ∈
        vaultFuncs := by
    simp [vaultFuncs]
  rcases runCompiled_enters_body_compiled_logs run selectorEq member with
    ⟨bodyPre, valueZero, -, entryState, entryMemory, entryLogs, -, bodyRun⟩
  have bodyWf : Mem.Wf bodyPre.memory := by
    rw [← entryMemory]
    exact memoryWf
  obtain ⟨callerNonzero, receiverValid, receiverNonzero, returnsTrue,
      supplyKept, ownerBalance, receiverBalance, ownerBalanceEq, covered,
      receiverBalanceEq, noWrap, settleStorage, foreign, logged⟩ :=
    transfer_body_effect bodyWf transferStaged_lookup nil_pref bodyRun
  have storEq : Devm.getStor pre = Devm.getStor bodyPre :=
    funext (getStor_eq_of_state_eq entryState)
  have storVal : ∀ k, Devm.getStorVal pre sevm.currentTarget k =
      Devm.getStorVal bodyPre sevm.currentTarget k := by
    intro k
    change (Devm.getStor pre sevm.currentTarget).get k =
      (Devm.getStor bodyPre sevm.currentTarget).get k
    rw [congrFun storEq sevm.currentTarget]
  refine ⟨valueZero, callerNonzero, receiverValid, receiverNonzero,
    returnsTrue, ?_, ownerBalance, receiverBalance,
    ownerBalanceEq.trans (storVal _).symm, covered, ?_, noWrap, ?_, ?_, ?_⟩
  · rw [storVal supplySlot]
    exact supplyKept
  · rw [receiverBalanceEq, ← congrFun storEq sevm.currentTarget]
  · rw [settleStorage, ← congrFun storEq sevm.currentTarget]
  · intro account accountNe
    rw [foreign account accountNe, ← congrFun storEq account]
  · rw [logged, ← entryLogs]

/-- Public compiled `transferFrom(owner, receiver, amount)`. -/
theorem transferFrom_compiled_effect
    {sevm : Sevm} {pre post : Devm}
    (memoryWf : Mem.Wf pre.memory)
    (run : Prog.RunCompiled sevm pre vault post)
    (selectorEq : Sevm.selector sevm =
      selector "transferFrom" [.address, .address, .uint256]) :
    sevm.value = 0 ∧
      sevm.caller.toB256 ≠ 0 ∧
      ValidAdr (Sevm.argWord sevm 0) ∧
      Sevm.argWord sevm 0 ≠ 0 ∧
      ValidAdr (Sevm.argWord sevm 1) ∧
      Sevm.argWord sevm 1 ≠ 0 ∧
      AbiReturnsTrue post ∧
      ¬ ValidAdr (allowanceKey (Sevm.argWord sevm 0) sevm.caller.toB256) ∧
      allowanceKey (Sevm.argWord sevm 0) sevm.caller.toB256 ≠ supplySlot ∧
      Devm.getStorVal post sevm.currentTarget supplySlot =
        Devm.getStorVal pre sevm.currentTarget supplySlot ∧
      ∃ allowance afterAllowance ownerBalance receiverBalance,
        allowance = Devm.getStorVal pre sevm.currentTarget
          (allowanceKey (Sevm.argWord sevm 0) sevm.caller.toB256) ∧
        (Sevm.argWord sevm 2).toNat ≤ allowance.toNat ∧
        ((allowance = B256.max ∧
            afterAllowance = Devm.getStor pre sevm.currentTarget) ∨
          afterAllowance = (Devm.getStor pre sevm.currentTarget).set
            (allowanceKey (Sevm.argWord sevm 0) sevm.caller.toB256)
            (allowance - Sevm.argWord sevm 2)) ∧
        ownerBalance = afterAllowance.get (Sevm.argWord sevm 0) ∧
        (Sevm.argWord sevm 2).toNat ≤ ownerBalance.toNat ∧
        receiverBalance =
          (afterAllowance.set (Sevm.argWord sevm 0)
            (ownerBalance - Sevm.argWord sevm 2)).get
              (Sevm.argWord sevm 1) ∧
        receiverBalance.toNat + (Sevm.argWord sevm 2).toNat < wordModulusN ∧
        Devm.getStor post sevm.currentTarget =
          ((afterAllowance.set (Sevm.argWord sevm 0)
            (ownerBalance - Sevm.argWord sevm 2)).set (Sevm.argWord sevm 1)
              (receiverBalance + Sevm.argWord sevm 2)) ∧
        (∀ account, sevm.currentTarget ≠ account →
          Devm.getStor post account = Devm.getStor pre account) ∧
        post.logs = pre.logs ++
          [transferLogEntry sevm (Sevm.argWord sevm 0) (Sevm.argWord sevm 1)
            (Sevm.argWord sevm 2)] := by
  have member :
      (selector "transferFrom" [.address, .address, .uint256],
        routed 3 transferFrom) ∈ vaultFuncs := by
    simp [vaultFuncs]
  rcases runCompiled_enters_body_compiled_logs run selectorEq member with
    ⟨bodyPre, valueZero, -, entryState, entryMemory, entryLogs, -, bodyRun⟩
  have bodyWf : Mem.Wf bodyPre.memory := by
    rw [← entryMemory]
    exact memoryWf
  obtain ⟨callerNonzero, ownerValid, ownerNonzero, receiverValid,
      receiverNonzero, returnsTrue, keyNotAddress, keyNotSupply, supplyKept,
      allowance, afterAllowance, ownerBalance, receiverBalance, allowanceEq,
      amountFits, route, ownerBalanceEq, covered, receiverBalanceEq, noWrap,
      settleStorage, foreign, logged⟩ :=
    transferFrom_body_effect bodyWf transferStaged_lookup nil_pref bodyRun
  have storEq : Devm.getStor pre = Devm.getStor bodyPre :=
    funext (getStor_eq_of_state_eq entryState)
  have storVal : ∀ k, Devm.getStorVal pre sevm.currentTarget k =
      Devm.getStorVal bodyPre sevm.currentTarget k := by
    intro k
    change (Devm.getStor pre sevm.currentTarget).get k =
      (Devm.getStor bodyPre sevm.currentTarget).get k
    rw [congrFun storEq sevm.currentTarget]
  refine ⟨valueZero, callerNonzero, ownerValid, ownerNonzero, receiverValid,
    receiverNonzero, returnsTrue, keyNotAddress, keyNotSupply, ?_,
    allowance, afterAllowance, ownerBalance, receiverBalance,
    allowanceEq.trans (storVal _).symm, amountFits, ?_, ownerBalanceEq,
    covered, receiverBalanceEq, noWrap, settleStorage, ?_, ?_⟩
  · rw [storVal supplySlot]
    exact supplyKept
  · rcases route with ⟨isMax, unchanged⟩ | decremented
    · exact Or.inl ⟨isMax,
        unchanged.trans (congrFun storEq sevm.currentTarget).symm⟩
    · exact Or.inr (decremented.trans
        (congrArg (fun storage : Stor => storage.set
          (allowanceKey (Sevm.argWord sevm 0) sevm.caller.toB256)
          (allowance - Sevm.argWord sevm 2))
          (congrFun storEq sevm.currentTarget).symm))
  · intro account accountNe
    rw [foreign account accountNe, ← congrFun storEq account]
  · rw [logged, ← entryLogs]

/-! ## Ledger conservation

The share ledger is conserved when the supply word is exactly the sum of every
share balance.  Each mutating share operation preserves it, and for different
reasons: an approval writes a slot the invariant cannot see, and a transfer is
a conservative rearrangement that leaves the supply alone. -/

/-- The vault's share ledger is conserved. -/
abbrev Conserved (s : Stor) : Prop := LedgerConserved supplySlot s

/-- `approve` cannot move the invariant: its write lands at a key the collision
guard has proved is not address-shaped, so the balances cannot see it, and not
the supply slot, so the supply cannot see it either. -/
theorem approve_preserves_conserved
    {sevm : Sevm} {pre post : Devm}
    (memoryWf : Mem.Wf pre.memory)
    (run : Prog.RunCompiled sevm pre vault post)
    (selectorEq :
      Sevm.selector sevm = selector "approve" [.address, .uint256])
    (conserved : Conserved (Devm.getStor pre sevm.currentTarget)) :
    Conserved (Devm.getStor post sevm.currentTarget) := by
  obtain ⟨-, -, -, -, keyNotAddress, keyNotSupply, -, allowanceSet, -, -⟩ :=
    approve_compiled_effect memoryWf run selectorEq
  refine conserved.of_rest_eq ?_ ?_
  · rw [allowanceSet, rest_set_of_not_validAdr keyNotAddress]
  · rw [allowanceSet, Stor.get_set_ne _ keyNotSupply]

/-- `transfer` is a conservative rearrangement: the supply word does not move,
so the sum cannot either. -/
theorem transfer_preserves_conserved
    {sevm : Sevm} {pre post : Devm}
    (memoryWf : Mem.Wf pre.memory)
    (run : Prog.RunCompiled sevm pre vault post)
    (selectorEq :
      Sevm.selector sevm = selector "transfer" [.address, .uint256])
    (conserved : Conserved (Devm.getStor pre sevm.currentTarget)) :
    Conserved (Devm.getStor post sevm.currentTarget) := by
  obtain ⟨-, -, receiverValid, -, -, supplyKept, ownerBalance,
      receiverBalance, ownerBalanceEq, covered, receiverBalanceEq, -,
      settleStorage, -, -⟩ :=
    transfer_compiled_effect memoryWf run selectorEq
  obtain ⟨receiverAdr, receiverAdrEq⟩ := receiverValid
  have coveredRest :
      Sevm.argWord sevm 1 ≤ Stor.rest (Devm.getStor pre sevm.currentTarget)
        sevm.caller := by
    have : Stor.rest (Devm.getStor pre sevm.currentTarget) sevm.caller =
        ownerBalance := ownerBalanceEq.symm
    rw [this]
    exact B256.le_of_toNat_le_toNat covered
  refine conserved.transfer (a := sevm.caller) (a' := receiverAdr)
    (x := Sevm.argWord sevm 1) ?_ ?_
  · have shape := transfer_of_debit_credit (s :=
      Devm.getStor pre sevm.currentTarget) (owner := sevm.caller)
      (receiver := receiverAdr) (amount := Sevm.argWord sevm 1) coveredRest
    rw [settleStorage]
    have ownerRest : Stor.rest (Devm.getStor pre sevm.currentTarget)
        sevm.caller = ownerBalance := ownerBalanceEq.symm
    have receiverRest :
        Stor.rest ((Devm.getStor pre sevm.currentTarget).set
          sevm.caller.toB256 (ownerBalance - Sevm.argWord sevm 1))
            receiverAdr = receiverBalance := by
      rw [← receiverAdrEq] at receiverBalanceEq
      exact receiverBalanceEq.symm
    rw [← receiverAdrEq]
    rw [ownerRest] at shape
    rw [receiverRest] at shape
    exact shape
  · exact supplyKept

/-- `transferFrom` is the same rearrangement, after an allowance write the
invariant cannot see. -/
theorem transferFrom_preserves_conserved
    {sevm : Sevm} {pre post : Devm}
    (memoryWf : Mem.Wf pre.memory)
    (run : Prog.RunCompiled sevm pre vault post)
    (selectorEq : Sevm.selector sevm =
      selector "transferFrom" [.address, .address, .uint256])
    (conserved : Conserved (Devm.getStor pre sevm.currentTarget)) :
    Conserved (Devm.getStor post sevm.currentTarget) := by
  obtain ⟨-, -, ownerValid, -, receiverValid, -, -, keyNotAddress,
      keyNotSupply, supplyKept, allowance, afterAllowance, ownerBalance,
      receiverBalance, -, -, route, ownerBalanceEq, covered,
      receiverBalanceEq, -, settleStorage, -, -⟩ :=
    transferFrom_compiled_effect memoryWf run selectorEq
  obtain ⟨ownerAdr, ownerAdrEq⟩ := ownerValid
  obtain ⟨receiverAdr, receiverAdrEq⟩ := receiverValid
  have spentConserved : Conserved afterAllowance := by
    rcases route with ⟨-, unchanged⟩ | decremented
    · exact conserved.of_eq unchanged.symm
    · refine conserved.of_rest_eq ?_ ?_
      · rw [decremented, rest_set_of_not_validAdr keyNotAddress]
      · rw [decremented, Stor.get_set_ne _ keyNotSupply]
  have coveredRest :
      Sevm.argWord sevm 2 ≤ Stor.rest afterAllowance ownerAdr := by
    have ownerRest : Stor.rest afterAllowance ownerAdr = ownerBalance := by
      rw [← ownerAdrEq] at ownerBalanceEq
      exact ownerBalanceEq.symm
    rw [ownerRest]
    exact B256.le_of_toNat_le_toNat covered
  refine spentConserved.transfer (a := ownerAdr) (a' := receiverAdr)
    (x := Sevm.argWord sevm 2) ?_ ?_
  · have shape := transfer_of_debit_credit (s := afterAllowance)
      (owner := ownerAdr) (receiver := receiverAdr)
      (amount := Sevm.argWord sevm 2) coveredRest
    rw [settleStorage]
    have ownerRest : Stor.rest afterAllowance ownerAdr = ownerBalance := by
      rw [← ownerAdrEq] at ownerBalanceEq
      exact ownerBalanceEq.symm
    have receiverRest :
        Stor.rest (afterAllowance.set ownerAdr.toB256
          (ownerBalance - Sevm.argWord sevm 2)) receiverAdr =
          receiverBalance := by
      rw [← ownerAdrEq, ← receiverAdrEq] at receiverBalanceEq
      exact receiverBalanceEq.symm
    rw [← ownerAdrEq, ← receiverAdrEq]
    rw [ownerRest] at shape
    rw [receiverRest] at shape
    exact shape
  · rcases route with ⟨-, unchanged⟩ | decremented
    · rw [unchanged]
      exact supplyKept
    · rw [decremented, Stor.get_set_ne _ keyNotSupply]
      exact supplyKept

end ProrataWethVault

end Blanc
