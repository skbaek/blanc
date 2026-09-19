-- ProrataWethVaultNonrevertInbound.lean : `deposit` and `mint` up to their
-- capacity views revert only through a refused WETH child.

import Blanc.Composition.ProrataWethVaultRevertSteps
import Blanc.Composition.ProrataWethVaultPair
import Blanc.ProrataWethVaultMaxArithmetic

namespace Blanc.Composition.ProrataWethVault

open Jaune
open Jaune.Ninst Ninst
open scoped LogOutputHinv
open Source

/-!
# Walk-level revert cause of the inbound flows

Each core takes a reverting gas-exact walk of the deployed vault and shows
that it visits a refused WETH child.  The walk is entered through the
selector, the nonpayable wrapper and the static-head guard; the arguments are
staged; the booked WETH balance is read (a refused `balanceOf` is the
conclusion, otherwise its exact word is the booked balance) and the stable
supply guard passes on `PairStable`; the exact quote fits a word because the
amount is within the capacity view; the caller and receiver guards pass on
their premises; the share-room guard passes because the quote is within the
room; the `transferFrom` child either was refused (the conclusion) or
returned canonical `true`; and the receiver credit cannot wrap because the
ledger is conserved.  What follows is a tail with no `REVERT`.
-/

/-! ## Inbound guards along an avoiding walk -/

section

variable {P : Sevm → Devm → Ninst → Devm → Prop}
  {fs : List Func} {sevm : Sevm}

/-- The inbound share-room guard passes when the quoted shares fit the
remaining room. -/
theorem shareRoomGuard_avoiding {pre : Devm} {out : Execution}
    {image : Bytes} {sharesWord shares supply : B256}
    {body : Func} {tail : Stack}
    (memoryWf : Mem.Wf pre.memory)
    (memoryReads : Mem.Reads pre.memory image)
    (sharesAt : Bytes.toB256
      (image.sliceD (sharesWord * 32).toNat 32 0) = shares)
    (supplyAt : Bytes.toB256
      (image.sliceD (Blanc.ProrataWethVault.supplyWord * 32).toNat 32 0) =
        supply)
    (stable : supply.toNat ≤ Blanc.ProrataWethVault.maxSupplyN)
    (roomFits :
      shares.toNat ≤ Blanc.ProrataWethVault.shareRoomN supply.toNat)
    (stack : tail <<+ pre.stack)
    (run : Func.RunCompiledToAvoiding P fs sevm pre
      (Blanc.ProrataWethVault.loadWord sharesWord +++
        Blanc.ProrataWethVault.shareRoom +++ lt :::
        (Func.revert <?> body)) out) :
    ∃ bodyPre, tail <<+ bodyPre.stack ∧ Mem.Wf bodyPre.memory ∧
      Mem.Reads bodyPre.memory image ∧ pre.state = bodyPre.state ∧
      Func.RunCompiledToAvoiding P fs sevm bodyPre body out := by
  obtain ⟨roomPre, sharesRun, run⟩ := Func.RunCompiledToAvoiding.prepend_inv run
  obtain ⟨sharesPrefix, sharesWf, sharesReads, sharesState⟩ :=
    of_run_loadWordAt_image stack memoryWf memoryReads sharesAt sharesRun
  obtain ⟨testPre, roomRun, run⟩ := Func.RunCompiledToAvoiding.prepend_inv run
  obtain ⟨roomPrefix, roomWf, roomReads, roomState⟩ :=
    (Blanc.ProrataWethVault.ProducesWord.shareRoom (sevm := sevm) supplyAt
      stable) sharesWf sharesReads sharesPrefix roomRun
  obtain ⟨branchPre, testRun, -, branchRun⟩ :=
    Func.RunCompiledToAvoiding.next_inv run
  have testSource := Ninst.Run.of_runCompiled testRun
  have testPrefix := prefix_of_lt testSource roomPrefix
  have roomNat :
      (Nat.toB256 (Blanc.ProrataWethVault.shareRoomN supply.toNat)).toNat =
        Blanc.ProrataWethVault.shareRoomN supply.toNat :=
    B256.toNat_toB256_of_lt
      (Blanc.ProrataWethVault.shareRoomN_lt_wordModulusN supply.toNat)
  have roomLarge :
      ¬ Nat.toB256 (Blanc.ProrataWethVault.shareRoomN supply.toNat) <
        shares := by
    intro roomLt
    have := B256.toNat_lt_toNat roomLt
    rw [roomNat] at this
    omega
  have zeroPrefix : (0 : B256) :: tail <<+ branchPre.stack := by
    simpa [B256.ltCheck, roomLarge] using testPrefix
  obtain ⟨bodyPre, bodyPop, bodyRun, bodyPrefix⟩ :=
    Func.RunCompiledToAvoiding.zero_branch_of_prefix zeroPrefix branchRun
  have bodyPop' := Devm.PopBurn.of_popBurnBy bodyPop
  refine ⟨bodyPre, bodyPrefix, ?_, ?_, ?_, bodyRun⟩
  · rw [← bodyPop'.memory, ← Ninst.Hinv.inv (f := Devm.memory) testSource]
    exact roomWf
  · rw [← bodyPop'.memory, ← Ninst.Hinv.inv (f := Devm.memory) testSource]
    exact roomReads
  · exact sharesState.trans
      (roomState.1.trans
        ((Ninst.Hinv.inv (f := Devm.state) testSource).trans bodyPop'.state))

/-- The inbound receiver credit cannot wrap once the receiver's booked
balance plus the credited shares fit a word, so its guard passes. -/
theorem inboundCredit_avoiding {pre : Devm} {out : Execution}
    {sharesWord receiver shares : B256} {body : Func} {tail : Stack}
    (receiverWindow : MemWordAt pre
      (Blanc.ProrataWethVault.receiverWord * 32).toNat receiver)
    (sharesWindow : MemWordAt pre (sharesWord * 32).toNat shares)
    (sharesMiss : (sharesWord * 32).toNat + 32 ≤
      (Blanc.ProrataWethVault.balanceWord * 32).toNat)
    (noWrap : (Devm.getStorVal pre sevm.currentTarget receiver).toNat +
      shares.toNat < wordModulusN)
    (stack : tail <<+ pre.stack)
    (run : Func.RunCompiledToAvoiding P fs sevm pre
      (Blanc.ProrataWethVault.loadWord Blanc.ProrataWethVault.receiverWord +++
        sload ::: mstoreAt Blanc.ProrataWethVault.balanceWord +++
        Blanc.ProrataWethVault.loadWord sharesWord +++
        Blanc.ProrataWethVault.loadWord Blanc.ProrataWethVault.balanceWord +++
        add ::: mstoreAt Blanc.ProrataWethVault.scratchWord +++
        Blanc.ProrataWethVault.loadWord Blanc.ProrataWethVault.balanceWord +++
        Blanc.ProrataWethVault.loadWord Blanc.ProrataWethVault.scratchWord +++
        lt ::: (Func.revert <?> body)) out) :
    ∃ bodyPre, Func.RunCompiledToAvoiding P fs sevm bodyPre body out := by
  obtain ⟨s1, receiverRun, run⟩ := Func.RunCompiledToAvoiding.prepend_inv run
  have p1 := prefix_of_loadWord_window receiverWindow stack receiverRun
  have state1 : pre.state = s1.state :=
    Line.of_inv Devm.state
      (by unfold Blanc.ProrataWethVault.loadWord; line_inv) receiverRun
  obtain ⟨s2, sloadRun, -, run⟩ := Func.RunCompiledToAvoiding.next_inv run
  have sloadSource := Ninst.Run.of_runCompiled sloadRun
  obtain ⟨balance, p2, balanceEq⟩ := prefix_of_sload sloadSource p1
  have balanceValue : balance =
      Devm.getStorVal pre sevm.currentTarget receiver := by
    rw [balanceEq]
    change (Devm.getStor s1 sevm.currentTarget).get receiver =
      (Devm.getStor pre sevm.currentTarget).get receiver
    rw [funext (getStor_eq_of_state_eq state1)]
  have wf2 : Mem.Wf s2.memory := by
    rw [← Ninst.Hinv.inv (f := Devm.memory) sloadSource]
    exact (sharesWindow.acrossLoadWord receiverRun).1
  obtain ⟨s3, balanceStoreRun, run⟩ :=
    Func.RunCompiledToAvoiding.prepend_inv run
  obtain ⟨p3, wf3, balanceWindow, balanceMiss, -⟩ :=
    mstoreAt_window p2 wf2 balanceStoreRun
  have sharesWindow3 : MemWordAt s3 (sharesWord * 32).toNat shares :=
    balanceMiss (Or.inl sharesMiss)
      ((sharesWindow.acrossLoadWord receiverRun).acrossNinst sloadSource)
  obtain ⟨s4, sharesRun, run⟩ := Func.RunCompiledToAvoiding.prepend_inv run
  have p4 := prefix_of_loadWord_window sharesWindow3 p3 sharesRun
  obtain ⟨s5, balanceRun, run⟩ := Func.RunCompiledToAvoiding.prepend_inv run
  have p5 := prefix_of_loadWord_window
    (balanceWindow.acrossLoadWord sharesRun) p4 balanceRun
  obtain ⟨s6, addRun, -, run⟩ := Func.RunCompiledToAvoiding.next_inv run
  have addSource := Ninst.Run.of_runCompiled addRun
  have p6 := prefix_of_add addSource p5
  have wf6 : Mem.Wf s6.memory := by
    rw [← Ninst.Hinv.inv (f := Devm.memory) addSource]
    exact ((balanceWindow.acrossLoadWord sharesRun).acrossLoadWord
      balanceRun).1
  obtain ⟨s7, scratchStoreRun, run⟩ :=
    Func.RunCompiledToAvoiding.prepend_inv run
  obtain ⟨p7, -, scratchWindow, scratchMiss, -⟩ :=
    mstoreAt_window p6 wf6 scratchStoreRun
  have balanceWindow7 : MemWordAt s7
      (Blanc.ProrataWethVault.balanceWord * 32).toNat balance :=
    scratchMiss (Or.inr (by decide +kernel))
      ((((balanceWindow.acrossLoadWord sharesRun).acrossLoadWord
        balanceRun).acrossNinst addSource))
  obtain ⟨s8, balanceRun2, run⟩ := Func.RunCompiledToAvoiding.prepend_inv run
  have p8 := prefix_of_loadWord_window balanceWindow7 p7 balanceRun2
  obtain ⟨s9, scratchRun, run⟩ := Func.RunCompiledToAvoiding.prepend_inv run
  have p9 := prefix_of_loadWord_window
    (scratchWindow.acrossLoadWord balanceRun2) p8 scratchRun
  obtain ⟨s10, ltRun, -, branchRun⟩ := Func.RunCompiledToAvoiding.next_inv run
  have ltSource := Ninst.Run.of_runCompiled ltRun
  have flag := prefix_of_lt ltSource p9
  have noWrap' : B256.Nof balance shares := by
    unfold B256.Nof
    rw [balanceValue]
    unfold wordModulusN at noWrap
    omega
  have notLess : ¬ balance + shares < balance := by
    intro less
    have := B256.toNat_lt_toNat less
    rw [B256.toNat_add_eq_of_nof _ _ noWrap'] at this
    omega
  have zeroPrefix : (0 : B256) :: tail <<+ s10.stack := by
    simpa [B256.ltCheck, notLess] using flag
  obtain ⟨bodyPre, -, bodyRun, -⟩ :=
    Func.RunCompiledToAvoiding.zero_branch_of_prefix zeroPrefix branchRun
  exact ⟨bodyPre, bodyRun⟩

end

/-- The shared inbound continuation after the quote is staged: with the
caller, receiver and share room passing on their premises, the only way it
reverts is through a refused `transferFrom`. -/
theorem inboundGuardedTail_revert {fs : List Func} {sevm : Sevm}
    {entry d : Devm} {sharesWord assetsSourceWord : B256}
    {receiver supply shares assets : B256} {tail : Stack}
    (config : DirectWethConfiguration sevm.currentTarget sevm entry)
    (memoryWf : Mem.Wf entry.memory)
    (receiverWindow : MemWordAt entry
      (Blanc.ProrataWethVault.receiverWord * 32).toNat receiver)
    (supplyWindow : MemWordAt entry
      (Blanc.ProrataWethVault.supplyWord * 32).toNat supply)
    (sharesWindow : MemWordAt entry (sharesWord * 32).toNat shares)
    (assetsWindow : MemWordAt entry (assetsSourceWord * 32).toNat assets)
    (sharesAbove : 128 ≤ (sharesWord * 32).toNat)
    (sharesMiss : (sharesWord * 32).toNat + 32 ≤
      (Blanc.ProrataWethVault.balanceWord * 32).toNat)
    (assetsAbove : 96 ≤ (assetsSourceWord * 32).toNat)
    (callerNonzero : sevm.caller.toB256 ≠ 0)
    (receiverValid : ValidAdr receiver) (receiverNonzero : receiver ≠ 0)
    (stable : supply.toNat ≤ Blanc.ProrataWethVault.maxSupplyN)
    (roomFits :
      shares.toNat ≤ Blanc.ProrataWethVault.shareRoomN supply.toNat)
    (conserved : LedgerConserved Blanc.ProrataWethVault.supplySlot
      (Devm.getStor entry sevm.currentTarget))
    (supplyEq : supply = Devm.getStorVal entry sevm.currentTarget
      Blanc.ProrataWethVault.supplySlot)
    (stack : tail <<+ entry.stack)
    (run : Func.RunCompiledToAvoiding WethChildRefused fs sevm entry
      (Blanc.ProrataWethVault.nonzeroCaller
        (Blanc.ProrataWethVault.nonzeroStagedAddress
          Blanc.ProrataWethVault.receiverWord
          (Blanc.ProrataWethVault.finishInbound
            (Blanc.ProrataWethVault.loadWord sharesWord)
            (Blanc.ProrataWethVault.loadWord assetsSourceWord)
            (Blanc.ProrataWethVault.loadWord
              Blanc.ProrataWethVault.quoteWord))))
      (.error (.revert, d))) : False := by
  obtain ⟨s1, p1, memory1, state1, run⟩ :=
    nonzeroCaller_avoiding callerNonzero stack run
  have wf1 : Mem.Wf s1.memory := memory1 ▸ memoryWf
  have move1 : ∀ {offset : Nat} {w : B256}, MemWordAt entry offset w →
      MemWordAt s1 offset w := fun window =>
    MemWordAt.of_memory_eq memory1.symm window
  unfold Blanc.ProrataWethVault.nonzeroStagedAddress at run
  obtain ⟨s2, p2, wf2, reads2, state2, run⟩ :=
    canonicalNonzero_avoiding wf1 (selfReads s1)
      (Blanc.ProrataWethVault.ProducesWord.loadWord
        (MemWordAt.self_toB256 (move1 receiverWindow)))
      receiverValid receiverNonzero p1 run
  have move2 : ∀ {offset : Nat} {w : B256}, MemWordAt entry offset w →
      MemWordAt s2 offset w := fun window =>
    MemWordAt.of_selfReads (move1 window) wf2 reads2
  rw [Blanc.ProrataWethVault.finishInbound_shape] at run
  obtain ⟨s3, -, wf3, reads3, state3, run⟩ :=
    shareRoomGuard_avoiding wf2 (selfReads s2) (MemWordAt.self_toB256 (move2 sharesWindow))
      (MemWordAt.self_toB256 (move2 supplyWindow)) stable roomFits p2 run
  have move3 : ∀ {offset : Nat} {w : B256}, MemWordAt entry offset w →
      MemWordAt s3 offset w := fun window =>
    MemWordAt.of_selfReads (move2 window) wf3 reads3
  have state13 : entry.state = s3.state := state1.trans (state2.trans state3)
  obtain ⟨s4, -, carry4, storage4, -, run⟩ :=
    callWethTransferFrom_avoiding (config.of_state_eq' state13) ⟨wf3, reads3⟩
      ((move2 assetsWindow).slice_eq (selfReads s2)) assetsAbove run
  have receiverAbove : 128 ≤ (Blanc.ProrataWethVault.receiverWord * 32).toNat :=
    by decide +kernel
  obtain ⟨s5, run⟩ :=
    inboundCredit_avoiding (tail := [])
      (carry4 receiverAbove (move3 receiverWindow))
      (carry4 sharesAbove (move3 sharesWindow)) sharesMiss
      (by
        have storageEq : Devm.getStor s4 sevm.currentTarget =
            Devm.getStor entry sevm.currentTarget := by
          rw [storage4]
          exact (getStor_eq_of_state_eq state13 _).symm
        change ((Devm.getStor s4 sevm.currentTarget).get receiver).toNat +
          shares.toNat < wordModulusN
        rw [storageEq]
        obtain ⟨receiverAdr, rfl⟩ := receiverValid
        have booked := conserved.le_supply receiverAdr
        have supplyNat : supply.toNat =
            ((Devm.getStor entry sevm.currentTarget).get
              Blanc.ProrataWethVault.supplySlot).toNat :=
          congrArg B256.toNat supplyEq
        have total :=
          Blanc.ProrataWethVault.supply_add_le_maxSupplyN_of_le_shareRoomN
            stable roomFits
        have maxLt : Blanc.ProrataWethVault.maxSupplyN < wordModulusN := by
          unfold Blanc.ProrataWethVault.maxSupplyN maxWordN wordModulusN
          omega
        change (Stor.rest (Devm.getStor entry sevm.currentTarget)
          receiverAdr).toNat + shares.toNat < wordModulusN
        omega)
      nil_pref run
  have free : Func.revertFreeIn []
      (Blanc.ProrataWethVault.loadWord Blanc.ProrataWethVault.scratchWord +++
        Blanc.ProrataWethVault.loadWord Blanc.ProrataWethVault.receiverWord +++
        sstore :::
        Blanc.ProrataWethVault.loadWord sharesWord +++
        Blanc.ProrataWethVault.loadWord Blanc.ProrataWethVault.supplyWord +++
        add ::: Blanc.ProrataWethVault.pushSupplySlot +++ sstore :::
        Blanc.ProrataWethVault.logMintTransfer
          (Blanc.ProrataWethVault.loadWord sharesWord) +++
        Blanc.ProrataWethVault.logDeposit
          (Blanc.ProrataWethVault.loadWord assetsSourceWord)
          (Blanc.ProrataWethVault.loadWord sharesWord) +++
        Blanc.ProrataWethVault.loadWord Blanc.ProrataWethVault.quoteWord +++
        Blanc.ProrataWethVault.returnWord) = true := by
    simp [Func.revertFreeIn_prepend, Func.revertFreeIn,
      Blanc.ProrataWethVault.returnWord, returnMemoryRange, Func.return_]
  exact Func.RunCompiledTo.not_revert_of_revertFreeIn (safe := [])
    (fun _ member => absurd member List.not_mem_nil) run.1 free d rfl

private theorem vault_depositAfterQuote_lookup :
    (Blanc.ProrataWethVault.vault.main ::
        Blanc.ProrataWethVault.vault.aux)[
          Blanc.ProrataWethVault.depositAfterQuoteSlot]? =
      some Blanc.ProrataWethVault.depositAfterQuote := rfl

private theorem vault_mintAfterQuote_lookup :
    (Blanc.ProrataWethVault.vault.main ::
        Blanc.ProrataWethVault.vault.aux)[
          Blanc.ProrataWethVault.mintAfterQuoteSlot]? =
      some Blanc.ProrataWethVault.mintAfterQuote := rfl

/-- The inbound entry along an avoiding walk: the two arguments are staged,
the booked WETH balance and the share supply are read at their pre-state
values, and the stable-supply guard passes. -/
theorem inboundEntry_avoiding {fs : List Func} {sevm : Sevm}
    {pre bodyPre : Devm} {out : Execution} {arithmetic : Func}
    (stable : PairStable sevm.currentTarget sevm.benvStat.rules pre.state)
    (memoryWf : Mem.Wf pre.memory)
    (entryState : pre.state = bodyPre.state)
    (entryMemory : pre.memory = bodyPre.memory)
    (run : Func.RunCompiledToAvoiding WethChildRefused fs sevm bodyPre
      (Blanc.arg 0 +++ mstoreAt Blanc.ProrataWethVault.amountWord +++
        Blanc.arg 1 +++ mstoreAt Blanc.ProrataWethVault.receiverWord +++
        Blanc.ProrataWethVault.snapshotQuoteState arithmetic) out) :
    ∃ quotePre : Devm,
      Mem.Wf quotePre.memory ∧
      MemWordAt quotePre (Blanc.ProrataWethVault.amountWord * 32).toNat
        (Sevm.argWord sevm 0) ∧
      MemWordAt quotePre (Blanc.ProrataWethVault.receiverWord * 32).toNat
        (Sevm.argWord sevm 1) ∧
      MemWordAt quotePre (Blanc.ProrataWethVault.assetsWord * 32).toNat
        ((pre.state.getStor wethAccount).get sevm.currentTarget.toB256) ∧
      MemWordAt quotePre (Blanc.ProrataWethVault.supplyWord * 32).toNat
        (Devm.getStorVal pre sevm.currentTarget
          Blanc.ProrataWethVault.supplySlot) ∧
      Devm.getStor quotePre = Devm.getStor pre ∧
      DirectWethConfiguration sevm.currentTarget sevm quotePre ∧
      Func.RunCompiledToAvoiding WethChildRefused fs sevm quotePre arithmetic
        out := by
  have config : DirectWethConfiguration sevm.currentTarget sevm pre :=
    stable.configuration rfl rfl
  obtain ⟨a1, amountArg, run⟩ := Func.RunCompiledToAvoiding.prepend_inv run
  obtain ⟨a2, amountStore, run⟩ := Func.RunCompiledToAvoiding.prepend_inv run
  obtain ⟨a3, receiverArg, run⟩ := Func.RunCompiledToAvoiding.prepend_inv run
  obtain ⟨a4, receiverStore, run⟩ := Func.RunCompiledToAvoiding.prepend_inv run
  have argSource : Func.Run ([] : List Func) sevm bodyPre
      (Blanc.arg 0 +++ mstoreAt Blanc.ProrataWethVault.amountWord +++
        Blanc.arg 1 +++ mstoreAt Blanc.ProrataWethVault.receiverWord +++
        Func.stop) a4 :=
    Func.Run.prepend_line amountArg (Func.Run.prepend_line amountStore
      (Func.Run.prepend_line receiverArg (Func.Run.prepend_line receiverStore
        (Func.Run.last rfl))))
  have bodyWf : Mem.Wf bodyPre.memory := entryMemory ▸ memoryWf
  obtain ⟨readPre, -, readWf, readReads, argState, -, stopRun⟩ :=
    Blanc.ProrataWethVault.inboundArgs_trace (R := Func.Run) bodyWf
      (selfReads bodyPre) nil_pref argSource
  obtain rfl := Func.Run.stop_inv stopRun
  have readState : pre.state = a4.state := entryState.trans argState
  have readStorage : Devm.getStor a4 = Devm.getStor pre :=
    funext (getStor_eq_of_state_eq readState.symm)
  have amountWindow : MemWordAt a4
      (Blanc.ProrataWethVault.amountWord * 32).toNat (Sevm.argWord sevm 0) :=
    MemWordAt.of_memImage ⟨readWf, readReads⟩ (sliceBytes_of_toB256
      (Blanc.ProrataWethVault.inboundArgImage_amount _ _ _))
  have receiverWindow : MemWordAt a4
      (Blanc.ProrataWethVault.receiverWord * 32).toNat (Sevm.argWord sevm 1) :=
    MemWordAt.of_memImage ⟨readWf, readReads⟩ (sliceBytes_of_toB256
      (Blanc.ProrataWethVault.inboundArgImage_receiver _ _ _))
  have supplyStable : (Devm.getStorVal a4 sevm.currentTarget
      Blanc.ProrataWethVault.supplySlot).toNat ≤
        Blanc.ProrataWethVault.maxSupplyN := by
    change ((Devm.getStor a4 sevm.currentTarget).get
      Blanc.ProrataWethVault.supplySlot).toNat ≤ _
    rw [readStorage]
    exact stable.backed.2.1
  obtain ⟨quotePre, quoteWf, assetsWindow, supplyWindow, carry, quoteStorage,
      quoteConfig, run⟩ :=
    snapshotQuoteState_avoiding (config.of_state_eq' readState) readWf
      supplyStable run
  refine ⟨quotePre, quoteWf,
    carry (by decide +kernel) (by decide +kernel) amountWindow,
    carry (by decide +kernel) (by decide +kernel) receiverWindow, ?_, ?_,
    quoteStorage.trans readStorage, quoteConfig, run⟩
  · have assetsEq : (a4.state.getStor wethAccount).get
        sevm.currentTarget.toB256 =
        (pre.state.getStor wethAccount).get sevm.currentTarget.toB256 := by
      rw [readState]
    rw [← assetsEq]
    exact assetsWindow
  · have supplyEq : Devm.getStorVal a4 sevm.currentTarget
        Blanc.ProrataWethVault.supplySlot =
        Devm.getStorVal pre sevm.currentTarget
          Blanc.ProrataWethVault.supplySlot := by
      change (Devm.getStor a4 sevm.currentTarget).get _ =
        (Devm.getStor pre sevm.currentTarget).get _
      rw [readStorage]
    rw [← supplyEq]
    exact supplyWindow

/-- **`deposit` up to `maxDeposit` does not take a vault revert.**  At a stable
pair state, a `deposit(assets, receiver)` frame with zero value, a complete
static ABI head, a nonzero caller, a canonical nonzero receiver and
`assets ≤ maxDeposit(receiver)` reverts only through a refused WETH child
(`balanceOf` or `transferFrom`).  Caller-side WETH balance and allowance,
out-of-gas halts and the call-depth limit are what remain. -/
theorem deposit_revert_visits_refused_weth_child
    {sevm : Sevm} {pre d : Devm}
    (stable : PairStable sevm.currentTarget sevm.benvStat.rules pre.state)
    (memoryWf : Mem.Wf pre.memory)
    (selectorEq :
      Sevm.selector sevm = selector "deposit" [.uint256, .address])
    (valueZero : sevm.value = 0)
    (argsPresent :
      B256.ltCheck sevm.data.length.toB256 (Nat.toB256 (4 + 32 * 2)) = 0)
    (callerNonzero : sevm.caller.toB256 ≠ 0)
    (receiverValid : ValidAdr (Sevm.argWord sevm 1))
    (receiverNonzero : Sevm.argWord sevm 1 ≠ 0)
    (withinMax :
      (Sevm.argWord sevm 0).toNat ≤
        Blanc.ProrataWethVault.maxDepositViewN (Sevm.argWord sevm 1).toNat
          ((pre.state.getStor wethAccount).get
            sevm.currentTarget.toB256).toNat
          (Devm.getStorVal pre sevm.currentTarget
            Blanc.ProrataWethVault.supplySlot).toNat)
    (walk : Prog.RunCompiledTo sevm pre Blanc.ProrataWethVault.vault
      (.error (.revert, d))) :
    Prog.RunCompiledToVisiting WethChildRefused sevm pre
      Blanc.ProrataWethVault.vault (.error (.revert, d)) := by
  have stableSupply : (Devm.getStorVal pre sevm.currentTarget
      Blanc.ProrataWethVault.supplySlot).toNat ≤
        Blanc.ProrataWethVault.maxSupplyN := stable.backed.2.1
  have amountWord : (Sevm.argWord sevm 0).toNat ≤ maxWordN := by
    have := B256.toNat_lt (Sevm.argWord sevm 0)
    unfold maxWordN wordModulusN
    omega
  rw [Blanc.ProrataWethVault.maxDepositViewN_eq_of_stable
    (B256.toNat_ne_zero receiverNonzero) stableSupply] at withinMax
  -- The share-room guard's revert arm is refuted by this fact: the exact
  -- quote fits the remaining room because the amount is within `maxDeposit`.
  have roomFits := (Blanc.ProrataWethVault.le_maxDepositN_iff amountWord).mp
    withinMax
  have quoteFits := Nat.lt_of_le_of_lt roomFits
    (Blanc.ProrataWethVault.shareRoomN_lt_wordModulusN _)
  refine vault_revert_visits_of_body selectorEq
    (List.mem_of_getElem? (i := 11) rfl) valueZero argsPresent walk ?_
  intro bodyPre entryState entryMemory run
  unfold Blanc.ProrataWethVault.deposit at run
  obtain ⟨quotePre, quoteWf, amountWindow, receiverWindow, assetsWindow,
      supplyWindow, quoteStorage, quoteConfig, run⟩ :=
    inboundEntry_avoiding stable memoryWf entryState entryMemory run
  obtain ⟨afterPre, afterImage, afterStack, afterMemImage, afterFrame,
      afterQuiet, run⟩ :=
    Blanc.ProrataWethVault.depositQuote_avoiding quoteWf (selfReads quotePre)
      (MemWordAt.self_toB256 amountWindow) (MemWordAt.self_toB256 assetsWindow)
      (MemWordAt.self_toB256 supplyWindow) stableSupply nil_pref
      vault_depositAfterQuote_lookup run quoteFits
  have scratchEnd : Blanc.ProrataWethVault.arithmeticScratchEnd = 896 := by
    decide +kernel
  unfold Blanc.ProrataWethVault.depositAfterQuote at run
  obtain ⟨guardPre, storeRun, run⟩ := Func.RunCompiledToAvoiding.prepend_inv run
  obtain ⟨guardStack, guardWf, quoteWindow, storeMiss, storeState⟩ :=
    mstoreAt_window afterStack afterMemImage.1 storeRun
  have move : ∀ {offset : Nat} {w : B256}, 896 ≤ offset →
      (offset + 32 ≤ (Blanc.ProrataWethVault.quoteWord * 32).toNat ∨
        (Blanc.ProrataWethVault.quoteWord * 32).toNat + 32 ≤ offset) →
      MemWordAt quotePre offset w → MemWordAt guardPre offset w := by
    intro offset w above miss window
    exact storeMiss miss (window.of_wordFrame (selfReads quotePre)
      afterMemImage afterFrame (by rw [scratchEnd]; exact above))
  have guardStorage : Devm.getStor guardPre = Devm.getStor pre :=
    (funext (getStor_eq_of_state_eq (afterQuiet.1.trans storeState))).symm.trans
      quoteStorage
  refine inboundGuardedTail_revert
    (quoteConfig.of_state_eq' (afterQuiet.1.trans storeState)) guardWf
    (move (by decide +kernel) (Or.inl (by decide +kernel)) receiverWindow)
    (move (by decide +kernel) (Or.inr (by decide +kernel)) supplyWindow)
    quoteWindow
    (move (by decide +kernel) (Or.inl (by decide +kernel)) amountWindow)
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    callerNonzero receiverValid receiverNonzero stableSupply ?_ ?_ ?_
    guardStack run
  · rw [B256.toNat_toB256_of_lt quoteFits]
    exact roomFits
  · rw [guardStorage]
    exact stable.backed.1
  · change _ = (Devm.getStor guardPre sevm.currentTarget).get _
    rw [guardStorage]
    rfl

/-- **`mint` up to `maxMint` does not take a vault revert.**  As for
`deposit`, with `shares ≤ maxMint(receiver)`. -/
theorem mint_revert_visits_refused_weth_child
    {sevm : Sevm} {pre d : Devm}
    (stable : PairStable sevm.currentTarget sevm.benvStat.rules pre.state)
    (memoryWf : Mem.Wf pre.memory)
    (selectorEq :
      Sevm.selector sevm = selector "mint" [.uint256, .address])
    (valueZero : sevm.value = 0)
    (argsPresent :
      B256.ltCheck sevm.data.length.toB256 (Nat.toB256 (4 + 32 * 2)) = 0)
    (callerNonzero : sevm.caller.toB256 ≠ 0)
    (receiverValid : ValidAdr (Sevm.argWord sevm 1))
    (receiverNonzero : Sevm.argWord sevm 1 ≠ 0)
    (withinMax :
      (Sevm.argWord sevm 0).toNat ≤
        Blanc.ProrataWethVault.maxMintViewN (Sevm.argWord sevm 1).toNat
          ((pre.state.getStor wethAccount).get
            sevm.currentTarget.toB256).toNat
          (Devm.getStorVal pre sevm.currentTarget
            Blanc.ProrataWethVault.supplySlot).toNat)
    (walk : Prog.RunCompiledTo sevm pre Blanc.ProrataWethVault.vault
      (.error (.revert, d))) :
    Prog.RunCompiledToVisiting WethChildRefused sevm pre
      Blanc.ProrataWethVault.vault (.error (.revert, d)) := by
  have stableSupply : (Devm.getStorVal pre sevm.currentTarget
      Blanc.ProrataWethVault.supplySlot).toNat ≤
        Blanc.ProrataWethVault.maxSupplyN := stable.backed.2.1
  rw [Blanc.ProrataWethVault.maxMintViewN_eq_of_stable
    (B256.toNat_ne_zero receiverNonzero) stableSupply] at withinMax
  -- The share-room guard's revert arm is refuted by the room half of this
  -- fact; the ceiling quote fits a word by its other half.
  obtain ⟨roomFits, quoteWord⟩ :=
    (Blanc.ProrataWethVault.le_maxMintN_iff _ _ _).mp withinMax
  have quoteFits : Blanc.ProrataWethVault.previewMintN
      (Sevm.argWord sevm 0).toNat
      ((pre.state.getStor wethAccount).get sevm.currentTarget.toB256).toNat
      (Devm.getStorVal pre sevm.currentTarget
        Blanc.ProrataWethVault.supplySlot).toNat < wordModulusN := by
    unfold maxWordN at quoteWord
    have := wordModulusN_pos
    omega
  refine vault_revert_visits_of_body selectorEq
    (List.mem_of_getElem? (i := 13) rfl) valueZero argsPresent walk ?_
  intro bodyPre entryState entryMemory run
  unfold Blanc.ProrataWethVault.mint at run
  obtain ⟨quotePre, quoteWf, amountWindow, receiverWindow, assetsWindow,
      supplyWindow, quoteStorage, quoteConfig, run⟩ :=
    inboundEntry_avoiding stable memoryWf entryState entryMemory run
  obtain ⟨afterPre, afterImage, afterStack, afterMemImage, afterFrame,
      afterQuiet, run⟩ :=
    Blanc.ProrataWethVault.mintQuote_avoiding quoteWf (selfReads quotePre)
      (MemWordAt.self_toB256 amountWindow) (MemWordAt.self_toB256 assetsWindow)
      (MemWordAt.self_toB256 supplyWindow) stableSupply nil_pref
      vault_mintAfterQuote_lookup run quoteFits
  have scratchEnd : Blanc.ProrataWethVault.arithmeticScratchEnd = 896 := by
    decide +kernel
  unfold Blanc.ProrataWethVault.mintAfterQuote at run
  obtain ⟨guardPre, storeRun, run⟩ := Func.RunCompiledToAvoiding.prepend_inv run
  obtain ⟨guardStack, guardWf, quoteWindow, storeMiss, storeState⟩ :=
    mstoreAt_window afterStack afterMemImage.1 storeRun
  have move : ∀ {offset : Nat} {w : B256}, 896 ≤ offset →
      (offset + 32 ≤ (Blanc.ProrataWethVault.quoteWord * 32).toNat ∨
        (Blanc.ProrataWethVault.quoteWord * 32).toNat + 32 ≤ offset) →
      MemWordAt quotePre offset w → MemWordAt guardPre offset w := by
    intro offset w above miss window
    exact storeMiss miss (window.of_wordFrame (selfReads quotePre)
      afterMemImage afterFrame (by rw [scratchEnd]; exact above))
  have guardStorage : Devm.getStor guardPre = Devm.getStor pre :=
    (funext (getStor_eq_of_state_eq (afterQuiet.1.trans storeState))).symm.trans
      quoteStorage
  refine inboundGuardedTail_revert
    (quoteConfig.of_state_eq' (afterQuiet.1.trans storeState)) guardWf
    (move (by decide +kernel) (Or.inl (by decide +kernel)) receiverWindow)
    (move (by decide +kernel) (Or.inr (by decide +kernel)) supplyWindow)
    (move (by decide +kernel) (Or.inl (by decide +kernel)) amountWindow)
    quoteWindow
    (by decide +kernel) (by decide +kernel) (by decide +kernel)
    callerNonzero receiverValid receiverNonzero stableSupply roomFits ?_ ?_
    guardStack run
  · rw [guardStorage]
    exact stable.backed.1
  · change _ = (Devm.getStor guardPre sevm.currentTarget).get _
    rw [guardStorage]
    rfl

end Blanc.Composition.ProrataWethVault
