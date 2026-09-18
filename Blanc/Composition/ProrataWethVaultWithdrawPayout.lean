-- ProrataWethVaultWithdrawPayout.lean : WETH `withdraw` split at its accepted payout.

import Blanc.Composition.ProrataWethVaultHistory

/-!
# WETH `withdraw` at its accepted payout

The pair history's WETH `withdraw` segment hypothesis,
`WethWithdrawAcceptedPayout`, discharged.  `weth_withdraw_preCall_split`
supplies the debited storage, the seven payout operands and the nonzero success
word; this module opens the `CALL` with `of_run_call_val_with_depth_frame`,
builds the accepted payout trace with the exact child message in hand, and
hands WETH's own precondition to the callback entry through the outbound value
transfer.  Nothing is said about the callback's behaviour.
-/

namespace Blanc.Composition.ProrataWethVault

open Jaune

/-- **WETH `withdraw` splits at its accepted payout.**  Every committed compiled
`withdraw` entered under WETH's precondition by a caller other than WETH
exposes its accepted payout `CALL`, the storage written before it, and the
callback entry's inherited code, block statics and WETH precondition. -/
theorem wethWithdrawAcceptedPayout : WethWithdrawAcceptedPayout := by
  intro sevm pre post run target _ callerNe selected precondition _
  obtain ⟨callPre, callPost, -, written, foreignKept, callRun, after, callStack,
    callBal, callCode, solvent, success, guardPost, nonzero, successPop⟩ :=
    weth_withdraw_preCall_split run selected
  rcases of_run_call_val_with_depth_frame (xs := []) callStack callRun with
    failed | entered
  · exact absurd (popBurn_pref successPop failed.1).1 nonzero
  rcases entered with
    ⟨parent, child, xl, delegated, nextAddress, code, avail, pc, -, positive, -,
      parentState, -, -, -, -, filled, processed, clean, -, callPostState,
      -, -, -⟩
  let wad := Sevm.argWord sevm 0
  let childMsg :=
    callMsg sevm parent
      (min (0 : B256).toNat (except64th avail) +
        (if wad.toNat = 0 then 0 else gCallStipend))
      wad sevm.currentTarget sevm.caller.toB256.toAdr nextAddress true false
      ((callPre.memory.read (0 : B256).toNat (0 : B256).toNat).1) code delegated
  change ProcessMessage childMsg xl (.ok child) at processed
  obtain ⟨retained⟩ := ExecutionTrace.exists_retainedXlot_of_filled filled
  have recipientNe : sevm.caller.toB256.toAdr ≠ sevm.currentTarget := by
    rw [toAdr_toB256, target]
    exact callerNe
  obtain ⟨settledRaw, frameBody, settled⟩ := ProcessMessage.iff_body.mp processed
  unfold FrameBody at frameBody
  rcases transfer : childMsg.benvAfterTransfer with error | entry <;>
    rw [transfer] at frameBody
  · rw [frameBody.2, processMessage.settle_error] at settled
    cases settled
  rcases of_benvAfterTransfer (rfl : childMsg.shouldTransferValue = true) transfer with
    ⟨debited, debit, entryEq⟩
  change parent.state.subBal sevm.currentTarget wad = some debited at debit
  rw [parentState] at debit
  have entryState : entry.state = debited.addBal sevm.caller.toB256.toAdr wad := by
    rw [entryEq]
    rfl
  have fields := of_state_transfer_fields (callee := sevm.caller.toB256.toAdr) debit
  let payout : Blanc.Prorata.AcceptedPayoutTrace sevm wad callPre callPost :=
    { childMsg := childMsg
      entry := entry
      child := child
      trace := ⟨xl, retained, processed⟩
      childClean := clean
      messageState := parentState
      shouldTransferValue := rfl
      caller := rfl
      value := rfl
      target := rfl
      targetNe := recipientNe
      depth := by
        change sevm.depth - 1 < sevm.depth
        omega
      entryTransfer := transfer
      entryStor := by
        rw [entryState]
        exact fields.1 sevm.currentTarget
      entryBalance := by
        rw [entryState]
        exact fields.2.2.2.2 recipientNe
      callPostState := callPostState }
  have atTarget : wethSpec.Pre sevm.currentTarget sevm pre := target ▸ precondition
  refine ⟨⟨callPre, callPost, payout, written, foreignKept, ?_, ?_, ?_, after⟩⟩
  · intro account
    change ((entry.state).get account).code = (pre.getAcct account).code
    rw [entryState, fields.2.1 account]
    exact congrFun callCode account
  · change entry.stat = sevm.benvStat
    rw [benvAfterTransfer_stat transfer]
    rfl
  · apply ContractSpec.Pre.child_of_outbound_transfer
      (st := callPre.state) (st_mid := debited)
      (target := sevm.caller.toB256.toAdr) (value := wad)
    · have entryCode := atTarget.code
      rw [← congrFun callCode sevm.currentTarget] at entryCode
      exact entryCode
    · have side := atTarget.side
      rw [← callBal] at side
      exact side
    · exact solvent atTarget
    · exact debit
    · exact entryState
    · rfl
    · rfl

end Blanc.Composition.ProrataWethVault
