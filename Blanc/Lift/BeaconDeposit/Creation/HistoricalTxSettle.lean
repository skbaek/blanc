import Blanc.Lift.BeaconDeposit.Creation.HistoricalTxInput
import Blanc.TransactionHistoricalForward
import Blanc.ExecutionInCellProvenance

/-! The actual recovered Beacon CREATE through Muir message and transaction settlement.
The real pre-state, carried output and transaction index remain arbitrary inputs. -/

namespace Blanc.Lift.BeaconDeposit.Creation.HistoricalTx

open Jaune Blanc.BeaconDeposit ExecutionTrace

/-- Muir's actual refund cap, retained even though this constructor refunds zero. -/
def muirGasUsed (post : Devm) : Nat :=
  selectedTxGasUsed 2 tx.gas 0 post.gasLeft 0

theorem muirGasUsed_eq (post : Devm) : muirGasUsed post = tx.gas - post.gasLeft := by
  simp only [muirGasUsed, selectedTxGasUsed, Nat.min_zero, Nat.sub_zero, Nat.max_zero]

/-- The actual Muir sweep after the sender's gas refund and coinbase's fee credit. -/
def muirSettledState (benv : Benv) (post : Devm) : State :=
  sweepTouchedAccounts muirGlacierRules post.meta.touchedAccounts.toList
    ((post.state.addBal deployer
      ((tx.gas - muirGasUsed post) * 147000000000).toB256).addBal benv.stat.coinbase
      (muirGasUsed post * 147000000000).toB256)

/-- The prepared actual transaction executes its ordinary CREATE wrapper cleanly. -/
theorem msgCall_muir {benv : Benv} {bout : BlockOutput} {index intrinsic : Nat}
    {debit : State} {msg : Msg} {post : Devm}
    (p : PreparedCreation benv bout index intrinsic debit msg post) :
    processMessageCall msg = .ok (post.state, directCreateMessageOutputOf post) := by
  simpa only [directCreateMessageOutputOf, p.error, Nat.cast_zero] using
    (processMessageCall_create_of_message (refund := 0)
      (by rw [p.rules]; rfl) (by rw [p.creation])
      p.collision p.process p.error (by rw [p.refund]; rfl))

/-- The real transaction settles from the producer's actual stages. It credits
the sender and coinbase, applies the historical touched-account sweep, advances
both gas counters and appends the receipt at the carried index. -/
theorem settle_muir_prepared_creation
    {benv : Benv} {bout : BlockOutput} {index intrinsic : Nat}
    {debit : State} {msg : Msg} {post : Devm}
    (hfork : benv.stat.fork = .muirGlacier)
    (hbasefee : benv.stat.baseFeePerGas = 0)
    (p : PreparedCreation benv bout index intrinsic debit msg post) :
    ∃ bout', processTransaction benv bout tx index = .ok (muirSettledState benv post, bout') ∧
      bout'.cumulativeGasUsed = bout.cumulativeGasUsed + muirGasUsed post ∧
      bout'.blockGasUsed = bout.blockGasUsed + muirGasUsed post ∧
      bout'.receiptKeys = bout.receiptKeys ++ [BLT.toBytes (.bytes index.toBytes)] ∧
      bout'.receiptsTrie[BLT.toBytes (.bytes index.toBytes)]? =
        some (makeReceipt tx none bout'.cumulativeGasUsed []) ∧
      bout'.blockLogs = bout.blockLogs := by
  have hrules : benv.stat.rules = muirGlacierRules := by
    change Fork.ruleSet benv.stat.fork = muirGlacierRules
    rw [hfork]
    rfl
  have hquot : muirGlacierRules.settle.refundQuotient = 2 := rfl
  have hdebit : (benv.state.incrNonce deployer).subBal deployer
      (tx.gas * 147000000000 + transactionBlobGasFee benv tx).toB256 = some debit := by
    change (benv.state.incrNonce deployer).subBal deployer
      (tx.gas * 147000000000 + 0).toB256 = some debit
    rw [Nat.add_zero, p.feeEq]
    exact p.debited
  obtain ⟨bout', htx, hcum, hblk, hkeys, hreceipt, hlogs⟩ :=
    processTransaction_of_stages_selected_receipts
      (by rw [hrules]; rfl) (by rw [hrules]; rfl) p.validated p.checked
      hdebit p.prepared (msgCall_muir p) (by rfl)
  refine ⟨bout', ?_, ?_, ?_, hkeys, ?_, ?_⟩
  · simpa only [selectedTxFinalState, directCreateMessageOutputOf, p.deletions,
      Std.HashSet.toList_emptyWithCapacity, List.foldl_nil, hrules, hquot, hbasefee,
      Nat.sub_zero, muirGasUsed, muirSettledState] using htx
  · simpa only [hrules, hquot, directCreateMessageOutputOf, muirGasUsed] using hcum
  · simpa only [hrules, hquot, directCreateMessageOutputOf, muirGasUsed] using hblk
  · simpa only [directCreateMessageOutputOf, p.error, p.logs] using hreceipt
  · simpa only [directCreateMessageOutputOf, p.logs, List.append_nil] using hlogs

/-- The two balance credits and Muir sweep preserve the created account's code
and storage. This also covers a coinbase equal to the newly created address. -/
theorem muirSettledState_invariant {benv : Benv} {bout : BlockOutput} {index intrinsic : Nat}
    {debit : State} {msg : Msg} {post : Devm}
    (p : PreparedCreation benv bout index intrinsic debit msg post) :
    ((muirSettledState benv post).getCode depositAddress).toList =
        Blanc.Lift.BeaconDeposit.code.toList ∧
      SolInv ((muirSettledState benv post).getStor depositAddress) [] := by
  have hcode : (post.state.getCode depositAddress).toList ≠ [] := by
    rw [show (post.state.getCode depositAddress).toList =
      Blanc.Lift.BeaconDeposit.code.toList from p.installed]
    intro hempty
    have hwindow : runtimeWindow = Blanc.Lift.BeaconDeposit.code.toList := by
      rw [runtimeWindow, ByteArray.sliceD_eq]
      exact runtime_window
    have hlen := runtimeWindow_length
    rw [hwindow, hempty] at hlen
    cases hlen
  have hcode1 : ((post.state.addBal deployer
      ((tx.gas - muirGasUsed post) * 147000000000).toB256).getCode depositAddress).toList ≠ [] := by
    rw [State.addBal_getCode]
    exact hcode
  have hcode2 : (((post.state.addBal deployer
      ((tx.gas - muirGasUsed post) * 147000000000).toB256).addBal benv.stat.coinbase
        (muirGasUsed post * 147000000000).toB256).getCode depositAddress).toList ≠ [] := by
    rw [State.addBal_getCode]
    exact hcode1
  constructor
  · unfold muirSettledState
    rw [sweepTouchedAccounts_getCode_of_nonempty _ _ hcode2,
      State.addBal_getCode, State.addBal_getCode]
    exact p.installed
  · unfold muirSettledState
    rw [sweepTouchedAccounts_getStor_of_nonempty _ _ hcode2,
      addBal_getStor_of_codenonempty hcode1, addBal_getStor_of_codenonempty hcode]
    exact p.invariant

/-- The actual signed Muir CREATE is admitted, executed and settled from honest
pre-execution conditions. No post-state, successful result or constructor metadata
is an assumption. Historical inclusion and the rest of the block remain separate. -/
theorem settle_muir_actual_creation
    (benv : Benv) (bout : BlockOutput) (index : Nat)
    (hfork : benv.stat.fork = .muirGlacier)
    (hchain : benv.stat.chainId = 1)
    (hbasefee : benv.stat.baseFeePerGas = 0)
    (hnonce : benv.state.getNonce deployer = 0)
    (hsenderCode : (benv.state.getCode deployer).isEmpty = true)
    (hfunds : 461814024000000000 ≤ (benv.state.bal deployer).toNat)
    (hroom : 3141592 ≤ benv.stat.blockGasLimit - bout.blockGasUsed)
    (hfresh : accountHasCodeOrNonce benv.state depositAddress = false) :
    ∃ intrinsic debit msg post bout',
      PreparedCreation benv bout index intrinsic debit msg post ∧
      processMessageCall msg = .ok (post.state, directCreateMessageOutputOf post) ∧
      processTransaction benv bout tx index = .ok (muirSettledState benv post, bout') ∧
      bout'.cumulativeGasUsed = bout.cumulativeGasUsed + muirGasUsed post ∧
      bout'.blockGasUsed = bout.blockGasUsed + muirGasUsed post ∧
      bout'.receiptKeys = bout.receiptKeys ++ [BLT.toBytes (.bytes index.toBytes)] ∧
      bout'.receiptsTrie[BLT.toBytes (.bytes index.toBytes)]? =
        some (makeReceipt tx none bout'.cumulativeGasUsed []) ∧
      bout'.blockLogs = bout.blockLogs ∧
      ((muirSettledState benv post).getCode depositAddress).toList =
        Blanc.Lift.BeaconDeposit.code.toList ∧
      SolInv ((muirSettledState benv post).getStor depositAddress) [] := by
  obtain ⟨intrinsic, debit, msg, post, p⟩ := prepare_muir_actual_creation benv bout index
    hfork hchain hbasefee hnonce hsenderCode hfunds hroom hfresh
  obtain ⟨bout', htx, hcum, hblk, hkeys, hreceipt, hlogs⟩ :=
    settle_muir_prepared_creation hfork hbasefee p
  obtain ⟨hcode, hinv⟩ := muirSettledState_invariant p
  exact ⟨intrinsic, debit, msg, post, bout', p, msgCall_muir p, htx, hcum, hblk,
    hkeys, hreceipt, hlogs, hcode, hinv⟩

end Blanc.Lift.BeaconDeposit.Creation.HistoricalTx

