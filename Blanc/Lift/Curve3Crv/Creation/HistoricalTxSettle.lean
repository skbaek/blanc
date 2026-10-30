import Blanc.Lift.Curve3Crv.Creation.HistoricalTxInput
import Blanc.TransactionHistoricalForward
import Blanc.ExecutionInCellProvenance

/-!
# The 3Crv creation transaction through Muir message and transaction settlement

`settle_muir_actual_creation`: from honest pre-execution facts, the recorded signed CREATE is
admitted, executed and settled. Its gas used is exactly the signed limit 678,343
(`muirGasUsed_eq_limit`, a theorem: the constructor leaves no gas), its receipt at the carried
index carries the single `Transfer(0, deployer, 0)` log, the block log list gains that log, and
the settled state holds the certified runtime at `tokenAddress` with storage
`deployedStor deployer` (through both fee credits and the Muir touched-account sweep, including
a coinbase equal to the token address).
-/

namespace Blanc.Lift.Curve3Crv.Creation.HistoricalTx

open Jaune Blanc.Lift ExecutionTrace

/-- Muir's gas used for the transaction (refund quotient 2, no calldata floor, no refund). -/
def muirGasUsed (post : Devm) : Nat :=
  selectedTxGasUsed 2 tx.gas 0 post.gasLeft 0

theorem muirGasUsed_eq (post : Devm) : muirGasUsed post = tx.gas - post.gasLeft := by
  simp only [muirGasUsed, selectedTxGasUsed, Nat.min_zero, Nat.sub_zero, Nat.max_zero]

/-- The Muir sweep after the sender's gas refund and coinbase's fee credit. -/
def muirSettledState (benv : Benv) (post : Devm) : State :=
  sweepTouchedAccounts muirGlacierRules post.meta.touchedAccounts.toList
    ((post.state.addBal deployer
      ((tx.gas - muirGasUsed post) * 120427120878).toB256).addBal benv.stat.coinbase
      (muirGasUsed post * 120427120878).toB256)

/-- The single creation log, `Transfer(0, deployer, 0)` emitted by the token. -/
def creationLog : Log := transferLog tokenAddress deployer.toB256

/-- The prepared transaction executes its CREATE wrapper cleanly. -/
theorem msgCall_muir {benv : Benv} {bout : BlockOutput} {index : Nat}
    {debit : State} {msg : Msg} {post : Devm}
    (p : PreparedCreation benv bout index debit msg post) :
    processMessageCall msg = .ok (post.state, directCreateMessageOutputOf post) := by
  simpa only [directCreateMessageOutputOf, p.error, Nat.cast_zero] using
    (processMessageCall_create_of_message (refund := 0)
      (by rw [p.rules]; rfl) (by rw [p.creation])
      p.collision p.process p.error (by rw [p.refund]; rfl))

/-- **The gas used is the signed gas limit**, reproduced: the constructor and code deposit
consume exactly the message gas. -/
theorem muirGasUsed_eq_limit {benv : Benv} {bout : BlockOutput} {index : Nat}
    {debit : State} {msg : Msg} {post : Devm}
    (p : PreparedCreation benv bout index debit msg post) : muirGasUsed post = 678343 := by
  rw [muirGasUsed_eq, p.gasLeft]
  rfl

/-- The transaction settles from the producer's stages: both fee credits, the Muir sweep, both
gas counters advanced, the receipt at the carried index with the one creation log, and the block
log list extended by that log. -/
theorem settle_muir_prepared_creation
    {benv : Benv} {bout : BlockOutput} {index : Nat}
    {debit : State} {msg : Msg} {post : Devm}
    (hfork : benv.stat.fork = .muirGlacier)
    (hbasefee : benv.stat.baseFeePerGas = 0)
    (p : PreparedCreation benv bout index debit msg post) :
    ∃ bout', processTransaction benv bout tx index = .ok (muirSettledState benv post, bout') ∧
      bout'.cumulativeGasUsed = bout.cumulativeGasUsed + muirGasUsed post ∧
      bout'.blockGasUsed = bout.blockGasUsed + muirGasUsed post ∧
      bout'.receiptKeys = bout.receiptKeys ++ [BLT.toBytes (.bytes index.toBytes)] ∧
      bout'.receiptsTrie[BLT.toBytes (.bytes index.toBytes)]? =
        some (makeReceipt tx none bout'.cumulativeGasUsed [creationLog]) ∧
      bout'.blockLogs = bout.blockLogs ++ [creationLog] := by
  have hrules : benv.stat.rules = muirGlacierRules := by
    change Fork.ruleSet benv.stat.fork = muirGlacierRules
    rw [hfork]
    rfl
  have hquot : muirGlacierRules.settle.refundQuotient = 2 := rfl
  have hdebit : (benv.state.incrNonce deployer).subBal deployer
      (tx.gas * 120427120878 + transactionBlobGasFee benv tx).toB256 = some debit := by
    change (benv.state.incrNonce deployer).subBal deployer
      (tx.gas * 120427120878 + 0).toB256 = some debit
    rw [Nat.add_zero, fee_eq]
    exact p.debited
  have hvalid : validateTransaction benv.stat.rules tx 0 = .ok (97992, 0) := p.validated
  obtain ⟨bout', htx, hcum, hblk, hkeys, hreceipt, hlogs⟩ :=
    processTransaction_of_stages_selected_receipts
      (by rw [hrules]; rfl) (by rw [hrules]; rfl) hvalid p.checked
      hdebit p.prepared (msgCall_muir p) (by rfl)
  refine ⟨bout', ?_, ?_, ?_, hkeys, ?_, ?_⟩
  · simpa only [selectedTxFinalState, directCreateMessageOutputOf, p.deletions,
      Std.HashSet.toList_emptyWithCapacity, List.foldl_nil, hrules, hquot, hbasefee,
      Nat.sub_zero, muirGasUsed, muirSettledState] using htx
  · simpa only [hrules, hquot, directCreateMessageOutputOf, muirGasUsed] using hcum
  · simpa only [hrules, hquot, directCreateMessageOutputOf, muirGasUsed] using hblk
  · simpa only [directCreateMessageOutputOf, p.error, p.logs, creationLog] using hreceipt
  · simpa only [directCreateMessageOutputOf, p.logs, creationLog] using hlogs

/-- The certified runtime is nonempty. -/
theorem runtime_ne_nil : Blanc.Lift.Curve3Crv.code.toList ≠ [] := by
  rw [ByteArray.toList_eq_toList_data]
  decide +kernel

/-- The two balance credits and the Muir sweep preserve the token's code and storage, also for a
coinbase equal to the token address. -/
theorem muirSettledState_installed {benv : Benv} {bout : BlockOutput} {index : Nat}
    {debit : State} {msg : Msg} {post : Devm}
    (p : PreparedCreation benv bout index debit msg post) :
    ((muirSettledState benv post).getCode tokenAddress).toList =
        Blanc.Lift.Curve3Crv.code.toList ∧
      (muirSettledState benv post).getStor tokenAddress = deployedStor deployer.toB256 := by
  have hcode : (post.state.getCode tokenAddress).toList ≠ [] := by
    rw [show (post.state.getCode tokenAddress).toList =
      Blanc.Lift.Curve3Crv.code.toList from p.installed]
    exact runtime_ne_nil
  have hcode1 : ((post.state.addBal deployer
      ((tx.gas - muirGasUsed post) * 120427120878).toB256).getCode tokenAddress).toList ≠ [] := by
    rw [State.addBal_getCode]
    exact hcode
  have hcode2 : (((post.state.addBal deployer
      ((tx.gas - muirGasUsed post) * 120427120878).toB256).addBal benv.stat.coinbase
        (muirGasUsed post * 120427120878).toB256).getCode tokenAddress).toList ≠ [] := by
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
    exact p.storage

/-- **The recorded signed Muir CREATE is admitted, executed and settled** from honest
pre-execution conditions. No post-state, successful result, constructor metadata or gas
observation is an assumption; block inclusion is separate. -/
theorem settle_muir_actual_creation
    (benv : Benv) (bout : BlockOutput) (index : Nat)
    (hfork : benv.stat.fork = .muirGlacier)
    (hbasefee : benv.stat.baseFeePerGas = 0)
    (hnonce : benv.state.getNonce deployer = 42)
    (hsenderCode : (benv.state.getCode deployer).isEmpty = true)
    (hfunds : 81690894457745154 ≤ (benv.state.bal deployer).toNat)
    (hroom : 678343 ≤ benv.stat.blockGasLimit - bout.blockGasUsed)
    (hfresh : accountHasCodeOrNonce benv.state tokenAddress = false) :
    ∃ debit msg post bout',
      PreparedCreation benv bout index debit msg post ∧
      processTransaction benv bout tx index = .ok (muirSettledState benv post, bout') ∧
      muirGasUsed post = 678343 ∧
      bout'.cumulativeGasUsed = bout.cumulativeGasUsed + 678343 ∧
      bout'.blockGasUsed = bout.blockGasUsed + 678343 ∧
      bout'.receiptsTrie[BLT.toBytes (.bytes index.toBytes)]? =
        some (makeReceipt tx none bout'.cumulativeGasUsed [creationLog]) ∧
      bout'.blockLogs = bout.blockLogs ++ [creationLog] ∧
      ((muirSettledState benv post).getCode tokenAddress).toList =
        Blanc.Lift.Curve3Crv.code.toList ∧
      (muirSettledState benv post).getStor tokenAddress = deployedStor deployer.toB256 := by
  obtain ⟨debit, msg, post, p⟩ := prepare_muir_actual_creation benv bout index
    hfork hbasefee hnonce hsenderCode hfunds hroom hfresh
  obtain ⟨bout', htx, hcum, hblk, -, hreceipt, hlogs⟩ :=
    settle_muir_prepared_creation hfork hbasefee p
  have hused := muirGasUsed_eq_limit p
  rw [hused] at hcum hblk
  obtain ⟨hcode, hstor⟩ := muirSettledState_installed p
  exact ⟨debit, msg, post, bout', p, htx, hused, hcum, hblk, hreceipt, hlogs, hcode, hstor⟩

end Blanc.Lift.Curve3Crv.Creation.HistoricalTx
