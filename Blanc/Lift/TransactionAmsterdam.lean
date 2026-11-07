import Blanc.TransactionForward
import Blanc.Lift.SystemCallAmsterdam

/-!
# A transaction from its stages under Amsterdam

`Blanc/TransactionForward.lean` assembles `processTransaction` from its stages for the forks without a state-gas
dimension or a block access list. This is the same assembly under Amsterdam, for the ordinary case, where the transaction's
gas is within the execution budget and the reservoir is empty. Settlement goes through `settleTransactionGas` and the
block's three gas counters, and the transaction incorporates into the access-list builder at `index + 1`.
Contract-neutral.
-/

namespace Blanc.Lift

open Jaune ExecutionTrace

/-- The storage writes a transaction hands the access-list builder: the message's, with an empty sender or coinbase
erased, as `processTransaction` does. -/
def txSettledWrites (writes : KeySet) (afterRefund final : State) (sender coinbase : Adr) : KeySet :=
  let w1 := if (afterRefund.get sender).Empty then writes.eraseAddress sender else writes
  if (final.get coinbase).Empty then w1.eraseAddress coinbase else w1

/-- The state a settled transaction leaves: the message's, with the sender's gas refund and the coinbase's priority fee
credited. -/
def txFinal (mpost : State) (sender coinbase : Adr) (refund fee : Nat) : State :=
  (mpost.addBal sender refund.toB256).addBal coinbase fee.toB256

/-- **A transaction from its stages, under Amsterdam, with an empty reservoir.** The validation sender, validation,
admission, debit, prepared message and message call of a transaction, with no account to delete, are its
`processTransaction`: the message's state, the sender's refund and the coinbase's fee, by `settleTransactionGas`. The
block's counters advance by the settlement, the receipt holds the message's error and logs, and the builder takes the
transaction at `index + 1`, with the sender and the coinbase among the reads. -/
theorem processTransaction_amsterdam_of_stages {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {i f : Nat} {vs sender : Adr} {price blobGas : Nat} {hashes : List B256} {debit : State} {msg : Msg}
    {mpost : State} {mout : MsgCallOutput} {refund : Nat}
    (hfork : benv.stat.fork = .amsterdam)
    (hvs : recoverValidationSender benv.beginTransaction tx = .ok vs)
    (hvalid : validateTransaction benv.stat.rules tx vs = .ok (i, f))
    (hchecked : checkTransaction benv.beginTransaction (transactionPreludeBout bout tx index) tx =
      .ok (sender, price, hashes, blobGas))
    (halloc : allocateEvmGas benv.stat.rules tx.gas i = ⟨tx.gas - i, 0⟩)
    (hdebit : (benv.state.incrNonce sender).subBal sender
      (tx.gas * price + transactionBlobGasFee benv tx).toB256 = some debit)
    (hprepared : prepareMessage { benv.beginTransaction with state := debit }
      (transactionTenv benv.beginTransaction tx index sender price i hashes) tx = .ok msg)
    (hcall : processMessageCall msg = .ok (mpost, mout))
    (hrefund : Int.toNat? mout.refundCounter = some refund)
    (hdel : mout.accountsToDelete.toList = []) :
    let settlement := settleTransactionGas benv.stat.rules tx.gas f mout.gasLeft mout.stateGasLeft refund
      mout.stateGasUsed
    let refunded := mpost.addBal sender (settlement.gasLeft * price).toB256
    let final := txFinal mpost sender benv.stat.coinbase (settlement.gasLeft * price)
      (settlement.gasUsed * (price - benv.stat.baseFeePerGas))
    ∃ bout', processTransaction benv bout tx index = .ok (final, bout') ∧
      bout'.cumulativeGasUsed = bout.cumulativeGasUsed + settlement.gasUsed ∧
      bout'.blockGasUsed = bout.blockGasUsed + settlement.executionGasUsed ∧
      bout'.blockStateGasUsed = bout.blockStateGasUsed + settlement.stateGasUsed ∧
      bout'.blockLogs = bout.blockLogs ++ mout.logs ∧
      bout'.receiptKeys = bout.receiptKeys ++ [BLT.toBytes (.bytes index.toBytes)] ∧
      bout'.receiptsTrie[BLT.toBytes (.bytes index.toBytes)]? =
        some (makeReceipt tx mout.error bout'.cumulativeGasUsed mout.logs) ∧
      bout'.bal = bout.bal.incorporate (index + 1) benv.state final
        (sender :: benv.stat.coinbase :: mout.accountReads.toList) mout.storageReads.toList
        (txSettledWrites mout.storageWrites refunded final sender benv.stat.coinbase).toList := by
  intro settlement refunded final
  have hrules : benv.beginTransaction.stat.rules = amsterdamRules := amsterdam_rules hfork
  have hrules' : benv.stat.rules = amsterdamRules := amsterdam_rules hfork
  unfold processTransaction
  simp only [bind, Except.bind]
  rw [hvs]
  simp only [BenvStat.rules, Benv.beginTransaction, transactionPreludeBout, transactionBlobGasFee,
    transactionTenv, Except.mapError] at hvalid hchecked hdebit hprepared hrules hrules' halloc ⊢
  have hsweep : benv.stat.fork.ruleSet.settle.touchedSweep = false := by
    rw [hrules]
    rfl
  have hbal : ∃ r, benv.stat.fork.ruleSet.bal = some r := by
    rw [hrules]
    exact ⟨_, rfl⟩
  obtain ⟨r, hbal⟩ := hbal
  have hsg : benv.stat.fork.ruleSet.stateGas = some amsterdamStateGasRules := by
    rw [hrules]
    rfl
  simp only [hvalid, hchecked, hdebit, Option.toExcept, halloc, hprepared, hcall, hrefund, hdel, hbal, hsg,
    settleSelfdestructs, List.foldl_nil, sweepTouchedAccounts_of_not_touchedSweep hsweep]
  apply Exists.intro
  refine ⟨rfl, ?_⟩
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_, rfl⟩
  exact Std.TreeMap.getElem?_insert_self

/-- What a direct type-2 call takes from its block and its sender, under Amsterdam, with no access list: fee rules,
intrinsic gas and the calldata floor by Jaune's own formula, the sender's nonce, code and funds, and room in the block.
These are checks a block's transaction must pass; nothing here proves the block is valid. `price` is the effective gas
price. -/
structure DirectTx (benv : Benv) (bout : BlockOutput) (tx : Tx) (E t : Adr) (chainId : UInt64)
    (prio maxFee i f : Nat) : Prop where
  fork : benv.stat.fork = .amsterdam
  type : tx.type = .two chainId prio maxFee (some t) []
  chain : chainId = benv.stat.chainId
  prioLe : prio ≤ maxFee
  baseLe : benv.stat.baseFeePerGas ≤ maxFee
  cost : calculateIntrinsicCost benv.stat.rules tx E = (i, f)
  /-- The intrinsic cost and the floor fit the gas; the gas is the ordinary case, within the execution budget, so the
  reservoir is empty. -/
  intrinsic : i ≤ tx.gas
  floor : f ≤ tx.gas
  budget : tx.gas ≤ 16777216
  /-- Room in the block's execution and state dimensions. -/
  room : tx.gas ≤ benv.stat.blockGasLimit - bout.blockGasUsed
  stateRoom : tx.gas ≤ benv.stat.blockGasLimit - bout.blockStateGasUsed
  /-- The signature recovers to the sender. -/
  recover : recoverSender benv.stat.chainId tx = .ok E
  nonce : (benv.state.get E).nonce = tx.nonce
  nonceMax : tx.nonce ≠ UInt64.max
  /-- The sender has no code. -/
  noCode : (benv.state.get E).code.isEmpty = true
  funds : tx.gas * maxFee + tx.value ≤ (benv.state.get E).bal.toNat

/-- The effective gas price of a type-2 transaction. -/
def twoPrice (base prio maxFee : Nat) : Nat := min prio (maxFee - base) + base

/-- The state a transaction debits: the nonce bumped, the whole gas fee taken. -/
def txDebit (σ : State) (E : Adr) (fee : Nat) : State :=
  (σ.incrNonce E).setBal E (σ.bal E - fee.toB256)

/-- The message a transaction prepares. -/
def txMsg (benv : Benv) (tx : Tx) (index : Nat) (E t : Adr) (price i : Nat) : Msg :=
  callMessage { benv.beginTransaction with state := txDebit benv.state E (tx.gas * price) }
    (transactionTenv benv.beginTransaction tx index E price i []) tx t

namespace DirectTx

variable {benv : Benv} {bout : BlockOutput} {tx : Tx} {E t : Adr} {chainId : UInt64} {prio maxFee i f : Nat}

/-- The stages of a direct call, from its facts. -/
theorem stages (d : DirectTx benv bout tx E t chainId prio maxFee i f) (index : Nat) :
    let price := twoPrice benv.stat.baseFeePerGas prio maxFee
    recoverValidationSender benv.beginTransaction tx = .ok E ∧
      validateTransaction benv.stat.rules tx E = .ok (i, f) ∧
      checkTransaction benv.beginTransaction (transactionPreludeBout bout tx index) tx =
        .ok (E, price, [], 0) ∧
      allocateEvmGas benv.stat.rules tx.gas i = ⟨tx.gas - i, 0⟩ ∧
      (benv.state.incrNonce E).subBal E (tx.gas * price + transactionBlobGasFee benv tx).toB256 =
        some (txDebit benv.state E (tx.gas * price)) ∧
      prepareMessage { benv.beginTransaction with state := txDebit benv.state E (tx.gas * price) }
        (transactionTenv benv.beginTransaction tx index E price i []) tx =
          .ok (txMsg benv tx index E t price i) := by
  intro price
  have hrules : benv.stat.rules = amsterdamRules := amsterdam_rules d.fork
  have hbeginRules : (benv.beginTransaction).stat.rules = amsterdamRules := amsterdam_rules d.fork
  have hrec : tx.type.receiver? = some t := by rw [d.type]; rfl
  have hprice : price ≤ maxFee := by
    have := d.baseLe
    have := d.prioLe
    simp only [price, twoPrice]
    omega
  have hmul : tx.gas * price ≤ tx.gas * maxFee := Nat.mul_le_mul_left _ hprice
  have hbal := B256.toNat_lt (benv.state.get E).bal
  have hfunds := d.funds
  have hfit : tx.gas * maxFee ≤ B256.max.toNat := by
    have hmax : B256.max.toNat = 2 ^ 256 - 1 := by decide
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_, prepareMessage_call hrec⟩
  · unfold recoverValidationSender
    have hsg : (benv.beginTransaction).stat.rules.stateGas = some amsterdamStateGasRules := by
      rw [hbeginRules]
      rfl
    rw [hsg]
    simp only [bind, Except.bind, Except.mapError]
    rw [checkTransactionChainId_two (benv := benv.beginTransaction) d.type d.chain]
    have hr : recoverSender (benv.beginTransaction).stat.chainId tx = .ok E := d.recover
    rw [hr]
  · exact validateTransaction_amsterdam_two hrules d.type d.prioLe d.nonceMax (by have := d.budget; omega) d.cost
      d.intrinsic d.floor (by have := d.budget; have := d.intrinsic; omega)
      (by have := d.budget; have := d.floor; omega)
  · have hgas : checkTransactionGasLimits benv.beginTransaction (transactionPreludeBout bout tx index) tx = .ok 0 := by
      unfold checkTransactionGasLimits
      have hblob : calculateTotalBlobGas tx = 0 := calculateTotalBlobGas_two d.type
      rw [hbeginRules, hblob]
      show (if min (16777216 : Nat) tx.gas > benv.stat.blockGasLimit - bout.blockGasUsed then _ else
        if tx.gas > benv.stat.blockGasLimit - bout.blockStateGasUsed then _ else
        if 0 > _ then _ else _) = _
      have h1 : ¬ min (16777216 : Nat) tx.gas > benv.stat.blockGasLimit - bout.blockGasUsed := by
        have := d.room
        omega
      simp only [h1, gt_iff_lt, Nat.not_lt.mpr d.stateRoom, Nat.not_lt_zero, ↓reduceIte]
    exact checkTransaction_ok_of_parts hgas
      (checkTransactionChainId_two (benv := benv.beginTransaction) d.type d.chain) d.recover
      (checkTransactionGasFee_two (benv := benv.beginTransaction) d.type d.prioLe d.baseLe hfit)
      (checkTransactionBlobData_two (benv := benv.beginTransaction) d.type _)
      (checkTransactionReceiver_two d.type) (checkTransactionAuthorizationList_two d.type)
      (checkTransactionSenderAccount_ok_of_noCode d.nonce d.funds d.noCode)
  · simp only [allocateEvmGas, hrules]
    show (⟨min (16777216 - i) (tx.gas - i), tx.gas - i - min (16777216 - i) (tx.gas - i)⟩ : EvmGasAllocation) = _
    have h1 : min (16777216 - i) (tx.gas - i) = tx.gas - i := by
      have := d.budget
      omega
    rw [h1, Nat.sub_self]
  · rw [transactionBlobGasFee_two d.type, Nat.add_zero]
    refine subBal_incrNonce_of_le ?_
    rw [B256.le_iff_toNat_le_toNat, B256.toNat_toB256_of_lt (by omega)]
    show tx.gas * price ≤ (benv.state.get E).bal.toNat
    omega

end DirectTx

end Blanc.Lift
