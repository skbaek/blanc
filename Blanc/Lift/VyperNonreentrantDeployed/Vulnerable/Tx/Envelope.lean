import Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Tx.Closed
import Blanc.TransactionForward

/-!
# V- as an admitted transaction: the transaction envelope

The transaction `tx0` (a real signature over its signing hash under `E`'s key, type 2, zero fees,
zero value, 30,021,064 gas) is run by Jaune's `processTransaction` over the block `benvPre`.
Every admission check is discharged here by evaluating it on the concrete transaction and block
-- validation and intrinsic gas, chain id, fee rules with base fee 0, nonce, balance against the
maximum fee and value, EIP-3607 (the sender `E` has no code), receiver, authorization list --
except two things that are not evaluations of this block: the signature recovery, which is the
one premise (`recoverSender 0 tx0 = .ok E`, true by evaluation: the `#guard` in `TxTop`), and the
room in the block for the transaction's gas (`bout.blockGasUsed`).  The debit, the prepared
message (which is `msg0tx`, the message of the closed message-level theorem) and the settlement
are `Blanc.processTransaction_of_stages`.
-/

namespace Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Tx

open Jaune Blanc Blanc.ExecutionTrace Blanc.Lift Blanc.Lift.Witness
open Blanc.Lift.VyperNonreentrantDeployed Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Frame1
open Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.TxTop

/-! ### The admission checks, evaluated on the concrete transaction and block -/

theorem benvPre_stateGas : benvPre.stat.rules.stateGas = none :=
  CoveredFork.prague.rules_stateGas_none

theorem benvPre_bal : benvPre.stat.rules.bal = none := CoveredFork.prague.rules_bal_none

/-- Validation: the transaction is well formed and its intrinsic gas (21,000 plus the 64 of its
four nonzero calldata bytes) and calldata floor (21,160) are within its gas. -/
theorem tx0_validated : validateTransaction benvPre.stat.rules tx0 0 = .ok (21064, 21160) := by
  kernel_rfl

/-- The type-2 transaction's chain id is the block's. -/
theorem tx0_chain : checkTransactionChainId benvPre.beginTransaction tx0 = .ok () := by
  kernel_rfl

/-- Fee rules with base fee 0: `maxPriorityFee = maxFee = 0` is legal, and the effective gas
price and the maximum fee are 0. -/
theorem tx0_fee : checkTransactionGasFee benvPre.beginTransaction tx0 = .ok (0, 0) := by
  kernel_rfl

theorem tx0_blob : checkTransactionBlobData benvPre.beginTransaction tx0 0 = .ok (0, []) := by
  kernel_rfl

theorem tx0_receiver : checkTransactionReceiver tx0 = .ok () := by kernel_rfl

theorem tx0_auth : checkTransactionAuthorizationList tx0 = .ok () := by kernel_rfl

/-- The sender account: nonce 0 is the transaction's nonce, its balance 0 covers the maximum fee
0 plus the value 0, and it has no code (EIP-3607): `E` is an EOA. -/
theorem tx0_sender :
    checkTransactionSenderAccount (benvPre.beginTransaction.state.get eAddress) tx0 0 = .ok () := by
  kernel_rfl

/-- **Admission**: with the signature recovering `E` and room in the block for the transaction's
gas, `checkTransaction` accepts `tx0` (blob-free, effective gas price 0). -/
theorem tx0_checked (bout : BlockOutput) (hroom : bout.blockGasUsed + tx0.gas ≤ 60000000)
    (hrecover : recoverSender benvPre.stat.chainId tx0 = .ok eAddress) :
    checkTransaction benvPre.beginTransaction (transactionPreludeBout bout tx0 0) tx0 =
      .ok (eAddress, 0, [], 0) := by
  have hgas : checkTransactionGasLimits benvPre.beginTransaction
      (transactionPreludeBout bout tx0 0) tx0 = .ok 0 := by
    have h := checkTransactionGasLimits_ok_of_room (benv := benvPre.beginTransaction)
      (bout := transactionPreludeBout bout tx0 0) (tx := tx0) benvPre_stateGas
      (by
        show tx0.gas ≤ 60000000 - bout.blockGasUsed
        omega)
      (Nat.zero_le _)
    exact h
  exact checkTransaction_ok_of_parts hgas tx0_chain hrecover tx0_fee tx0_blob tx0_receiver
    tx0_auth tx0_sender

/-! ### The debit, the prepared message and the call wrapper -/

/-- The zero-fee debit of `E` is the world the message runs in. -/
theorem tx0_debit : (benvPre.state.incrNonce eAddress).subBal eAddress
    (tx0.gas * 0 + transactionBlobGasFee benvPre tx0).toB256 = some worldTx := by
  rw [show (tx0.gas * 0 + transactionBlobGasFee benvPre tx0).toB256 = 0 from rfl]
  exact worldPre_debit

/-- **The prepared message is `msg0tx`**, the message of the closed message-level theorem. -/
theorem tx0_prepared : prepareMessage { benvPre.beginTransaction with state := worldTx }
    (transactionTenv benvPre.beginTransaction tx0 0 eAddress 0 21064 []) tx0 = .ok msg0tx := by
  kernel_rfl

theorem msg0tx_call_shape : msg0tx.benv.stat.rules.stateGas = none ∧
    msg0tx.target.isNone = false ∧ msg0tx.tenv.stat.auths.isEmpty = true ∧
    getDelegatedCodeAddress msg0tx.code = none := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> kernel_rfl

/-! ### The transaction -/

/-- **V- as an admitted transaction.**  Jaune's `processTransaction` accepts `tx0` -- a type-2,
zero-fee, zero-value transaction signed by the EOA `E` (nonce 0, no code) -- over the block
`benvPre`, and in the world it returns the pool `P`'s ledger is corrupted: `totalSupply = 1800 <
1906 = balanceOf[A']`, `A'` being the attacker contract the transaction calls (the reentrant
`add_liquidity` inside `remove_liquidity`).  Every admission check (validation and intrinsic gas,
chain id, fee rules with base fee 0, nonce, balance against fee and value, EIP-3607 sender code,
receiver, authorization list) is discharged above by evaluation; the premises are the signature
(`hrecover`, true by evaluation: the `#guard` in `TxTop`) and that the block has the room
(`hroom`).  The settlement (the sender's gas refund and the coinbase's priority fee, both zero,
and the message's empty set of accounts to delete) leaves `P`'s storage alone. -/
theorem vminus_tx_process (bout : BlockOutput) (hroom : bout.blockGasUsed + tx0.gas ≤ 60000000)
    (hrecover : recoverSender benvPre.stat.chainId tx0 = .ok eAddress) :
    ∃ (st : State) (bout' : BlockOutput), processTransaction benvPre bout tx0 0 = .ok (st, bout') ∧
      (storOf st proxyAddress (26 : Nat).toB256).toNat = 1800 ∧
      (storOf st proxyAddress balanceOfA2Slot.toB256).toNat = 1906 ∧
      (storOf st proxyAddress (26 : Nat).toB256).toNat <
        (storOf st proxyAddress balanceOfA2Slot.toB256).toNat := by
  obtain ⟨-, -, -, -, post, -, hpm, herr, -, -, hrf, hatd, h26, hA, hlt⟩ := vminus_tx_message
  obtain ⟨hsg, htarget, hauths, hdeleg⟩ := msg0tx_call_shape
  have hrefund : Int.toNat? post.refundCounter = some 42600 := by rw [hrf]; rfl
  have hcall := processMessageCall_call_of_message hsg htarget hauths hdeleg hpm herr hrefund
  obtain ⟨bout', hproc⟩ := processTransaction_of_stages (benv := benvPre) (bout := bout)
    (tx := tx0) (index := 0) (intrinsicGas := 21064) (calldataFloorGas := 21160)
    (sender := eAddress) (effectiveGasPrice := 0) (blobVersionedHashes := []) (txBlobGasUsed := 0)
    (debit := worldTx) (msg := msg0tx) benvPre_stateGas benvPre_bal tx0_validated
    (tx0_checked bout hroom hrecover) tx0_debit tx0_prepared hcall (by rfl)
  refine ⟨_, bout', hproc, ?_⟩
  have hlist : Std.HashSet.toList post.accountsToDelete = [] := by rw [hatd]; simp
  have hst : ∀ (v₁ v₂ : B256) (a : Adr) (k : B256),
      storOf ((post.state.addBal eAddress v₁).addBal benvPre.stat.coinbase v₂) a k =
        storOf post.state a k := by
    intro v₁ v₂ a k
    simp only [State.addBal, storOf_setBal]
  simp only [hlist, List.foldl_nil, hst]
  exact ⟨h26, hA, hlt⟩

end Blanc.Lift.VyperNonreentrantDeployed.Vulnerable.Tx
