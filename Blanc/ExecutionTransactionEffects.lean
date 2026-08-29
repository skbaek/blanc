-- ExecutionTransactionEffects.lean : contract-invariant transaction facts.

import Blanc.ExecutionMessageEffects
import Blanc.ExecutionTransactionStateTrace

/-!
Contract-neutral transaction-envelope facts.

A retained `TransactionTrace` moves the world in five places: the nonce bump
and up-front gas debit, the prepared message, the sender gas refund, the
coinbase priority-fee credit, and the final account-deletion fold.  This
module says what each of those does to an installed contract address `ca`
carrying an *arbitrary* `ContractSpec` invariant, so no contract has to
re-derive its own copy.  `Blanc/ExecutionMessageEffects.lean` is the message
level of the same seam; this is the transaction level.
-/

namespace Blanc

open Jaune

namespace ExecutionTrace

variable {c : ContractSpec}

/-! ## The up-front debit -/

/-- A checked transaction's sender is never an installed contract: successful
`checkTransaction` accepted the sender as an EOA or delegation account, and an
installed contract's code is a non-empty, non-delegation compilation. -/
theorem TransactionTrace.sender_ne
    {ca : Adr} {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (inv : c.StateInv ca benv.state)
    (notCreated : ca ∉ benv.createdAccounts) :
    trace.sender ≠ ca := by
  have beginInv : c.BenvInv ca benv.beginTransaction := by
    refine ⟨?_, ?_⟩
    · simpa [Benv.beginTransaction] using inv
    · simpa [Benv.beginTransaction] using notCreated
  exact ContractSpec.checkTransaction_sender_ne_of_inv trace.checked beginInv

/-- The nonce bump and up-front gas debit leave a non-sender account's
balance alone. -/
theorem TransactionTrace.debitState_bal_eq
    {ca : Adr} {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (senderNe : trace.sender ≠ ca) :
    trace.debitState.bal ca = benv.state.bal ca := by
  rcases State.of_subBal trace.debit with ⟨_, debitEq⟩
  rw [debitEq]
  show (((benv.state.incrNonce trace.sender).setBal trace.sender _).get ca).bal = _
  rw [State.setBal_get_ne senderNe]
  rw [State.incrNonce_get_bal]
  rfl

/-- The nonce bump and up-front gas debit leave every account's persistent
storage alone. -/
theorem TransactionTrace.debitState_getStor_eq
    {ca : Adr} {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout') :
    trace.debitState.getStor ca = benv.state.getStor ca := by
  rcases State.of_subBal trace.debit with ⟨_, debitEq⟩
  rw [debitEq]
  show (((benv.state.incrNonce trace.sender).setBal trace.sender _).get ca).stor = _
  rw [State.setBal_get_stor]
  exact State.incrNonce_get_stor

/-! ## The prepared message -/

/-- The transaction's prepared message carries the contract invariant. -/
theorem TransactionTrace.msgInv
    {ca : Adr} {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (inv : c.StateInv ca benv.state)
    (notCreated : ca ∉ benv.createdAccounts) :
    c.MsgInv ca trace.msg := by
  have senderNe := trace.sender_ne inv notCreated
  have debitInv : c.StateInv ca trace.debitState :=
    ContractSpec.StateInv.subBal senderNe trace.debit
      (ContractSpec.StateInv.incrNonce inv)
  have origin :
      (transactionTenv benv.beginTransaction tx index trace.sender
        trace.effectiveGasPrice trace.intrinsicGas
        trace.blobVersionedHashes).stat.origin ≠ ca := by
    simpa [transactionTenv] using senderNe
  exact ContractSpec.prepareMessage_preserves_inv trace.prepared debitInv
    (by simpa [Benv.beginTransaction] using notCreated) origin

/-- A transaction message always transfers its value. -/
theorem TransactionTrace.msg_shouldTransferValue
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout') :
    trace.msg.shouldTransferValue = true := by
  have prepared := trace.prepared
  unfold prepareMessage at prepared
  cases receiver : tx.type.receiver? with
  | none =>
      simp only [receiver] at prepared
      rw [← Except.ok.inj prepared]
  | some target =>
      simp only [receiver] at prepared
      rw [← Except.ok.inj prepared]

/-! ## Final settlement -/

/-- A transaction never destroys an installed contract account. -/
theorem TransactionTrace.accountsToDelete_ne
    {ca : Adr} {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (preserves : c.Preserves ca)
    (inv : c.StateInv ca benv.state)
    (notCreated : ca ∉ benv.createdAccounts) :
    ∀ address ∈ trace.messageOut.accountsToDelete.toList, address ≠ ca :=
  (ContractSpec.processMessageCall_preserves_inv preserves
    trace.message.result (trace.msgInv inv notCreated)).2

/-- An account the deletion fold never names survives the fold untouched. -/
theorem foldl_destroyAccount_get_eq
    {ca : Adr} {state : State} {addresses : List Adr}
    (hne : ∀ address ∈ addresses, address ≠ ca) :
    (addresses.foldl destroyAccount state).get ca = state.get ca := by
  induction addresses generalizing state with
  | nil => rfl
  | cons address addresses ih =>
      rw [List.foldl_cons, ih]
      · exact State.get_erase_ne (Ne.symm (hne address (by simp)))
      · intro tail htail
        exact hne tail (by simp [htail])

/-- The two settlement credits are funded by the transaction's own up-front
debit, so neither can wrap the global balance sum.  Proving this from the
checked debit rather than assuming it is what lets a coinbase equal to the
contract be handled without a side condition. -/
theorem TransactionTrace.settlement_sum_bounds
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (refundCounter : Nat)
    (baseSum : sum benv.state.bal < 2 ^ 256) :
    sum trace.messageState.bal +
        (trace.refundValue refundCounter).toNat < 2 ^ 256 ∧
      sum (trace.refundedState refundCounter).bal +
        (trace.coinbaseValue refundCounter).toNat < 2 ^ 256 := by
  have feeLt := checkTransaction_upfront_lt_modulus trace.checked
  simp only [Benv.beginTransaction] at feeLt
  have floor := validateTransaction_calldataFloorGasCost_le_gas trace.validation
  have usedLe : trace.chargedGas refundCounter ≤ tx.gas := by
    unfold TransactionTrace.chargedGas
    exact max_le (by omega) floor
  have creditsLe :
      (tx.gas - trace.chargedGas refundCounter) * trace.effectiveGasPrice +
          trace.chargedGas refundCounter *
            (trace.effectiveGasPrice - benv.stat.baseFeePerGas) ≤
        tx.gas * trace.effectiveGasPrice := by
    apply le_trans (Nat.add_le_add_left
      (Nat.mul_le_mul_left _
        (Nat.sub_le trace.effectiveGasPrice benv.stat.baseFeePerGas)) _)
    rw [← Nat.add_mul, Nat.sub_add_cancel usedLe]
  have refundLe : (trace.refundValue refundCounter).toNat ≤
      (tx.gas - trace.chargedGas refundCounter) * trace.effectiveGasPrice := by
    unfold TransactionTrace.refundValue
    exact toB256_toNat_le _
  have tipLe : (trace.coinbaseValue refundCounter).toNat ≤
      trace.chargedGas refundCounter *
        (trace.effectiveGasPrice - benv.stat.baseFeePerGas) := by
    unfold TransactionTrace.coinbaseValue
    exact toB256_toNat_le _
  have debitSum := State.balSum_subBal trace.debit
  dsimp only [State.balSum, transactionBlobGasFee] at debitSum
  rw [State.incrNonce_bal] at debitSum
  rw [B256.toNat_toB256_of_lt feeLt] at debitSum
  have messageSum := processMessageCall_sum_le trace.message.result
  rw [prepareMessage_benv trace.prepared] at messageSum
  change sum trace.messageState.bal ≤ sum trace.debitState.bal at messageSum
  have refundBound :
      sum trace.messageState.bal +
        (trace.refundValue refundCounter).toNat < 2 ^ 256 := by
    omega
  refine ⟨refundBound, ?_⟩
  have refundedSum :
      sum (trace.refundedState refundCounter).bal =
        sum trace.messageState.bal + (trace.refundValue refundCounter).toNat := by
    unfold TransactionTrace.refundedState
    exact sum_addBal_eq _ _ _ refundBound
  rw [refundedSum]
  omega

end ExecutionTrace

end Blanc
