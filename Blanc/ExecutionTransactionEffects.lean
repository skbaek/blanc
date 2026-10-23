-- ExecutionTransactionEffects.lean : contract-invariant transaction facts.

import Blanc.ExecutionMessageEffects
import Blanc.ExecutionSelectedTransactionStateTrace
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
    · simpa only [Benv.beginTransaction] using inv
    · simpa only [Benv.beginTransaction] using notCreated
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

/-- Successful transaction validation excludes the maximal nonce on every fork. -/
theorem validateTransaction_nonce_ne_max {rules : ForkRules} {tx : Tx}
    {sender : Adr} {intrinsic floor : Nat}
    (validation : validateTransaction rules tx sender = .ok (intrinsic, floor)) :
    tx.nonce ≠ UInt64.max := by
  intro hmax
  unfold validateTransaction at validation
  cases stateGas : rules.stateGas with
  | some pricing =>
      simp only [stateGas, hmax, ite_true, bind, Except.bind] at validation
      cases validation
  | none =>
      rw [stateGas] at validation
      rcases cost : calculateIntrinsicCost rules tx sender with ⟨ig, fc⟩
      rw [cost] at validation
      dsimp only at validation
      split at validation
      · cases validation
      · cases cap : rules.tx.maxGas with
        | none =>
            simp only [cap, bind, Except.bind] at validation
            cases validation
        | some gasCap =>
            rw [cap] at validation
            obtain ⟨_, _, validation⟩ := Except.bind_eq_ok validation
            obtain ⟨_, _, validation⟩ := Except.bind_eq_ok validation
            simp only [bind, Except.bind] at validation
            cases validation

/-- Successful transaction admission checks the sender's exact nonce. -/
theorem checkTransaction_sender_nonce {benv : Benv} {bout : BlockOutput} {tx : Tx}
    {sender : Adr} {price : Nat} {hashes : List B256} {blobGas : Nat}
    (checked : checkTransaction benv bout tx = .ok (sender, price, hashes, blobGas)) :
    (benv.state.get sender).nonce = tx.nonce := by
  unfold checkTransaction at checked
  rcases Except.bind_eq_ok checked with ⟨_, _, checked⟩
  rcases Except.bind_eq_ok checked with ⟨_, _, checked⟩
  rcases Except.bind_eq_ok checked with ⟨recovered, _, checked⟩
  rcases Except.bind_eq_ok checked with ⟨_, _, checked⟩
  rcases Except.bind_eq_ok checked with ⟨_, _, checked⟩
  rcases Except.bind_eq_ok checked with ⟨_, _, checked⟩
  rcases Except.bind_eq_ok checked with ⟨_, _, checked⟩
  rcases Except.bind_eq_ok checked with ⟨_, account, checked⟩
  have senderEq : recovered = sender := congrArg Prod.fst (Except.ok.inj checked)
  rw [senderEq, Except.mapError_eq_ok_iff] at account
  unfold checkTransactionSenderAccountFor at account
  rcases Except.bind_eq_ok account with ⟨_, account, _⟩
  unfold checkTransactionSenderAccount at account
  split at account
  · cases account
  · split at account
    · cases account
    · rename_i notGreater notLess
      exact le_antisymm (le_of_not_gt notGreater) (le_of_not_gt notLess)

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
  have nonceEq := checkTransaction_sender_nonce trace.checked
  have nonceBound : (benv.state.get trace.sender).nonce ≠ UInt64.max := by
    simpa only [Benv.beginTransaction] using
      (nonceEq.trans_ne (validateTransaction_nonce_ne_max trace.validation))
  have nonzero := UInt64.add_one_ne_zero_of_ne_max nonceBound
  have bumpedNonce : ((benv.state.incrNonce trace.sender).get trace.sender).nonce ≠ 0 := by
    simpa only [State.incrNonce, State.setAccount_get_self, Acct.clearIfEmpty_nonce] using nonzero
  rw [State.setBal_get_stor, ite_eq_right (by
    intro empty
    exact bumpedNonce empty.2.2.1)]
  rw [State.incrNonce_get_stor, ite_eq_right (by
    intro empty
    exact nonzero empty.2.2.1)]
  rfl

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
    simpa only [transactionTenv, Std.TreeMap.empty_eq_emptyc, ne_eq] using senderNe
  exact ContractSpec.prepareMessage_preserves_inv trace.prepared debitInv
    (by simpa only [Benv.beginTransaction] using notCreated) origin

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

/-- An arbitrary contract invariant survives one whole retained transaction.
The balance-sum bound is an explicit premise rather than a projection of the
invariant: a general `ContractSpec.Side` need not be `SumNof`. -/
theorem TransactionTrace.benvInv
    {ca : Adr} {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (preserves : c.Preserves ca)
    (sumNof : sum benv.state.bal < 2 ^ 256)
    (inv : c.BenvInv ca benv)
    (hfork : CoveredFork benv.stat.fork) :
    c.BenvInv ca (benv.withState state) :=
  ContractSpec.processTransaction_preserves_inv ca preserves benv bout bout' tx
    index state trace.result sumNof inv hfork

/-! ## Final settlement -/

/-- A transaction's prepared message inherits no pending deletions: no account
is in its `inheritedDeletions`. -/
theorem TransactionTrace.not_mem_msg_inheritedDeletions
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout') (a : Adr) :
    a ∉ trace.msg.inheritedDeletions := by
  have prepared := trace.prepared
  unfold prepareMessage at prepared
  have fields := congrArg Msg.inheritedDeletions (Except.ok.inj prepared)
  rw [← fields]
  exact AdrSet.not_mem_empty

/-- A transaction never destroys an installed contract account. -/
theorem TransactionTrace.accountsToDelete_ne
    {ca : Adr} {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (preserves : c.Preserves ca)
    (inv : c.StateInv ca benv.state)
    (notCreated : ca ∉ benv.createdAccounts)
    (hfork : CoveredFork benv.stat.fork) :
    ∀ address ∈ trace.messageOut.accountsToDelete.toList, address ≠ ca := by
  have inherited : ca ∉ trace.msg.inheritedDeletions :=
    trace.not_mem_msg_inheritedDeletions ca
  exact (ContractSpec.processMessageCall_preserves_inv (by
    rw [prepareMessage_benv trace.prepared]
    simpa only [Benv.beginTransaction] using hfork) preserves
    trace.message.result (trace.msgInv inv notCreated) inherited).2

/-- An account the deletion fold never names survives the fold untouched. -/
theorem foldl_destroyAccount_get_eq
    {ca : Adr} {state : State} {addresses : List Adr}
    (hne : ∀ address ∈ addresses, address ≠ ca) :
    (addresses.foldl destroyAccount state).get ca = state.get ca := by
  induction addresses generalizing state with
  | nil => rfl
  | cons address addresses ih =>
      rw [List.foldl_cons, ih]
      · exact State.get_erase_ne (Ne.symm (hne address (by simp only [List.mem_cons, true_or])))
      · intro tail htail
        exact hne tail (by simp only [List.mem_cons, htail, or_true])

/-- Selected gas used cannot exceed the transaction reservation: under
`stateGas = none` the settled charge is `max _ floor` with the validated
floor below `tx.gas`. -/
theorem TransactionTrace.selectedGasUsed_le_gas
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (hsg : benv.stat.rules.stateGas = none)
    (refundCounter : Nat) :
    (trace.selectedGasSettlement refundCounter).gasUsed ≤ tx.gas := by
  have floor := validateTransaction_calldataFloorGasCost_le_gas trace.validation
  unfold TransactionTrace.selectedGasSettlement settleTransactionGas
  rw [hsg]
  dsimp only
  exact max_le ((Nat.sub_le _ _).trans (Nat.sub_le _ _)) floor

/-- Under `stateGas = none` the selected settlement leaves `tx.gas - gasUsed`. -/
theorem TransactionTrace.selectedGasSettlement_gasLeft_eq
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (hsg : benv.stat.rules.stateGas = none)
    (refundCounter : Nat) :
    (trace.selectedGasSettlement refundCounter).gasLeft =
      tx.gas - (trace.selectedGasSettlement refundCounter).gasUsed := by
  unfold TransactionTrace.selectedGasSettlement settleTransactionGas
  rw [hsg]

/-- Selected refund in `gasUsed` form, matching the shared core's shape. -/
theorem TransactionTrace.selectedRefundValue_eq
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (hsg : benv.stat.rules.stateGas = none)
    (refundCounter : Nat) :
    trace.selectedRefundValue refundCounter =
      ((tx.gas - (trace.selectedGasSettlement refundCounter).gasUsed) *
        trace.effectiveGasPrice).toB256 := by
  unfold TransactionTrace.selectedRefundValue
  rw [trace.selectedGasSettlement_gasLeft_eq hsg]

/-- Shared credit arithmetic: with `used ≤ tx.gas`, the refund
`((tx.gas - used) * price).toB256` and the tip
`(used * (price - base)).toB256` are both funded by the checked up-front
debit, under only a `stateGas = none` fact for the message's rules. -/
private theorem TransactionTrace.settlement_sum_bounds_core
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (used : Nat)
    (hused : used ≤ tx.gas)
    (hmsg : trace.msg.benv.stat.rules.stateGas = none)
    (baseSum : sum benv.state.bal < 2 ^ 256) :
    sum trace.messageState.bal +
        (((tx.gas - used) * trace.effectiveGasPrice).toB256).toNat < 2 ^ 256 ∧
      sum (trace.messageState.addBal trace.sender
          (((tx.gas - used) * trace.effectiveGasPrice).toB256)).bal +
        ((used *
          (trace.effectiveGasPrice - benv.stat.baseFeePerGas)).toB256).toNat <
        2 ^ 256 := by
  have feeLt : tx.gas * trace.effectiveGasPrice +
      (if tx.isTypeThree = true then
        calculateDataFee benv.stat.rules.blob benv.stat.excessBlobGas tx
      else 0) < 2 ^ 256 := by
    simpa only [BenvStat.rules, Nat.reducePow, Benv.beginTransaction] using
      checkTransaction_upfront_lt_modulus trace.checked
  have creditsLe :
      (tx.gas - used) * trace.effectiveGasPrice +
          used * (trace.effectiveGasPrice - benv.stat.baseFeePerGas) ≤
        tx.gas * trace.effectiveGasPrice := by
    apply le_trans (Nat.add_le_add_left
      (Nat.mul_le_mul_left _
        (Nat.sub_le trace.effectiveGasPrice benv.stat.baseFeePerGas)) _)
    rw [← Nat.add_mul, Nat.sub_add_cancel hused]
  have refundLe : (((tx.gas - used) * trace.effectiveGasPrice).toB256).toNat ≤
      (tx.gas - used) * trace.effectiveGasPrice :=
    toB256_toNat_le _
  have tipLe : ((used *
      (trace.effectiveGasPrice - benv.stat.baseFeePerGas)).toB256).toNat ≤
      used * (trace.effectiveGasPrice - benv.stat.baseFeePerGas) :=
    toB256_toNat_le _
  have debitSum := State.balSum_subBal trace.debit
  dsimp only [State.balSum, transactionBlobGasFee] at debitSum
  rw [State.incrNonce_bal] at debitSum
  rw [B256.toNat_toB256_of_lt feeLt] at debitSum
  have messageSum := processMessageCall_sum_le hmsg trace.message.result
  rw [prepareMessage_benv trace.prepared] at messageSum
  change sum trace.messageState.bal ≤ sum trace.debitState.bal at messageSum
  have refundBound :
      sum trace.messageState.bal +
        (((tx.gas - used) * trace.effectiveGasPrice).toB256).toNat < 2 ^ 256 := by
    omega
  refine ⟨refundBound, ?_⟩
  have refundedSum :
      sum (trace.messageState.addBal trace.sender
          (((tx.gas - used) * trace.effectiveGasPrice).toB256)).bal =
        sum trace.messageState.bal +
          (((tx.gas - used) * trace.effectiveGasPrice).toB256).toNat :=
    sum_addBal_eq _ _ _ refundBound
  rw [refundedSum]
  omega

/-- The two selected settlement credits are funded by the transaction's own
up-front debit under only `stateGas = none`. -/
theorem TransactionTrace.selected_settlement_sum_bounds
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (refundCounter : Nat)
    (baseSum : sum benv.state.bal < 2 ^ 256)
    (hsg : benv.stat.rules.stateGas = none) :
    sum trace.messageState.bal +
        (trace.selectedRefundValue refundCounter).toNat < 2 ^ 256 ∧
      sum (trace.selectedRefundedState refundCounter).bal +
        (trace.selectedCoinbaseValue refundCounter).toNat < 2 ^ 256 := by
  have hused := trace.selectedGasUsed_le_gas hsg refundCounter
  have hmsg : trace.msg.benv.stat.rules.stateGas = none := by
    rw [prepareMessage_benv trace.prepared]
    simpa only [BenvStat.rules, Benv.beginTransaction] using hsg
  have core := trace.settlement_sum_bounds_core
    (trace.selectedGasSettlement refundCounter).gasUsed hused hmsg baseSum
  have hrefund := trace.selectedRefundValue_eq hsg refundCounter
  simpa only [TransactionTrace.selectedRefundedState,
    TransactionTrace.selectedCoinbaseValue, hrefund] using core

/-- The two settlement credits are funded by the transaction's own up-front
debit, so neither can wrap the global balance sum.  Proving this from the
checked debit rather than assuming it is what lets a coinbase equal to the
contract be handled without a side condition. -/
theorem TransactionTrace.settlement_sum_bounds
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (refundCounter : Nat)
    (baseSum : sum benv.state.bal < 2 ^ 256)
    (hfork : CoveredFork benv.stat.fork) :
    sum trace.messageState.bal +
        (trace.refundValue refundCounter).toNat < 2 ^ 256 ∧
      sum (trace.refundedState refundCounter).bal +
        (trace.coinbaseValue refundCounter).toNat < 2 ^ 256 := by
  have floor := validateTransaction_calldataFloorGasCost_le_gas trace.validation
  have usedLe : trace.chargedGas refundCounter ≤ tx.gas := by
    unfold TransactionTrace.chargedGas
    exact max_le (by omega) floor
  have hmsg : trace.msg.benv.stat.rules.stateGas = none := by
    rw [prepareMessage_benv trace.prepared]
    simpa only [BenvStat.rules, Benv.beginTransaction] using hfork.rules_stateGas_none
  have core := trace.settlement_sum_bounds_core
    (trace.chargedGas refundCounter) usedLe hmsg baseSum
  simpa only [TransactionTrace.refundValue, TransactionTrace.refundedState,
    TransactionTrace.coinbaseValue] using core

end ExecutionTrace

end Blanc
