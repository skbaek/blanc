import Blanc.TransactionForward
import Blanc.ExecutionTransactionStateTrace

namespace Blanc.ExecutionTrace

open Jaune

private theorem validation_cost_none {rules : ForkRules} {tx : Tx} {sender : Adr}
    {intrinsic floor : Nat} (stateGas : rules.stateGas = none)
    (validation : validateTransaction rules tx sender = .ok (intrinsic, floor)) :
    calculateIntrinsicCost rules tx sender = (intrinsic, floor) ∧
      max intrinsic floor ≤ tx.gas := by
  unfold validateTransaction at validation
  rw [stateGas] at validation
  rcases cost : calculateIntrinsicCost rules tx sender with ⟨ig, fc⟩
  rw [cost] at validation
  dsimp only at validation
  by_cases bad : max ig fc > tx.gas
  · rw [ite_eq_left bad] at validation
    cases validation
  · rw [ite_eq_right bad] at validation
    have finish : (Except.ok (ig, fc) : Except TxValidationError (Nat × Nat)) =
        .ok (intrinsic, floor) →
        (ig, fc) = (intrinsic, floor) ∧
          max intrinsic floor ≤ tx.gas := by
      intro result
      rcases Prod.mk.inj (Except.ok.inj result) with ⟨rfl, rfl⟩
      exact ⟨rfl, Nat.le_of_not_lt bad⟩
    cases cap : rules.tx.maxGas with
    | none =>
      rw [cap] at validation
      by_cases nonce : tx.nonce = UInt64.max
      · rw [ite_eq_left nonce] at validation
        cases validation
      · rw [ite_eq_right nonce] at validation
        obtain ⟨_, _, result⟩ := Except.bind_eq_ok validation
        exact finish result
    | some cap =>
      rw [cap] at validation
      obtain ⟨_, _, validation⟩ := Except.bind_eq_ok validation
      obtain ⟨_, _, validation⟩ := Except.bind_eq_ok validation
      by_cases nonce : tx.nonce = UInt64.max
      · rw [ite_eq_left nonce] at validation
        cases validation
      · rw [ite_eq_right nonce] at validation
        exact finish validation

/-- Before initcode metering, a legacy creation's intrinsic charge is bounded
by charging every input byte at the larger of the zero and nonzero rates. -/
theorem calculateIntrinsicCost_legacy_create_le {rules : ForkRules} {tx : Tx}
    {sender : Adr} {gasPrice : Nat} (stateGas : rules.stateGas = none)
    (initcode : rules.creation.initCodeLimit = false)
    (txType : tx.type = .zero gasPrice none) :
    (calculateIntrinsicCost rules tx sender).1 ≤
      rules.gas.txBase + rules.gas.createAccess +
        max standardCallDataTokenCost rules.txr.dataNonZero * tx.data.length := by
  have bound (bytes : Bytes) (acc : Nat) :
      bytes.foldl (fun n x => n +
        (if x = 0 then standardCallDataTokenCost else rules.txr.dataNonZero)) acc ≤
      acc + max standardCallDataTokenCost rules.txr.dataNonZero * bytes.length := by
    induction bytes generalizing acc with
    | nil => simp only [List.foldl_nil, List.length_nil, Nat.mul_zero, Nat.add_zero, le_refl]
    | cons x xs ih =>
      rw [List.foldl_cons, List.length_cons, Nat.mul_succ]
      have next := ih (acc + (if x = 0 then standardCallDataTokenCost else rules.txr.dataNonZero))
      have zeroLe := Nat.le_max_left standardCallDataTokenCost rules.txr.dataNonZero
      have nonzeroLe := Nat.le_max_right standardCallDataTokenCost rules.txr.dataNonZero
      split_ifs at next ⊢ <;> omega
  simpa only [calculateIntrinsicCost, txType, TxType.receiver?, stateGas, initcode,
    Bool.false_eq_true, ↓reduceIte, List.map_nil, List.sum_nil, Nat.add_zero, Nat.zero_add]
    using Nat.add_le_add_left (bound tx.data 0) (rules.gas.txBase + rules.gas.createAccess)

/-- The same byte-count bound applies to the intrinsic charge retained by an
actual admitted legacy creation transaction. -/
theorem TransactionTrace.intrinsicGas_legacy_create_le
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput} {gasPrice : Nat}
    (trace : TransactionTrace benv bout tx index state bout')
    (stateGas : benv.stat.rules.stateGas = none)
    (initcode : benv.stat.rules.creation.initCodeLimit = false)
    (txType : tx.type = .zero gasPrice none) :
    trace.intrinsicGas ≤ benv.stat.rules.gas.txBase + benv.stat.rules.gas.createAccess +
      max standardCallDataTokenCost benv.stat.rules.txr.dataNonZero * tx.data.length := by
  have cost := (validation_cost_none stateGas trace.validation).1
  have bound := calculateIntrinsicCost_legacy_create_le
    (sender := trace.validationSender) stateGas initcode txType
  rw [cost] at bound
  exact bound

/-- Preparation allocates exactly the transaction gas left after intrinsic cost. -/
theorem TransactionTrace.msg_gas_noStateGas
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout') :
    trace.msg.gas = tx.gas - trace.intrinsicGas := by
  have prepared := trace.prepared
  unfold prepareMessage at prepared
  cases receiver : tx.type.receiver?
  all_goals
    simp only [receiver] at prepared
    exact (congrArg Msg.gas (Except.ok.inj prepared)).symm

theorem TransactionTrace.msg_gas
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (_fork : CoveredFork benv.stat.fork) :
    trace.msg.gas = tx.gas - trace.intrinsicGas :=
  trace.msg_gas_noStateGas

/-- Covered-fork validation retains the intrinsic base charge and reservation bounds. -/
theorem TransactionTrace.intrinsicGas_bounds_noStateGas
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (fork : benv.stat.rules.stateGas = none)
    (hbase : benv.stat.rules.gas.txBase = 21000) :
    21000 ≤ trace.intrinsicGas ∧ trace.intrinsicGas ≤ tx.gas ∧
      trace.calldataFloorGasCost ≤ tx.gas := by
  obtain ⟨cost, bound⟩ := validation_cost_none fork trace.validation
  have base : benv.stat.rules.gas.txBase ≤
      (calculateIntrinsicCost benv.stat.rules tx trace.validationSender).1 := by
    simp only [calculateIntrinsicCost]
    omega
  rw [cost] at base
  rw [hbase] at base
  exact ⟨base, Nat.le_trans (Nat.le_max_left _ _) bound,
    Nat.le_trans (Nat.le_max_right _ _) bound⟩

theorem TransactionTrace.intrinsicGas_bounds
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (fork : CoveredFork benv.stat.fork) :
    21000 ≤ trace.intrinsicGas ∧ trace.intrinsicGas ≤ tx.gas ∧
      trace.calldataFloorGasCost ≤ tx.gas :=
  trace.intrinsicGas_bounds_noStateGas fork.rules_stateGas_none fork.rules_txBase

/-- The intrinsic charge pays for the extra root in a retained frame-count budget. -/
theorem TransactionTrace.msg_gas_succ_le_noStateGas
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (fork : benv.stat.rules.stateGas = none)
    (hbase : benv.stat.rules.gas.txBase = 21000) :
    trace.msg.gas + 1 ≤ tx.gas := by
  rw [trace.msg_gas_noStateGas]
  have bounds := trace.intrinsicGas_bounds_noStateGas fork hbase
  omega

theorem TransactionTrace.msg_gas_succ_le
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (fork : CoveredFork benv.stat.fork) : trace.msg.gas + 1 ≤ tx.gas :=
  trace.msg_gas_succ_le_noStateGas fork.rules_stateGas_none fork.rules_txBase

/-- Actual transaction counters use the very message outcome and refund retained by the trace. -/
theorem TransactionTrace.exists_gasSettlement
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (fork : CoveredFork benv.stat.fork) :
    ∃ refund : Nat, Int.toNat? trace.messageOut.refundCounter = some refund ∧
      bout'.blockGasUsed = bout.blockGasUsed + trace.chargedGas refund ∧
      bout'.cumulativeGasUsed = bout.cumulativeGasUsed + trace.chargedGas refund := by
  have stateGas := fork.rules_stateGas_none
  have validation : validateTransaction benv.stat.rules tx 0 =
      .ok (trace.intrinsicGas, trace.calldataFloorGasCost) := by
    rw [validateTransaction_sender_congr_none stateGas]
    exact trace.validation
  obtain ⟨refund, refundEq, _⟩ := trace.exists_finalStateForm fork
  obtain ⟨settled, result, cumulative, block⟩ :=
    processTransaction_of_stages_gasUsed stateGas fork.rules_bal_none
      fork.rules_touchedSweep fork.rules_refundQuotient validation trace.checked
      trace.debit trace.prepared trace.message.result refundEq
  have output := (Prod.mk.inj (Except.ok.inj (trace.result.symm.trans result))).2
  subst settled
  exact ⟨refund, refundEq, block, cumulative⟩

/-- At most one fifth of gross spending is refunded, so actual block gas pays at least four fifths. -/
theorem TransactionTrace.grossGas_refund_bound
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (fork : CoveredFork benv.stat.fork) :
    4 * (tx.gas - trace.messageOut.gasLeft) ≤
      5 * (bout'.blockGasUsed - bout.blockGasUsed) := by
  obtain ⟨refund, _, block, _⟩ := trace.exists_gasSettlement fork
  rw [block, Nat.add_sub_cancel_left]
  unfold TransactionTrace.chargedGas
  have capped := Nat.min_le_left ((tx.gas - trace.messageOut.gasLeft) / 5) refund
  have charged := Nat.le_max_left
    (tx.gas - trace.messageOut.gasLeft -
      min ((tx.gas - trace.messageOut.gasLeft) / 5) refund) trace.calldataFloorGasCost
  omega

/-- Actual charged gas cannot exceed the validated transaction gas reservation. -/
theorem TransactionTrace.chargedGas_le
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (fork : CoveredFork benv.stat.fork) (refund : Nat) :
    trace.chargedGas refund ≤ tx.gas := by
  have valid := (validation_cost_none fork.rules_stateGas_none trace.validation).2
  unfold TransactionTrace.chargedGas
  omega

/-- Checked reservation fits the remaining allowance, retaining the incoming counter. -/
theorem TransactionTrace.gas_le_remaining_noStateGas
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (fork : benv.stat.rules.stateGas = none) :
    tx.gas ≤ benv.stat.blockGasLimit - bout.blockGasUsed := by
  have checked := trace.checked
  simp only [checkTransaction] at checked
  obtain ⟨_, limits, _⟩ := Except.bind_eq_ok checked
  rw [Except.mapError_eq_ok_iff] at limits
  simp only [checkTransactionGasLimits] at limits
  have stateGas : benv.beginTransaction.stat.rules.stateGas = none :=
    fork
  rw [stateGas] at limits
  change (if tx.gas > benv.stat.blockGasLimit - bout.blockGasUsed then _ else _) =
    Except.ok _ at limits
  by_cases exceeds : tx.gas > benv.stat.blockGasLimit - bout.blockGasUsed
  · rw [ite_eq_left exceeds] at limits
    cases limits
  · exact Nat.le_of_not_lt exceeds

theorem TransactionTrace.gas_le_remaining
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (fork : CoveredFork benv.stat.fork) :
    tx.gas ≤ benv.stat.blockGasLimit - bout.blockGasUsed :=
  trace.gas_le_remaining_noStateGas fork.rules_stateGas_none

/-- Successful settlement never decreases actual block gas consumption. -/
theorem TransactionTrace.blockGasUsed_mono
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (fork : CoveredFork benv.stat.fork) : bout.blockGasUsed ≤ bout'.blockGasUsed := by
  obtain ⟨refund, _, block, _⟩ := trace.exists_gasSettlement fork
  rw [block]
  exact Nat.le_add_right _ _

/-- A successful transaction preserves a previously satisfied block gas cap. -/
theorem TransactionTrace.blockGasUsed_le_limit
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (fork : CoveredFork benv.stat.fork)
    (prior : bout.blockGasUsed ≤ benv.stat.blockGasLimit) :
    bout'.blockGasUsed ≤ benv.stat.blockGasLimit := by
  obtain ⟨refund, _, block, _⟩ := trace.exists_gasSettlement fork
  have reserved := trace.gas_le_remaining fork
  have charged := trace.chargedGas_le fork refund
  rw [block]
  omega

/-- Actual transaction replay increases consumption while preserving the block cap. -/
theorem ApplyTransactionsTrace.blockGasUsed_bounds
    {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (fork : CoveredFork benv.stat.fork)
    (prior : bout.blockGasUsed ≤ benv.stat.blockGasLimit) :
    bout.blockGasUsed ≤ finalBout.blockGasUsed ∧
      finalBout.blockGasUsed ≤ benv.stat.blockGasLimit := by
  induction trace with
  | nil => exact ⟨Nat.le_refl _, prior⟩
  | cons head tail ih =>
    have next := head.blockGasUsed_le_limit fork prior
    have bounds := ih fork next
    exact ⟨Nat.le_trans (head.blockGasUsed_mono fork) bounds.1, bounds.2⟩

end Blanc.ExecutionTrace
