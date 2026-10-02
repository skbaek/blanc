import Blanc.ExecutionMessageGas
import Blanc.ExecutionTransactionGas
import Blanc.ExecutionTraceCalldata

namespace Blanc.ExecutionTrace

open Jaune

/-- The actual settled transaction count is paid by gross gas after the
intrinsic charge absorbs the root allowance, and by the actual refund cap. -/
theorem TransactionTrace.settledFrames_refund_bound
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (fork : CoveredFork benv.stat.fork) :
    4 * trace.settledFrames.length ≤ 5 * (bout'.blockGasUsed - bout.blockGasUsed) := by
  have messageFork : CoveredFork trace.msg.benv.stat.fork := by
    rw [prepareMessage_benv trace.prepared]
    exact fork
  have message := trace.message.settledFrames_length_gas_le messageFork
  have allocation := trace.msg_gas_succ_le fork
  have refund := trace.grossGas_refund_bound fork
  change trace.message.settledFrames.length + trace.messageOut.gasLeft ≤ _ at message
  change 4 * trace.message.settledFrames.length ≤ _
  omega

/-- Retained multiplicity telescopes over the actual transaction settlement
increments. Reservations are never summed as if they were spending. -/
theorem ApplyTransactionsTrace.settledFrames_gas_budget
    {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (fork : CoveredFork benv.stat.fork) :
    bout.blockGasUsed ≤ finalBout.blockGasUsed ∧
      4 * trace.settledFrames.length ≤ 5 * (finalBout.blockGasUsed - bout.blockGasUsed) := by
  induction trace with
  | nil =>
    simp only [ApplyTransactionsTrace.settledFrames, List.length_nil,
      Nat.mul_zero, Nat.sub_self, Nat.le_refl, and_self]
  | cons head tail ih =>
    have spent := head.settledFrames_refund_bound fork
    have monotone := head.blockGasUsed_mono fork
    have remaining := ih fork
    simp only [ApplyTransactionsTrace.settledFrames, List.length_append]
    omega

private theorem SystemMessageTrace.settledFrames_length_le
    {benv : Benv} {target : Adr} {data : Bytes} {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out)
    (fork : CoveredFork benv.stat.fork) :
    trace.settledFrames.length ≤ systemTransactionGas + 1 := by
  have messageFork : CoveredFork
      (systemTransactionMessage benv target data).benv.stat.fork := fork
  have budget := trace.message.settledFrames_length_gas_le messageFork
  change trace.settledFrames.length + out.gasLeft ≤ systemTransactionGas + 1 at budget
  omega

private theorem RequestsTrace.settledFrames_length_le
    {benv : Benv} {bout : BlockOutput} {state : State} {bout' : BlockOutput}
    (trace : RequestsTrace benv bout state bout')
    (fork : CoveredFork benv.stat.fork) :
    trace.settledFrames.length ≤ 2 * (systemTransactionGas + 1) := by
  have withdrawal := trace.withdrawal.settledFrames_length_le fork
  have consolidation := trace.consolidation.settledFrames_length_le fork
  simp only [RequestsTrace.settledFrames, List.length_append]
  omega

/-- All four system-message grants remain in the full-body budget, including
their descendants even when their code is not canonical. -/
theorem AppliedBodyTrace.settledFrames_gas_bound
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs wds state bout)
    (fork : CoveredFork benv.stat.fork) :
    4 * trace.settledFrames.length ≤
      5 * benv.stat.blockGasLimit + 16 * (systemTransactionGas + 1) := by
  have beacon := trace.beacon.settledFrames_length_le fork
  have history := trace.history.settledFrames_length_le fork
  have transactions := trace.transactions.settledFrames_gas_budget fork
  have cap := (trace.transactions.blockGasUsed_bounds fork (Nat.zero_le _)).2
  have requestFork : CoveredFork trace.transactionBenv.stat.fork := by
    rw [trace.transactions.stat_eq]
    exact fork
  have requests := trace.requests.settledFrames_length_le requestFork
  change 0 ≤ trace.transactionBout.blockGasUsed ∧
    4 * trace.transactions.settledFrames.length ≤ 5 * trace.transactionBout.blockGasUsed at transactions
  change trace.transactionBout.blockGasUsed ≤ benv.stat.blockGasLimit at cap
  simp only [AppliedBodyTrace.settledFrames, List.length_append]
  omega

/-- An actual configured block's retained frame count fits in 64 bits. The
header limit and four system grants are derived from this very block trace. -/
theorem ConfiguredBlockTrace.settledFrames_length_lt
    {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTrace cfg pre post) :
    trace.settledFrames.length < 2 ^ 64 := by
  have budget := trace.bodyTrace.settledFrames_gas_bound trace.covered
  have limit := trace.header_gasLimit_lt
  change 4 * trace.settledFrames.length ≤
    5 * trace.block.header.gasLimit + 16 * (systemTransactionGas + 1) at budget
  simp only [systemTransactionGas] at budget
  omega

end Blanc.ExecutionTrace
