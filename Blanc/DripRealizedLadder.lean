import Blanc.DripRealizedExec
import Blanc.ExecutionAccountingLadder

namespace Blanc
open Jaune
namespace Drip

/-- DRIP's realized accounting as an `AccountingLadder` over the storage-only
`dripSpec`.  `dripSpec.Side` is `True`, so the root replay rebuilds the
balance-side `dripEntrySpec` readiness from the word bound the ladder threads. -/
noncomputable def ladder (coalition : Finset Adr) (ca : Adr) :
    ExecutionAccountingReplay.AccountingLadder dripSpec ca where
  carrier := carrier coalition ca
  append := fun first second => Chain.append first second
  tag _ _ := ()
  root := by
    intro _ _ msg entry pc sevm pre out run transfer evmEq committed runReady
      callerNe sumNof
    exact (_root_.Blanc.Exec.dripRealizedChain_of_messageRoot coalition run
      transfer evmEq committed (dripEntrySpec_messageRunReady runReady sumNof)
      callerNe).imp fun _ both => both.1
  preserves := dripSpec_preserves ca

/-- T4a. -/
theorem retainedProcessMessageReplay (coalition : Finset Adr)
    {ca : Adr} {msg : Msg} {post : Devm}
    (trace : ExecutionTrace.ProcessMessageTrace msg (.ok post))
    (ready : dripSpec.MessageRunReady ca msg)
    (callerNe : msg.currentTarget = ca → msg.caller ≠ ca)
    (sumNof : sum msg.benv.state.bal < 2 ^ 256)
    (hfork : CoveredFork msg.benv.stat.fork) :
    ∃ steps, RealizedChain (snapshot coalition ca msg.benv.state) steps
      (snapshot coalition ca post.state) :=
  (ladder coalition ca).processMessage trace ready callerNe sumNof 0 none

/-- T4b. -/
theorem retainedProcessCreateMessageReplay (coalition : Finset Adr)
    {ca : Adr} {msg : Msg} {post : Devm}
    (trace : ExecutionTrace.ProcessCreateMessageTrace msg (.ok post))
    (ready : dripSpec.MessageRunReady ca msg)
    (sumNof : sum msg.benv.state.bal < 2 ^ 256)
    (targetNone : msg.target.isNone = true) (targetNe : msg.currentTarget ≠ ca)
    (fresh : msg.benv.state.getStor msg.currentTarget = .empty) :
    ∃ steps, RealizedChain (snapshot coalition ca msg.benv.state) steps
      (snapshot coalition ca post.state) :=
  (ladder coalition ca).processCreateMessage trace ready sumNof targetNone
    targetNe fresh 0 none

/-- T4c. -/
theorem retainedMessageCallReplay (coalition : Finset Adr)
    {ca : Adr} {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : ExecutionTrace.MessageCallTrace msg state out)
    (ready : dripSpec.MessageRunReady ca msg)
    (callerNe : msg.currentTarget = ca → msg.caller ≠ ca)
    (sumNof : sum msg.benv.state.bal < 2 ^ 256) :
    ∃ steps, RealizedChain (snapshot coalition ca msg.benv.state) steps
      (snapshot coalition ca state) :=
  (ladder coalition ca).messageCall trace ready callerNe sumNof hfork 0 none

/-- T5. -/
theorem retainedTransactionReplay (coalition : Finset Adr)
    {ca : Adr} {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : ExecutionTrace.TransactionTrace benv bout tx index state bout')
    (inv : dripSpec.StateInv ca benv.state)
    (notCreated : ca ∉ benv.createdAccounts)
    (sumNof : sum benv.state.bal < 2 ^ 256)
    (hfork : CoveredFork benv.stat.fork) :
    ∃ steps, RealizedChain (snapshot coalition ca benv.state) steps
      (snapshot coalition ca state) :=
  (ladder coalition ca).transaction trace inv notCreated sumNof hfork 0 none

/-- T6. -/
theorem retainedTransactionListReplay (coalition : Finset Adr)
    {ca : Adr} {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput}
    (trace : ExecutionTrace.ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (inv : dripSpec.StateInv ca benv.state)
    (notCreated : ca ∉ benv.createdAccounts)
    (sumNof : sum benv.state.bal < 2 ^ 256)
    (hfork : CoveredFork benv.stat.fork) :
    ∃ steps, RealizedChain (snapshot coalition ca benv.state) steps
      (snapshot coalition ca finalBenv.state) :=
  (ladder coalition ca).transactionList trace inv notCreated sumNof hfork 0

/-- T7a. -/
theorem retainedSystemMessageReplay (coalition : Finset Adr)
    {ca : Adr} {benv : Benv} {target : Adr} {data : Bytes}
    {state : State} {out : MsgCallOutput}
    (trace : ExecutionTrace.SystemMessageTrace benv target data state out)
    (inv : dripSpec.StateInv ca benv.state)
    (notCreated : ca ∉ benv.createdAccounts)
    (systemNe : target ≠ systemAddress)
    (sumNof : sum benv.state.bal < 2 ^ 256)
    (hfork : CoveredFork benv.stat.fork) :
    ∃ steps, RealizedChain (snapshot coalition ca benv.state) steps
      (snapshot coalition ca state) :=
  (ladder coalition ca).systemMessage trace inv notCreated systemNe sumNof hfork 0

/-- T7b. -/
theorem retainedRequestsReplay (coalition : Finset Adr)
    {ca : Adr} {benv : Benv} {bout : BlockOutput} {state : State}
    {bout' : BlockOutput}
    (trace : ExecutionTrace.RequestsTrace benv bout state bout')
    (inv : dripSpec.StateInv ca benv.state)
    (notCreated : ca ∉ benv.createdAccounts)
    (sumNof : sum benv.state.bal < 2 ^ 256)
    (hfork : CoveredFork benv.stat.fork) :
    ∃ steps, RealizedChain (snapshot coalition ca benv.state) steps
      (snapshot coalition ca state) :=
  (ladder coalition ca).requests trace inv notCreated sumNof hfork 0

/-- T8. -/
theorem retainedDirectWithdrawalReplay (coalition : Finset Adr) {ca : Adr}
    (pre : State) (wds : List Withdrawal)
    (bound : sum pre.bal + wdsum wds < 2 ^ 256) :
    ∃ steps, RealizedChain (snapshot coalition ca pre) steps
      (snapshot coalition ca (processWithdrawalsState pre wds)) :=
  (ladder coalition ca).directWithdrawal pre wds bound 0

/-- T9. -/
theorem retainedBodyReplay (coalition : Finset Adr)
    {ca : Adr} {benv : Benv} {txs : List (Bytes ⊕ Tx)} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    (trace : ExecutionTrace.AppliedBodyTrace benv txs wds state bout)
    (inv : dripSpec.StateInv ca benv.state)
    (notCreated : ca ∉ benv.createdAccounts)
    (bound : sum benv.state.bal + wdsum wds < 2 ^ 256)
    (hfork : CoveredFork benv.stat.fork) :
    ∃ steps, RealizedChain (snapshot coalition ca benv.state) steps
      (snapshot coalition ca state) :=
  (ladder coalition ca).body trace inv notCreated bound hfork 0

/-- T10. -/
theorem retainedConfiguredBlockReplay (coalition : Finset Adr)
    {ca : Adr} {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ExecutionTrace.ConfiguredBlockTrace cfg pre post)
    (inv : dripSpec.StateInv ca pre.state) :
    ∃ steps, RealizedChain (snapshot coalition ca pre.state) steps
      (snapshot coalition ca post.state) :=
  (ladder coalition ca).configuredBlock trace inv 0

/-- T11. -/
theorem retainedConfiguredHistoryReplay (coalition : Finset Adr)
    {ca : Adr} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ExecutionTrace.ConfiguredHistoryTrace cfg checkpoint future)
    (inv : dripSpec.StateInv ca checkpoint.state)
    (hcov : ∀ timestamp fork, cfg.forkAt timestamp = .ok fork → CoveredFork fork) :
    ∃ steps, RealizedChain (snapshot coalition ca checkpoint.state) steps
      (snapshot coalition ca future.state) :=
  (ladder coalition ca).configuredHistory history inv hcov

/-- Occurrence form of T4c: the word bound supplied by the retained chronology,
not by the caller. -/
theorem TransactionMessageOccurrence.messageCallReplay_of_configuredBlock
    (coalition : Finset Adr) {ca : Adr}
    {cfg : ChainConfig} {pre post : BlockChain}
    (block : ExecutionTrace.ConfiguredBlockTrace cfg pre post)
    {msg : Msg} {messageState : State} {out : MsgCallOutput}
    {message : ExecutionTrace.MessageCallTrace msg messageState out}
    (occurrence : TransactionMessageOccurrence block.bodyTrace.transactions message)
    (ready : dripSpec.MessageRunReady ca msg)
    (callerNe : msg.currentTarget = ca → msg.caller ≠ ca) :
    ∃ steps, RealizedChain (snapshot coalition ca msg.benv.state) steps
      (snapshot coalition ca messageState) :=
  retainedMessageCallReplay coalition message ready callerNe
    (occurrence.msg_sum_nof_of_configuredBlock block) (by
      rw [occurrence.message_benv_stat_fork_eq]
      rw [block.bodyTrace.transactions.stat_eq]
      simpa [Benv.withState, initBenv] using block.covered)

end Drip
end Blanc
