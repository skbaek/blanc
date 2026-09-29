import Blanc.ExecutionTraceFrames
import Blanc.LockExclusion
import Blanc.ExecutionBodyEffects

/-!
# Entry facts of the raw frame roots retained by execution traces

Every interpreter root a retained trace holds starts at program counter zero on the fork of
the message that entered it, and so does every frame below it.  `RootEntry` is that pair of
facts; each retained carrier from a call or create message to a configured history derives
it for all of its `rawFrames` from the fork of its own opening benv.  These are the two
facts about a raw root that the execution-level theorems take as `Exec 0 …` and
`CoveredFork`.
-/

namespace Blanc

open Jaune

namespace ExecutionTrace

/-- A raw frame root starts at program counter zero on a covered fork. -/
def RootEntry (root : Exec.Deriv) : Prop :=
  root.pc = 0 ∧ CoveredFork root.sevm.benvStat.fork

/-- A retained slot entered by a frame whose inner message runs on a covered fork holds only
raw roots that start at pc zero on a covered fork. -/
theorem RetainedXlot.rootEntry_of_runFrame {frame : Frame} {slot : Xlot}
    {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (retained : RetainedXlot slot) (hrun : RunFrame frame slot out)
    (hfork : CoveredFork frame.inner.benv.stat.fork) :
    ∀ root ∈ retained.rawFrames, RootEntry root := by
  cases retained with
  | none => intro root member; simp [RetainedXlot.rawFrames] at member
  | @some pc sevm pre execution run =>
      have pcZero : pc = 0 := Frame.enter_run_pc (RunFrame.some_inv hrun).1
      subst pcZero
      have rootFork : CoveredFork sevm.benvStat.fork := by
        rw [RunFrame.benvStat_eq hrun]; exact hfork
      intro root member
      exact LockExclusion.rawFrameRoots_entry run rootFork member

theorem ProcessMessageTrace.rootEntry {msg : Msg}
    {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (trace : ProcessMessageTrace msg out) (hfork : CoveredFork msg.benv.stat.fork) :
    ∀ root ∈ trace.rawFrames, RootEntry root :=
  trace.retained.rootEntry_of_runFrame trace.run hfork

theorem ProcessCreateMessageTrace.rootEntry {msg : Msg}
    {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (trace : ProcessCreateMessageTrace msg out) (hfork : CoveredFork msg.benv.stat.fork) :
    ∀ root ∈ trace.rawFrames, RootEntry root :=
  trace.retained.rootEntry_of_runFrame trace.run (by
    show CoveredFork (processCreateMessage.msg msg).benv.stat.fork
    rw [processCreateMessage.msg_benvStat]
    exact hfork)

theorem MessageCallTrace.rootEntry {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out) (hfork : CoveredFork msg.benv.stat.fork) :
    ∀ root ∈ trace.rawFrames, RootEntry root := by
  cases trace with
  | createCollision => intro root member; simp [MessageCallTrace.rawFrames] at member
  | createRun target collision evm core coreTrace result =>
      exact coreTrace.rootEntry hfork
  | callRun target delegated refund delegation execMsg execMsgEq evm core coreTrace result =>
      subst execMsgEq
      refine coreTrace.rootEntry ?_
      rw [messageCallExecutionMessage_benv_stat, messageCallDelegation_benv_stat delegation]
      exact hfork

theorem TransactionTrace.rootEntry {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (hfork : CoveredFork benv.stat.fork) :
    ∀ root ∈ trace.rawFrames, RootEntry root :=
  trace.message.rootEntry (by
    rw [prepareMessage_benv trace.prepared]
    simpa [Benv.beginTransaction] using hfork)

theorem ApplyTransactionsTrace.rootEntry {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (hfork : CoveredFork benv.stat.fork) :
    ∀ root ∈ trace.rawFrames, RootEntry root := by
  induction trace with
  | nil => intro root member; simp [ApplyTransactionsTrace.rawFrames] at member
  | cons head tail ih =>
      intro root member
      simp only [ApplyTransactionsTrace.rawFrames, List.mem_append] at member
      rcases member with member | member
      · exact head.rootEntry hfork root member
      · exact ih (by simpa [Benv.withState] using hfork) root member

theorem SystemMessageTrace.rootEntry {benv : Benv} {target : Adr} {data : Bytes}
    {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out)
    (hfork : CoveredFork benv.stat.fork) :
    ∀ root ∈ trace.rawFrames, RootEntry root :=
  trace.message.rootEntry (by
    simpa [systemTransactionMessage, processSystemTransactionMsg,
      Benv.beginTransaction] using hfork)

theorem RequestsTrace.rootEntry {benv : Benv} {bout : BlockOutput} {state : State}
    {bout' : BlockOutput} (trace : RequestsTrace benv bout state bout')
    (hfork : CoveredFork benv.stat.fork) :
    ∀ root ∈ trace.rawFrames, RootEntry root := by
  intro root member
  simp only [RequestsTrace.rawFrames, List.mem_append] at member
  rcases member with member | member
  · exact trace.withdrawal.rootEntry hfork root member
  · exact trace.consolidation.rootEntry (by simpa [Benv.withState] using hfork) root member

theorem AppliedBodyTrace.rootEntry {benv : Benv} {txs : List (Bytes ⊕ Tx)}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs wds state bout)
    (hfork : CoveredFork benv.stat.fork) :
    ∀ root ∈ trace.rawFrames, RootEntry root := by
  intro root member
  simp only [AppliedBodyTrace.rawFrames, List.mem_append] at member
  rcases member with ((member | member) | member) | member
  · exact trace.beacon.rootEntry hfork root member
  · exact trace.history.rootEntry (by simpa [Benv.withState] using hfork) root member
  · exact trace.transactions.rootEntry (by simpa [Benv.withState] using hfork) root member
  · refine trace.requests.rootEntry ?_ root member
    have transactionFork : CoveredFork trace.transactionBenv.stat.fork := by
      rw [trace.transactions.stat_eq]
      simpa [Benv.withState] using hfork
    simpa [Benv.withState] using transactionFork

theorem ConfiguredBlockTrace.rootEntry {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTrace cfg pre post) :
    ∀ root ∈ trace.rawFrames, RootEntry root :=
  trace.bodyTrace.rootEntry trace.covered

/-- **Every raw frame root a configured history retains starts at pc zero on a covered
fork**, whatever it later does and however it settles. -/
theorem ConfiguredHistoryTrace.rootEntry {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future) :
    ∀ root ∈ trace.rawFrames, RootEntry root := by
  induction trace with
  | refl => intro root member; simp [ConfiguredHistoryTrace.rawFrames] at member
  | step prior block ih =>
      intro root member
      simp only [ConfiguredHistoryTrace.rawFrames, List.mem_append] at member
      rcases member with member | member
      · exact ih root member
      · exact block.rootEntry root member

end ExecutionTrace

end Blanc
