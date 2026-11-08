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

/-! ## Selected-fork entry facts

The same inductions with an arbitrary fork predicate `F` in place of
`CoveredFork`: every transport below rewrites a `benvStat` equality, so no
rule fact is needed. -/

/-- A raw frame root starts at program counter zero on a selected fork. -/
def RootEntryIn (F : Fork → Prop) (root : Exec.Deriv) : Prop :=
  root.pc = 0 ∧ F root.sevm.benvStat.fork

/-- A retained slot entered by a frame whose inner message runs on a selected fork holds only
raw roots that start at pc zero on a selected fork. -/
theorem RetainedXlot.rootEntryIn_of_runFrame {F : Fork → Prop} {frame : Frame} {slot : Xlot}
    {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (retained : RetainedXlot slot) (hrun : RunFrame frame slot out)
    (hfork : F frame.inner.benv.stat.fork) :
    ∀ root ∈ retained.rawFrames, RootEntryIn F root := by
  cases retained with
  | none => intro root member; simp only [rawFrames, List.not_mem_nil] at member
  | @some pc sevm pre execution run =>
      have pcZero : pc = 0 := Frame.enter_run_pc (RunFrame.some_inv hrun).1
      subst pcZero
      have rootFork : F sevm.benvStat.fork := by
        rw [RunFrame.benvStat_eq hrun]; exact hfork
      intro root member
      exact LockExclusion.rawFrameRoots_entryIn run rootFork member

theorem ProcessMessageTrace.rootEntryIn {F : Fork → Prop} {msg : Msg}
    {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (trace : ProcessMessageTrace msg out) (hfork : F msg.benv.stat.fork) :
    ∀ root ∈ trace.rawFrames, RootEntryIn F root :=
  trace.retained.rootEntryIn_of_runFrame trace.run hfork

theorem ProcessCreateMessageTrace.rootEntryIn {F : Fork → Prop} {msg : Msg}
    {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (trace : ProcessCreateMessageTrace msg out) (hfork : F msg.benv.stat.fork) :
    ∀ root ∈ trace.rawFrames, RootEntryIn F root :=
  trace.retained.rootEntryIn_of_runFrame trace.run (by
    show F (processCreateMessage.msg msg).benv.stat.fork
    rw [processCreateMessage.msg_benvStat]
    exact hfork)

theorem MessageCallTrace.rootEntryIn {F : Fork → Prop} {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out) (hfork : F msg.benv.stat.fork) :
    ∀ root ∈ trace.rawFrames, RootEntryIn F root := by
  cases trace with
  | createCollision => intro root member; simp only [rawFrames, List.not_mem_nil] at member
  | createRun target collision evm core coreTrace result =>
      exact coreTrace.rootEntryIn hfork
  | callRun target delegated refund delegation execMsg execMsgEq evm core coreTrace result =>
      subst execMsgEq
      refine coreTrace.rootEntryIn ?_
      rw [messageCallExecutionMessage_benv_stat, messageCallDelegation_benv_stat delegation]
      exact hfork

theorem TransactionTrace.rootEntryIn {F : Fork → Prop} {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (hfork : F benv.stat.fork) :
    ∀ root ∈ trace.rawFrames, RootEntryIn F root :=
  trace.message.rootEntryIn (by
    rw [prepareMessage_benv trace.prepared]
    simpa only [Benv.beginTransaction] using hfork)

theorem ApplyTransactionsTrace.rootEntryIn {F : Fork → Prop} {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (hfork : F benv.stat.fork) :
    ∀ root ∈ trace.rawFrames, RootEntryIn F root := by
  induction trace with
  | nil => intro root member; simp only [rawFrames, List.not_mem_nil] at member
  | cons head tail ih =>
      intro root member
      simp only [ApplyTransactionsTrace.rawFrames, List.mem_append] at member
      rcases member with member | member
      · exact head.rootEntryIn hfork root member
      · exact ih (by simpa only [Benv.withState] using hfork) root member

theorem SystemMessageTrace.rootEntryIn {F : Fork → Prop} {benv : Benv} {target : Adr} {data : Bytes}
    {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out)
    (hfork : F benv.stat.fork) :
    ∀ root ∈ trace.rawFrames, RootEntryIn F root :=
  trace.message.rootEntryIn (by
    simpa only [systemTransactionMessage, processSystemTransactionMsg, Benv.beginTransaction] using
      hfork)

theorem RequestsTrace.rootEntryIn {F : Fork → Prop} {benv : Benv} {bout : BlockOutput} {state : State}
    {bout' : BlockOutput} (trace : RequestsTrace benv bout state bout')
    (hfork : F benv.stat.fork) :
    ∀ root ∈ trace.rawFrames, RootEntryIn F root := by
  intro root member
  simp only [RequestsTrace.rawFrames, List.mem_append] at member
  rcases member with member | member
  · exact trace.withdrawal.rootEntryIn hfork root member
  · exact trace.consolidation.rootEntryIn (by simpa only [Benv.withState] using hfork) root member

theorem AppliedBodyTrace.rootEntryIn {F : Fork → Prop} {benv : Benv} {txs : List (Bytes ⊕ Tx)}
    {ommers : List Header} {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs ommers wds state bout)
    (hfork : F benv.stat.fork) :
    ∀ root ∈ trace.rawFrames, RootEntryIn F root := by
  intro root member
  simp only [AppliedBodyTrace.rawFrames, List.mem_append] at member
  rcases member with ((member | member) | member) | member
  · exact trace.beacon.rootEntryIn hfork root member
  · exact trace.history.rootEntryIn (by simpa only [Benv.withState] using hfork) root member
  · exact trace.transactions.rootEntryIn (by simpa only [Benv.withState] using hfork) root member
  · refine trace.requests.rootEntryIn ?_ root member
    have transactionFork : F trace.transactionBenv.stat.fork := by
      rw [trace.transactions.stat_eq]
      simpa only [Benv.withState] using hfork
    simpa only [Benv.withState] using transactionFork

end ExecutionTrace

end Blanc
