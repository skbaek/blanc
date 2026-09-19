import Blanc.ExecutionFrames
import Blanc.ExecutionTraceFrames
import Blanc.ExecutionHistoryAdmission
import Blanc.ExecutionAccountingLadder

/-!
# Block-environment inheritance for execution frames

Every frame entered by an execution inherits the block environment statics of
the execution's outer frame.  The result is stated over the raw frame-root
traversal so it can be combined with trace-local admission conditions.
-/

namespace Blanc

open Jaune Jaune.List Jaune.Except _root_.List _root_.Nat

private lemma Frame.enter_run_benvStat_of_step
    {pc : Nat} {sevm : Sevm} {pre : Devm}
    {frame : Frame} {resume : Resume} {pc' : Nat} {child : Evm}
    (hstep : Evm.step ⟨pc, sevm, pre⟩ = .spawn frame resume pc')
    (henter : frame.enter = .run child) :
    child.sta.benvStat = sevm.benvStat := by
  obtain ⟨x, _at, hspawn, _pc⟩ := Evm.step_spawn_inv hstep
  rw [Frame.enter_run_benvStat henter]
  exact Xinst.step_spawn_benvStat hspawn

theorem Exec.frameAdmitted_benvStat {pc : Nat} {sevm : Sevm} {pre : Devm}
    {out : Execution} (run : Exec pc sevm pre out) (ca : Adr) :
    Exec.FrameAdmitted ca (fun frameSevm _ => frameSevm.benvStat = sevm.benvStat) run := by
  induction run with
  | halt hstep =>
      intro root member target
      simp [Exec.rawFrameRoots, Exec.rawFrameDescendants] at member
      rcases member with rfl
      rfl
  | cont hstep next ih =>
      intro root member target
      simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons] at member
      rcases member with rfl | member
      · rfl
      · exact ih root (by simp [Exec.rawFrameRoots, member]) target
  | doneErr hstep henter hresume =>
      intro root member target
      simp [Exec.rawFrameRoots, Exec.rawFrameDescendants] at member
      rcases member with rfl
      rfl
  | doneOk hstep henter hresume next ih =>
      intro root member target
      simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons] at member
      rcases member with rfl | member
      · rfl
      · exact ih root (by simp [Exec.rawFrameRoots, member]) target
  | runErr hstep henter child hresume ih =>
      intro root member target
      simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons] at member
      rcases member with rfl | member
      · rfl
      · rcases member with rfl | member
        · exact Frame.enter_run_benvStat_of_step hstep henter
        · exact (ih root (by simp [Exec.rawFrameRoots, member]) target).trans
            (Frame.enter_run_benvStat_of_step hstep henter)
  | runOk hstep henter child hresume next ihChild ihNext =>
      intro root member target
      simp only [Exec.rawFrameRoots, Exec.rawFrameDescendants, List.mem_cons,
        List.mem_append] at member
      rcases member with rfl | member
      · rfl
      · rcases member with rfl | member
        · exact Frame.enter_run_benvStat_of_step hstep henter
        · rcases member with member | member
          · exact (ihChild root (by simp [Exec.rawFrameRoots, member]) target).trans
              (Frame.enter_run_benvStat_of_step hstep henter)
          · exact ihNext root (by simp [Exec.rawFrameRoots, member]) target

/-! ## Retained traces run at their block's environment

C2b/C2c: every interpreter frame retained by a raw message trace runs at the
message's block statics, and every frame retained by a configured block runs at
that block's header timestamp.  The configured transition also fixes the new
chain tip and orders the block strictly after its parent. -/

namespace ExecutionTrace

/-- A retained recursive slot entered by a frame whose inner message's block
statics satisfy `Q` runs every entered frame under statics satisfying `Q`. -/
theorem RetainedXlot.frameAdmitted_benvStat_of_runFrame
    {frame : Frame} {slot : Xlot}
    {out : Except (EvmError × State × AdrSet × Tra) Devm} {Q : BenvStat → Prop}
    (retained : RetainedXlot slot) (hrun : RunFrame frame slot out)
    (hQ : Q frame.inner.benv.stat) (ca : Adr) :
    retained.FrameAdmitted ca (fun sevm _ => Q sevm.benvStat) := by
  cases retained with
  | none => trivial
  | @some pc sevm pre execution run =>
      intro root member target
      rw [(Exec.frameAdmitted_benvStat run ca root member target).trans
        (RunFrame.benvStat_eq hrun)]
      exact hQ

private theorem ProcessMessageTrace.frameAdmitted_benvStat_of
    {msg : Msg} {out : Except (EvmError × State × AdrSet × Tra) Devm}
    {Q : BenvStat → Prop} (trace : ProcessMessageTrace msg out)
    (hQ : Q msg.benv.stat) (ca : Adr) :
    trace.FrameAdmitted ca (fun sevm _ => Q sevm.benvStat) :=
  RetainedXlot.frameAdmitted_benvStat_of_runFrame trace.retained trace.run hQ ca

theorem ProcessMessageTrace.frameAdmitted_benvStat
    {msg : Msg} {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (trace : ProcessMessageTrace msg out) (ca : Adr) :
    trace.FrameAdmitted ca (fun sevm _ => sevm.benvStat = msg.benv.stat) :=
  trace.frameAdmitted_benvStat_of (Q := fun stat => stat = msg.benv.stat) rfl ca

/-- The block time, read through the statics of the frames a settled message
call actually entered. -/
private theorem MessageCallTrace.frameAdmitted_time
    {msg : Msg} {state : State} {out : MsgCallOutput} {time : B256}
    (trace : MessageCallTrace msg state out)
    (htime : msg.benv.stat.time = time) (ca : Adr) :
    trace.FrameAdmitted ca (fun sevm _ => sevm.benvStat.time = time) := by
  cases trace with
  | createCollision => trivial
  | createRun target collision evm core coreTrace result =>
      exact RetainedXlot.frameAdmitted_benvStat_of_runFrame
        (Q := fun stat => stat.time = time) coreTrace.retained coreTrace.run htime ca
  | callRun target delegated refund delegation execMsg execMsgEq evm core
      coreTrace result =>
      subst execMsgEq
      refine coreTrace.frameAdmitted_benvStat_of (Q := fun stat => stat.time = time) ?_ ca
      rw [messageCallExecutionMessage_benv_stat delegated,
        messageCallDelegation_benv_stat delegation]
      exact htime

private theorem SystemMessageTrace.frameAdmitted_time
    {benv : Benv} {target : Adr} {data : Bytes}
    {state : State} {out : MsgCallOutput} {time : B256}
    (trace : SystemMessageTrace benv target data state out)
    (htime : benv.stat.time = time) (ca : Adr) :
    trace.FrameAdmitted ca (fun sevm _ => sevm.benvStat.time = time) :=
  trace.message.frameAdmitted_time htime ca

private theorem ApplyTransactionsTrace.frameAdmitted_time
    {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput} {time : B256}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (htime : benv.stat.time = time) (ca : Adr) :
    trace.FrameAdmitted ca (fun sevm _ => sevm.benvStat.time = time) := by
  induction trace with
  | nil => trivial
  | cons head tail ih =>
      refine ⟨head.message.frameAdmitted_time ?_ ca, ih htime⟩
      rw [prepareMessage_benv head.prepared]
      exact htime

private theorem AppliedBodyTrace.frameAdmitted_time
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput} {time : B256}
    (trace : AppliedBodyTrace benv txs wds state bout)
    (htime : benv.stat.time = time) (ca : Adr) :
    trace.FrameAdmitted ca (fun sevm _ => sevm.benvStat.time = time) where
  beacon := trace.beacon.frameAdmitted_time htime ca
  history := trace.history.frameAdmitted_time htime ca
  transactions := trace.transactions.frameAdmitted_time htime ca
  requests :=
    ⟨trace.requests.withdrawal.frameAdmitted_time
        ((congrArg BenvStat.time trace.transactions.stat_eq).trans htime) ca,
      trace.requests.consolidation.frameAdmitted_time
        ((congrArg BenvStat.time trace.transactions.stat_eq).trans htime) ca⟩

theorem ConfiguredBlockTrace.frameAdmitted_time
    {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTrace cfg pre post) (ca : Adr) :
    trace.FrameAdmitted ca
      (fun sevm _ => sevm.benvStat.time = trace.block.header.timestamp.toB256) := by
  exact trace.bodyTrace.frameAdmitted_time rfl ca

theorem ConfiguredBlockTrace.post_blocks_getLast
    {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTrace cfg pre post) :
    post.blocks.getLast? = some trace.block := by
  cases trace with
  | mk block bound rules rulesAt transition bodyState blockOutput bodyRun bodyTrace
      postEq =>
      show post.blocks.getLast? = some block
      rw [postEq]
      exact appendBlock_getLast? pre.blocks block

/-- Jaune's header validation rejects a block whose timestamp is at or below its
parent's (`timestampOlderThanParent`), so an accepted header is strictly
newer than the chain tip. -/
private theorem validateHeader_parent_timestamp_lt
    {rules : ForkRules} {chain : BlockChain} {header : Header} {parent : Block}
    (valid : validateHeader rules chain header = .ok ())
    (head : chain.blocks.getLast? = some parent) :
    parent.header.timestamp < header.timestamp := by
  unfold validateHeader at valid
  rw [head] at valid
  by_contra hle
  have hle' : header.timestamp ≤ parent.header.timestamp := Nat.le_of_not_lt hle
  simp only [Option.toExcept, bind, Except.bind] at valid
  repeat' split at valid
  all_goals cases valid

theorem ConfiguredBlockTrace.parent_timestamp_lt
    {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTrace cfg pre post) {parent : Block}
    (head : pre.blocks.getLast? = some parent) :
    parent.header.timestamp < trace.block.header.timestamp := by
  have h := trace.transition
  have hId : cfg.chainId = pre.chainId := stateTransitionUsing_success_chainId_eq h
  rw [stateTransitionUsing_eq_of_chainId_eq hId] at h
  obtain ⟨rules, _, hWith⟩ := Except.bind_eq_ok h
  rw [stateTransitionWith_eq_ok_iff, stateTransitionE] at hWith
  obtain ⟨u, hvalid, _⟩ := Except.bind_eq_ok hWith
  exact validateHeader_parent_timestamp_lt hvalid head

end ExecutionTrace

end Blanc
