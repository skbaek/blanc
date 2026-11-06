import Blanc.ExecutionFrameTime
import Blanc.ExecutionMidHistoryIn

/-!
# Settled frames of a selected-domain mid history run at their block's header time

`ExecutionHistoryFrameTime.lean` over the selected-domain carriers:

* `StagedBodyTrace.frameAdmitted_time`, `ConfiguredBlockTraceIn.frameAdmitted_time` — every entered
  frame of a staged body runs at its environment's time, of a configured block at the header
  timestamp;
* `MidHistoryTraceIn.blockFrames` — the settled frames of a mid history, in trace order, each paired
  with the block whose body retained it (`blockFrames_map_snd`: forgetting the block gives
  `settledFrames`);
* `MidHistoryTraceIn.blockFrames_time`, `settledFrames_time` — every settled frame of a mid history,
  in the remainder of the starting block or in a later one, reads its own block's header timestamp.

Contract-neutral, and generic in the fork domain.
-/

namespace Blanc.ExecutionTrace

open Jaune

section Stages

variable {benv : Benv} {time : B256}

theorem BeaconStageTrace.frameAdmitted_time {rules : ForkRules} {state : State} {bal : BalBuilder}
    (trace : BeaconStageTrace rules benv state bal) (htime : benv.stat.time = time) (ca : Adr) :
    trace.FrameAdmitted ca (fun sevm _ => sevm.benvStat.time = time) := by
  cases trace with
  | skipped => trivial
  | called _ _ message _ _ => exact message.frameAdmitted_time htime ca

theorem HistoryStageTrace.frameAdmitted_time {rules : ForkRules} {inputBal bal : BalBuilder}
    {state : State} (trace : HistoryStageTrace rules benv inputBal state bal)
    (htime : benv.stat.time = time) (ca : Adr) :
    trace.FrameAdmitted ca (fun sevm _ => sevm.benvStat.time = time) := by
  cases trace with
  | skipped => trivial
  | called _ _ _ _ message _ _ => exact message.frameAdmitted_time htime ca

theorem RequestStageTrace.frameAdmitted_time {rules : ForkRules} {bout bout' : BlockOutput}
    {state : State} (trace : RequestStageTrace rules benv bout state bout')
    (htime : benv.stat.time = time) (ca : Adr) :
    trace.FrameAdmitted ca (fun sevm _ => sevm.benvStat.time = time) := by
  cases trace with
  | skipped => trivial
  | called _ requests _ =>
      exact ⟨requests.withdrawal.frameAdmitted_time htime ca,
        requests.consolidation.frameAdmitted_time htime ca⟩

/-- Every entered frame of a staged body runs at the body environment's time. -/
theorem StagedBodyTrace.frameAdmitted_time {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout)
    (htime : benv.stat.time = time) (ca : Adr) :
    trace.FrameAdmitted ca (fun sevm _ => sevm.benvStat.time = time) where
  beacon := trace.beacon.frameAdmitted_time htime ca
  history := trace.history.frameAdmitted_time htime ca
  transactions := trace.transactions.frameAdmitted_time htime ca
  requests := trace.requests.frameAdmitted_time
    ((congrArg BenvStat.time trace.transactions.stat_eq).trans htime) ca

end Stages

variable {F : Fork → Prop} {cfg : ChainConfig}

/-- Every entered frame of a selected-domain configured block runs at its header timestamp. -/
theorem ConfiguredBlockTraceIn.frameAdmitted_time {pre post : BlockChain}
    (trace : ConfiguredBlockTraceIn F cfg pre post) (ca : Adr) :
    trace.FrameAdmitted ca
      (fun sevm _ => sevm.benvStat.time = trace.block.header.timestamp.toB256) :=
  trace.bodyTrace.frameAdmitted_time rfl ca

/-- Every settled frame of a selected-domain configured block runs at its header timestamp. -/
theorem ConfiguredBlockTraceIn.settledFrames_time {pre post : BlockChain}
    (trace : ConfiguredBlockTraceIn F cfg pre post) :
    ∀ frame ∈ trace.settledFrames,
      frame.sevm.benvStat.time = trace.block.header.timestamp.toB256 := by
  intro frame member
  exact (trace.frameAdmitted_iff_rawFrames frame.sevm.currentTarget _).1
    (trace.frameAdmitted_time frame.sevm.currentTarget) _
    (trace.mem_rawFrames_of_mem_settledFrames frame member) rfl

/-- The settled frames of a mid history, in trace order, each paired with the block whose body
retained it. -/
def MidHistoryTraceIn.blockFrames :
    {start : Benv} → {future : BlockChain} →
    MidHistoryTraceIn F cfg start future → List (Block × Exec.Frame)
  | _, _, .tail block cut =>
      (cut.after.settledFrames ++ block.bodyTrace.requests.settledFrames).map
        (fun frame => (block.block, frame))
  | _, _, .step prior block =>
      prior.blockFrames ++ block.settledFrames.map (fun frame => (block.block, frame))

theorem MidHistoryTraceIn.blockFrames_map_snd {start : Benv} {future : BlockChain}
    (trace : MidHistoryTraceIn F cfg start future) :
    trace.blockFrames.map Prod.snd = trace.settledFrames := by
  induction trace with
  | tail block cut =>
      simp only [blockFrames, settledFrames, List.map_map]
      exact List.map_id' _
  | step prior block ih =>
      simp only [blockFrames, settledFrames, List.map_append, List.map_map, ih]
      congr 1
      exact List.map_id' _

/-- Every settled frame of a mid history runs at the header timestamp of the block that retained
it. -/
theorem MidHistoryTraceIn.blockFrames_time {start : Benv} {future : BlockChain}
    (trace : MidHistoryTraceIn F cfg start future) :
    ∀ entry ∈ trace.blockFrames,
      entry.2.sevm.benvStat.time = entry.1.header.timestamp.toB256 := by
  induction trace with
  | tail block cut =>
      intro entry member
      simp only [blockFrames, List.mem_map] at member
      obtain ⟨frame, frameMember, rfl⟩ := member
      apply block.settledFrames_time frame
      rw [block.settledFrames_txSplit cut]
      exact List.mem_append_right _ frameMember
  | step prior block ih =>
      intro entry member
      simp only [blockFrames, List.mem_append, List.mem_map] at member
      rcases member with member | ⟨frame, frameMember, rfl⟩
      · exact ih entry member
      · exact block.settledFrames_time frame frameMember

/-- **Time link.** Every settled frame of a mid history reads, as its block time, the header
timestamp of the block that retained it. -/
theorem MidHistoryTraceIn.settledFrames_time {start : Benv} {future : BlockChain}
    (trace : MidHistoryTraceIn F cfg start future) :
    ∀ frame ∈ trace.settledFrames, ∃ block : Block,
      (block, frame) ∈ trace.blockFrames ∧
        frame.sevm.benvStat.time = block.header.timestamp.toB256 := by
  intro frame member
  rw [← trace.blockFrames_map_snd, List.mem_map] at member
  obtain ⟨⟨block, frame'⟩, entryMember, rfl⟩ := member
  exact ⟨block, entryMember, trace.blockFrames_time _ entryMember⟩

end Blanc.ExecutionTrace
