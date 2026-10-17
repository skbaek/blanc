import Blanc.ExecutionFrameTime
import Blanc.ExecutionTraceSettledOrigin
import Blanc.ExecutionTraceSettledFrames
import Blanc.ExecutionTraceAdmission

/-!
# Settled frames of a configured history run at their block's header time

`ConfiguredBlockTrace.frameAdmitted_time` admits every entered frame of a
configured block at `block.header.timestamp.toB256`.  This module transports
that fact to the settlement-retained frames:

* `ConfiguredBlockTrace.settledFrames_time` — every settled frame of one block
  reads the block's header timestamp as `sevm.benvStat.time`;
* `ConfiguredHistoryTrace.blockFrames` — the settled frames of a history, in
  trace order, each paired with the block whose body retained it
  (`blockFrames_map_snd`: forgetting the block gives `settledFrames`);
* `ConfiguredHistoryTrace.blockFrames_time` / `settledFrames_time` — every
  settled frame of a history reads its own block's header timestamp;
* `ConfiguredBlockTrace.settledFrame_time_ne_parent` — the control: under the
  wire bound on the header timestamp, no settled frame reads the parent's
  (pre-chain tip's) timestamp, since a configured block is strictly newer.
-/

namespace Blanc.ExecutionTrace

open Jaune

theorem RequestsTrace.mem_rawFrames_of_mem_settledFrames
    {benv : Benv} {bout : BlockOutput} {state : State} {bout' : BlockOutput}
    (trace : RequestsTrace benv bout state bout') (frame : Exec.Frame)
    (member : frame ∈ trace.settledFrames) :
    (Blanc.Exec.Frame.rootDeriv (frame := frame)) ∈ trace.rawFrames := by
  simp only [RequestsTrace.settledFrames, List.mem_append] at member
  simp only [RequestsTrace.rawFrames, List.mem_append]
  rcases member with h | h
  · exact Or.inl (trace.withdrawal.mem_rawFrames_of_mem_settledFrames frame h)
  · exact Or.inr (trace.consolidation.mem_rawFrames_of_mem_settledFrames frame h)

theorem AppliedBodyTrace.mem_rawFrames_of_mem_settledFrames
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {wds : List Withdrawal}
    {state : State} {bout : BlockOutput}
    (trace : AppliedBodyTrace benv txs wds state bout) (frame : Exec.Frame)
    (member : frame ∈ trace.settledFrames) :
    (Blanc.Exec.Frame.rootDeriv (frame := frame)) ∈ trace.rawFrames := by
  simp only [AppliedBodyTrace.settledFrames, List.mem_append] at member
  simp only [AppliedBodyTrace.rawFrames, List.mem_append]
  rcases member with ((h | h) | h) | h
  · exact Or.inl (Or.inl (Or.inl (trace.beacon.mem_rawFrames_of_mem_settledFrames frame h)))
  · exact Or.inl (Or.inl (Or.inr (trace.history.mem_rawFrames_of_mem_settledFrames frame h)))
  · exact Or.inl (Or.inr (trace.transactions.mem_rawFrames_of_mem_settledFrames frame h))
  · exact Or.inr (trace.requests.mem_rawFrames_of_mem_settledFrames frame h)

/-- A settled frame of a configured block came from an actually entered raw
frame root of that block. -/
theorem ConfiguredBlockTrace.mem_rawFrames_of_mem_settledFrames
    {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTrace cfg pre post) (frame : Exec.Frame)
    (member : frame ∈ trace.settledFrames) :
    (Blanc.Exec.Frame.rootDeriv (frame := frame)) ∈ trace.rawFrames :=
  trace.bodyTrace.mem_rawFrames_of_mem_settledFrames frame member

/-- Every settled frame of a configured block runs at the block's header
timestamp. -/
theorem ConfiguredBlockTrace.settledFrames_time
    {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTrace cfg pre post) :
    ∀ frame ∈ trace.settledFrames,
      frame.sevm.benvStat.time = trace.block.header.timestamp.toB256 := by
  intro frame member
  exact (trace.frameAdmitted_iff_rawFrames frame.sevm.currentTarget _).1
    (trace.frameAdmitted_time frame.sevm.currentTarget) _
    (trace.mem_rawFrames_of_mem_settledFrames frame member) rfl

/-- **Control.**  A settled frame of a configured block never reads its
parent's timestamp: the block is strictly newer than the pre-chain tip, and a
wire-bounded header timestamp survives `toB256` exactly.  So the statement of
`settledFrames_time` with the parent (checkpoint) timestamp in place of the
header timestamp is refuted on every configured block that settles a frame. -/
theorem ConfiguredBlockTrace.settledFrame_time_ne_parent
    {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTrace cfg pre post) {parent : Block}
    (head : pre.blocks.getLast? = some parent)
    (bound : trace.block.header.timestamp < 2 ^ 256)
    {frame : Exec.Frame} (member : frame ∈ trace.settledFrames) :
    frame.sevm.benvStat.time ≠ parent.header.timestamp.toB256 := by
  intro eq
  have hlt := trace.parent_timestamp_lt head
  have h := congrArg B256.toNat ((trace.settledFrames_time frame member).symm.trans eq)
  rw [B256.toNat_toB256_of_lt bound,
    B256.toNat_toB256_of_lt (Nat.lt_trans hlt bound)] at h
  omega

/-- The settled frames of a configured history, in trace order, each paired
with the block whose body retained it. -/
def ConfiguredHistoryTrace.blockFrames {cfg : ChainConfig} {checkpoint future : BlockChain} :
    ConfiguredHistoryTrace cfg checkpoint future → List (Block × Exec.Frame)
  | .refl _ _ _ => []
  | .step prior block =>
      prior.blockFrames ++ block.settledFrames.map (fun frame => (block.block, frame))

theorem ConfiguredHistoryTrace.blockFrames_map_snd
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future) :
    trace.blockFrames.map Prod.snd = trace.settledFrames := by
  induction trace with
  | refl => rfl
  | step prior block ih =>
      simp only [blockFrames, settledFrames, List.map_append, List.map_map, ih]
      congr 1
      exact List.map_id' _

/-- Every settled frame of a configured history runs at the header timestamp of
the block that retained it. -/
theorem ConfiguredHistoryTrace.blockFrames_time
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future) :
    ∀ entry ∈ trace.blockFrames,
      entry.2.sevm.benvStat.time = entry.1.header.timestamp.toB256 := by
  induction trace with
  | refl => intro entry member; simp only [blockFrames, List.not_mem_nil] at member
  | step prior block ih =>
      intro entry member
      simp only [blockFrames, List.mem_append, List.mem_map] at member
      rcases member with member | ⟨frame, frameMember, rfl⟩
      · exact ih entry member
      · exact block.settledFrames_time frame frameMember

/-- **U5 history link.**  Every settled frame of a configured history reads, as
its block time, the header timestamp of the block that retained it. -/
theorem ConfiguredHistoryTrace.settledFrames_time
    {cfg : ChainConfig} {checkpoint future : BlockChain}
    (trace : ConfiguredHistoryTrace cfg checkpoint future) :
    ∀ frame ∈ trace.settledFrames, ∃ block : Block,
      (block, frame) ∈ trace.blockFrames ∧
        frame.sevm.benvStat.time = block.header.timestamp.toB256 := by
  intro frame member
  rw [← trace.blockFrames_map_snd, List.mem_map] at member
  obtain ⟨⟨block, frame'⟩, entryMember, rfl⟩ := member
  exact ⟨block, entryMember, trace.blockFrames_time _ entryMember⟩

end Blanc.ExecutionTrace
