import Blanc.ExecutionParentLogAttribution
import Blanc.ExecutionIndexedReceipts
import Blanc.ExecutionMidHistoryIn
import Blanc.ExecutionHistoryInSystemEnvironment

/-!
# A settled frame's log reaches its block's receipts

A reader sees receipts; a frame law speaks of a settled frame's `post.logs`. This is the link: every log in the endpoint
of a settled frame of a block's transaction stage is in a successful receipt of that block. So a log filter that finds
nothing over the block's receipts rules the log out of every such frame. System stages have no receipts, so their
frames are not covered by the receipts; `MidHistoryTraceIn.no_log_at` covers them at an account no system frame targets,
and `MidHistoryTraceIn.system_ne` gives that from `MidHistoryTraceIn.SystemConfined` for an account outside the four
system addresses.
-/

namespace Blanc.ExecutionTrace

open Jaune

/-- Each settled frame of a transaction stage belongs to one actual indexed transaction. -/
theorem ApplyTransactionsTrace.exists_splitAt_of_mem_settledFrames
    {txs : List (Nat × Tx)} {benv finalBenv : Benv} {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout) {frame : Exec.Frame}
    (member : frame ∈ trace.settledFrames) :
    ∃ (i : Nat) (lt : i < txs.length), frame ∈ (trace.splitAt i lt).head.settledFrames := by
  induction trace with
  | nil => simp only [ApplyTransactionsTrace.settledFrames, List.not_mem_nil] at member
  | cons head tail ih =>
    change frame ∈ head.settledFrames ++ tail.settledFrames at member
    rcases List.mem_append.mp member with first | rest
    · exact ⟨0, by simp only [List.length_cons]; omega, first⟩
    · obtain ⟨i, lt, found⟩ := ih rest
      exact ⟨i + 1, by simp only [List.length_cons]; omega, found⟩

/-- **A log of a settled frame of a block's transaction stage is in a successful receipt of that block.** -/
theorem ConfiguredBlockTraceIn.log_mem_receipt_of_settledFrame
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (block : ConfiguredBlockTraceIn F cfg pre post) (hsg : block.fork.ruleSet.stateGas = none)
    {frame : Exec.Frame} (member : frame ∈ block.bodyTrace.transactions.settledFrames)
    {entry : Log} (event : entry ∈ frame.post.logs) :
    ∃ (i : Nat) (receipt : Fin 5 × Receipt),
      i < block.bodyTrace.decodedTxs.putIndex.length ∧
      block.blockOutput.receiptsTrie[BLT.toBytes (.bytes i.toBytes)]? = some receipt ∧
      receipt.2.succeeded = true ∧ entry ∈ receipt.2.logs := by
  obtain ⟨i, lt, found⟩ := block.bodyTrace.transactions.exists_splitAt_of_mem_settledFrames member
  let cut := block.bodyTrace.transactions.splitAt i lt
  have lookup := block.receipt_of_txSplit cut hsg
  have keyEq := congrArg (fun index : Nat =>
    block.blockOutput.receiptsTrie[BLT.toBytes (.bytes index.toBytes)]?) cut.putIndex_eq.1
  have indexed := keyEq.symm.trans lookup
  have headSg : cut.benv.stat.rules.stateGas = none := by
    rw [cut.before.stat_eq]
    exact hsg
  obtain ⟨r₀, lookup₀, ok, mem⟩ := cut.head.log_mem_receipt_of_settledFrame headSg found event
  have same := cut.head.receipt_of_settledRoots headSg
  rw [lookup₀] at same
  cases Option.some.inj same
  exact ⟨i, _, lt, indexed, ok, mem⟩

/-- **No log in a block's receipts satisfying `property` means none in its transaction stage's settled frames.** -/
theorem ConfiguredBlockTraceIn.no_log_of_receipts
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (block : ConfiguredBlockTraceIn F cfg pre post) (hsg : block.fork.ruleSet.stateGas = none)
    (property : Log → Prop)
    (receipts : ∀ (i : Nat), i < block.bodyTrace.decodedTxs.putIndex.length →
      ∀ (receipt : Fin 5 × Receipt),
        block.blockOutput.receiptsTrie[BLT.toBytes (.bytes i.toBytes)]? = some receipt →
        receipt.2.succeeded = true → ∀ entry ∈ receipt.2.logs, ¬ property entry) :
    ∀ frame ∈ block.bodyTrace.transactions.settledFrames, ∀ entry ∈ frame.post.logs, ¬ property entry := by
  intro frame member entry event
  obtain ⟨i, r, lt, lookup, ok, mem⟩ := block.log_mem_receipt_of_settledFrame hsg member event
  exact receipts i lt r lookup ok entry mem

/-- The settled frames of a mid history's transaction stages: its remainder's suffix, then each later block's. -/
def MidHistoryTraceIn.txFrames {F : Fork → Prop} {cfg : ChainConfig} :
    {start : Benv} → {future : BlockChain} → MidHistoryTraceIn F cfg start future → List Exec.Frame
  | _, _, .tail _ cut => cut.after.settledFrames
  | _, _, .step prior block => prior.txFrames ++ block.bodyTrace.transactions.settledFrames

/-- **What a reader's filter says of a block**: no successful receipt of the block holds a log with `property`. -/
def ConfiguredBlockTraceIn.NoLogInReceipts {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (block : ConfiguredBlockTraceIn F cfg pre post) (property : Log → Prop) : Prop :=
  ∀ (i : Nat), i < block.bodyTrace.decodedTxs.putIndex.length → ∀ (receipt : Fin 5 × Receipt),
    block.blockOutput.receiptsTrie[BLT.toBytes (.bytes i.toBytes)]? = some receipt →
    receipt.2.succeeded = true → ∀ entry ∈ receipt.2.logs, ¬ property entry

/-- **What a reader's filter says of a mid history**: `NoLogInReceipts` for every block it touches. -/
def MidHistoryTraceIn.NoLogInReceipts {F : Fork → Prop} {cfg : ChainConfig} (property : Log → Prop) :
    {start : Benv} → {future : BlockChain} → MidHistoryTraceIn F cfg start future → Prop
  | _, _, .tail block _ => block.NoLogInReceipts property
  | _, _, .step prior block => prior.NoLogInReceipts property ∧ block.NoLogInReceipts property

/-- **Zero matching logs in a mid history's receipts means none in the settled frames of its transaction stages.** -/
theorem MidHistoryTraceIn.no_log_of_receipts {F : Fork → Prop} {cfg : ChainConfig}
    (hsg : ∀ {fork}, F fork → fork.ruleSet.stateGas = none) (property : Log → Prop)
    {start : Benv} {future : BlockChain} (trace : MidHistoryTraceIn F cfg start future)
    (receipts : trace.NoLogInReceipts property) :
    ∀ frame ∈ trace.txFrames, ∀ entry ∈ frame.post.logs, ¬ property entry := by
  induction trace with
  | tail block cut =>
    intro frame member
    have whole : frame ∈ block.bodyTrace.transactions.settledFrames := by
      rw [cut.settledFrames_eq]
      exact List.mem_append_right _ member
    exact block.no_log_of_receipts (hsg block.forkIn) property receipts frame whole
  | step prior block ih =>
    intro frame member
    rcases List.mem_append.mp member with early | late
    · exact ih receipts.1 frame early
    · exact block.no_log_of_receipts (hsg block.forkIn) property receipts.2 frame late

/-! ## System stages -/

/-- The system-message frames of a mid history: its remainder's request stage, then each later block's system stages. -/
def MidHistoryTraceIn.systemRawFrames {F : Fork → Prop} {cfg : ChainConfig} :
    {start : Benv} → {future : BlockChain} → MidHistoryTraceIn F cfg start future → List Exec.Deriv
  | _, _, .tail block _ => block.bodyTrace.requests.rawFrames
  | _, _, .step prior block => prior.systemRawFrames ++ block.systemRawFrames

/-- A settled frame of a block is a transaction stage's, or a system stage's root. -/
theorem ConfiguredBlockTraceIn.settled_tx_or_system {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (block : ConfiguredBlockTraceIn F cfg pre post) {frame : Exec.Frame} (member : frame ∈ block.settledFrames) :
    frame ∈ block.bodyTrace.transactions.settledFrames ∨
      Blanc.Exec.Frame.rootDeriv (frame := frame) ∈ block.systemRawFrames := by
  simp only [ConfiguredBlockTraceIn.settledFrames, StagedBodyTrace.settledFrames, List.mem_append] at member
  simp only [ConfiguredBlockTraceIn.systemRawFrames, StagedBodyTrace.systemRawFrames, List.mem_append]
  rcases member with ((beacon | history) | tx) | requests
  · exact .inr (.inl (.inl (block.bodyTrace.beacon.mem_rawFrames_of_mem_settledFrames frame beacon)))
  · exact .inr (.inl (.inr (block.bodyTrace.history.mem_rawFrames_of_mem_settledFrames frame history)))
  · exact .inl tx
  · exact .inr (.inr (block.bodyTrace.requests.mem_rawFrames_of_mem_settledFrames frame requests))

/-- A settled frame of a mid history is a transaction stage's, or a system stage's root. -/
theorem MidHistoryTraceIn.settled_tx_or_system {F : Fork → Prop} {cfg : ChainConfig} {start : Benv}
    {future : BlockChain} (trace : MidHistoryTraceIn F cfg start future) {frame : Exec.Frame}
    (member : frame ∈ trace.settledFrames) :
    frame ∈ trace.txFrames ∨ Blanc.Exec.Frame.rootDeriv (frame := frame) ∈ trace.systemRawFrames := by
  induction trace with
  | tail block cut =>
    rcases List.mem_append.mp member with tx | requests
    · exact .inl tx
    · exact .inr (block.bodyTrace.requests.mem_rawFrames_of_mem_settledFrames frame requests)
  | step prior block ih =>
    rcases List.mem_append.mp member with early | late
    · rcases ih early with tx | system
      · exact .inl (List.mem_append_left _ tx)
      · exact .inr (List.mem_append_left _ system)
    · rcases block.settled_tx_or_system late with tx | system
      · exact .inl (List.mem_append_right _ tx)
      · exact .inr (List.mem_append_right _ system)

/-- **Zero matching logs in a mid history's receipts means none in a settled frame at an account no system frame
targets.** -/
theorem MidHistoryTraceIn.no_log_at {F : Fork → Prop} {cfg : ChainConfig}
    (hsg : ∀ {fork}, F fork → fork.ruleSet.stateGas = none) (property : Log → Prop)
    {start : Benv} {future : BlockChain} (trace : MidHistoryTraceIn F cfg start future)
    (receipts : trace.NoLogInReceipts property) {T : Adr}
    (sysNe : ∀ root ∈ trace.systemRawFrames, root.sevm.currentTarget ≠ T) :
    ∀ frame ∈ trace.settledFrames, frame.sevm.currentTarget = T → ∀ entry ∈ frame.post.logs, ¬ property entry := by
  intro frame member target
  rcases trace.settled_tx_or_system member with tx | system
  · exact trace.no_log_of_receipts hsg property receipts frame tx
  · exact absurd target (sysNe _ system)

/-- The facts that confine a block's system stages to the system addresses: the canonical code at the block's opening,
no authorization recovering to a system address, and no CREATE frame landing on one. All three are empty before Cancun,
and the authorization clause before Prague. -/
def ConfiguredBlockTraceIn.SystemConfined {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (block : ConfiguredBlockTraceIn F cfg pre post) : Prop :=
  block.SystemCodeAtOpening ∧ (∀ p ∈ systemContracts, block.PragueNoAuthorityAt p.1) ∧ block.InstalledNoFrame

/-- `SystemConfined` at every block a mid history touches. -/
def MidHistoryTraceIn.SystemConfined {F : Fork → Prop} {cfg : ChainConfig} :
    {start : Benv} → {future : BlockChain} → MidHistoryTraceIn F cfg start future → Prop
  | _, _, .tail block _ => block.SystemConfined
  | _, _, .step prior block => prior.SystemConfined ∧ block.SystemConfined

/-- What a fork installs is at a system address. -/
theorem mem_systemTargets_of_installedAt {f : Fork} {a : Adr} (h : a ∈ (installedAt f).map Prod.fst) :
    a ∈ systemTargets := by
  have all : ∀ f, ((installedAt f).map Prod.fst).all (fun a => a ∈ systemTargets) = true := by
    intro f
    cases f <;> decide +kernel
  exact of_decide_eq_true (List.all_eq_true.mp (all f) a h)

/-- A confined block's system frames miss an account outside the system addresses. -/
theorem ConfiguredBlockTraceIn.system_ne {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (block : ConfiguredBlockTraceIn F cfg pre post) (hHist : HistFork block.fork) (confined : block.SystemConfined)
    {T : Adr} (notSystem : T ∉ systemTargets) :
    ∀ root ∈ block.systemRawFrames, root.sevm.currentTarget ≠ T := fun root member eq =>
  notSystem (eq ▸ mem_systemTargets_of_installedAt
    (block.systemFrames_target_of_installedAt hHist confined.1 confined.2.1 confined.2.2 root member))

/-- **No system frame of a confined mid history targets an account outside the system addresses.** -/
theorem MidHistoryTraceIn.system_ne {F : Fork → Prop} {cfg : ChainConfig} (hHist : ∀ f, F f → HistFork f)
    {start : Benv} {future : BlockChain} (trace : MidHistoryTraceIn F cfg start future)
    (confined : trace.SystemConfined) {T : Adr} (notSystem : T ∉ systemTargets) :
    ∀ root ∈ trace.systemRawFrames, root.sevm.currentTarget ≠ T := by
  induction trace with
  | tail block cut =>
    intro root member
    refine block.system_ne (hHist _ block.forkIn) confined notSystem root ?_
    exact List.mem_append_right _ member
  | step prior block ih =>
    intro root member
    rcases List.mem_append.mp member with early | late
    · exact ih confined.1 root early
    · exact block.system_ne (hHist _ block.forkIn) confined.2 notSystem root late

end Blanc.ExecutionTrace
