import Blanc.ExecutionParentLogAttribution
import Blanc.ExecutionHistoryCommittedCuts
import Blanc.RlpBytesInjective
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

/-- The settled frames of a mid history's transaction stages: its remainder's suffix, then each later block's. -/
def MidHistoryTraceIn.txFrames {F : Fork → Prop} {cfg : ChainConfig} :
    {start : Benv} → {future : BlockChain} → MidHistoryTraceIn F cfg start future → List Exec.Frame
  | _, _, .tail _ cut => cut.after.settledFrames
  | _, _, .step prior block => prior.txFrames ++ block.bodyTrace.transactions.settledFrames

/-! ## System stages -/

/-- The system-message frames of a mid history: its remainder's request stage, then each later block's system stages. -/
def MidHistoryTraceIn.systemRawFrames {F : Fork → Prop} {cfg : ChainConfig} :
    {start : Benv} → {future : BlockChain} → MidHistoryTraceIn F cfg start future → List Exec.Deriv
  | _, _, .tail block _ => block.bodyTrace.requests.rawFrames
  | _, _, .step prior block => prior.systemRawFrames ++ block.systemRawFrames

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
