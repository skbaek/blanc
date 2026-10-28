import Blanc.ExecutionInCodeImage
import Blanc.ExecutionMidHistoryIn
import Blanc.Lift.CallChildren
import Blanc.ExecutionTraceRootCallers
import Blanc.ExecutionMidHistoryInCallerExclusion
import Blanc.ExecutionHistoryCommittedCuts
import Blanc.ExecutionSenderRootCallers

/-!
# Retained caller provenance for selected-domain whole and mid-block histories

These are settlement-forest facts. They impose no fork capability, code image,
storage invariant or successful-outcome assumption beyond the retained trace.
The caller's root and direct-child obligations remain explicit.
-/

namespace Blanc.ExecutionTrace

open Jaune



/-- The caller fold over a selected fork-domain history. -/
theorem ConfiguredHistoryTraceIn.settledFrames_callerTarget_of_children
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    {p ca : Adr} {Q : Sevm → Prop} (trace : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (roots : ∀ R ∈ trace.settledRoots, CallerTarget p ca Q R.sevm)
    (children : ∀ G ∈ trace.settledFrames, CallerChildren p ca Q G.sevm (Exec.childFrames G.run)) :
    ∀ G ∈ trace.settledFrames, CallerTarget p ca Q G.sevm := by
  rw [trace.settledFrames_eq] at children ⊢
  exact rootFrames_callerTarget_of_children trace.settledRoots roots children

/-- The same caller fold starts at the actual transaction cut, without including
the deployment transaction or earlier transactions in its retained forest. -/
theorem MidHistoryTraceIn.settledFrames_callerTarget_of_children
    {F : Fork → Prop} {cfg : ChainConfig} {start : Benv} {future : BlockChain}
    {p ca : Adr} {Q : Sevm → Prop} (trace : MidHistoryTraceIn F cfg start future)
    (roots : ∀ R ∈ trace.settledRoots, CallerTarget p ca Q R.sevm)
    (children : ∀ G ∈ trace.settledFrames, CallerChildren p ca Q G.sevm (Exec.childFrames G.run)) :
    ∀ G ∈ trace.settledFrames, CallerTarget p ca Q G.sevm := by
  rw [trace.settledFrames_eq] at children ⊢
  exact rootFrames_callerTarget_of_children trace.settledRoots roots children

/-- A transaction message root carries its checked sender, on every fork. -/
theorem ApplyTransactionsTrace.settledRoots_caller_ne_of_noSender
    {a : Adr} {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (senders : trace.NoSenderAt a) :
    ∀ R ∈ trace.settledRoots, R.sevm.caller ≠ a :=
  trace.settledRoots_caller_ne_of_noSenderAt senders




/-- Root caller exclusion uses checked senders and the distinguished system address,
not EIP-3607 or a modern-fork assumption. -/
theorem StagedBodyTrace.settledRoots_caller_ne_of_noSender
    {a : Adr} {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout)
    (senders : trace.transactions.NoSenderAt a) (notSystem : a ≠ systemAddress) :
    ∀ R ∈ trace.settledRoots, R.sevm.caller ≠ a :=
  trace.settledRoots_caller_ne_of_noSenderAt senders notSystem

/-- Checked-sender exclusion covers precisely the suffix and subsequent blocks.
System roots are handled separately, including requests in the initial suffix. -/
theorem MidHistoryTraceIn.settledRoots_caller_ne_of_noSender
    {F : Fork → Prop} {cfg : ChainConfig} {start : Benv} {future : BlockChain}
    {a : Adr} (trace : MidHistoryTraceIn F cfg start future)
    (senders : trace.NoSenderAt a) (notSystem : a ≠ systemAddress) :
    ∀ R ∈ trace.settledRoots, R.sevm.caller ≠ a := by
  induction trace with
  | tail block cut =>
    intro R member same
    rcases List.mem_append.mp member with member | member
    · exact cut.after.settledRoots_caller_ne_of_noSender senders R member same
    · exact notSystem (same.symm.trans (block.bodyTrace.requests.settledRoots_caller R member))
  | step prior block ih =>
    intro R member
    rcases List.mem_append.mp member with member | member
    · exact ih senders.1 R member
    · exact block.bodyTrace.settledRoots_caller_ne_of_noSender senders.2 notSystem R member

end Blanc.ExecutionTrace
