import Blanc.ExecutionHistory

/-!
Header commitments recovered from the checks of the original configured block
transition. The selected fork and deterministic body result identify the
checked output with the output already retained by the supplied trace.
-/

namespace Blanc.ExecutionTrace

open Jaune

/-- The original successful transition checked these three header commitments
against this trace's actual body output. No equality of independently supplied
tries or body outputs is required. -/
theorem ConfiguredBlockTraceIn.headerCommitments
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTraceIn F cfg pre post) :
    trace.block.header.receiptRoot = getReceiptRoot trace.blockOutput ∧
      trace.block.header.bloom = logsBloom trace.blockOutput.blockLogs ∧
      trace.block.header.txsRoot = getTransactionsRoot trace.blockOutput := by
  obtain ⟨fork, hFork, hScheduled⟩ := stateTransitionUsing_scheduled_ok trace.transition
  have hForkEq : fork = trace.fork := Except.ok.inj (hFork.symm.trans trace.forkAt)
  subst fork
  have hCore := stateTransitionScheduledE_eq_ok_iff.mp hScheduled
  unfold stateTransitionCoreE at hCore
  obtain ⟨_, _, hCore⟩ := Except.bind_eq_ok hCore
  obtain ⟨_, _, hCore⟩ := Except.bind_eq_ok hCore
  obtain ⟨⟨bodyState, blockOutput⟩, hBody, hCore⟩ := Except.bind_eq_ok hCore
  have hBodyEq := Except.mapError_eq_ok_iff.mp hBody
  rw [trace.bodyRun] at hBodyEq
  cases Except.ok.inj hBodyEq
  dsimp only at hCore
  obtain ⟨checked, hChecks, _⟩ := Except.bind_eq_ok hCore
  cases checked
  have hChecks := Except.mapError_eq_ok_iff.mp hChecks
  unfold stateTransitionChecks at hChecks
  dsimp only at hChecks
  by_cases hGas : max trace.blockOutput.blockGasUsed trace.blockOutput.blockStateGasUsed ≠
      trace.block.header.gasUsed
  · rw [ite_eq_left hGas] at hChecks
    obtain ⟨_, hError, _⟩ := Except.bind_eq_ok hChecks
    cases hError
  rw [ite_eq_right hGas] at hChecks
  by_cases hTxs : getTransactionsRoot trace.blockOutput ≠ trace.block.header.txsRoot
  · rw [ite_eq_left hTxs] at hChecks
    obtain ⟨_, hError, _⟩ := Except.bind_eq_ok hChecks
    cases hError
  rw [ite_eq_right hTxs] at hChecks
  by_cases hState : trace.bodyState.root ≠ trace.block.header.stateRoot
  · rw [ite_eq_left hState] at hChecks
    obtain ⟨_, hError, _⟩ := Except.bind_eq_ok hChecks
    cases hError
  rw [ite_eq_right hState] at hChecks
  by_cases hReceipt : getReceiptRoot trace.blockOutput ≠ trace.block.header.receiptRoot
  · rw [ite_eq_left hReceipt] at hChecks
    obtain ⟨_, hError, _⟩ := Except.bind_eq_ok hChecks
    cases hError
  rw [ite_eq_right hReceipt] at hChecks
  by_cases hBloom : logsBloom trace.blockOutput.blockLogs ≠ trace.block.header.bloom
  · rw [ite_eq_left hBloom] at hChecks
    obtain ⟨_, hError, _⟩ := Except.bind_eq_ok hChecks
    cases hError
  simp only [ne_eq, not_not] at hReceipt hBloom hTxs
  exact ⟨hReceipt.symm, hBloom.symm, hTxs.symm⟩

/-- The receipt root checked by the original configured transition. -/
theorem ConfiguredBlockTraceIn.receiptRoot
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTraceIn F cfg pre post) :
    trace.block.header.receiptRoot = getReceiptRoot trace.blockOutput :=
  trace.headerCommitments.1

/-- The logs bloom checked by the original configured transition. -/
theorem ConfiguredBlockTraceIn.bloom
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTraceIn F cfg pre post) :
    trace.block.header.bloom = logsBloom trace.blockOutput.blockLogs :=
  trace.headerCommitments.2.1

/-- The transaction root checked by the original configured transition. -/
theorem ConfiguredBlockTraceIn.txsRoot
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTraceIn F cfg pre post) :
    trace.block.header.txsRoot = getTransactionsRoot trace.blockOutput :=
  trace.headerCommitments.2.2

end Blanc.ExecutionTrace
