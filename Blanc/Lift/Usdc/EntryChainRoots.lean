import Blanc.Lift.Usdc.EntryTarget
import Blanc.Lift.RootReady
import Blanc.ExecutionAccountingPositionalHistory

/-!
# USDC's entry frames carry the ledger view along a mid history

`usdc_viewSettled`: the settled entry frames of a mid history from a state with the proxy installed at `T`
carry the proxy's ledger view to the end, and to the entry of every settled frame no earlier non-static frame
at `T` encloses, whenever the frames concerned are allowed (`EntryAllowed`). The deletion exclusion
`OutputNotDeleted` is the one remaining fact about the whole history.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace Blanc.ExecutionAccountingReplay

section

variable {T : Adr}

local notation "Ca" => viewCarrier T ledgerView (EntryGood T) (EntryAllowed T) entryKeep
local notation "Ob" => viewObservation T ledgerView (EntryObs T) (EntryGood T) (EntryAllowed T) entryKeep

/-- Whole-frame accounting of every derivation at the proxy. -/
theorem entry_core : Exec.Fa (Exec.WknSem T entrySem
    (fun pc s d e _ => Exec.CoreAccountingIn HistFork T entrySem (fun _ _ => True) Ca Ob pc s d e)) :=
  Exec.coreAccountingIn HistFork T entrySem (fun _ _ => True) Ca Ob viewCarrier_append
    (fun _ _ => ()) (fun _ _ _ => rfl)
    (fun f hf => ite_eq_right fun h => hf h.1) HistFork.stateGas_none
    (fun hrun target deeper => entryTarget hrun target deeper)

/-- Positional accounting of every derivation at the proxy. -/
theorem entry_positional : Exec.Fa (Exec.WknSem T entrySem
    (fun pc s d e _ => Exec.PositionalAccountingIn HistFork T entrySem (fun _ _ => True) Ca Ob
      (fun A => A.sevm.currentTarget = T ∧ A.sevm.isStatic = false) pc s d e)) :=
  Exec.positionalAccountingIn HistFork.stateGas_none (fun _ _ => rfl) entry_ofStateGet
    (fun f hf => ite_eq_right fun h => hf h.1) viewCarrier_append (fun _ op => op.1) entry_core
    (fun _ target _ => Exec.PositionalAccounting.wholeFrameTarget HistFork.stateGas_none
      entry_ofStateGet entry_core target)

/-- **The settled roots carry the view**, from the deletion exclusion and the proxy at the start. -/
theorem usdc_viewSettled {cfg : ChainConfig} {start : Benv} {future : BlockChain}
    (trace : MidHistoryTraceIn HistFork cfg start future)
    (capabilities : BodyStageCapabilities HistFork)
    (installed : start.state.getCode T = Proxy.code) (notDeleted : trace.OutputNotDeleted T) :
    ViewSettled T ledgerView (EntryObs T) (EntryGood T) (EntryAllowed T) entryKeep
      (ledgerView (wordsAt T start.state)) (ledgerView (wordsAt T future.state))
      trace.settledFrames := by
  rw [trace.settledFrames_eq]
  refine viewSettled_of_roots (F := HistFork) (sem := entrySem) (entry := fun _ _ => True)
    (fun R ready => ?_) (fun R ready before f after split noOpaque => ?_)
    (Blanc.Lift.MidHistoryTraceIn.rootChain trace (fun _ h => HistFork.stateGas_none h) installed proxy_toList_ne_nil
      proxy_not_delegation notDeleted)
    (Blanc.Lift.MidHistoryTraceIn.rootsReady trace capabilities (C := Proxy.code) rfl installed proxy_toList_ne_nil
      proxy_not_delegation notDeleted)
  · obtain ⟨fork, at_, admitted, bound, -⟩ := ready
    exact (entry_core R.pc R.sevm R.pre R.out R.run at_ R.run R.committed fork at_ admitted).2 bound
  · obtain ⟨fork, at_, admitted, bound, -⟩ := ready
    obtain ⟨steps, replay, observed⟩ := entry_positional R.pc R.sevm R.pre R.out R.run at_ R.run
      R.committed fork at_ admitted bound before f after split noOpaque
    exact ⟨steps, replay, observed⟩

end

end Blanc.Lift.Usdc
