import Blanc.ExecutionRetainedNoDelTransaction
import Blanc.ExecutionHistoryCommittedCell

/-!
No-deletion and installed-code survival through actual enabled body stages
and configured histories, from conditional laws on their own settled roots.
-/

namespace Blanc.ExecutionTrace

open Jaune

/-- An actual system message uses its own complete-settlement roots. -/
theorem SystemMessageTrace.noDel_of_settledRoots {wa : Adr} {C : ByteArray}
    (hCdel : ¬ isValidDelegation C) (hCne : C.toList ≠ [])
    {benv : Benv} {target : Adr} {data : Bytes} {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out)
    (hsg : benv.stat.rules.stateGas = none)
    (installed : benv.state.getCode wa = C) (notCreated : wa ∉ benv.createdAccounts)
    (roots : ∀ R ∈ trace.settledRoots,
      Devm.NoDel wa R.pre → Devm.NoDel wa R.post) :
    wa ∉ out.accountsToDelete ∧ state.getCode wa = C := by
  exact trace.message.noDel_of_settledRoots hCdel hsg installed (fun _ => ⟨rfl, rfl⟩)
    ⟨notCreated, show (benv.state.getCode wa).toList ≠ [] by rw [installed]; exact hCne⟩
    AdrSet.not_mem_empty roots

/-- Both actual request outputs exclude deletion, in their original order. -/
theorem RequestsTrace.noDel_of_settledRoots {wa : Adr} {C : ByteArray}
    (hCdel : ¬ isValidDelegation C) (hCne : C.toList ≠ [])
    {benv : Benv} {bout : BlockOutput} {state : State} {bout' : BlockOutput}
    (trace : RequestsTrace benv bout state bout')
    (hsg : benv.stat.rules.stateGas = none)
    (installed : benv.state.getCode wa = C) (notCreated : wa ∉ benv.createdAccounts)
    (roots : ∀ R ∈ trace.settledRoots,
      Devm.NoDel wa R.pre → Devm.NoDel wa R.post) :
    wa ∉ trace.withdrawalOut.accountsToDelete ∧
      wa ∉ trace.consolidationOut.accountsToDelete ∧ state.getCode wa = C := by
  obtain ⟨withdrawal, withdrawalCode⟩ := trace.withdrawal.noDel_of_settledRoots
    hCdel hCne hsg installed notCreated
    (fun R member => roots R (List.mem_append_left _ member))
  obtain ⟨consolidation, consolidationCode⟩ := trace.consolidation.noDel_of_settledRoots
    (benv := benv.withState trace.withdrawalState) hCdel hCne hsg withdrawalCode notCreated
    (fun R member => roots R (List.mem_append_right _ member))
  exact ⟨withdrawal, consolidation, by rw [trace.state_eq_consolidationState]; exact consolidationCode⟩

/-- Actual enabled beacon calls remain present; skipped stages are unchanged. -/
theorem BeaconStageTrace.code_of_settledRoots {wa : Adr} {C : ByteArray}
    (hCdel : ¬ isValidDelegation C) (hCne : C.toList ≠ [])
    {rules : ForkRules} {benv : Benv} {state : State} {bal : BalBuilder}
    (trace : BeaconStageTrace rules benv state bal)
    (hsg : benv.stat.rules.stateGas = none)
    (installed : benv.state.getCode wa = C) (notCreated : wa ∉ benv.createdAccounts)
    (roots : ∀ R ∈ trace.settledRoots,
      Devm.NoDel wa R.pre → Devm.NoDel wa R.post) : state.getCode wa = C := by
  cases trace with
  | skipped => exact installed
  | called _ _ message _ _ =>
    exact (message.noDel_of_settledRoots hCdel hCne hsg installed notCreated roots).2

/-- Actual enabled history-storage calls remain in the selected root law. -/
theorem HistoryStageTrace.code_of_settledRoots {wa : Adr} {C : ByteArray}
    (hCdel : ¬ isValidDelegation C) (hCne : C.toList ≠ [])
    {rules : ForkRules} {benv : Benv} {inputBal : BalBuilder} {state : State} {bal : BalBuilder}
    (trace : HistoryStageTrace rules benv inputBal state bal)
    (hsg : benv.stat.rules.stateGas = none)
    (installed : benv.state.getCode wa = C) (notCreated : wa ∉ benv.createdAccounts)
    (roots : ∀ R ∈ trace.settledRoots,
      Devm.NoDel wa R.pre → Devm.NoDel wa R.post) : state.getCode wa = C := by
  cases trace with
  | skipped => exact installed
  | called _ _ _ _ message _ _ =>
    exact (message.noDel_of_settledRoots hCdel hCne hsg installed notCreated roots).2

/-- The actual request stage retains both enabled request calls. -/
theorem RequestStageTrace.code_of_settledRoots {wa : Adr} {C : ByteArray}
    (hCdel : ¬ isValidDelegation C) (hCne : C.toList ≠ [])
    {rules : ForkRules} {benv : Benv} {bout : BlockOutput} {state : State} {bout' : BlockOutput}
    (trace : RequestStageTrace rules benv bout state bout')
    (hsg : benv.stat.rules.stateGas = none)
    (installed : benv.state.getCode wa = C) (notCreated : wa ∉ benv.createdAccounts)
    (roots : ∀ R ∈ trace.settledRoots,
      Devm.NoDel wa R.pre → Devm.NoDel wa R.post) : state.getCode wa = C := by
  cases trace with
  | skipped => exact installed
  | called _ requests _ =>
    exact (requests.noDel_of_settledRoots hCdel hCne hsg installed notCreated roots).2.2

/-- Opening calls provide the actual transaction entry code; the registered
body cell transport supplies withdrawals, requests, rewards and finalization. -/
theorem StagedBodyTrace.noDel_of_settledRoots {wa : Adr} {C : ByteArray}
    (hCdel : ¬ isValidDelegation C) (hCne : C.toList ≠ [])
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout)
    (hsg : benv.stat.rules.stateGas = none)
    (installed : benv.state.getCode wa = C) (notCreated : wa ∉ benv.createdAccounts)
    (roots : ∀ R ∈ trace.settledRoots,
      Devm.NoDel wa R.pre → Devm.NoDel wa R.post) :
    trace.transactions.NoDelScheduled wa ∧ state.getCode wa = C := by
  have beaconRoots : ∀ R ∈ trace.beacon.settledRoots,
      Devm.NoDel wa R.pre → Devm.NoDel wa R.post := by
    intro R member
    exact roots R (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ member)))
  have historyRoots : ∀ R ∈ trace.history.settledRoots,
      Devm.NoDel wa R.pre → Devm.NoDel wa R.post := by
    intro R member
    exact roots R (List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_right _ member)))
  have transactionRoots : ∀ R ∈ trace.transactions.settledRoots,
      Devm.NoDel wa R.pre → Devm.NoDel wa R.post := by
    intro R member
    exact roots R (List.mem_append_left _ (List.mem_append_right _ member))
  have beaconCode := trace.beacon.code_of_settledRoots hCdel hCne hsg installed
    notCreated beaconRoots
  have historyCode := trace.history.code_of_settledRoots
    (benv := benv.withState trace.beaconState) hCdel hCne hsg beaconCode notCreated historyRoots
  have transactions := trace.transactions.noDel_of_settledRoots
    hCdel hCne hsg historyCode notCreated transactionRoots
  refine ⟨transactions.1, ?_⟩
  exact (trace.cell_property_of_settledRoots 0 hsg installed hCne hCdel
    ((trace.transactions.outputNotDeleted_iff_noDelScheduled wa).mpr transactions.1)
    (fun _ => True) (by intro R member ready; trivial) trivial).2

/-- A selected block uses its real stage roots and actual fork capability. -/
theorem ConfiguredBlockTraceIn.noDel_of_settledRoots {wa : Adr} {C : ByteArray}
    (hCdel : ¬ isValidDelegation C) (hCne : C.toList ≠ [])
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTraceIn F cfg pre post)
    (capabilities : BodyStageCapabilities F) (installed : pre.state.getCode wa = C)
    (roots : ∀ R ∈ trace.settledRoots,
      Devm.NoDel wa R.pre → Devm.NoDel wa R.post) :
    trace.NoDelScheduled wa ∧ post.state.getCode wa = C := by
  obtain ⟨scheduled, code⟩ := trace.bodyTrace.noDel_of_settledRoots hCdel hCne
    (capabilities.stateGas_none trace.forkIn) installed AdrSet.not_mem_empty roots
  exact ⟨scheduled, by rw [trace.postEq]; exact code⟩

/-- Conditional preservation at original settled roots composes along the
same configured history, preserving every actual transaction deletion output. -/
theorem ConfiguredHistoryTraceIn.noDel_of_settledRoots {wa : Adr} {C : ByteArray}
    (hCdel : ¬ isValidDelegation C) (hCne : C.toList ≠ [])
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) (installed : checkpoint.state.getCode wa = C)
    (roots : ∀ R ∈ history.settledRoots,
      Devm.NoDel wa R.pre → Devm.NoDel wa R.post) :
    history.NoDelScheduled wa ∧ future.state.getCode wa = C := by
  induction history with
  | refl => exact ⟨trivial, installed⟩
  | step prior block ih =>
    have priorRoots : ∀ R ∈ prior.settledRoots,
        Devm.NoDel wa R.pre → Devm.NoDel wa R.post :=
      fun R member => roots R (List.mem_append_left _ member)
    have blockRoots : ∀ R ∈ block.settledRoots,
        Devm.NoDel wa R.pre → Devm.NoDel wa R.post :=
      fun R member => roots R (List.mem_append_right _ member)
    obtain ⟨priorScheduled, currentCode⟩ := ih priorRoots
    obtain ⟨blockScheduled, finalCode⟩ := block.noDel_of_settledRoots hCdel hCne
      capabilities currentCode blockRoots
    exact ⟨⟨priorScheduled, blockScheduled⟩, finalCode⟩

/-- The same root law supplies the actual output predicate used by cell history. -/
theorem ConfiguredHistoryTraceIn.outputNotDeleted_of_settledRoots {wa : Adr} {C : ByteArray}
    (hCdel : ¬ isValidDelegation C) (hCne : C.toList ≠ [])
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) (installed : checkpoint.state.getCode wa = C)
    (roots : ∀ R ∈ history.settledRoots,
      Devm.NoDel wa R.pre → Devm.NoDel wa R.post) :
    history.OutputNotDeleted wa ∧ future.state.getCode wa = C := by
  have result := history.noDel_of_settledRoots hCdel hCne capabilities installed roots
  exact ⟨(history.outputNotDeleted_iff_noDelScheduled wa).mpr result.1, result.2⟩

end Blanc.ExecutionTrace
