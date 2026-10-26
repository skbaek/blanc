import Blanc.ExecutionSettledRootEntry
import Blanc.Lift.Usdc.V1RetainedContext
import Blanc.ExecutionNoDelTransaction

/-! Actual transaction continuity of the original Proxy/V1 control state. -/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

variable {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
  (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
  (capabilities : BodyStageCapabilities F)
  (bal : ∀ {fork}, F fork → fork.ruleSet.bal = none)
  {P I : Adr} {initial : HistoricalMappingKey → Prop}
  (initialApart : SlotFootprint.Apart HistoricalMappingKey.slot fixedSlots initial)
  (fresh : V1MappingFreshKeys P history initial)

include capabilities bal initialApart fresh

/-- One actual admitted transaction carries both installed codes and the exact
implementation word through settlement. Root entry facts are derived from this
transaction; only its retained upgrade logs are excluded. -/
theorem ConfiguredHistoryTraceIn.v1_transaction_preserves
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (rootsIn : ∀ R ∈ trace.settledRoots, R ∈ history.settledRoots)
    (hsg : benv.stat.rules.stateGas = none)
    (proxy : benv.state.getCode P = Proxy.code)
    (impl : benv.state.getCode I = ImplV1.code)
    (slot : ((benv.state.getStor P).get implSlot).toAdr = I)
    (notCreatedP : P ∉ benv.createdAccounts)
    (notCreatedI : I ∉ benv.createdAccounts)
    (noUpgraded : ∀ R ∈ trace.settledRoots, ¬ ∃ entry ∈ R.post.logs,
      entry.address = P ∧ entry.topics = [Proxy.upgradedTopic]) :
    P ∉ trace.messageOut.accountsToDelete ∧
      state.getCode P = Proxy.code ∧ state.getCode I = ImplV1.code ∧
      (state.getStor P).get implSlot = (benv.state.getStor P).get implSlot ∧
      ∀ R ∈ trace.settledRoots,
        R.pre.getCode P = Proxy.code ∧ R.pre.getCode I = ImplV1.code ∧
        (R.pre.getStor P).get implSlot = (benv.state.getStor P).get implSlot := by
  have proxyFam : UsdcContextCode Proxy.code := .inl rfl
  have implFam : UsdcContextCode ImplV1.code := .inr (.inl rfl)
  have implEntry := trace.settledRoots_entry_code_cell
    impl implFam.ne_nil implFam.not_delegation implSlot
  have carried := trace.cell_noDel_of_settledRoots implSlot hsg proxy
    proxyFam.ne_nil proxyFam.not_delegation notCreatedP
    (fun value => value = (benv.state.getStor P).get implSlot)
    (by
      intro R member rootProxy rootCell
      have rootImpl := (implEntry R member).1
      have rootSlot : ((R.pre.getStor P).get implSlot).toAdr = I := by
        rw [rootCell]
        exact slot
      refine ⟨?_, ?_⟩
      · intro rootNoDel
        exact (ConfiguredHistoryTraceIn.settledRoot_proxyV1_preserves_of_freshKeys
          history capabilities initialApart fresh bal (rootsIn R member)
          rootProxy rootImpl rootSlot (noUpgraded R member) rootNoDel).1
      · exact (ConfiguredHistoryTraceIn.settledRoot_proxyV1_implSlot_eq_of_freshKeys
          history capabilities initialApart fresh bal (rootsIn R member)
          rootProxy rootImpl rootSlot (noUpgraded R member)).trans rootCell)
    rfl
  have implPreserved := trace.noDel_of_installedCert ImplV1.cert_check
    ImplV1.cert_callOnly ImplV1.cert_noSelfdestruct implFam.not_delegation
    implFam.ne_nil hsg impl notCreatedI
  refine ⟨carried.1, carried.2.2.1, implPreserved.2.2, carried.2.1, ?_⟩
  intro R member
  exact ⟨(carried.2.2.2 R member).1, (implEntry R member).1,
    (carried.2.2.2 R member).2⟩

/-- The real ordered transaction sequence propagates Proxy/V1 entry control
from its initial state, including empty retained-root lists and failed calls.
No per-transaction or per-root installed-code/slot oracle is required. -/
theorem ConfiguredHistoryTraceIn.v1_transactions_preserve
    {txs : List (Nat × Tx)} {benv finalBenv : Benv} {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (rootsIn : ∀ R ∈ trace.settledRoots, R ∈ history.settledRoots)
    (hsg : benv.stat.rules.stateGas = none)
    (proxy : benv.state.getCode P = Proxy.code)
    (impl : benv.state.getCode I = ImplV1.code)
    (slot : ((benv.state.getStor P).get implSlot).toAdr = I)
    (notCreatedP : P ∉ benv.createdAccounts)
    (notCreatedI : I ∉ benv.createdAccounts)
    (noUpgraded : ∀ R ∈ trace.settledRoots, ¬ ∃ entry ∈ R.post.logs,
      entry.address = P ∧ entry.topics = [Proxy.upgradedTopic]) :
    trace.NoDelScheduled P ∧
      finalBenv.state.getCode P = Proxy.code ∧ finalBenv.state.getCode I = ImplV1.code ∧
      (finalBenv.state.getStor P).get implSlot = (benv.state.getStor P).get implSlot ∧
      ∀ R ∈ trace.settledRoots,
        R.pre.getCode P = Proxy.code ∧ R.pre.getCode I = ImplV1.code ∧
        (R.pre.getStor P).get implSlot = (benv.state.getStor P).get implSlot := by
  induction trace with
  | nil => exact ⟨trivial, proxy, impl, rfl, by intro R member; cases member⟩
  | cons head tail ih =>
    have headResult := ConfiguredHistoryTraceIn.v1_transaction_preserves
      history capabilities bal initialApart fresh head
      (fun R member => rootsIn R (List.mem_append_left _ member))
      hsg proxy impl slot notCreatedP notCreatedI
      (fun R member => noUpgraded R (List.mem_append_left _ member))
    have tailResult := ih (fun R member => rootsIn R (List.mem_append_right _ member))
      hsg headResult.2.1 headResult.2.2.1
      ((congrArg B256.toAdr headResult.2.2.2.1).trans slot) notCreatedP notCreatedI
      (fun R member => noUpgraded R (List.mem_append_right _ member))
    refine ⟨⟨headResult.1, tailResult.1⟩, tailResult.2.1, tailResult.2.2.1,
      tailResult.2.2.2.1.trans headResult.2.2.2.1, ?_⟩
    intro R member
    rcases List.mem_append.mp member with earlier | later
    · exact headResult.2.2.2.2 R earlier
    · obtain ⟨codeP, codeI, cell⟩ := tailResult.2.2.2.2 R later
      exact ⟨codeP, codeI, cell.trans headResult.2.2.2.1⟩

end Blanc.Lift.Usdc
