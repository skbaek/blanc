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

/-- Actual retained terminal safety preserves Proxy/V1 control through one
transaction. Both accounts may have been created earlier in the block; their
code is installed at this transaction's entry, and no created-set exclusion is
required. Actual root entries, proxy classification and implementation safety
are derived by the shared certificate and original-history producers. -/
theorem ConfiguredHistoryTraceIn.v1_transaction_preserves_retained
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (rootsIn : ∀ R ∈ trace.settledRoots, R ∈ history.settledRoots)
    (hsg : benv.stat.rules.stateGas = none)
    (proxy : benv.state.getCode P = Proxy.code)
    (impl : benv.state.getCode I = ImplV1.code)
    (slot : ((benv.state.getStor P).get implSlot).toAdr = I)
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
  have proxyEntry := trace.settledRoots_entry_code_cell
    proxy proxyFam.ne_nil proxyFam.not_delegation implSlot
  have implEntry := trace.settledRoots_entry_code_cell
    impl implFam.ne_nil implFam.not_delegation implSlot
  have rootSlot (R : Exec.Frame) (member : R ∈ trace.settledRoots) :
      ((R.pre.getStor P).get implSlot).toAdr = I := by
    rw [(proxyEntry R member).2]
    exact slot
  have safe : ∀ R ∈ trace.settledRoots, ∀ N ∈ Exec.retainedNodes R.run,
      N.sevm.currentTarget = P → ¬ Linst.At N.sevm.code N.pc .selfdestruct := by
    intro R member
    have classified := ConfiguredHistoryTraceIn.settledRoot_proxyV1_context_of_freshKeys
      history capabilities initialApart fresh bal (rootsIn R member)
      (proxyEntry R member).1 (implEntry R member).1 (rootSlot R member)
      (noUpgraded R member)
    apply ConfiguredHistoryTraceIn.settledRoot_usdcContext_terminal_safe
      history capabilities (rootsIn R member)
    intro N retained target
    rcases (classified N retained).2.1 target with proxyCode | implCode
    · exact .inl proxyCode
    · exact .inr (.inl implCode)
  have noDel := trace.not_deleted_of_retained_terminals hsg safe
  have carried := trace.cell_property_of_settledRoots implSlot hsg proxy
    proxyFam.ne_nil proxyFam.not_delegation noDel
    (fun value => value = (benv.state.getStor P).get implSlot)
    (by
      intro R member _
      exact (ConfiguredHistoryTraceIn.settledRoot_proxyV1_implSlot_eq_of_freshKeys
        history capabilities initialApart fresh bal (rootsIn R member)
        (proxyEntry R member).1 (implEntry R member).1 (rootSlot R member)
        (noUpgraded R member)).trans (proxyEntry R member).2)
    rfl
  have implPreserved := trace.code_preserved_of_installedCert ImplV1.cert_check
    ImplV1.cert_callOnly ImplV1.cert_noSelfdestruct implFam.not_delegation
    implFam.ne_nil hsg impl
  refine ⟨noDel, carried.2, implPreserved.2, carried.1, ?_⟩
  intro R member
  exact ⟨(proxyEntry R member).1, (implEntry R member).1, (proxyEntry R member).2⟩

/-- Original stronger interface, retained for callers carrying created-set
exclusions. The retained-safety producer no longer needs either exclusion. -/
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
  exact ConfiguredHistoryTraceIn.v1_transaction_preserves_retained
    history capabilities bal initialApart fresh trace rootsIn hsg proxy impl slot noUpgraded

/-- The stronger retained-safety transaction invariant composes over the exact
ordered list without created-account exclusions for either protected account. -/
theorem ConfiguredHistoryTraceIn.v1_transactions_preserve_retained
    {txs : List (Nat × Tx)} {benv finalBenv : Benv} {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (rootsIn : ∀ R ∈ trace.settledRoots, R ∈ history.settledRoots)
    (hsg : benv.stat.rules.stateGas = none)
    (proxy : benv.state.getCode P = Proxy.code)
    (impl : benv.state.getCode I = ImplV1.code)
    (slot : ((benv.state.getStor P).get implSlot).toAdr = I)
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
    have headResult := ConfiguredHistoryTraceIn.v1_transaction_preserves_retained
      history capabilities bal initialApart fresh head
      (fun R member => rootsIn R (List.mem_append_left _ member))
      hsg proxy impl slot
      (fun R member => noUpgraded R (List.mem_append_left _ member))
    have tailResult := ih (fun R member => rootsIn R (List.mem_append_right _ member))
      hsg headResult.2.1 headResult.2.2.1
      ((congrArg B256.toAdr headResult.2.2.2.1).trans slot)
      (fun R member => noUpgraded R (List.mem_append_right _ member))
    refine ⟨⟨headResult.1, tailResult.1⟩, tailResult.2.1, tailResult.2.2.1,
      tailResult.2.2.2.1.trans headResult.2.2.2.1, ?_⟩
    intro R member
    rcases List.mem_append.mp member with earlier | later
    · exact headResult.2.2.2.2 R earlier
    · obtain ⟨codeP, codeI, cell⟩ := tailResult.2.2.2.2 R later
      exact ⟨codeP, codeI, cell.trans headResult.2.2.2.1⟩

/-- Original transaction-list interface with its statement preserved. -/
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
  exact ConfiguredHistoryTraceIn.v1_transactions_preserve_retained
    history capabilities bal initialApart fresh trace rootsIn hsg proxy impl slot noUpgraded

end Blanc.Lift.Usdc
