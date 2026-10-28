import Blanc.Lift.Usdc.ProxyRetainedNoDel

/-!
Complete allowed-family coverage after the last implementation creation.
The initial runtime family is carried through the original history; guarded
upgrades select it directly, without an additional upgrade census.
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace

/-- Installed USDC runtime and conditional library code reach every retained
node of the same actual root. -/
private theorem runtimeReady_at_retainedNode {e : UsdcDeployedEntry}
    (family : UsdcImplCode e.code) {R : Exec.Frame}
    (installed : R.pre.getCode e.adr = e.code)
    (library : e.code = Impl.code → R.pre.getCode usdcLib = Lib.code)
    {N : Exec.Deriv} (retained : N ∈ Exec.retainedNodes R.run) :
    e.RuntimeReady N.devm := by
  have raw := (Exec.retainedNodes_sublist_rawNodes R.run).subset retained
  refine ⟨Exec.rawNodes_getCode R.run installed family.context.ne_nil N raw, ?_⟩
  intro implementation
  have libFamily : UsdcContextCode Lib.code := .inr (.inr (.inr (.inr (.inr rfl))))
  exact Exec.rawNodes_getCode R.run (library implementation) libFamily.ne_nil N raw

/-- Coverage of the allowed addresses selects an originally installed entry
at each guarded upgrade in this actual transaction. -/
theorem TransactionTrace.usdc_origins_of_complete_available_family
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    {P : Adr} {W available : List UsdcDeployedEntry}
    (subset : ∀ e ∈ available, e ∈ W)
    (impls : ∀ e ∈ available, UsdcImplCode e.code)
    (complete : ∀ a ∈ F2prime.upgradeTargets, ∃ e ∈ available, a = e.adr)
    (ready : UsdcEntriesReady available benv.state) :
    UsdcTransactionOrigins P W trace ∧ UsdcGuardedInstallations P W trace.settledRoots := by
  have origins : UsdcTransactionOrigins P W trace := by
    intro R root N retained _ _ _ write _ _ allowed _
    obtain ⟨e, member, address⟩ := complete write.value.toAdr allowed
    have entry := ready e member
    have family := impls e member
    have installed := (trace.settledRoots_entry_code_cell entry.1 family.context.ne_nil
      family.context.not_delegation 0 R root).1
    have library : e.code = Impl.code → R.pre.getCode usdcLib = Lib.code := by
      intro implementation
      have libFamily : UsdcContextCode Lib.code := .inr (.inr (.inr (.inr (.inr rfl))))
      exact (trace.settledRoots_entry_code_cell (entry.2 implementation)
        libFamily.ne_nil libFamily.not_delegation 0 R root).1
    exact ⟨e, subset e member, address,
      runtimeReady_at_retainedNode family installed library retained,
      e.transactionOrigin_of_entry trace entry.1 entry.2⟩
  refine ⟨origins, ?_⟩
  intro R root N retained target code codeAddress write found key allowed nonempty
  obtain ⟨e, member, address, localReady, _⟩ :=
    origins R root N retained target code codeAddress write found key allowed nonempty
  exact ⟨e, member, address, localReady⟩

section CompleteFamily

variable {P : Adr} {W available : List UsdcDeployedEntry}
  (subset : ∀ e ∈ available, e ∈ W)
  (impls : ∀ e ∈ available, UsdcImplCode e.code)
  (complete : ∀ a ∈ F2prime.upgradeTargets, ∃ e ∈ available, a = e.adr)

include subset impls complete

/-- Complete settlement preserves the available family between successive
original transactions, including those with no retained execution root. -/
theorem ConfiguredHistoryTraceIn.transactions_origins_of_complete_available_family
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    (bal : ∀ {fork}, F fork → fork.ruleSet.bal = none)
    {txs : List (Nat × Tx)} {benv finalBenv : Benv} {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (rootsIn : ∀ R ∈ trace.settledRoots, R ∈ history.settledRoots)
    (hsg : benv.stat.rules.stateGas = none)
    (ready : UsdcEntriesReady available benv.state) :
    UsdcTransactionsOrigins P W trace ∧
      UsdcGuardedInstallations P W trace.settledRoots ∧
      UsdcEntriesReady available finalBenv.state := by
  induction trace with
  | nil =>
    exact ⟨trivial, (fun R member => nomatch member), ready⟩
  | cons head tail ih =>
    have first := TransactionTrace.usdc_origins_of_complete_available_family
      head (P := P) subset impls complete ready
    have after : UsdcEntriesReady available _ := fun e member =>
      (ConfiguredHistoryTraceIn.impl_transaction_preserves_retained history capabilities bal
        (impls e member) head (fun R root => rootsIn R (List.mem_append_left _ root))
        hsg (ready e member).1 (ready e member).2).2
    have rest := ih (fun R member => rootsIn R (List.mem_append_right _ member)) hsg after
    exact ⟨⟨first.1, rest.1⟩, UsdcGuardedInstallations.append first.2 rest.2.1, rest.2.2⟩

/-- A system message needs no upgrade census once all allowed implementations
are available; its wrapper preserves both their code and conditional library. -/
theorem SystemMessageTrace.usdc_complete_available_family
    {benv : Benv} {target : Adr} {data : Bytes} {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out)
    (hsg : benv.stat.rules.stateGas = none)
    (ready : UsdcEntriesReady available benv.state) :
    UsdcEntriesReady available state ∧ UsdcGuardedInstallations P W trace.settledRoots := by
  have entry {a : Adr} {C : ByteArray} (family : UsdcContextCode C)
      (present : benv.state.getCode a = C) (R : Exec.Frame) (root : R ∈ trace.settledRoots) :
      R.pre.getCode a = C := by
    exact (trace.message.settledRoots_entry_code_cell
      (by rw [systemTransactionMessage_benv_state]; exact present)
      family.ne_nil family.not_delegation 0 R root).1
  have finalCode {a : Adr} {C : ByteArray} (family : UsdcContextCode C)
      (present : benv.state.getCode a = C) : state.getCode a = C :=
    (trace.cell_property_of_settledRoots 0 hsg present family.ne_nil family.not_delegation
      (fun _ => True) (by intro R root initial; trivial) trivial).2
  have libFamily : UsdcContextCode Lib.code := .inr (.inr (.inr (.inr (.inr rfl))))
  refine ⟨?_, ?_⟩
  · intro e member
    exact ⟨finalCode (impls e member).context (ready e member).1,
      fun implementation => finalCode libFamily ((ready e member).2 implementation)⟩
  · intro R root N retained _ _ _ write _ _ allowed _
    obtain ⟨e, member, address⟩ := complete write.value.toAdr allowed
    exact ⟨e, subset e member, address, runtimeReady_at_retainedNode (impls e member)
      (entry (impls e member).context (ready e member).1 R root)
      (fun implementation => entry libFamily ((ready e member).2 implementation) R root) retained⟩

/-- The two requests execute in their original order and retain availability. -/
theorem RequestsTrace.usdc_complete_available_family
    {benv : Benv} {bout : BlockOutput} {state : State} {bout' : BlockOutput}
    (trace : RequestsTrace benv bout state bout')
    (hsg : benv.stat.rules.stateGas = none)
    (ready : UsdcEntriesReady available benv.state) :
    UsdcEntriesReady available state ∧ UsdcGuardedInstallations P W trace.settledRoots := by
  have withdrawal := SystemMessageTrace.usdc_complete_available_family
    (P := P) subset impls complete trace.withdrawal hsg ready
  have consolidation := SystemMessageTrace.usdc_complete_available_family
    (P := P) subset impls complete trace.consolidation hsg withdrawal.1
  exact ⟨trace.state_eq_consolidationState ▸ consolidation.1,
    UsdcGuardedInstallations.append withdrawal.2 consolidation.2⟩

/-- The enabled beacon stage uses the same complete family as transactions. -/
theorem BeaconStageTrace.usdc_complete_available_family
    {rules : ForkRules} {benv : Benv} {state : State} {outputBal : BalBuilder}
    (trace : BeaconStageTrace rules benv state outputBal)
    (hsg : benv.stat.rules.stateGas = none)
    (ready : UsdcEntriesReady available benv.state) :
    UsdcEntriesReady available state ∧ UsdcGuardedInstallations P W trace.settledRoots := by
  cases trace with
  | skipped => exact ⟨ready, fun R member => nomatch member⟩
  | called _ _ message _ _ =>
    exact SystemMessageTrace.usdc_complete_available_family subset impls complete message hsg ready

/-- Availability and guarded installations include the enabled history stage. -/
theorem HistoryStageTrace.usdc_complete_available_family
    {rules : ForkRules} {benv : Benv} {inputBal : BalBuilder} {state : State} {outputBal : BalBuilder}
    (trace : HistoryStageTrace rules benv inputBal state outputBal)
    (hsg : benv.stat.rules.stateGas = none)
    (ready : UsdcEntriesReady available benv.state) :
    UsdcEntriesReady available state ∧ UsdcGuardedInstallations P W trace.settledRoots := by
  cases trace with
  | skipped => exact ⟨ready, fun R member => nomatch member⟩
  | called _ _ _ _ message _ _ =>
    exact SystemMessageTrace.usdc_complete_available_family subset impls complete message hsg ready

/-- Availability and guarded installations include the enabled requests stage. -/
theorem RequestStageTrace.usdc_complete_available_family
    {rules : ForkRules} {benv : Benv} {bout : BlockOutput} {state : State} {bout' : BlockOutput}
    (trace : RequestStageTrace rules benv bout state bout')
    (hsg : benv.stat.rules.stateGas = none)
    (ready : UsdcEntriesReady available benv.state) :
    UsdcEntriesReady available state ∧ UsdcGuardedInstallations P W trace.settledRoots := by
  cases trace with
  | skipped => exact ⟨ready, fun R member => nomatch member⟩
  | called _ message _ =>
    exact RequestsTrace.usdc_complete_available_family subset impls complete message hsg ready

/-- Withdrawals and rewards preserve code while the actual request roots
derive their guarded installations from the complete available family. -/
theorem StagedBodyTrace.usdc_complete_available_family_after_transactions
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout)
    (hsg : benv.stat.rules.stateGas = none)
    (ready : UsdcEntriesReady available trace.transactionBenv.state) :
    UsdcEntriesReady available state ∧ UsdcGuardedInstallations P W trace.requests.settledRoots := by
  have withdrawn : UsdcEntriesReady available trace.withdrawalState := fun e member =>
    ⟨trace.withdrawalCode_of_code (ready e member).1,
      fun implementation => trace.withdrawalCode_of_code ((ready e member).2 implementation)⟩
  have requestGas : (trace.transactionBenv.withState trace.withdrawalState).stat.rules.stateGas = none := by
    change trace.transactionBenv.stat.rules.stateGas = none
    rw [trace.transactions.stat_eq]
    exact hsg
  have requests := RequestStageTrace.usdc_complete_available_family (P := P)
    subset impls complete trace.requests requestGas withdrawn
  refine ⟨?_, requests.2⟩
  have code (a : Adr) : state.getCode a = trace.requestState.getCode a := by
    simp only [trace.finalState_eq, trace.rewardState_eq]
    split
    · rfl
    · exact payRewards_getCode _ _ _ _ _ _
  intro e member
  exact ⟨(code e.adr).trans (requests.1 e member).1,
    fun implementation => (code usdcLib).trans ((requests.1 e member).2 implementation)⟩

end CompleteFamily

section CompleteHistory

variable {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
  (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
  (capabilities : BodyStageCapabilities F)
  (bal : ∀ {fork}, F fork → fork.ruleSet.bal = none)
  {P : Adr} {W available : List UsdcDeployedEntry}
  (subset : ∀ e ∈ available, e ∈ W)
  (impls : ∀ e ∈ available, UsdcImplCode e.code)
  (complete : ∀ a ∈ F2prime.upgradeTargets, ∃ e ∈ available, a = e.adr)

include capabilities bal subset impls complete

/-- Every stage of an original block preserves the complete available family
and derives the transaction origins and guarded installations it actually uses. -/
theorem ConfiguredHistoryTraceIn.block_origins_of_complete_available_family
    {pre post : BlockChain} (block : ConfiguredBlockTraceIn F cfg pre post)
    (rootsIn : ∀ R ∈ block.settledRoots, R ∈ history.settledRoots)
    (ready : UsdcEntriesReady available pre.state) :
    UsdcTransactionsOrigins P W block.bodyTrace.transactions ∧
      UsdcGuardedInstallations P W block.settledRoots ∧
      UsdcEntriesReady available post.state := by
  have hsg := capabilities.stateGas_none block.forkIn
  have beacon := BeaconStageTrace.usdc_complete_available_family (P := P)
    subset impls complete block.bodyTrace.beacon hsg ready
  have opening := HistoryStageTrace.usdc_complete_available_family (P := P)
    subset impls complete block.bodyTrace.history hsg beacon.1
  have transactions := ConfiguredHistoryTraceIn.transactions_origins_of_complete_available_family
    (P := P) subset impls complete history capabilities bal block.bodyTrace.transactions
    (fun R member => rootsIn R (List.mem_append_left _ (List.mem_append_right _ member))) hsg opening.1
  have closing := StagedBodyTrace.usdc_complete_available_family_after_transactions (P := P)
    subset impls complete block.bodyTrace hsg transactions.2.2
  refine ⟨transactions.1, ?_, ?_⟩
  · exact UsdcGuardedInstallations.append
      (UsdcGuardedInstallations.append
        (UsdcGuardedInstallations.append beacon.2 opening.2) transactions.2.1) closing.2
  · rw [block.postEq]
    exact closing.1

/-- Start after the selected transaction, retaining its original suffix,
withdrawals, enabled requests and rewards. No earlier availability is assumed. -/
theorem ConfiguredHistoryTraceIn.after_txSplit_origins_of_complete_available_family
    {pre post : BlockChain} (block : ConfiguredBlockTraceIn F cfg pre post) {i : Nat}
    (cut : block.bodyTrace.transactions.TxSplit i)
    (rootsIn : ∀ R ∈ (MidHistoryTraceIn.tail block cut).settledRoots,
      R ∈ history.settledRoots)
    (ready : UsdcEntriesReady available cut.afterBenv.state) :
    UsdcTransactionsOrigins P W cut.after ∧
      UsdcGuardedInstallations P W (MidHistoryTraceIn.tail block cut).settledRoots ∧
      UsdcEntriesReady available post.state := by
  have hsg := capabilities.stateGas_none block.forkIn
  have cutGas : cut.afterBenv.stat.rules.stateGas = none := by
    rw [block.txSplit_stat cut]; exact hsg
  have transactions := ConfiguredHistoryTraceIn.transactions_origins_of_complete_available_family
    (P := P) subset impls complete history capabilities bal cut.after
    (fun R member => rootsIn R (List.mem_append_left _ member)) cutGas ready
  have closing := StagedBodyTrace.usdc_complete_available_family_after_transactions (P := P)
    subset impls complete block.bodyTrace hsg transactions.2.2
  refine ⟨transactions.1, UsdcGuardedInstallations.append transactions.2.1 closing.2, ?_⟩
  rw [block.postEq]
  exact closing.1

/-- Complete coverage of the allowed implementation addresses and availability
at the original start cut suffice for every later origin and guarded installation.
All enabled stages and full transaction settlement remain in this exact history;
no upgrade census, final runtime oracle or allowance premise is required. -/
theorem ConfiguredHistoryTraceIn.mid_origins_of_complete_available_family
    {start : Benv} {finish : BlockChain} (mid : MidHistoryTraceIn F cfg start finish)
    (rootsIn : ∀ R ∈ mid.settledRoots, R ∈ history.settledRoots)
    (ready : UsdcEntriesReady available start.state) :
    UsdcMidHistoryOrigins P W mid ∧
      UsdcGuardedInstallations P W mid.settledRoots ∧
      UsdcEntriesReady available finish.state := by
  induction mid with
  | tail block cut =>
    exact ConfiguredHistoryTraceIn.after_txSplit_origins_of_complete_available_family
      history capabilities bal subset impls complete block cut rootsIn ready
  | step prior block ih =>
    have first := ih (fun R member => rootsIn R (List.mem_append_left _ member)) ready
    have next := ConfiguredHistoryTraceIn.block_origins_of_complete_available_family
      (P := P) history capabilities bal subset impls complete block
      (fun R member => rootsIn R (List.mem_append_right _ member)) first.2.2
    exact ⟨⟨first.1, next.1⟩, UsdcGuardedInstallations.append first.2.1 next.2.1, next.2.2⟩

end CompleteHistory

end Blanc.Lift.Usdc
