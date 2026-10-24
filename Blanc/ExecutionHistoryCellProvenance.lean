import Blanc.ExecutionInCellProvenance
import Blanc.ExecutionInRawNodes
import Blanc.ExecutionInCodeImageSafe
import Blanc.ExecutionNoDelSafeHistory
import Blanc.ExecutionOccurrence
import Blanc.ExecutionTransactionEffects
import Blanc.ExecutionBodyEffects
import Blanc.ExecutionAccountingAdmission
import Blanc.ExecutionStagedBodyTrace
import Blanc.ExecutionHistory

/-!
# Cell provenance above transactions (L3-L7) and the top-level statement

`Blanc/ExecutionInCellProvenance.lean` proves cell provenance for retained
messages (L1) and selected transactions (L2). This module lifts it through
transaction lists (L3), system and request calls (L4), stages and staged
bodies with withdrawals and rewards (L5), configured blocks (L6) and
configured histories (L7), then proves
`ConfiguredHistoryTraceIn.rawNode_cellProvenance` in exactly the Mac's
statement, plus `rawNode_cellInv` and `rawFrame_entryCellInv`.

Every `…cellProv_at` lemma concludes the pair `CellProv … ∧ node code = C`;
every `…cellProv_post` concludes `CellProv … ∧ post code = C`. Cell parts
reuse L1-L2; code parts reuse the safety-free `codeImage_of_safe` leaves
(`MessageCallTrace`, `TransactionTrace`) and the `noDel_of_safe` chain for
completed parts. At every `xs ++ ys` split, `List.split_append_cons`
dispatches: left reuses the same `before`, right composes the left post
(safety restricted from `safeBefore`) with the right at.

Reused (not copied): all of `ExecutionInCellProvenance` (L1-L2);
`TransactionTrace.codeImage_of_safe`, `MessageCallTrace.codeImage_of_safe`,
`…noDel_of_safe` at every level (`ExecutionNoDelSafeHistory`);
`Exec.rawNodes_getCode` (`ExecutionCellProvenance`);
`systemTransactionMessage_benv_state`, `systemTransactionMessage_benv_createdAccounts`
(`ExecutionBodyEffects`); `processWithdrawalsState_getStor_eq`
(`ExecutionAccountingAdmission`); `payRewards_getStor` and
`sweepTouchedAccounts_getStor_of_nonempty` (`ExecutionCellProvenance`);
`payRewards_getCode` (`ExecutionNoDelSafeHistory`); `List.split_append_cons`
(`ExecutionAccountingPositional`); `Exec.Deriv.successfulSstore?_sound_raw`
(`ExecutionCellProvenance`) for the final attribution, with
`Exec.Deriv.ParentPrefix.sevm_eq` for the writer frame's target.
-/

namespace Blanc

open Jaune

namespace ExecutionTrace

/-- A node of a covered message keeps the message entry code. -/
theorem msgNode_code {wa : Adr} {C : ByteArray} (hCdel : ¬ isValidDelegation C)
    (hCne : C.toList ≠ [])
    {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out)
    (installed : msg.benv.state.getCode wa = C) (h : Msg.NoDel wa msg)
    {n : Exec.Deriv} (hmem : n ∈ trace.rawNodes) : n.devm.getCode wa = C := by
  obtain ⟨R, hR, hp⟩ :=
    (trace.mem_rawNodes_iff_rawFrame_parentPrefix n).mp hmem
  have hRcode := trace.codeImage_of_safe hCdel hCne installed h R hR
  rcases R with ⟨pc, sevm, pre, out, run⟩
  have hmemR : n ∈ Exec.rawNodes run := by
    exact (Exec.mem_rawNodes_iff_rawFrameRoot_parentPrefix run n).mpr
      ⟨_, List.mem_cons_self, hp⟩
  exact Exec.rawNodes_getCode run hRcode hCne n hmemR

/-- A node of a covered transaction keeps the transaction entry code. -/
theorem txNode_code {wa : Adr} {C : ByteArray} (hCdel : ¬ isValidDelegation C)
    (hCne : C.toList ≠ [])
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (installed : benv.state.getCode wa = C)
    (notCreated : wa ∉ benv.createdAccounts)
    {n : Exec.Deriv} (hmem : n ∈ trace.rawNodes) : n.devm.getCode wa = C := by
  obtain ⟨R, hR, hp⟩ :=
    (trace.mem_rawNodes_iff_rawFrame_parentPrefix n).mp hmem
  have hRcode :=
    trace.codeImage_of_safe hCdel hCne installed notCreated R hR
  rcases R with ⟨pc, sevm, pre, out, run⟩
  have hmemR : n ∈ Exec.rawNodes run := by
    exact (Exec.mem_rawNodes_iff_rawFrameRoot_parentPrefix run n).mpr
      ⟨_, List.mem_cons_self, hp⟩
  exact Exec.rawNodes_getCode run hRcode hCne n hmemR

/-- A transaction list carries its entry cell to every raw node and keeps
the entry code there. -/
theorem ApplyTransactionsTrace.cellProv_at {wa : Adr} {C : ByteArray}
    (hCdel : ¬ isValidDelegation C)
    {txs : List (Nat × Tx)} {benv : Benv} {bout : BlockOutput}
    {finalBenv : Benv} {finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (k : B256)
    (hsg : benv.stat.rules.stateGas = Option.none)
    (hC : benv.state.getCode wa = C) (hCne : C.toList ≠ [])
    (hnotCreated : wa ∉ benv.createdAccounts)
    {n : Exec.Deriv} {before after : List Exec.Deriv}
    (hsplit : trace.rawNodes = before ++ n :: after)
    {init : B256}
    (hentry : init = ((benv.state.getStor wa).get k))
    (safeBefore : ∀ m ∈ before, m.sevm.currentTarget = wa →
      ¬ Linst.At m.sevm.code m.pc .selfdestruct) :
    CellProv wa k init before ((n.devm.getStor wa).get k) ∧
      n.devm.getCode wa = C := by
  induction trace generalizing before n after init with
  | nil benv bout =>
      simp only [ApplyTransactionsTrace.rawNodes] at hsplit
      have hlen := congrArg List.length hsplit
      simp only [List.length_nil, List.length_append,
        List.length_cons] at hlen
      omega
  | cons head tail ih =>
      simp only [ApplyTransactionsTrace.rawNodes] at hsplit
      rcases List.split_append_cons hsplit with ⟨m, hX, ha⟩ | ⟨nb, hb, hY⟩
      · obtain hcell :=
          head.cellProv_at hCdel k hsg hC hCne hX hentry
        have hmemN : n ∈ head.rawNodes := by
          rw [hX]
          exact List.mem_append.mpr (Or.inr List.mem_cons_self)
        exact ⟨hcell,
          txNode_code hCdel hCne head hC hnotCreated hmemN⟩
      · have hsafeHead : SafeRawFrames wa head.rawFrames :=
          head.safeRawFrames_of_rawNodes (fun m hm ht =>
            safeBefore m (hb ▸ List.mem_append.mpr (Or.inl hm)) ht)
        obtain hcellH :=
          head.cellProv_post hCdel k hsg hC hCne hnotCreated hsafeHead
        obtain ⟨-, -, hstateCodeH⟩ :=
          head.noDel_of_safe hCdel hCne hsg hC hnotCreated hsafeHead
        have hsafeTail : ∀ m ∈ nb, m.sevm.currentTarget = wa →
            ¬ Linst.At m.sevm.code m.pc .selfdestruct := by
          intro m hm ht
          exact safeBefore m (hb ▸ List.mem_append.mpr (Or.inr hm)) ht
        obtain ⟨hcellT, hcodeT⟩ :=
          ih hsg hstateCodeH hnotCreated hY rfl hsafeTail
        have htrans := CellProv.trans hcellH hcellT
        rw [hb, hentry]
        exact ⟨htrans, hcodeT⟩

/-- A transaction list carries its entry cell to its post cell and keeps
the entry code there. -/
theorem ApplyTransactionsTrace.cellProv_post {wa : Adr} {C : ByteArray}
    (hCdel : ¬ isValidDelegation C)
    {txs : List (Nat × Tx)} {benv : Benv} {bout : BlockOutput}
    {finalBenv : Benv} {finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (k : B256)
    (hsg : benv.stat.rules.stateGas = Option.none)
    (hC : benv.state.getCode wa = C) (hCne : C.toList ≠ [])
    (hnotCreated : wa ∉ benv.createdAccounts)
    (safe : SafeRawFrames wa trace.rawFrames) :
    CellProv wa k ((benv.state.getStor wa).get k) trace.rawNodes
      ((finalBenv.state.getStor wa).get k) ∧
      finalBenv.state.getCode wa = C := by
  revert hsg hC hnotCreated safe
  induction trace with
  | nil benv bout =>
      intro hsg hC hnotCreated safe
      show CellProv wa k ((benv.state.getStor wa).get k) []
        ((benv.state.getStor wa).get k) ∧ benv.state.getCode wa = C
      exact ⟨Or.inl rfl, hC⟩
  | cons head tail ih =>
      intro hsg hC hnotCreated safe
      have safeHead : SafeRawFrames wa head.rawFrames :=
        SafeRawFrames.of_append_left safe
      have safeTail : SafeRawFrames wa tail.rawFrames :=
        SafeRawFrames.of_append_right safe
      obtain hcellH :=
        head.cellProv_post hCdel k hsg hC hCne hnotCreated safeHead
      obtain ⟨-, -, hstateCodeH⟩ :=
        head.noDel_of_safe hCdel hCne hsg hC hnotCreated safeHead
      obtain ⟨hcellT, hcodeT⟩ := ih hsg hstateCodeH hnotCreated safeTail
      have htrans := CellProv.trans hcellH hcellT
      simp only [ApplyTransactionsTrace.rawNodes]
      exact ⟨htrans, hcodeT⟩

/-- A system message carries its entry cell to every raw node and keeps
the entry code there: the system message world is the block opening world. -/
theorem SystemMessageTrace.cellProv_at {wa : Adr} {C : ByteArray}
    (hCdel : ¬ isValidDelegation C)
    {benv : Benv} {target : Adr} {data : Bytes} {state : State}
    {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out) (k : B256)
    (hsg : benv.stat.rules.stateGas = Option.none)
    (hC : benv.state.getCode wa = C) (hCne : C.toList ≠ [])
    (hnotCreated : wa ∉ benv.createdAccounts)
    {n : Exec.Deriv} {before after : List Exec.Deriv}
    (hsplit : trace.rawNodes = before ++ n :: after)
    {init : B256}
    (hentry : init = ((benv.state.getStor wa).get k))
    (_safeBefore : ∀ m ∈ before, m.sevm.currentTarget = wa →
      ¬ Linst.At m.sevm.code m.pc .selfdestruct) :
    CellProv wa k init before ((n.devm.getStor wa).get k) ∧
      n.devm.getCode wa = C := by
  have hsgMsg :
      (systemTransactionMessage benv target data).benv.stat.rules.stateGas =
        Option.none := by
    simpa only [BenvStat.rules, systemTransactionMessage,
      processSystemTransactionMsg, Benv.beginTransaction] using hsg
  have hCmsg : (systemTransactionMessage benv target data).benv.state.getCode
      wa = C := by
    rw [systemTransactionMessage_benv_state]
    exact hC
  have hentryMsg :
      init = (((systemTransactionMessage benv target data).benv.state.getStor
        wa).get k) := by
    rw [systemTransactionMessage_benv_state]
    exact hentry
  have hnodel : Msg.NoDel wa (systemTransactionMessage benv target data) := by
    refine ⟨?_, ?_⟩
    · rw [systemTransactionMessage_benv_createdAccounts]
      exact hnotCreated
    · rw [systemTransactionMessage_benv_state, hC]
      exact hCne
  obtain hcell :=
    trace.message.cellProv_at hCdel k hsgMsg hCmsg hCne hsplit hentryMsg
  have hmemN : n ∈ trace.message.rawNodes := by
    show n ∈ trace.rawNodes
    rw [hsplit]
    exact List.mem_append.mpr (Or.inr List.mem_cons_self)
  exact ⟨hcell, msgNode_code hCdel hCne trace.message hCmsg hnodel hmemN⟩

/-- A system message carries its entry cell to its post cell and keeps the
entry code there. -/
theorem SystemMessageTrace.cellProv_post {wa : Adr} {C : ByteArray}
    (hCdel : ¬ isValidDelegation C)
    {benv : Benv} {target : Adr} {data : Bytes} {state : State}
    {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out) (k : B256)
    (hsg : benv.stat.rules.stateGas = Option.none)
    (hC : benv.state.getCode wa = C) (hCne : C.toList ≠ [])
    (hnotCreated : wa ∉ benv.createdAccounts)
    (safe : SafeRawFrames wa trace.rawFrames) :
    CellProv wa k ((benv.state.getStor wa).get k) trace.rawNodes
      ((state.getStor wa).get k) ∧
      state.getCode wa = C := by
  have hsgMsg :
      (systemTransactionMessage benv target data).benv.stat.rules.stateGas =
        Option.none := by
    simpa only [BenvStat.rules, systemTransactionMessage,
      processSystemTransactionMsg, Benv.beginTransaction] using hsg
  have hCmsg : (systemTransactionMessage benv target data).benv.state.getCode
      wa = C := by
    rw [systemTransactionMessage_benv_state]
    exact hC
  have hcell := trace.message.cellProv_post hCdel k hsgMsg hCmsg hCne
  obtain ⟨-, hcode⟩ := trace.noDel_of_safe hCdel hCne hsg hC hnotCreated safe
  exact ⟨hcell, hcode⟩

/-- The two checked request calls carry the entry cell to every raw node
and keep the entry code there. -/
theorem RequestsTrace.cellProv_at {wa : Adr} {C : ByteArray}
    (hCdel : ¬ isValidDelegation C)
    {benv : Benv} {bout : BlockOutput} {state : State} {bout' : BlockOutput}
    (trace : RequestsTrace benv bout state bout') (k : B256)
    (hsg : benv.stat.rules.stateGas = Option.none)
    (hC : benv.state.getCode wa = C) (hCne : C.toList ≠ [])
    (hnotCreated : wa ∉ benv.createdAccounts)
    {n : Exec.Deriv} {before after : List Exec.Deriv}
    (hsplit : trace.rawNodes = before ++ n :: after)
    {init : B256}
    (hentry : init = ((benv.state.getStor wa).get k))
    (safeBefore : ∀ m ∈ before, m.sevm.currentTarget = wa →
      ¬ Linst.At m.sevm.code m.pc .selfdestruct) :
    CellProv wa k init before ((n.devm.getStor wa).get k) ∧
      n.devm.getCode wa = C := by
  simp only [RequestsTrace.rawNodes] at hsplit
  rcases List.split_append_cons hsplit with ⟨m, hX, ha⟩ | ⟨nb, hb, hY⟩
  · exact trace.withdrawal.cellProv_at hCdel k hsg hC hCne hnotCreated hX
      hentry safeBefore
  · have hsafeW : SafeRawFrames wa trace.withdrawal.rawFrames :=
      trace.withdrawal.safeRawFrames_of_rawNodes (fun m hm ht =>
        safeBefore m (hb ▸ List.mem_append.mpr (Or.inl hm)) ht)
    obtain ⟨hcellW, -⟩ := trace.withdrawal.cellProv_post hCdel k hsg hC hCne
      hnotCreated hsafeW
    obtain ⟨-, hcodeW⟩ :=
      trace.withdrawal.noDel_of_safe hCdel hCne hsg hC hnotCreated hsafeW
    have hsafeTail : ∀ m ∈ nb, m.sevm.currentTarget = wa →
        ¬ Linst.At m.sevm.code m.pc .selfdestruct := by
      intro m hm ht
      exact safeBefore m (hb ▸ List.mem_append.mpr (Or.inr hm)) ht
    obtain ⟨hcellC, hcodeC⟩ := trace.consolidation.cellProv_at hCdel k hsg
      hcodeW hCne hnotCreated hY rfl hsafeTail
    have htrans := CellProv.trans hcellW hcellC
    rw [hb, hentry]
    exact ⟨htrans, hcodeC⟩

/-- The two checked request calls carry the entry cell to the
consolidation post cell and keep the entry code there. -/
theorem RequestsTrace.cellProv_post {wa : Adr} {C : ByteArray}
    (hCdel : ¬ isValidDelegation C)
    {benv : Benv} {bout : BlockOutput} {state : State} {bout' : BlockOutput}
    (trace : RequestsTrace benv bout state bout') (k : B256)
    (hsg : benv.stat.rules.stateGas = Option.none)
    (hC : benv.state.getCode wa = C) (hCne : C.toList ≠ [])
    (hnotCreated : wa ∉ benv.createdAccounts)
    (safe : SafeRawFrames wa trace.rawFrames) :
    CellProv wa k ((benv.state.getStor wa).get k) trace.rawNodes
      ((state.getStor wa).get k) ∧
      state.getCode wa = C := by
  have safeW : SafeRawFrames wa trace.withdrawal.rawFrames :=
    SafeRawFrames.of_append_left safe
  have safeC : SafeRawFrames wa trace.consolidation.rawFrames :=
    SafeRawFrames.of_append_right safe
  obtain ⟨hcellW, -⟩ := trace.withdrawal.cellProv_post hCdel k hsg hC hCne
    hnotCreated safeW
  obtain ⟨-, hcodeW⟩ :=
    trace.withdrawal.noDel_of_safe hCdel hCne hsg hC hnotCreated safeW
  obtain ⟨hcellC, hcodeC⟩ := trace.consolidation.cellProv_post hCdel k hsg
    hcodeW hCne hnotCreated safeC
  have htrans := CellProv.trans hcellW hcellC
  have hcellEq : ((state.getStor wa).get k) =
      ((trace.consolidationState.getStor wa).get k) :=
    congrArg (fun s : State => (s.getStor wa).get k)
      trace.state_eq_consolidationState
  have hcodeEq : state.getCode wa = trace.consolidationState.getCode wa :=
    congrArg (fun s : State => s.getCode wa)
      trace.state_eq_consolidationState
  simp only [RequestsTrace.rawNodes]
  rw [hcellEq, hcodeEq]
  exact ⟨htrans, hcodeC⟩

/-- A beacon stage carries its entry cell to every raw node and keeps the
entry code there. -/
theorem BeaconStageTrace.cellProv_at {wa : Adr} {C : ByteArray}
    (hCdel : ¬ isValidDelegation C)
    {rules : ForkRules} {benv : Benv} {state : State} {bal : BalBuilder}
    (trace : BeaconStageTrace rules benv state bal) (k : B256)
    (hsg : benv.stat.rules.stateGas = Option.none)
    (hC : benv.state.getCode wa = C) (hCne : C.toList ≠ [])
    (hnotCreated : wa ∉ benv.createdAccounts)
    {n : Exec.Deriv} {before after : List Exec.Deriv}
    (hsplit : trace.rawNodes = before ++ n :: after)
    {init : B256}
    (hentry : init = ((benv.state.getStor wa).get k))
    (safeBefore : ∀ m ∈ before, m.sevm.currentTarget = wa →
      ¬ Linst.At m.sevm.code m.pc .selfdestruct) :
    CellProv wa k init before ((n.devm.getStor wa).get k) ∧
      n.devm.getCode wa = C := by
  cases trace with
  | skipped disabled run =>
      simp only [BeaconStageTrace.rawNodes] at hsplit
      have hlen := congrArg List.length hsplit
      simp only [List.length_nil, List.length_append,
        List.length_cons] at hlen
      omega
  | called enabled out message incorporated =>
      exact message.cellProv_at hCdel k hsg hC hCne hnotCreated hsplit
        hentry safeBefore

/-- A beacon stage carries its entry cell to its post cell and keeps the
entry code there. -/
theorem BeaconStageTrace.cellProv_post {wa : Adr} {C : ByteArray}
    (hCdel : ¬ isValidDelegation C)
    {rules : ForkRules} {benv : Benv} {state : State} {bal : BalBuilder}
    (trace : BeaconStageTrace rules benv state bal) (k : B256)
    (hsg : benv.stat.rules.stateGas = Option.none)
    (hC : benv.state.getCode wa = C) (hCne : C.toList ≠ [])
    (hnotCreated : wa ∉ benv.createdAccounts)
    (safe : SafeRawFrames wa trace.rawFrames) :
    CellProv wa k ((benv.state.getStor wa).get k) trace.rawNodes
      ((state.getStor wa).get k) ∧
      state.getCode wa = C := by
  cases trace with
  | skipped disabled run =>
      show CellProv wa k ((benv.state.getStor wa).get k) []
        ((benv.state.getStor wa).get k) ∧ benv.state.getCode wa = C
      exact ⟨Or.inl rfl, hC⟩
  | called enabled out message incorporated =>
      exact message.cellProv_post hCdel k hsg hC hCne hnotCreated safe

/-- A history stage carries its entry cell to every raw node and keeps the
entry code there. -/
theorem HistoryStageTrace.cellProv_at {wa : Adr} {C : ByteArray}
    (hCdel : ¬ isValidDelegation C)
    {rules : ForkRules} {benv : Benv} {inputBal : BalBuilder} {state : State}
    {bal : BalBuilder}
    (trace : HistoryStageTrace rules benv inputBal state bal) (k : B256)
    (hsg : benv.stat.rules.stateGas = Option.none)
    (hC : benv.state.getCode wa = C) (hCne : C.toList ≠ [])
    (hnotCreated : wa ∉ benv.createdAccounts)
    {n : Exec.Deriv} {before after : List Exec.Deriv}
    (hsplit : trace.rawNodes = before ++ n :: after)
    {init : B256}
    (hentry : init = ((benv.state.getStor wa).get k))
    (safeBefore : ∀ m ∈ before, m.sevm.currentTarget = wa →
      ¬ Linst.At m.sevm.code m.pc .selfdestruct) :
    CellProv wa k init before ((n.devm.getStor wa).get k) ∧
      n.devm.getCode wa = C := by
  cases trace with
  | skipped disabled run =>
      simp only [HistoryStageTrace.rawNodes] at hsplit
      have hlen := congrArg List.length hsplit
      simp only [List.length_nil, List.length_append,
        List.length_cons] at hlen
      omega
  | called enabled lastHash lastHashRun out message incorporated =>
      exact message.cellProv_at hCdel k hsg hC hCne hnotCreated hsplit
        hentry safeBefore

/-- A history stage carries its entry cell to its post cell and keeps the
entry code there. -/
theorem HistoryStageTrace.cellProv_post {wa : Adr} {C : ByteArray}
    (hCdel : ¬ isValidDelegation C)
    {rules : ForkRules} {benv : Benv} {inputBal : BalBuilder} {state : State}
    {bal : BalBuilder}
    (trace : HistoryStageTrace rules benv inputBal state bal) (k : B256)
    (hsg : benv.stat.rules.stateGas = Option.none)
    (hC : benv.state.getCode wa = C) (hCne : C.toList ≠ [])
    (hnotCreated : wa ∉ benv.createdAccounts)
    (safe : SafeRawFrames wa trace.rawFrames) :
    CellProv wa k ((benv.state.getStor wa).get k) trace.rawNodes
      ((state.getStor wa).get k) ∧
      state.getCode wa = C := by
  cases trace with
  | skipped disabled run =>
      show CellProv wa k ((benv.state.getStor wa).get k) []
        ((benv.state.getStor wa).get k) ∧ benv.state.getCode wa = C
      exact ⟨Or.inl rfl, hC⟩
  | called enabled lastHash lastHashRun out message incorporated =>
      exact message.cellProv_post hCdel k hsg hC hCne hnotCreated safe

/-- A request stage carries its entry cell to every raw node and keeps the
entry code there. -/
theorem RequestStageTrace.cellProv_at {wa : Adr} {C : ByteArray}
    (hCdel : ¬ isValidDelegation C)
    {rules : ForkRules} {benv : Benv} {bout : BlockOutput} {state : State}
    {bout' : BlockOutput}
    (trace : RequestStageTrace rules benv bout state bout') (k : B256)
    (hsg : benv.stat.rules.stateGas = Option.none)
    (hC : benv.state.getCode wa = C) (hCne : C.toList ≠ [])
    (hnotCreated : wa ∉ benv.createdAccounts)
    {n : Exec.Deriv} {before after : List Exec.Deriv}
    (hsplit : trace.rawNodes = before ++ n :: after)
    {init : B256}
    (hentry : init = ((benv.state.getStor wa).get k))
    (safeBefore : ∀ m ∈ before, m.sevm.currentTarget = wa →
      ¬ Linst.At m.sevm.code m.pc .selfdestruct) :
    CellProv wa k init before ((n.devm.getStor wa).get k) ∧
      n.devm.getCode wa = C := by
  cases trace with
  | skipped disabled run =>
      simp only [RequestStageTrace.rawNodes] at hsplit
      have hlen := congrArg List.length hsplit
      simp only [List.length_nil, List.length_append,
        List.length_cons] at hlen
      omega
  | called enabled requests run =>
      exact requests.cellProv_at hCdel k hsg hC hCne hnotCreated hsplit
        hentry safeBefore

/-- A request stage carries its entry cell to its post cell and keeps the
entry code there. -/
theorem RequestStageTrace.cellProv_post {wa : Adr} {C : ByteArray}
    (hCdel : ¬ isValidDelegation C)
    {rules : ForkRules} {benv : Benv} {bout : BlockOutput} {state : State}
    {bout' : BlockOutput}
    (trace : RequestStageTrace rules benv bout state bout') (k : B256)
    (hsg : benv.stat.rules.stateGas = Option.none)
    (hC : benv.state.getCode wa = C) (hCne : C.toList ≠ [])
    (hnotCreated : wa ∉ benv.createdAccounts)
    (safe : SafeRawFrames wa trace.rawFrames) :
    CellProv wa k ((benv.state.getStor wa).get k) trace.rawNodes
      ((state.getStor wa).get k) ∧
      state.getCode wa = C := by
  cases trace with
  | skipped disabled run =>
      show CellProv wa k ((benv.state.getStor wa).get k) []
        ((benv.state.getStor wa).get k) ∧ benv.state.getCode wa = C
      exact ⟨Or.inl rfl, hC⟩
  | called enabled requests run =>
      exact requests.cellProv_post hCdel k hsg hC hCne hnotCreated safe

/-- A staged body's withdrawal pass keeps a protected owner's cell: disabled
passes are identities, enabled passes replay direct withdrawals. -/
theorem StagedBodyTrace.withdrawalCell_of_code {wa : Adr} {C : ByteArray}
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout)
    (hcodeTx : trace.transactionBenv.state.getCode wa = C)
    (hCne : C.toList ≠ []) (k : B256) :
    ((trace.withdrawalState.getStor wa).get k) =
      ((trace.transactionBenv.state.getStor wa).get k) := by
  have run := trace.withdrawalsRun
  cases enabled : benv.stat.rules.header.withdrawalsRoot with
  | false =>
      rw [(trace.withdrawals_disabled enabled).1]
  | true =>
      simp only [withdrawalsPass, processWithdrawals, enabled,
        ↓reduceIte] at run
      rw [← (Prod.mk.inj run).1]
      exact congrArg (fun storage : Stor => storage.get k)
        (processWithdrawalsState_getStor_eq wa _ _
          (State.Protected.of_code_ne_nil (by rw [hcodeTx]; exact hCne)))

/-- A staged body's withdrawal pass keeps a protected owner's code. -/
theorem StagedBodyTrace.withdrawalCode_of_code {wa : Adr} {C : ByteArray}
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout)
    (hcodeTx : trace.transactionBenv.state.getCode wa = C) :
    trace.withdrawalState.getCode wa = C := by
  have run := trace.withdrawalsRun
  cases enabled : benv.stat.rules.header.withdrawalsRoot with
  | false =>
      rw [(trace.withdrawals_disabled enabled).1]
      exact hcodeTx
  | true =>
      simp only [withdrawalsPass, processWithdrawals, enabled,
        ↓reduceIte] at run
      rw [← (Prod.mk.inj run).1, processWithdrawalsState_getCode]
      exact hcodeTx

/-- A staged body carries its entry cell to every raw node and keeps the
entry code there. -/
theorem StagedBodyTrace.cellProv_at {wa : Adr} {C : ByteArray}
    (hCdel : ¬ isValidDelegation C)
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout) (k : B256)
    (hsg : benv.stat.rules.stateGas = Option.none)
    (hC : benv.state.getCode wa = C) (hCne : C.toList ≠ [])
    (hnotCreated : wa ∉ benv.createdAccounts)
    {n : Exec.Deriv} {before after : List Exec.Deriv}
    (hsplit : trace.rawNodes = before ++ n :: after)
    {init : B256}
    (hentry : init = ((benv.state.getStor wa).get k))
    (safeBefore : ∀ m ∈ before, m.sevm.currentTarget = wa →
      ¬ Linst.At m.sevm.code m.pc .selfdestruct) :
    CellProv wa k init before ((n.devm.getStor wa).get k) ∧
      n.devm.getCode wa = C := by
  have txStat : trace.transactionBenv.stat = benv.stat :=
    trace.transactions.stat_eq
  have txCreated : trace.transactionBenv.createdAccounts =
      benv.createdAccounts :=
    trace.transactions.createdAccounts_eq
  simp only [StagedBodyTrace.rawNodes] at hsplit
  rcases List.split_append_cons hsplit with ⟨mR, hXR, haR⟩ | ⟨nbR, hbR, hYR⟩
  · rcases List.split_append_cons hXR with ⟨mT, hXT, haT⟩ | ⟨nbT, hbT, hYT⟩
    · rcases List.split_append_cons hXT with ⟨mH, hXH, haH⟩ | ⟨nbH, hbH, hYH⟩
      · exact trace.beacon.cellProv_at hCdel k hsg hC hCne hnotCreated hXH
          hentry safeBefore
      · have hsafeB : SafeRawFrames wa trace.beacon.rawFrames :=
          trace.beacon.safeRawFrames_of_rawNodes (fun m hm ht =>
            safeBefore m
              (hbH ▸ List.mem_append_left nbH hm) ht)
        obtain ⟨hcellB, hcodeB⟩ := trace.beacon.cellProv_post hCdel k hsg
          hC hCne hnotCreated hsafeB
        have hsafeH : ∀ m ∈ nbH, m.sevm.currentTarget = wa →
            ¬ Linst.At m.sevm.code m.pc .selfdestruct := by
          intro m hm ht
          exact safeBefore m
            (hbH ▸ List.mem_append_right trace.beacon.rawNodes hm) ht
        obtain ⟨hcellH, hcodeH⟩ := trace.history.cellProv_at hCdel k hsg
          hcodeB hCne hnotCreated hYH rfl hsafeH
        have htrans := CellProv.trans hcellB hcellH
        rw [hbH, hentry]
        exact ⟨htrans, hcodeH⟩
    · have hsafeB : SafeRawFrames wa trace.beacon.rawFrames :=
          trace.beacon.safeRawFrames_of_rawNodes (fun m hm ht =>
            safeBefore m (hbT ▸ List.mem_append_left nbT
              (List.mem_append_left trace.history.rawNodes hm)) ht)
      have hsafeH : SafeRawFrames wa trace.history.rawFrames :=
          trace.history.safeRawFrames_of_rawNodes (fun m hm ht =>
            safeBefore m (hbT ▸ List.mem_append_left nbT
              (List.mem_append_right trace.beacon.rawNodes hm)) ht)
      obtain ⟨hcellB, hcodeB⟩ := trace.beacon.cellProv_post hCdel k hsg
        hC hCne hnotCreated hsafeB
      obtain ⟨hcellH, hcodeH⟩ := trace.history.cellProv_post hCdel k hsg
        hcodeB hCne hnotCreated hsafeH
      have hsafeT : ∀ m ∈ nbT, m.sevm.currentTarget = wa →
          ¬ Linst.At m.sevm.code m.pc .selfdestruct := by
        intro m hm ht
        exact safeBefore m (hbT ▸ List.mem_append_right
          (trace.beacon.rawNodes ++ trace.history.rawNodes) hm) ht
      obtain ⟨hcellT, hcodeT⟩ := trace.transactions.cellProv_at hCdel k
        hsg hcodeH hCne hnotCreated hYT rfl hsafeT
      have htrans := CellProv.trans (CellProv.trans hcellB hcellH) hcellT
      rw [hbT, hentry]
      exact ⟨htrans, hcodeT⟩
  · have hsafeB : SafeRawFrames wa trace.beacon.rawFrames :=
        trace.beacon.safeRawFrames_of_rawNodes (fun m hm ht =>
          safeBefore m (hbR ▸ List.mem_append_left nbR
            (List.mem_append_left trace.transactions.rawNodes
              (List.mem_append_left trace.history.rawNodes hm))) ht)
    have hsafeH : SafeRawFrames wa trace.history.rawFrames :=
        trace.history.safeRawFrames_of_rawNodes (fun m hm ht =>
          safeBefore m (hbR ▸ List.mem_append_left nbR
            (List.mem_append_left trace.transactions.rawNodes
              (List.mem_append_right trace.beacon.rawNodes hm))) ht)
    have hsafeT : SafeRawFrames wa trace.transactions.rawFrames :=
        trace.transactions.safeRawFrames_of_rawNodes (fun m hm ht =>
          safeBefore m (hbR ▸ List.mem_append_left nbR
            (List.mem_append_right
              (trace.beacon.rawNodes ++ trace.history.rawNodes) hm)) ht)
    obtain ⟨hcellB, hcodeB⟩ := trace.beacon.cellProv_post hCdel k hsg
      hC hCne hnotCreated hsafeB
    obtain ⟨hcellH, hcodeH⟩ := trace.history.cellProv_post hCdel k hsg
      hcodeB hCne hnotCreated hsafeH
    obtain ⟨hcellT, hcodeT⟩ := trace.transactions.cellProv_post hCdel k
      hsg hcodeH hCne hnotCreated hsafeT
    have hwdCell := trace.withdrawalCell_of_code hcodeT hCne k
    have hwdCode := trace.withdrawalCode_of_code hcodeT
    have hsafeR : ∀ m ∈ nbR, m.sevm.currentTarget = wa →
        ¬ Linst.At m.sevm.code m.pc .selfdestruct := by
      intro m hm ht
      exact safeBefore m (hbR ▸ List.mem_append.mpr (Or.inr hm)) ht
    have hsgR : (trace.transactionBenv.withState
        trace.withdrawalState).stat.rules.stateGas = Option.none := by
      change trace.transactionBenv.stat.rules.stateGas = Option.none
      rw [txStat]
      exact hsg
    have hnotCreatedR : wa ∉ (trace.transactionBenv.withState
        trace.withdrawalState).createdAccounts := by
      change wa ∉ trace.transactionBenv.createdAccounts
      rw [txCreated]
      exact hnotCreated
    obtain ⟨hcellR, hcodeR⟩ := trace.requests.cellProv_at hCdel k hsgR
      hwdCode hCne hnotCreatedR hYR hwdCell.symm hsafeR
    have htrans := CellProv.trans
      (CellProv.trans (CellProv.trans hcellB hcellH) hcellT) hcellR
    rw [hbR, hentry]
    exact ⟨htrans, hcodeR⟩

/-- A staged body carries its entry cell to its post cell and keeps the
entry code there: withdrawals and block rewards keep a code-bearing owner's
cell and code. -/
theorem StagedBodyTrace.cellProv_post {wa : Adr} {C : ByteArray}
    (hCdel : ¬ isValidDelegation C)
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout) (k : B256)
    (hsg : benv.stat.rules.stateGas = Option.none)
    (hC : benv.state.getCode wa = C) (hCne : C.toList ≠ [])
    (hnotCreated : wa ∉ benv.createdAccounts)
    (safe : SafeRawFrames wa trace.rawFrames) :
    CellProv wa k ((benv.state.getStor wa).get k) trace.rawNodes
      ((state.getStor wa).get k) ∧
      state.getCode wa = C := by
  have rawEq : trace.rawFrames =
      trace.beacon.rawFrames ++ trace.history.rawFrames ++
        trace.transactions.rawFrames ++ trace.requests.rawFrames := rfl
  rw [rawEq] at safe
  have safeR : SafeRawFrames wa trace.requests.rawFrames :=
    SafeRawFrames.of_append_right safe
  have safeBHT := SafeRawFrames.of_append_left safe
  have safeT : SafeRawFrames wa trace.transactions.rawFrames :=
    SafeRawFrames.of_append_right safeBHT
  have safeBH := SafeRawFrames.of_append_left safeBHT
  have safeH : SafeRawFrames wa trace.history.rawFrames :=
    SafeRawFrames.of_append_right safeBH
  have safeB : SafeRawFrames wa trace.beacon.rawFrames :=
    SafeRawFrames.of_append_left safeBH
  have txStat : trace.transactionBenv.stat = benv.stat :=
    trace.transactions.stat_eq
  have txCreated : trace.transactionBenv.createdAccounts =
      benv.createdAccounts :=
    trace.transactions.createdAccounts_eq
  obtain ⟨hcellB, hcodeB⟩ := trace.beacon.cellProv_post hCdel k hsg hC hCne
    hnotCreated safeB
  obtain ⟨hcellH, hcodeH⟩ := trace.history.cellProv_post hCdel k hsg hcodeB
    hCne hnotCreated safeH
  obtain ⟨hcellT, hcodeT⟩ := trace.transactions.cellProv_post hCdel k hsg
    hcodeH hCne hnotCreated safeT
  have hwdCell := trace.withdrawalCell_of_code hcodeT hCne k
  have hwdCode := trace.withdrawalCode_of_code hcodeT
  have hsgR : (trace.transactionBenv.withState
      trace.withdrawalState).stat.rules.stateGas = Option.none := by
    change trace.transactionBenv.stat.rules.stateGas = Option.none
    rw [txStat]
    exact hsg
  have hnotCreatedR : wa ∉ (trace.transactionBenv.withState
      trace.withdrawalState).createdAccounts := by
    change wa ∉ trace.transactionBenv.createdAccounts
    rw [txCreated]
    exact hnotCreated
  obtain ⟨hcellR, hcodeR⟩ := trace.requests.cellProv_post hCdel k hsgR
    hwdCode hCne hnotCreatedR safeR
  have hcellR' : CellProv wa k ((trace.transactionBenv.state.getStor wa).get k)
      trace.requests.rawNodes ((trace.requestState.getStor wa).get k) := by
    rw [← hwdCell]
    exact hcellR
  have htrans := CellProv.trans
    (CellProv.trans (CellProv.trans hcellB hcellH) hcellT) hcellR'
  have hreward : (trace.rewardState.getStor wa).get k =
      (trace.requestState.getStor wa).get k ∧
      trace.rewardState.getCode wa = C := by
    rw [trace.rewardState_eq]
    split
    · exact ⟨rfl, hcodeR⟩
    · rw [payRewards_getStor _ _ _ _ _ (by rw [hcodeR]; exact hCne),
        payRewards_getCode]
      exact ⟨rfl, hcodeR⟩
  rw [← trace.finalState_eq] at hreward
  simp only [StagedBodyTrace.rawNodes]
  rw [hreward.1]
  exact ⟨htrans, hreward.2⟩

/-- A configured block carries its pre cell to every raw node and keeps the
pre code there; `stateGas = none` comes from the history's capabilities. -/
theorem ConfiguredBlockTraceIn.cellProv_at {wa : Adr} {C : ByteArray}
    (hCdel : ¬ isValidDelegation C) (hCne : C.toList ≠ [])
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTraceIn F cfg pre post)
    (capabilities : BodyStageCapabilities F) (k : B256)
    (installed : pre.state.getCode wa = C)
    {n : Exec.Deriv} {before after : List Exec.Deriv}
    (hsplit : trace.rawNodes = before ++ n :: after)
    {init : B256}
    (hentry : init = ((pre.state.getStor wa).get k))
    (safeBefore : ∀ m ∈ before, m.sevm.currentTarget = wa →
      ¬ Linst.At m.sevm.code m.pc .selfdestruct) :
    CellProv wa k init before ((n.devm.getStor wa).get k) ∧
      n.devm.getCode wa = C :=
  trace.bodyTrace.cellProv_at hCdel k
    (capabilities.stateGas_none trace.forkIn) installed hCne
    AdrSet.not_mem_empty hsplit hentry safeBefore

/-- A configured block carries its pre cell to its post cell and keeps the
pre code there. -/
theorem ConfiguredBlockTraceIn.cellProv_post {wa : Adr} {C : ByteArray}
    (hCdel : ¬ isValidDelegation C) (hCne : C.toList ≠ [])
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTraceIn F cfg pre post)
    (capabilities : BodyStageCapabilities F) (k : B256)
    (installed : pre.state.getCode wa = C)
    (safe : SafeRawFrames wa trace.rawFrames) :
    CellProv wa k ((pre.state.getStor wa).get k) trace.rawNodes
      ((post.state.getStor wa).get k) ∧
      post.state.getCode wa = C := by
  obtain ⟨hcell, hcode⟩ := trace.bodyTrace.cellProv_post hCdel k
    (capabilities.stateGas_none trace.forkIn) installed hCne
    AdrSet.not_mem_empty safe
  have hstate : post.state = trace.bodyState :=
    congrArg BlockChain.state trace.postEq
  rw [hstate]
  exact ⟨hcell, hcode⟩

/-- A configured history carries the checkpoint cell to its endpoint cell
and keeps the checkpoint code there, from whole-history safety. -/
theorem ConfiguredHistoryTraceIn.cellProv_post {wa : Adr} {C : ByteArray}
    (hCdel : ¬ isValidDelegation C) (hCne : C.toList ≠ [])
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) (k : B256)
    (installed : checkpoint.state.getCode wa = C)
    (safe : SafeRawFrames wa history.rawFrames) :
    CellProv wa k ((checkpoint.state.getStor wa).get k) history.rawNodes
      ((future.state.getStor wa).get k) ∧
      future.state.getCode wa = C := by
  induction history with
  | refl =>
      show CellProv wa k ((checkpoint.state.getStor wa).get k) []
        ((checkpoint.state.getStor wa).get k) ∧ checkpoint.state.getCode wa = C
      exact ⟨Or.inl rfl, installed⟩
  | step prior block ih =>
      obtain ⟨hcellP, hcodeP⟩ := ih (SafeRawFrames.of_append_left safe)
      obtain ⟨hcellB, hcodeB⟩ := block.cellProv_post hCdel hCne capabilities
        k hcodeP (SafeRawFrames.of_append_right safe)
      exact ⟨CellProv.trans hcellP hcellB, hcodeB⟩

/-- A configured history carries the checkpoint cell to every raw node and
keeps the checkpoint code there, from safety of the earlier nodes only. -/
theorem ConfiguredHistoryTraceIn.cellProv_at {wa : Adr} {C : ByteArray}
    (hCdel : ¬ isValidDelegation C) (hCne : C.toList ≠ [])
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F) (k : B256)
    (installed : checkpoint.state.getCode wa = C)
    {n : Exec.Deriv} {before after : List Exec.Deriv}
    (hsplit : history.rawNodes = before ++ n :: after)
    (safeBefore : ∀ m ∈ before, m.sevm.currentTarget = wa →
      ¬ Linst.At m.sevm.code m.pc .selfdestruct) :
    CellProv wa k ((checkpoint.state.getStor wa).get k) before
      ((n.devm.getStor wa).get k) ∧
      n.devm.getCode wa = C := by
  induction history generalizing before n after with
  | refl =>
      simp only [ConfiguredHistoryTraceIn.rawNodes] at hsplit
      have hlen := congrArg List.length hsplit
      simp only [List.length_nil, List.length_append,
        List.length_cons] at hlen
      omega
  | step prior block ih =>
      simp only [ConfiguredHistoryTraceIn.rawNodes] at hsplit
      rcases List.split_append_cons hsplit with ⟨m, hX, -⟩ | ⟨nb, hb, hY⟩
      · exact ih hX safeBefore
      · have hsafeP : SafeRawFrames wa prior.rawFrames :=
          prior.safeRawFrames_of_rawNodes (fun m hm ht =>
            safeBefore m (hb ▸ List.mem_append_left nb hm) ht)
        obtain ⟨hcellP, hcodeP⟩ := prior.cellProv_post hCdel hCne
          capabilities k installed hsafeP
        have hsafeB : ∀ m ∈ nb, m.sevm.currentTarget = wa →
            ¬ Linst.At m.sevm.code m.pc .selfdestruct := by
          intro m hm ht
          exact safeBefore m (hb ▸ List.mem_append_right prior.rawNodes hm) ht
        obtain ⟨hcellB, hcodeB⟩ := block.cellProv_at hCdel hCne capabilities
          k hcodeP hY rfl hsafeB
        rw [hb]
        exact ⟨CellProv.trans hcellP hcellB, hcodeB⟩

/-- The recognizer projects its own node and the executing frame's target. -/
theorem successfulSstore?_node_owner {m : Exec.Deriv} {w : Exec.StorageWrite}
    (found : Exec.Deriv.successfulSstore? m = some w) :
    w.node = m ∧ w.owner = m.sevm.currentTarget := by
  unfold Exec.Deriv.successfulSstore? at found
  split at found
  · split at found
    · cases found
      exact ⟨rfl, rfl⟩
    · cases found
  · cases found

/-- **Code and cell provenance at every raw node of an In-history**, from
safety of the strictly earlier raw nodes only. The node sees the checkpoint
code `C` at `wa`, and its `(wa, k)` cell is the checkpoint value or the value
of an earlier successful raw `SSTORE` to `(wa, k)`, attributed to its raw
frame `G` of the history. -/
theorem ConfiguredHistoryTraceIn.rawNode_cellProvenance
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    {wa : Adr} {C : ByteArray}
    (hCdel : ¬ isValidDelegation C) (hCne : C.toList ≠ [])
    (installed : checkpoint.state.getCode wa = C) (k : B256)
    {before after : List Exec.Deriv} {n : Exec.Deriv}
    (split : history.rawNodes = before ++ n :: after)
    (safeBefore : ∀ m ∈ before, m.sevm.currentTarget = wa →
      ¬ Linst.At m.sevm.code m.pc .selfdestruct) :
    n.devm.getCode wa = C ∧
      ((Devm.getStor n.devm wa).get k = (checkpoint.state.getStor wa).get k ∨
        ∃ (b₁ b₂ : List Exec.Deriv) (m : Exec.Deriv) (G : Exec.Deriv)
          (write : Exec.SuccessfulSstoreOccurrence G),
          before = b₁ ++ m :: b₂ ∧
          G ∈ history.rawFrames ∧
          Exec.Deriv.ParentPrefix G m ∧
          write.occurrence.node = m ∧
          G.sevm.currentTarget = wa ∧
          write.storageOwner = wa ∧ write.key = k ∧
          write.value = (Devm.getStor n.devm wa).get k) := by
  obtain ⟨hcell, hcode⟩ := history.cellProv_at hCdel hCne capabilities k
    installed split safeBefore
  refine ⟨hcode, ?_⟩
  rcases hcell with hinit | ⟨b₁, b₂, m, w, hb, hfound, hown, hkey, hval⟩
  · exact Or.inl hinit
  · right
    have hmemM : m ∈ history.rawNodes := by
      rw [split, hb]
      exact List.mem_append_left _ (List.mem_append_right _ List.mem_cons_self)
    obtain ⟨G, hG, hp⟩ :=
      (history.mem_rawNodes_iff_rawFrame_parentPrefix m).mp hmemM
    have hmemG : m ∈ Exec.rawNodes G.exc := by
      rcases G with ⟨pc, sevm, pre, out, run⟩
      exact (Exec.mem_rawNodes_iff_rawFrameRoot_parentPrefix run m).mpr
        ⟨_, List.mem_cons_self, hp⟩
    obtain ⟨write, hwrite⟩ :=
      Exec.Deriv.successfulSstore?_sound_raw hmemG hfound
    obtain ⟨hnode, howner⟩ := successfulSstore?_node_owner hfound
    have hwnode : write.occurrence.node = m :=
      (congrArg Exec.StorageWrite.node hwrite).trans hnode
    refine ⟨b₁, b₂, m, G, write, hb, hG, hp, hwnode, ?_, ?_, ?_, ?_⟩
    · rw [← Exec.Deriv.ParentPrefix.sevm_eq hp, ← howner]
      exact hown
    · show write.storageWrite.owner = wa
      rw [hwrite]
      exact hown
    · show write.storageWrite.key = k
      rw [hwrite]
      exact hkey
    · show write.storageWrite.value = _
      rw [hwrite]
      exact hval

/-- **Invariant form**: a cell property that holds at the checkpoint and is
preserved by every earlier successful `SSTORE` to `(wa, k)` holds at the node. -/
theorem ConfiguredHistoryTraceIn.rawNode_cellInv
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    {wa : Adr} {C : ByteArray}
    (hCdel : ¬ isValidDelegation C) (hCne : C.toList ≠ [])
    (installed : checkpoint.state.getCode wa = C) {k : B256} {Inv : B256 → Prop}
    (initial : Inv ((checkpoint.state.getStor wa).get k))
    {before after : List Exec.Deriv} {n : Exec.Deriv}
    (split : history.rawNodes = before ++ n :: after)
    (safeBefore : ∀ m ∈ before, m.sevm.currentTarget = wa →
      ¬ Linst.At m.sevm.code m.pc .selfdestruct)
    (writesBefore : ∀ m ∈ before, ∀ w : Exec.StorageWrite,
      Exec.Deriv.successfulSstore? m = some w → w.owner = wa → w.key = k → Inv w.value) :
    Inv ((Devm.getStor n.devm wa).get k) := by
  obtain ⟨hcell, -⟩ := history.cellProv_at hCdel hCne capabilities k
    installed split safeBefore
  rcases hcell with hinit | ⟨b₁, b₂, m, w, hb, hfound, hown, hkey, hval⟩
  · rw [hinit]
    exact initial
  · rw [← hval]
    exact writesBefore m (by rw [hb]; exact List.mem_append_right _ List.mem_cons_self)
      w hfound hown hkey

/-- **At a raw frame's entry**: the frame root is its own first raw node, so
it sees the checkpoint code and an invariant cell. -/
theorem ConfiguredHistoryTraceIn.rawFrame_entryCellInv
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    {wa : Adr} {C : ByteArray}
    (hCdel : ¬ isValidDelegation C) (hCne : C.toList ≠ [])
    (installed : checkpoint.state.getCode wa = C) {k : B256} {Inv : B256 → Prop}
    (initial : Inv ((checkpoint.state.getStor wa).get k))
    {before after : List Exec.Deriv} {R : Exec.Deriv}
    (member : R ∈ history.rawFrames)
    (split : history.rawNodes = before ++ R :: after)
    (safeBefore : ∀ m ∈ before, m.sevm.currentTarget = wa →
      ¬ Linst.At m.sevm.code m.pc .selfdestruct)
    (writesBefore : ∀ m ∈ before, ∀ w : Exec.StorageWrite,
      Exec.Deriv.successfulSstore? m = some w → w.owner = wa → w.key = k → Inv w.value) :
    R.devm.getCode wa = C ∧ Inv ((Devm.getStor R.devm wa).get k) := by
  have _ := member
  exact ⟨(history.cellProv_at hCdel hCne capabilities k installed split
      safeBefore).2,
    history.rawNode_cellInv capabilities hCdel hCne installed initial split
      safeBefore writesBefore⟩

end ExecutionTrace

end Blanc
