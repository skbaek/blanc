import Blanc.ExecutionNoDelSafeHistory
import Blanc.ExecutionInCodeImage
import Blanc.ExecutionInOwnCode

/-!
# Safe-parametric per-frame code image over In-carrier staged histories

Contract-neutral analogue of `ConfiguredHistoryTraceIn.rawFrames_codeImage_of_installedIn`
(`Blanc/ExecutionInCodeImage.lean`) with the installed certificate replaced by
what the proof actually consumes, following `Blanc/ExecutionNoDelSafeHistory.lean`
(G4a): a raw-frame safety premise (`ExecutionTrace.SafeRawFrames`,
reused as stated — no new definition) plus the code facts on `C` at `wa`
(`C.toList ≠ []`, `¬ isValidDelegation C`).

Route: G4a gives no-deletion and code survival block by block
(`ConfiguredHistoryTraceIn.noDel_of_safe`); per raw frame, the code at `wa`
equals `C` at every raw-frame start because no transaction in between deletes
or re-creates `wa`. Concretely each message-level entry world still holds `C`
(threaded forward with G4a's `…_of_safe` chain), and inside one message every
raw root keeps its entry world's code (`Exec.rawFrameRoots_codePreserve`,
as in `RetainedXlot.rawFrames_codeImage`). No `CoveredFork`, no
`InstalledCert`, no `callOnly`, no fixed access or delegation premise — so a
proxy whose runtime `DELEGATECALL`s can produce `safe` (via per-frame execution
evidence) together with the two code facts.

Reused (not copied): `ExecutionTrace.SafeRawFrames` and the whole
`…_of_safe` / `…_code_of_safe` threading chain from
`Blanc/ExecutionNoDelSafeHistory.lean`; `Exec.rawFrameRoots_codePreserve`
from `Blanc/LockExclusion.lean`; `messageCallExecutionMessage_getCode` and
`processCreateMessage.msg_getCode` from `Blanc/ExecutionTraceCodeAt.lean`;
the public `setDelegation_benv_equiv` from `Blanc/LadderBase.lean` for the
one delegation-prefix step below. The only local helper is
`delegation_keeps_code` (EIP-7702 prefix keeps `wa`'s code), since G4a's
version is private to its file.
-/

namespace Blanc

open Jaune

namespace ExecutionTrace

/-- Every raw root of a retained slot keeps its entry world's code at `wa`.
This is the `getCode wa = C` analogue of `RetainedXlot.rawFrames_codeImage`,
stated with the entry equation so each message arm can supply its own. -/
theorem RetainedXlot.codeImage_of_safe_entry {wa : Adr} {C : ByteArray}
    {frame : Frame} {slot : Xlot}
    {out : Except (EvmError × State × AdrSet × Tra) Devm}
    (retained : RetainedXlot slot) (hrun : RunFrame frame slot out)
    (entryCode : frame.inner.benv.state.getCode wa = C) (hCne : C.toList ≠ []) :
    ∀ root ∈ retained.rawFrames, root.devm.getCode wa = C := by
  cases retained with
  | none => intro root member; simp only [RetainedXlot.rawFrames, List.not_mem_nil] at member
  | @some pc sevm pre execution run =>
      obtain ⟨henter, _⟩ := RunFrame.some_inv hrun
      have hcode : pre.getCode wa = frame.inner.benv.state.getCode wa :=
        Frame.enter_run_getCode henter wa
      have nonempty : (pre.getCode wa).toList ≠ [] := by
        rw [hcode, entryCode]
        exact hCne
      intro root member
      rw [Exec.rawFrameRoots_codePreserve run wa nonempty root member, hcode]
      exact entryCode

/-- The EIP-7702 authorization prefix keeps `wa`'s code: without authorizations
it is the identity, otherwise the public `setDelegation_benv_equiv` keeps the
nonempty undesignated code. G4a proves this as a private four-conjunct
theorem; only the code equation is needed here. -/
private theorem delegation_keeps_code {wa : Adr}
    {msg delegated : Msg} {refund : Nat}
    (run : messageCallDelegation msg = .ok ⟨delegated, refund⟩)
    (h : Msg.NoDel wa msg) (hCdel : ¬ isValidDelegation (msg.benv.state.getCode wa)) :
    delegated.benv.state.getCode wa = msg.benv.state.getCode wa := by
  unfold messageCallDelegation processMessageCall.legacyAuthorization at run
  split at run
  · simp only [Except.ok.injEq, Prod.mk.injEq] at run
    rcases run with ⟨rfl, -⟩
    rfl
  · obtain ⟨⟨middle, counter⟩, hdel, rest⟩ := Except.bind_eq_ok run
    simp only [Except.ok.injEq, Prod.mk.injEq] at rest
    rcases rest with ⟨rfl, -⟩
    exact (setDelegation_benv_equiv hdel).2 wa h.code hCdel

/-- **A settled message call keeps a protected code at every raw frame.**
The collision arm retains nothing; the create arm enters the prepared inner
message (whose world holds `msg`'s code); the call arm enters the resolved
execution message (authorization prefix and code-delegation resolution keep
`wa`'s undesignated code). Inside each arm the retained roots keep their
entry code. -/
theorem MessageCallTrace.codeImage_of_safe {wa : Adr} {C : ByteArray}
    (hCdel : ¬ isValidDelegation C) (hCne : C.toList ≠ [])
    {msg : Msg} {state : State} {out : MsgCallOutput}
    (trace : MessageCallTrace msg state out)
    (installed : msg.benv.state.getCode wa = C) (h : Msg.NoDel wa msg) :
    ∀ R ∈ trace.rawFrames, R.devm.getCode wa = C := by
  cases trace with
  | createCollision =>
      intro R hR
      simp only [MessageCallTrace.rawFrames, List.not_mem_nil] at hR
  | createRun target collision evm core coreTrace result =>
      have hentry : (Frame.ofCreate msg).inner.benv.state.getCode wa = C := by
        rw [show (Frame.ofCreate msg).inner = processCreateMessage.msg msg from rfl,
          processCreateMessage.msg_getCode]
        exact installed
      intro R hR
      simp only [MessageCallTrace.rawFrames, ProcessCreateMessageTrace.rawFrames] at hR
      exact RetainedXlot.codeImage_of_safe_entry coreTrace.retained coreTrace.run
        hentry hCne R hR
  | callRun target delegated refund delegation execMsg execMsgEq evm core coreTrace result =>
      have hdCode : delegated.benv.state.getCode wa = msg.benv.state.getCode wa :=
        delegation_keeps_code delegation h (by rw [installed]; exact hCdel)
      have execState : execMsg.benv.state.getCode wa = C := by
        rw [execMsgEq, messageCallExecutionMessage_getCode, hdCode, installed]
      intro R hR
      simp only [MessageCallTrace.rawFrames, ProcessMessageTrace.rawFrames] at hR
      exact RetainedXlot.codeImage_of_safe_entry coreTrace.retained coreTrace.run
        execState hCne R hR

/-- **A selected transaction keeps a protected code at every raw frame.**
The message entry world holds `C` across the nonce/balance debit, as in
`TransactionTrace.noDel_of_safe`; the transaction enumerates its message's
roots. -/
theorem TransactionTrace.codeImage_of_safe {wa : Adr} {C : ByteArray}
    (hCdel : ¬ isValidDelegation C) (hCne : C.toList ≠ [])
    {benv : Benv} {bout : BlockOutput} {tx : Tx} {index : Nat}
    {state : State} {bout' : BlockOutput}
    (trace : TransactionTrace benv bout tx index state bout')
    (installed : benv.state.getCode wa = C) (notCreated : wa ∉ benv.createdAccounts) :
    ∀ R ∈ trace.rawFrames, R.devm.getCode wa = C := by
  have hbenv := prepareMessage_benv trace.prepared
  have hdebit : trace.debitState.getCode wa = benv.state.getCode wa := by
    rw [State.subBal_getCode trace.debit]
    unfold State.getCode
    rw [State.incrNonce_get_code]
  have hmsgState : trace.msg.benv.state.getCode wa = C := by
    rw [hbenv]
    exact hdebit.trans installed
  have hnodel : Msg.NoDel wa trace.msg := by
    refine ⟨?_, ?_⟩
    · rw [hbenv]
      simpa only [Benv.beginTransaction] using notCreated
    · rw [hmsgState]
      exact hCne
  exact trace.message.codeImage_of_safe hCdel hCne hmsgState hnodel

/-- **A system message keeps a protected code at every raw frame.** A system
message is an ordinary message call to its target; no premise that `wa`
differs from the target is needed. -/
theorem SystemMessageTrace.codeImage_of_safe {wa : Adr} {C : ByteArray}
    (hCdel : ¬ isValidDelegation C) (hCne : C.toList ≠ [])
    {benv : Benv} {target : Adr} {data : Bytes} {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out)
    (installed : benv.state.getCode wa = C) (notCreated : wa ∉ benv.createdAccounts) :
    ∀ R ∈ trace.rawFrames, R.devm.getCode wa = C := by
  exact trace.message.codeImage_of_safe hCdel hCne installed
    ⟨notCreated, show (benv.state.getCode wa).toList ≠ [] by rw [installed]; exact hCne⟩

/-- **The two checked request calls keep a protected code at every raw frame.**
The consolidation entry code comes back out of the withdrawal's safe chain. -/
theorem RequestsTrace.codeImage_of_safe {wa : Adr} {C : ByteArray}
    (hCdel : ¬ isValidDelegation C) (hCne : C.toList ≠ [])
    {benv : Benv} {bout : BlockOutput} {state : State} {bout' : BlockOutput}
    (trace : RequestsTrace benv bout state bout')
    (hsg : benv.stat.rules.stateGas = none)
    (installed : benv.state.getCode wa = C) (notCreated : wa ∉ benv.createdAccounts)
    (safe : SafeRawFrames wa trace.rawFrames) :
    ∀ R ∈ trace.rawFrames, R.devm.getCode wa = C := by
  have hwCode : trace.withdrawalState.getCode wa = C :=
    (trace.withdrawal.noDel_of_safe hCdel hCne hsg installed notCreated
      (SafeRawFrames.of_append_left safe)).2
  intro R hR
  simp only [RequestsTrace.rawFrames, List.mem_append] at hR
  rcases hR with h | h
  · exact trace.withdrawal.codeImage_of_safe hCdel hCne installed notCreated R h
  · exact trace.consolidation.codeImage_of_safe
      (benv := benv.withState trace.withdrawalState)
      hCdel hCne hwCode notCreated R h

/-- **A selected transaction list keeps a protected code at every raw frame.**
The next entry code comes back out of the head's safe chain. -/
theorem ApplyTransactionsTrace.codeImage_of_safe {wa : Adr} {C : ByteArray}
    (hCdel : ¬ isValidDelegation C) (hCne : C.toList ≠ [])
    {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (hsg : benv.stat.rules.stateGas = none)
    (installed : benv.state.getCode wa = C) (notCreated : wa ∉ benv.createdAccounts)
    (safe : SafeRawFrames wa trace.rawFrames) :
    ∀ R ∈ trace.rawFrames, R.devm.getCode wa = C := by
  induction trace with
  | nil =>
      intro R hR
      simp only [ApplyTransactionsTrace.rawFrames, List.not_mem_nil] at hR
  | cons head tail ih =>
      have safeHead : SafeRawFrames wa head.rawFrames :=
        SafeRawFrames.of_append_left safe
      have safeTail : SafeRawFrames wa tail.rawFrames :=
        SafeRawFrames.of_append_right safe
      obtain ⟨-, -, hstate⟩ := head.noDel_of_safe hCdel hCne hsg installed notCreated
        safeHead
      intro R hR
      simp only [ApplyTransactionsTrace.rawFrames, List.mem_append] at hR
      rcases hR with h | h
      · exact head.codeImage_of_safe hCdel hCne installed notCreated R h
      · exact ih hsg hstate notCreated safeTail R h

/-- The beacon stage keeps a protected code at every raw frame. -/
theorem BeaconStageTrace.codeImage_of_safe {wa : Adr} {C : ByteArray}
    (hCdel : ¬ isValidDelegation C) (hCne : C.toList ≠ [])
    {rules : ForkRules} {benv : Benv} {state : State} {bal : BalBuilder}
    (trace : BeaconStageTrace rules benv state bal)
    (installed : benv.state.getCode wa = C) (notCreated : wa ∉ benv.createdAccounts) :
    ∀ R ∈ trace.rawFrames, R.devm.getCode wa = C := by
  cases trace with
  | skipped =>
      intro R hR
      simp only [BeaconStageTrace.rawFrames, List.not_mem_nil] at hR
  | called _ _ message _ _ =>
      exact message.codeImage_of_safe hCdel hCne installed notCreated

/-- The history-storage stage keeps a protected code at every raw frame. -/
theorem HistoryStageTrace.codeImage_of_safe {wa : Adr} {C : ByteArray}
    (hCdel : ¬ isValidDelegation C) (hCne : C.toList ≠ [])
    {rules : ForkRules} {benv : Benv} {inputBal : BalBuilder} {state : State}
    {bal : BalBuilder}
    (trace : HistoryStageTrace rules benv inputBal state bal)
    (installed : benv.state.getCode wa = C) (notCreated : wa ∉ benv.createdAccounts) :
    ∀ R ∈ trace.rawFrames, R.devm.getCode wa = C := by
  cases trace with
  | skipped =>
      intro R hR
      simp only [HistoryStageTrace.rawFrames, List.not_mem_nil] at hR
  | called _ _ _ _ message _ _ =>
      exact message.codeImage_of_safe hCdel hCne installed notCreated

/-- The request stage keeps a protected code at every raw frame. -/
theorem RequestStageTrace.codeImage_of_safe {wa : Adr} {C : ByteArray}
    (hCdel : ¬ isValidDelegation C) (hCne : C.toList ≠ [])
    {rules : ForkRules} {benv : Benv} {bout : BlockOutput} {state : State}
    {bout' : BlockOutput}
    (trace : RequestStageTrace rules benv bout state bout')
    (hsg : benv.stat.rules.stateGas = none)
    (installed : benv.state.getCode wa = C) (notCreated : wa ∉ benv.createdAccounts)
    (safe : SafeRawFrames wa trace.rawFrames) :
    ∀ R ∈ trace.rawFrames, R.devm.getCode wa = C := by
  cases trace with
  | skipped =>
      intro R hR
      simp only [RequestStageTrace.rawFrames, List.not_mem_nil] at hR
  | called _ requests _ =>
      exact requests.codeImage_of_safe hCdel hCne hsg installed notCreated safe

/-- **A staged body keeps a protected code at every raw frame**, stage by stage
in `applyBody` order. Stage entry codes thread exactly as in
`StagedBodyTrace.noDel_of_safe`; each stage's frames then keep their entry
code. -/
theorem StagedBodyTrace.codeImage_of_safe {wa : Adr} {C : ByteArray}
    (hCdel : ¬ isValidDelegation C) (hCne : C.toList ≠ [])
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout)
    (hsg : benv.stat.rules.stateGas = none)
    (installed : benv.state.getCode wa = C) (notCreated : wa ∉ benv.createdAccounts)
    (safe : SafeRawFrames wa trace.rawFrames) :
    ∀ R ∈ trace.rawFrames, R.devm.getCode wa = C := by
  have rawEq : trace.rawFrames =
      trace.beacon.rawFrames ++ trace.history.rawFrames ++
        trace.transactions.rawFrames ++ trace.requests.rawFrames := rfl
  -- Split the unfolded enumeration. `List.append` chains nest to the left
  -- here (`((b ++ h) ++ t) ++ r`), as in `StagedBodyTrace.noDel_of_safe`.
  have safeBeacon : SafeRawFrames wa trace.beacon.rawFrames := by
    intro R hR
    exact (rawEq ▸ safe) R (List.mem_append_left trace.requests.rawFrames
      (List.mem_append_left trace.transactions.rawFrames
        (List.mem_append_left trace.history.rawFrames hR)))
  have safeHistory : SafeRawFrames wa trace.history.rawFrames := by
    intro R hR
    exact (rawEq ▸ safe) R (List.mem_append_left trace.requests.rawFrames
      (List.mem_append_left trace.transactions.rawFrames
        (List.mem_append_right trace.beacon.rawFrames hR)))
  have safeTx : SafeRawFrames wa trace.transactions.rawFrames := by
    intro R hR
    exact (rawEq ▸ safe) R (List.mem_append_left trace.requests.rawFrames
      (List.mem_append_right
        (trace.beacon.rawFrames ++ trace.history.rawFrames) hR))
  have safeReq : SafeRawFrames wa trace.requests.rawFrames := by
    intro R hR
    exact (rawEq ▸ safe) R (List.mem_append_right
      (trace.beacon.rawFrames ++ trace.history.rawFrames ++ trace.transactions.rawFrames)
      hR)
  -- Stage entry codes thread exactly as in `StagedBodyTrace.noDel_of_safe`.
  have hbeaconCode := trace.beacon.code_of_safe hCdel hCne hsg installed notCreated
    safeBeacon
  have hhistoryCode := trace.history.code_of_safe (benv := benv.withState trace.beaconState)
    hCdel hCne hsg hbeaconCode notCreated safeHistory
  obtain ⟨-, htx⟩ := trace.transactions.noDel_of_safe
    (benv := (benv.withState trace.beaconState).withState trace.historyState)
    hCdel hCne hsg hhistoryCode notCreated safeTx
  have txStat : trace.transactionBenv.stat = benv.stat := trace.transactions.stat_eq
  have txCreated : trace.transactionBenv.createdAccounts = benv.createdAccounts :=
    trace.transactions.createdAccounts_eq
  have hwithdrawal : trace.withdrawalState.getCode wa = C := by
    have run := trace.withdrawalsRun
    cases enabled : benv.stat.rules.header.withdrawalsRoot with
    | false =>
        rw [(trace.withdrawals_disabled enabled).1]
        exact htx
    | true =>
        simp only [withdrawalsPass, processWithdrawals, enabled, ↓reduceIte] at run
        rw [← (Prod.mk.inj run).1, processWithdrawalsState_getCode]
        exact htx
  intro R hR
  simp only [StagedBodyTrace.rawFrames, List.mem_append] at hR
  rcases hR with ((hB | hH) | hT) | hReq
  · exact trace.beacon.codeImage_of_safe hCdel hCne installed notCreated R hB
  · exact trace.history.codeImage_of_safe (benv := benv.withState trace.beaconState)
      hCdel hCne hbeaconCode notCreated R hH
  · exact trace.transactions.codeImage_of_safe
      (benv := (benv.withState trace.beaconState).withState trace.historyState)
      hCdel hCne hsg hhistoryCode notCreated safeTx R hT
  · exact trace.requests.codeImage_of_safe
      (benv := trace.transactionBenv.withState trace.withdrawalState) hCdel hCne
      (by change trace.transactionBenv.stat.rules.stateGas = none; rw [txStat]; exact hsg)
      hwithdrawal
      (by change wa ∉ trace.transactionBenv.createdAccounts; rw [txCreated]; exact notCreated)
      safeReq R hReq

/-- **A configured block keeps a protected code at every raw frame**, with
per-block `stateGas = none` from the history's own capability evidence. -/
theorem ConfiguredBlockTraceIn.codeImage_of_safe {wa : Adr} {C : ByteArray}
    (hCdel : ¬ isValidDelegation C) (hCne : C.toList ≠ [])
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTraceIn F cfg pre post)
    (capabilities : BodyStageCapabilities F)
    (installed : pre.state.getCode wa = C)
    (safe : SafeRawFrames wa trace.rawFrames) :
    ∀ R ∈ trace.rawFrames, R.devm.getCode wa = C := by
  exact trace.bodyTrace.codeImage_of_safe hCdel hCne
    (capabilities.stateGas_none trace.forkIn) installed AdrSet.not_mem_empty safe

/-- **A protected code at every raw frame of a configured history**, from trace
safety and the code facts. If the checkpoint holds a nonempty, undesignated
code `C` at `wa`, every raw frame of a retained In-history — rolled back or
not — starts with `C` at `wa`: frames of the prior spine by induction, frames
of the head block from the prior endpoint's safe chain. No `CoveredFork`;
per-block `stateGas = none` from `BodyStageCapabilities F`; no premise that
`wa` is never targeted. -/
theorem ConfiguredHistoryTraceIn.rawFrames_codeImage_of_safe {wa : Adr} {C : ByteArray}
    (hCdel : ¬ isValidDelegation C) (hCne : C.toList ≠ [])
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    (installed : checkpoint.state.getCode wa = C)
    (safe : SafeRawFrames wa history.rawFrames) :
    ∀ R ∈ history.rawFrames, R.devm.getCode wa = C := by
  induction history with
  | refl =>
      intro R hR
      simp only [ConfiguredHistoryTraceIn.rawFrames, List.not_mem_nil] at hR
  | step prior block ih =>
      have safePrior : SafeRawFrames wa prior.rawFrames :=
        SafeRawFrames.of_append_left safe
      have safeBlock : SafeRawFrames wa block.rawFrames :=
        SafeRawFrames.of_append_right safe
      have hcurrent :=
        (prior.noDel_of_safe hCdel hCne capabilities installed safePrior).2
      intro R hR
      simp only [ConfiguredHistoryTraceIn.rawFrames, List.mem_append] at hR
      rcases hR with h | h
      · exact ih safePrior R h
      · exact block.codeImage_of_safe hCdel hCne capabilities hcurrent safeBlock R h

/-- **A protected code stays installed at every settled frame of an
In-history.** Settlement retains only raw roots, so the raw-frame version
applies through the settled-to-raw bridge; the root derivative's world is the
frame's entry world by construction. -/
theorem ConfiguredHistoryTraceIn.settled_codeImage_of_safe {wa : Adr} {C : ByteArray}
    (hCdel : ¬ isValidDelegation C) (hCne : C.toList ≠ [])
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    (installed : checkpoint.state.getCode wa = C)
    (safe : SafeRawFrames wa history.rawFrames) :
    ∀ f ∈ history.settledFrames, f.pre.getCode wa = C := by
  have code := history.rawFrames_codeImage_of_safe hCdel hCne capabilities installed safe
  intro f member
  exact code _ (history.mem_rawFrames_of_mem_settledFrames f member)

end ExecutionTrace

end Blanc
