import Blanc.ExecutionNoDelTransaction
import Blanc.ExecutionHistoryInStateTrace
import Blanc.ExecutionTraceCodeAt

/-!
# Protected-account code survival and no-deletion across configured histories

`Blanc/ExecutionNoDelTransaction.lean` keeps an account `wa` holding an installed checked
runtime `C` (`InstalledCert C`: a certificate check, `callOnly`, `noSelfdestruct`, no EIP-7702
designator, nonempty) through one selected transaction under `stateGas = none`. This module
threads that fact through every stage of a block body in `applyBody` order and along a
configured In-history, with no `CoveredFork` (per-block `stateGas = none` comes from
`BodyStageCapabilities F`) and no premise that `wa` is never targeted:

* system messages (beacon roots, history storage, the two checked request calls) are ordinary
  message calls to their fixed system targets, with empty inherited deletions; a system target
  equal to `wa` runs `wa`'s own checked code and is covered by the same argument;
* transaction lists thread `installed` through each transaction; `createdAccounts` is constant
  along a body (`Benv.withState`) and empty at `initBenv`, so `wa` is never block-created;
* withdrawals and proof-of-work rewards only credit balances.

`ConfiguredHistoryTraceIn.noDel_of_installedCert` is the target: the checkpoint's code `C` at
`wa` is the code at `wa` in the endpoint state of the history (by induction, at every checkpoint
of its spine), and no selected transaction along it schedules `wa` for deletion
(`ConfiguredHistoryTraceIn.NoDelScheduled`).
-/

namespace Blanc

open Jaune

/-- A byte array of nonzero size has a nonempty byte list. -/
theorem toList_ne_nil_of_size_ne_zero {C : ByteArray} (h : C.size ≠ 0) : C.toList ≠ [] := by
  intro hnil
  apply h
  rw [ByteArray.size_eq_length_toList, hnil, List.length_nil]

/-- The actual facts about an installed runtime `C` that the no-deletion producer consumes. -/
structure InstalledCert (C : ByteArray) : Prop where
  exists_cert : ∃ c : Lift.Cert, Lift.Cert.check C c = true ∧ c.callOnly = true ∧
    c.noSelfdestruct = true
  notDelegation : ¬ isValidDelegation C
  nonempty : C.toList ≠ []

/-- Proof-of-work rewards only credit balances. -/
theorem payRewards_getCode (pow : PowRules) (number : Nat) (coinbase : Adr)
    (ommers : List Header) (st : State) (a : Adr) :
    (payRewards pow number coinbase ommers st).getCode a = st.getCode a := by
  unfold payRewards
  suffices h : ∀ (os : List Header) (s : State),
      (os.foldl (fun acc ommer => acc.addBal ommer.coinbase
        ((8 + ommer.number - number) * pow.blockReward / 8).toB256) s).getCode a = s.getCode a by
    rw [h, State.addBal_getCode]
  intro os
  induction os with
  | nil => intro s; rfl
  | cons o os ih =>
      intro s
      rw [List.foldl_cons, ih, State.addBal_getCode]

namespace ExecutionTrace

variable {wa : Adr} {C : ByteArray}

/-- **A system message keeps a protected installed runtime**, and never schedules `wa` for
deletion, under `stateGas = none`. A system message is an ordinary message call to its target
with empty inherited deletions; no premise that `wa` differs from the target is needed. -/
theorem SystemMessageTrace.noDel_of_installedCert (K : InstalledCert C)
    {benv : Benv} {target : Adr} {data : Bytes} {state : State} {out : MsgCallOutput}
    (trace : SystemMessageTrace benv target data state out)
    (hsg : benv.stat.rules.stateGas = none)
    (installed : benv.state.getCode wa = C) (notCreated : wa ∉ benv.createdAccounts) :
    wa ∉ out.accountsToDelete ∧ state.getCode wa = C := by
  obtain ⟨c, hc, callOnly, noSelfdestruct⟩ := K.exists_cert
  exact trace.message.noDel_of_installedCert hc callOnly noSelfdestruct K.notDelegation hsg
    installed (fun _ => ⟨rfl, rfl⟩)
    ⟨notCreated, show (benv.state.getCode wa).toList ≠ [] by rw [installed]; exact K.nonempty⟩
    AdrSet.not_mem_empty

/-- The two checked request calls keep a protected installed runtime. -/
theorem RequestsTrace.noDel_of_installedCert (K : InstalledCert C)
    {benv : Benv} {bout : BlockOutput} {state : State} {bout' : BlockOutput}
    (trace : RequestsTrace benv bout state bout')
    (hsg : benv.stat.rules.stateGas = none)
    (installed : benv.state.getCode wa = C) (notCreated : wa ∉ benv.createdAccounts) :
    wa ∉ trace.withdrawalOut.accountsToDelete ∧
      wa ∉ trace.consolidationOut.accountsToDelete ∧ state.getCode wa = C := by
  obtain ⟨hw, hwCode⟩ := trace.withdrawal.noDel_of_installedCert K hsg installed notCreated
  obtain ⟨hc, hcCode⟩ := trace.consolidation.noDel_of_installedCert
    (benv := benv.withState trace.withdrawalState) K hsg hwCode notCreated
  exact ⟨hw, hc, by rw [trace.state_eq_consolidationState]; exact hcCode⟩

/-- No retained transaction of the list schedules `wa` for deletion. -/
def ApplyTransactionsTrace.NoDelScheduled (wa : Adr) :
    {txs : List (Nat × Tx)} → {benv : Benv} → {bout : BlockOutput} →
    {finalBenv : Benv} → {finalBout : BlockOutput} →
    ApplyTransactionsTrace txs benv bout finalBenv finalBout → Prop
  | _, _, _, _, _, .nil _ _ => True
  | _, _, _, _, _, .cons head tail =>
      wa ∉ head.messageOut.accountsToDelete ∧ tail.NoDelScheduled wa

/-- **A selected transaction list keeps a protected installed runtime** and schedules no
deletion of `wa`, under `stateGas = none`, when `wa` is not block-created. -/
theorem ApplyTransactionsTrace.noDel_of_installedCert (K : InstalledCert C)
    {txs : List (Nat × Tx)} {benv finalBenv : Benv}
    {bout finalBout : BlockOutput}
    (trace : ApplyTransactionsTrace txs benv bout finalBenv finalBout)
    (hsg : benv.stat.rules.stateGas = none)
    (installed : benv.state.getCode wa = C) (notCreated : wa ∉ benv.createdAccounts) :
    trace.NoDelScheduled wa ∧ finalBenv.state.getCode wa = C := by
  obtain ⟨c, hc, callOnly, noSelfdestruct⟩ := K.exists_cert
  induction trace with
  | nil => exact ⟨trivial, installed⟩
  | cons head tail ih =>
      obtain ⟨hnot, -, hstate⟩ := head.noDel_of_installedCert hc callOnly noSelfdestruct
        K.notDelegation K.nonempty hsg installed notCreated
      obtain ⟨htail, hfinal⟩ := ih hsg hstate notCreated
      exact ⟨⟨hnot, htail⟩, hfinal⟩

/-- The beacon stage keeps a protected installed runtime. -/
theorem BeaconStageTrace.code_of_installedCert (K : InstalledCert C)
    {rules : ForkRules} {benv : Benv} {state : State} {bal : BalBuilder}
    (trace : BeaconStageTrace rules benv state bal)
    (hsg : benv.stat.rules.stateGas = none)
    (installed : benv.state.getCode wa = C) (notCreated : wa ∉ benv.createdAccounts) :
    state.getCode wa = C := by
  cases trace with
  | skipped => exact installed
  | called _ _ message _ _ =>
      exact (message.noDel_of_installedCert K hsg installed notCreated).2

/-- The history-storage stage keeps a protected installed runtime. -/
theorem HistoryStageTrace.code_of_installedCert (K : InstalledCert C)
    {rules : ForkRules} {benv : Benv} {inputBal : BalBuilder} {state : State}
    {bal : BalBuilder}
    (trace : HistoryStageTrace rules benv inputBal state bal)
    (hsg : benv.stat.rules.stateGas = none)
    (installed : benv.state.getCode wa = C) (notCreated : wa ∉ benv.createdAccounts) :
    state.getCode wa = C := by
  cases trace with
  | skipped => exact installed
  | called _ _ _ _ message _ _ =>
      exact (message.noDel_of_installedCert K hsg installed notCreated).2

/-- The request stage keeps a protected installed runtime. -/
theorem RequestStageTrace.code_of_installedCert (K : InstalledCert C)
    {rules : ForkRules} {benv : Benv} {bout : BlockOutput} {state : State}
    {bout' : BlockOutput}
    (trace : RequestStageTrace rules benv bout state bout')
    (hsg : benv.stat.rules.stateGas = none)
    (installed : benv.state.getCode wa = C) (notCreated : wa ∉ benv.createdAccounts) :
    state.getCode wa = C := by
  cases trace with
  | skipped => exact installed
  | called _ requests _ =>
      exact (requests.noDel_of_installedCert K hsg installed notCreated).2.2

/-- **A staged body keeps a protected installed runtime**, stage by stage in `applyBody` order,
and no selected transaction of it schedules `wa` for deletion. -/
theorem StagedBodyTrace.noDel_of_installedCert (K : InstalledCert C)
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout)
    (hsg : benv.stat.rules.stateGas = none)
    (installed : benv.state.getCode wa = C) (notCreated : wa ∉ benv.createdAccounts) :
    trace.transactions.NoDelScheduled wa ∧ state.getCode wa = C := by
  have hbeacon := trace.beacon.code_of_installedCert K hsg installed notCreated
  have hhistory := trace.history.code_of_installedCert (benv := benv.withState trace.beaconState)
    K hsg hbeacon notCreated
  obtain ⟨hsched, htx⟩ := trace.transactions.noDel_of_installedCert
    (benv := (benv.withState trace.beaconState).withState trace.historyState)
    K hsg hhistory notCreated
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
  have hrequest := trace.requests.code_of_installedCert
    (benv := trace.transactionBenv.withState trace.withdrawalState) K
    (by change trace.transactionBenv.stat.rules.stateGas = none; rw [txStat]; exact hsg)
    hwithdrawal
    (by change wa ∉ trace.transactionBenv.createdAccounts; rw [txCreated]; exact notCreated)
  refine ⟨hsched, ?_⟩
  rw [trace.finalState_eq, trace.rewardState_eq]
  split
  · exact hrequest
  · rw [payRewards_getCode]
    exact hrequest

/-- No selected transaction of a retained block schedules `wa` for deletion. -/
def ConfiguredBlockTraceIn.NoDelScheduled {F : Fork → Prop} {cfg : ChainConfig}
    {pre post : BlockChain} (trace : ConfiguredBlockTraceIn F cfg pre post) (wa : Adr) : Prop :=
  trace.bodyTrace.transactions.NoDelScheduled wa

/-- **A configured block keeps a protected installed runtime**, with per-block
`stateGas = none` from the history's own capability evidence. -/
theorem ConfiguredBlockTraceIn.noDel_of_installedCert (K : InstalledCert C)
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTraceIn F cfg pre post)
    (capabilities : BodyStageCapabilities F)
    (installed : pre.state.getCode wa = C) :
    trace.NoDelScheduled wa ∧ post.state.getCode wa = C := by
  obtain ⟨hsched, hstate⟩ := trace.bodyTrace.noDel_of_installedCert K
    (capabilities.stateGas_none trace.forkIn) installed AdrSet.not_mem_empty
  refine ⟨hsched, ?_⟩
  rw [trace.postEq]
  exact hstate

/-- No selected transaction of any block of a retained history schedules `wa` for deletion. -/
def ConfiguredHistoryTraceIn.NoDelScheduled {F : Fork → Prop} {cfg : ChainConfig}
    {checkpoint : BlockChain} (wa : Adr) :
    {future : BlockChain} → ConfiguredHistoryTraceIn F cfg checkpoint future → Prop
  | _, .refl _ _ _ => True
  | _, .step prior block => prior.NoDelScheduled wa ∧ block.NoDelScheduled wa

/-- **Code survival and no-deletion along a configured history.** If the checkpoint holds an
installed checked runtime `C` at `wa`, the endpoint state of a retained In-history holds `C` at
`wa` (by induction, so does every checkpoint of its spine), and no selected transaction along it
schedules `wa` for deletion. No `CoveredFork`; per-block `stateGas = none` from
`BodyStageCapabilities F`; no premise that `wa` is never targeted. -/
theorem ConfiguredHistoryTraceIn.noDel_of_installedCert (K : InstalledCert C)
    {F : Fork → Prop} {cfg : ChainConfig} {checkpoint future : BlockChain}
    (history : ConfiguredHistoryTraceIn F cfg checkpoint future)
    (capabilities : BodyStageCapabilities F)
    (installed : checkpoint.state.getCode wa = C) :
    history.NoDelScheduled wa ∧ future.state.getCode wa = C := by
  induction history with
  | refl => exact ⟨trivial, installed⟩
  | step prior block ih =>
      obtain ⟨hprior, hcurrent⟩ := ih
      obtain ⟨hblock, hpost⟩ := block.noDel_of_installedCert K capabilities hcurrent
      exact ⟨⟨hprior, hblock⟩, hpost⟩

end ExecutionTrace

end Blanc
