import Blanc.ExecutionNoDelTransaction
import Blanc.ExecutionNoDelSafeHistory
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
  exact trace.noDel_of_safe K.notDelegation K.nonempty hsg installed notCreated
    (trace.safeRawFrames_of_installedCert hc callOnly noSelfdestruct K.notDelegation
      K.nonempty hsg installed notCreated)

/-- The two checked request calls keep a protected installed runtime. -/
theorem RequestsTrace.noDel_of_installedCert (K : InstalledCert C)
    {benv : Benv} {bout : BlockOutput} {state : State} {bout' : BlockOutput}
    (trace : RequestsTrace benv bout state bout')
    (hsg : benv.stat.rules.stateGas = none)
    (installed : benv.state.getCode wa = C) (notCreated : wa ∉ benv.createdAccounts) :
    wa ∉ trace.withdrawalOut.accountsToDelete ∧
      wa ∉ trace.consolidationOut.accountsToDelete ∧ state.getCode wa = C := by
  obtain ⟨c, hc, callOnly, noSelfdestruct⟩ := K.exists_cert
  exact trace.noDel_of_safe K.notDelegation K.nonempty hsg installed notCreated
    (trace.safeRawFrames_of_installedCert hc callOnly noSelfdestruct K.notDelegation
      K.nonempty hsg installed notCreated)

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
  exact trace.noDel_of_safe K.notDelegation K.nonempty hsg installed notCreated
    (trace.safeRawFrames_of_installedCert hc callOnly noSelfdestruct K.notDelegation
      K.nonempty hsg installed notCreated)

/-- The beacon stage keeps a protected installed runtime. -/
theorem BeaconStageTrace.code_of_installedCert (K : InstalledCert C)
    {rules : ForkRules} {benv : Benv} {state : State} {bal : BalBuilder}
    (trace : BeaconStageTrace rules benv state bal)
    (hsg : benv.stat.rules.stateGas = none)
    (installed : benv.state.getCode wa = C) (notCreated : wa ∉ benv.createdAccounts) :
    state.getCode wa = C := by
  obtain ⟨c, hc, callOnly, noSelfdestruct⟩ := K.exists_cert
  exact trace.code_of_safe K.notDelegation K.nonempty hsg installed notCreated
    (trace.safeRawFrames_of_installedCert hc callOnly noSelfdestruct K.notDelegation
      K.nonempty hsg installed notCreated)

/-- The history-storage stage keeps a protected installed runtime. -/
theorem HistoryStageTrace.code_of_installedCert (K : InstalledCert C)
    {rules : ForkRules} {benv : Benv} {inputBal : BalBuilder} {state : State}
    {bal : BalBuilder}
    (trace : HistoryStageTrace rules benv inputBal state bal)
    (hsg : benv.stat.rules.stateGas = none)
    (installed : benv.state.getCode wa = C) (notCreated : wa ∉ benv.createdAccounts) :
    state.getCode wa = C := by
  obtain ⟨c, hc, callOnly, noSelfdestruct⟩ := K.exists_cert
  exact trace.code_of_safe K.notDelegation K.nonempty hsg installed notCreated
    (trace.safeRawFrames_of_installedCert hc callOnly noSelfdestruct K.notDelegation
      K.nonempty hsg installed notCreated)

/-- The request stage keeps a protected installed runtime. -/
theorem RequestStageTrace.code_of_installedCert (K : InstalledCert C)
    {rules : ForkRules} {benv : Benv} {bout : BlockOutput} {state : State}
    {bout' : BlockOutput}
    (trace : RequestStageTrace rules benv bout state bout')
    (hsg : benv.stat.rules.stateGas = none)
    (installed : benv.state.getCode wa = C) (notCreated : wa ∉ benv.createdAccounts) :
    state.getCode wa = C := by
  obtain ⟨c, hc, callOnly, noSelfdestruct⟩ := K.exists_cert
  exact trace.code_of_safe K.notDelegation K.nonempty hsg installed notCreated
    (trace.safeRawFrames_of_installedCert hc callOnly noSelfdestruct K.notDelegation
      K.nonempty hsg installed notCreated)

/-- **A staged body keeps a protected installed runtime**, stage by stage in `applyBody` order,
and no selected transaction of it schedules `wa` for deletion. -/
theorem StagedBodyTrace.noDel_of_installedCert (K : InstalledCert C)
    {benv : Benv} {txs : List (Bytes ⊕ Tx)} {ommers : List Header}
    {wds : List Withdrawal} {state : State} {bout : BlockOutput}
    (trace : StagedBodyTrace benv txs ommers wds state bout)
    (hsg : benv.stat.rules.stateGas = none)
    (installed : benv.state.getCode wa = C) (notCreated : wa ∉ benv.createdAccounts) :
    trace.transactions.NoDelScheduled wa ∧ state.getCode wa = C := by
  obtain ⟨c, hc, callOnly, noSelfdestruct⟩ := K.exists_cert
  exact trace.noDel_of_safe K.notDelegation K.nonempty hsg installed notCreated
    (trace.safeRawFrames_of_installedCert hc callOnly noSelfdestruct K.notDelegation
      K.nonempty hsg installed notCreated)

/-- **A configured block keeps a protected installed runtime**, with per-block
`stateGas = none` from the history's own capability evidence. -/
theorem ConfiguredBlockTraceIn.noDel_of_installedCert (K : InstalledCert C)
    {F : Fork → Prop} {cfg : ChainConfig} {pre post : BlockChain}
    (trace : ConfiguredBlockTraceIn F cfg pre post)
    (capabilities : BodyStageCapabilities F)
    (installed : pre.state.getCode wa = C) :
    trace.NoDelScheduled wa ∧ post.state.getCode wa = C := by
  obtain ⟨c, hc, callOnly, noSelfdestruct⟩ := K.exists_cert
  exact trace.noDel_of_safe K.notDelegation K.nonempty capabilities installed
    (trace.safeRawFrames_of_installedCert hc callOnly noSelfdestruct K.notDelegation
      K.nonempty capabilities installed)

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
  obtain ⟨c, hc, callOnly, noSelfdestruct⟩ := K.exists_cert
  exact history.noDel_of_safe K.notDelegation K.nonempty capabilities installed
    (history.safeRawFrames_of_installedCert hc callOnly noSelfdestruct K.notDelegation
      K.nonempty capabilities installed)

end ExecutionTrace

end Blanc
