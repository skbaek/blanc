import Blanc.BeaconDepositSuccessPublic
import Blanc.MessageExecutionInversion

/-!
# Beacon deposit settled success effect

The raw compiled success theorem is transported to the actual retained
message-entry frame.  The entry `Sevm` and `Devm` are kept explicit: a payable
deposit can change balances before code starts, so replacing the retained
entry state with `initDevm msg` would silently exclude the value-transfer
case.
-/

namespace Blanc.BeaconDeposit

open Jaune
open Jaune.Ninst Blanc.Ninst

/-- A retained direct-message execution whose model deposit succeeds settles
to the exact compiled poststate.  The theorem exposes the model-prescribed
count/branch storage effect and one canonical, byte-exact `DepositEvent` log
at the message boundary.

`hprocess` identifies the actual post-transfer entry frame.  `hfilled`
certifies that its raw result is an execution rather than merely a value
carried by the settlement relation. -/
theorem deposit_success_settled_effects
    {msg : Msg} {sevm : Sevm} {base final settled : Devm}
    (pubkey withdrawalCredentials signature : Bytes)
    (depositDataRoot : B256) (s' : Acc) (ev : DepositEvent)
    (stor : Stor) (keys : KeySet) (countCost n G : Nat)
    (hdataBound : sevm.data.length < 2 ^ 256)
    (hdec : DepositAbiDecodable sevm.data pubkey withdrawalCredentials
      signature depositDataRoot)
    (hOk : deposit Bytes.sha256
      (accOfStor (Devm.getStor base sevm.currentTarget))
      pubkey withdrawalCredentials signature depositDataRoot
      sevm.value.toNat = .ok (s', ev))
    (hstor : Devm.getStor
      (afterSstore sevm (afterSload sevm base depositCountSlot)
        depositCountSlot
        (Nat.toB256
          (accOfStor (Devm.getStor base sevm.currentTarget)).count + 1))
      sevm.currentTarget = stor)
    (hkeys :
      (afterSstore sevm (afterSload sevm base depositCountSlot)
        depositCountSlot
        (Nat.toB256
          (accOfStor
            (Devm.getStor base sevm.currentTarget)).count + 1)).accessedStorageKeys =
        keys)
    (hcount : sstoreCost sevm
      (afterSload sevm base depositCountSlot) depositCountSlot
      (Nat.toB256
        (accOfStor (Devm.getStor base sevm.currentTarget)).count + 1) =
      countCost)
    (hheight : n < 32)
    (hfirst : FirstLive
      ((accOfStor (Devm.getStor base sevm.currentTarget)).count + 1) n)
    (hselector : Sevm.selector sevm = depositSelector)
    (hnodeleg : getDelegatedCodeAddress (base.getCode 2) = none)
    (hwarm : (2 : Adr) ∈ base.accessedAddresses)
    (hpre : decide (sevm.benvStat.rules.isPrecomp 2) = true)
    (hdepth : sevm.depth ≠ 0)
    (hstatic : sevm.isStatic = false)
    (hbranchSentry : gCallStipend < G + 2 +
      insertionFirstLiveStoreCost sevm stor keys 0 n depositDataRoot)
    (hbound :
      (G + 46 +
          insertionFirstLiveStoreCost sevm stor keys 0 n depositDataRoot) +
        insertionDeadGas sevm.currentTarget stor n
          (insertionNatState 0
            ((accOfStor
              (Devm.getStor base sevm.currentTarget)).count + 1)
            depositDataRoot keys) < 2 ^ 256)
    (hcountSentry : gCallStipend <
      ((G + 46 +
          insertionFirstLiveStoreCost sevm stor keys 0 n depositDataRoot) +
        insertionDeadGas sevm.currentTarget stor n
          (insertionNatState 0
            ((accOfStor
              (Devm.getStor base sevm.currentTarget)).count + 1)
            depositDataRoot keys)) + 14 + countCost)
    (hreconstructBound :
      ((((G + 46 +
          insertionFirstLiveStoreCost sevm stor keys 0 n depositDataRoot) +
        insertionDeadGas sevm.currentTarget stor n
          (insertionNatState 0
            ((accOfStor
              (Devm.getStor base sevm.currentTarget)).count + 1)
            depositDataRoot keys)) + 38 + countCost) + 59) +
        1762 < 2 ^ 256)
    (hcode : sevm.code.toList = code)
    (hgasEntry : base.gasLeft =
      depositRuntimeSuccessGas sevm base stor keys depositDataRoot n
        ((accOfStor (Devm.getStor base sevm.currentTarget)).count + 1)
        countCost G)
    (hprocess : ProcessMessage msg
      (.some ⟨⟨0, sevm, base⟩, .ok final⟩) (.ok settled))
    (hfilled : Xlot.Filled (.some ⟨⟨0, sevm, base⟩, .ok final⟩)) :
    settled.stack = [] ∧
      settled.gasLeft = G ∧
      settled.logs = base.logs ++
        [depositEventLog sevm.currentTarget ev] ∧
      CanonicalDepositEventData ev
        (depositEventLog sevm.currentTarget ev).data ∧
      stor =
        (Devm.getStor base sevm.currentTarget).set depositCountSlot
          (Nat.toB256
            (accOfStor (Devm.getStor base sevm.currentTarget)).count + 1) ∧
      (∀ a, Devm.getStor settled a =
        if a = sevm.currentTarget then
          stor.set (branchSlot n)
            (accumulatedNode Bytes.sha256 (accOfStor stor).branch
              0 n depositDataRoot)
        else Devm.getStor base a) ∧
      (∀ a, settled.getCode a = base.getCode a) ∧
      settled.accessedAddresses = base.accessedAddresses ∧
      settled.output = base.output ∧
      settled.error = base.error ∧
      some sevm.code.toList = Prog.compile runtime := by
  rcases deposit_success_runCompiled sevm base pubkey withdrawalCredentials
      signature depositDataRoot s' ev stor keys countCost n G hdataBound hdec
      hOk hstor hkeys hcount hheight hfirst hselector hnodeleg hwarm hpre
      hdepth hstatic hbranchSentry hbound hcountSentry hreconstructBound hcode
      with ⟨post, hrun, hstack, hgas, hlogs, hcountStor, hstorage, hcodes,
        haddresses, houtput, herror, hcompile⟩
  have hentryStack :=
    MessageExecution.processMessage_entry_stack hprocess
  have hentryMemory :=
    MessageExecution.processMessage_entry_memory hprocess
  have hentryState : base.setMach
      ⟨[], Mem.empty,
        depositRuntimeSuccessGas sevm base stor keys depositDataRoot n
          ((accOfStor
            (Devm.getStor base sevm.currentTarget)).count + 1)
          countCost G⟩ = base := by
    rw [← hentryStack, ← hentryMemory, ← hgasEntry]
    cases base
    rfl
  have hrunEntry : Prog.RunCompiledTo sevm base runtime (.ok post) := by
    rw [hentryState] at hrun
    exact Prog.RunCompiledTo.of_runCompiled hrun
  have hexecEq : exec ⟨0, sevm, base⟩ = .ok post :=
    Prog.exec_of_runCompiledTo hrunEntry hcompile
  obtain ⟨hpostExec⟩ :=
    (exec_iff_exec_eq 0 sevm base (.ok post)).mpr hexecEq
  change Nonempty (Exec 0 sevm base (.ok final)) at hfilled
  obtain ⟨hfinalExec⟩ := hfilled
  have hraw : (.ok final : Execution) = .ok post :=
    Exec.result_unique hfinalExec hpostExec
  have hfinalPost : final = post := Except.ok.inj hraw
  have hentryError : base.error = none := by
    have henter := (RunFrame.some_inv hprocess).1
    rcases Frame.enter_run_inv henter with ⟨entry, _htransfer, hevm⟩
    have herrorEq := congrArg (fun evm : Evm => evm.dyna.error) hevm
    simpa [initEvm, initDevm, Msg.withBenv, Devm.error] using herrorEq
  have hfinalError : final.error = none := by
    rw [hfinalPost, herror, hentryError]
  have hsettledFinal : settled = final := by
    have hsettle := (RunFrame.some_inv hprocess).2
    simp [Frame.ofCall, Frame.settle, Frame.settleMsg,
      executeCode.handleError, processMessage.settle] at hsettle
    have hnotError : final.error.isSome ≠ true := by
      rw [hfinalError]
      simp
    rw [if_neg hnotError] at hsettle
    exact Except.ok.inj hsettle
  have hsettledPost : settled = post := hsettledFinal.trans hfinalPost
  rw [hsettledPost]
  exact ⟨hstack, hgas, hlogs, rfl, hcountStor, hstorage, hcodes,
    haddresses, houtput, herror, hcompile⟩

end Blanc.BeaconDeposit
