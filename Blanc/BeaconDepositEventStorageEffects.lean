import Blanc.BeaconDepositEvent
import Blanc.ForwardStorageEffects

/-!
# Exact storage effects through Beacon deposit event staging

The entire event-staging line is childless and contains no SSTORE.  Its
existing existential world/log boundary is replayed to a designated `STOP`,
then the common successful-prefix splice attaches an arbitrary exact-effect
continuation.
-/

namespace Blanc.BeaconDeposit

open Jaune
open Jaune.Ninst Blanc.Ninst

/-- Exact-effect companion of `stageDepositEvent_runCompiledTo`. -/
theorem stageDepositEvent_storageEffectRun
    {fs : List Func} {sevm : Sevm} {base : Devm}
    {amount oldCount : B256} {G : Nat} {body : Func}
    {effects : List (Adr × B256 × B256)}
    (hdec0 : DynamicTailDecodable sevm.data 0)
    (hdec1 : DynamicTailDecodable sevm.data 1)
    (hdec2 : DynamicTailDecodable sevm.data 2)
    (hvalue : base.getStorVal sevm.currentTarget depositCountSlot = oldCount)
    (hstatic : sevm.isStatic = false) :
    ∃ logged : Devm,
      logged.logs =
        (afterSload sevm base depositCountSlot).logs ++
          [depositEventLog sevm.currentTarget
            (stagedDepositEvent sevm.data amount oldCount)] ∧
      (∀ (a : Adr) (k : B256),
        logged.getStorVal a k =
          (afterSload sevm base depositCountSlot).getStorVal a k) ∧
      (∀ a : Adr, Devm.getStor logged a =
        Devm.getStor (afterSload sevm base depositCountSlot) a) ∧
      (∀ a : Adr, logged.getBal a =
        (afterSload sevm base depositCountSlot).getBal a) ∧
      (∀ a : Adr, logged.getCode a =
        (afterSload sevm base depositCountSlot).getCode a) ∧
      logged.accessedStorageKeys =
        (afterSload sevm base depositCountSlot).accessedStorageKeys ∧
      logged.accessedAddresses =
        (afterSload sevm base depositCountSlot).accessedAddresses ∧
      logged.output =
        (afterSload sevm base depositCountSlot).output ∧
      logged.error =
        (afterSload sevm base depositCountSlot).error ∧
      ∀ {ex : Execution},
        Func.StorageEffectRun fs sevm
          (logged.setMach
            ⟨[], depositEventMemory sevm.data amount oldCount, G⟩)
          body ex effects →
        Func.StorageEffectRun fs sevm
          (base.setMach
            ⟨[], depositEventInputMemory sevm.data amount,
              G + 5799 + sloadCost sevm base depositCountSlot⟩)
          (stageDepositEvent +++ body) ex effects := by
  obtain ⟨logged, hlogs, hstor, hstorMap, hbal, hcode, haccess, haddresses,
      houtput, herror, hlift⟩ :=
    stageDepositEvent_runCompiledTo
      (fs := fs) (sevm := sevm) (base := base)
      (amount := amount) (oldCount := oldCount) (G := G)
      (body := .last .stop)
      hdec0 hdec1 hdec2 hvalue hstatic
  refine ⟨logged, hlogs, hstor, hstorMap, hbal, hcode, haccess, haddresses,
    houtput, herror, ?_⟩
  intro ex htail
  let stopPost := logged.setMach
    ⟨[], depositEventMemory sevm.data amount oldCount, G⟩
  have hstop : Func.RunCompiledTo fs sevm stopPost (.last .stop)
      (.ok stopPost) :=
    Func.RunCompiledTo.last rfl
  have hrun : Func.RunCompiledTo fs sevm
      (base.setMach
        ⟨[], depositEventInputMemory sevm.data amount,
          G + 5799 + sloadCost sevm base depositCountSlot⟩)
      (stageDepositEvent +++ (.last .stop)) (.ok stopPost) := by
    simpa only [stopPost] using hlift hstop
  have hprefix : Func.RunCompiledTo.SuccessfulStopPrefix hrun := by
    apply Func.RunCompiledTo.SuccessfulStopPrefix.of_execFree hrun
    · simp [stageDepositEvent, copyDynamicPayload, storeLe64At, loadWord,
        mstoreAt, logWith, prepend, funcExecFree, Ninst.pushB256]
    · simp [stageDepositEvent, copyDynamicPayload, storeLe64At, loadWord,
        mstoreAt, logWith, prepend, Func.LocalSstoreFree, Ninst.pushB256]
    · simp [stageDepositEvent, copyDynamicPayload, storeLe64At, loadWord,
        mstoreAt, logWith, prepend, Func.SuccessStopOnly, Ninst.pushB256]
  have hspliced := hprefix.splice htail
  simpa only [Func.replaceStopWith_prepend, Func.replaceStopWith] using
    hspliced

end Blanc.BeaconDeposit
