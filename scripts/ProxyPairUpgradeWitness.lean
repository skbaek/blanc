import Blanc.ProxyPairUpgradeRefinement

/-!
# Executable proxy-pair upgrade witnesses

This evaluator closes the concrete premise/success/rollback side of the
upgrade goal against the exact compiled proxy and implementation programs.
Its labelled rows are consumed by `check-proxy-pair-upgrade.py`; changing the
row order or silently dropping a control is therefore a gate failure.
-/

namespace Blanc.ProxyPair.Upgrade.Witness

open Jaune
open Blanc Blanc.ProxyPair Blanc.ProxyPair.Upgrade

private def outcomeRow (label : String) (msg : Msg) : String :=
  match processMessage msg with
  | .error _ => s!"{label}|wrapper=error"
  | .ok post =>
      s!"{label}|wrapper=ok|error={post.error.isSome}|gas={post.gasLeft}" ++
        s!"|implementation={(post.getStorVal upgradeProxy implementationSlotLit).toNat}" ++
        s!"|s1={(post.getStorVal upgradeProxy v1ValueSlot).toNat}" ++
        s!"|s2={(post.getStorVal upgradeProxy v2ValueSlot).toNat}" ++
        s!"|marker={(post.getStorVal upgradeProxy migrationMarkerSlot).toNat}" ++
        s!"|logs={post.logs.length}|output={post.output.length}"

private def unauthorizedMessage : Msg :=
  { primaryMessage with caller := v1Implementation }

private def ossifiedState : State :=
  fixturePrestate.setStorVal upgradeProxy adminSlotLit 0

private def ossifiedMessage : Msg :=
  { primaryMessage with
      benv := { primaryMessage.benv with
        state := ossifiedState
        stat := { primaryMessage.benv.stat with origState := ossifiedState } } }

private def missingCodeState : State :=
  State.set fixturePrestate v2Implementation Acct.nil

private def missingCodeMessage : Msg :=
  { primaryMessage with
      benv := { primaryMessage.benv with
        state := missingCodeState
        stat := { primaryMessage.benv.stat with origState := missingCodeState } } }

private def revertingSetupMessage : Msg :=
  upgradeMessage (proxyUpgradeToAndCallCalldata v2Implementation
    [0xde, 0xad, 0xbe, 0xef] false)

private def relationRow : String :=
  match processMessage primaryMessage with
  | .error _ => "RELATION|primary-wrapper=error"
  | .ok post =>
      let wrong := post.state.setStorVal upgradeProxy v2ValueSlot 41
      let preS1 := (storageWord fixturePrestate upgradeProxy v1ValueSlot).toNat
      let preS2 := (storageWord fixturePrestate upgradeProxy v2ValueSlot).toNat
      let preMarker :=
        (storageWord fixturePrestate upgradeProxy migrationMarkerSlot).toNat
      let postS2 := (storageWord post.state upgradeProxy v2ValueSlot).toNat
      let postMarker :=
        (storageWord post.state upgradeProxy migrationMarkerSlot).toNat
      let wrongS2 := (storageWord wrong upgradeProxy v2ValueSlot).toNat
      s!"RELATION|ordinary-identity-admissible={preMarker == migrationMarkerValue.toNat && preS1 == preS2}" ++
        s!"|primary-initialized={postMarker == migrationMarkerValue.toNat}" ++
        s!"|primary-r2={preS1 == postS2}" ++
        s!"|wrong-r2={preS1 == wrongS2}"

private def messageOnState (state : State) (data : Bytes) : Msg :=
  { upgradeMessage data with
      benv := { fixtureBenv with
        state := state
        stat := { fixtureBenv.stat with origState := state } } }

private def sharedOutcomeRow (label : String) (msg : Msg) : String :=
  match processMessage msg with
  | .error _ => s!"{label}|wrapper=error"
  | .ok post =>
      s!"{label}|wrapper=ok|error={post.error.isSome}|gas={post.gasLeft}" ++
        s!"|implementation={(post.getStorVal upgradeProxy implementationSlotLit).toNat}" ++
        s!"|s1={(post.getStorVal upgradeProxy v1ValueSlot).toNat}" ++
        s!"|s2={(post.getStorVal upgradeProxy v2ValueSlot).toNat}" ++
        s!"|marker={(post.getStorVal upgradeProxy migrationMarkerSlot).toNat}" ++
        s!"|logs={post.logs.length}|output={post.output.length}" ++
        s!"|word={(Bytes.toB256 post.output).toNat}"

#eval show IO Unit from do
  IO.println (outcomeRow "PRIMARY" primaryMessage)
  IO.println (outcomeRow "UPGRADE_TO" upgradeToMessage)
  IO.println (outcomeRow "SKIPPED_EMPTY" skippedEmptyMessage)
  IO.println (outcomeRow "UNAUTHORIZED" unauthorizedMessage)
  IO.println (outcomeRow "OSSIFIED" ossifiedMessage)
  IO.println (outcomeRow "MISSING_CODE" missingCodeMessage)
  IO.println (outcomeRow "REVERTING_SETUP" revertingSetupMessage)
  IO.println relationRow
  match processMessage primaryMessage with
  | .error _ =>
      IO.println "POST_VALUE|primary-wrapper=error"
      IO.println "POST_SET|primary-wrapper=error"
      IO.println "POST_GET|primary-wrapper=error"
      IO.println "POST_MARKER|primary-wrapper=error"
  | .ok primaryPost =>
      IO.println (sharedOutcomeRow "POST_VALUE"
        (messageOnState primaryPost.state valueCalldata))
      let setter := messageOnState primaryPost.state (setValueCalldata 73)
      IO.println (sharedOutcomeRow "POST_SET" setter)
      match processMessage setter with
      | .error _ => IO.println "POST_GET|setter-wrapper=error"
      | .ok setterPost =>
          IO.println (sharedOutcomeRow "POST_GET"
            (messageOnState setterPost.state valueCalldata))
      IO.println (sharedOutcomeRow "POST_MARKER"
        (messageOnState primaryPost.state migrationMarkerCalldata))

end Blanc.ProxyPair.Upgrade.Witness
