import Blanc.Lift.Witness

/-!
# Code children of a witness run, discharged by their own witness runs

`Blanc.Lift.Witness` runs a frame over its certificate and takes each code child of a
`CALL` as data: a settled machine with `ChildOk` (it is the settlement of an `Exec` from
the machine the call's frame enters with) and `ChildAgree` (its accessed sets, storage
and accounts, as shadows).  This module discharges those two obligations by running the
child itself: the child's frame starts from the machine `Frame.enter` builds, with the
parent's shadows (the callee added to the address shadow, the value transfer applied to
the account and storage shadows), and a halting run of the child's own checked certificate is its
`Exec` (through `lift_exact`/`lift_exactM`, supplied by the caller as `hexact`).  The
settled child is the halted machine itself (a successful call frame settles to its
result), and its shadows are those of the configuration that halted.

The same construction serves a child spawned by a `DELEGATECALL` of code the interpreter
does not run (`dcallPrep`, the `DELEGATECALL` arm up to its spawn, warm/cold on the
address shadow and the callee's code from the account shadow; `dcallPrep_spec`).
Nothing here is contract-specific.
-/

namespace Blanc.Lift.Witness

open Jaune Blanc.Lift

/-! ## Halting keeps the accessed sets -/

/-! ## A frame entered with shadows -/

/-! ## Code children of a `CALL` in a witness run -/

/-- The child frame a code `CALL` at `c` enters with: its machine, and its start
configuration at `f0` with the parent's shadows. -/
def childStart (sevm : Sevm) (c : Cfg) (f0 : SFunc) : Option (Evm × Cfg) :=
  match callPrep sevm c with
  | some cp =>
    match frameEnterS cp.f c.acs with
    | .run cevm =>
      if frameEntryForkFree cp.f = true then
        some (cevm, ⟨cevm.dyna, f0, [], c.keys, cp.adrs, storTransfer cp.f.inner c.stor c.acs, acsTransfer cp.f.inner c.acs⟩)
      else none
    | .done _ => none
  | none => none

/-- The child of the code `CALL` at `c`, run for at most `n` steps over `fs`, provided
its code is `code` (as bytes) and its fork is covered. -/
def childRun (fs : List SFunc) (code : ByteArray) (sevm : Sevm) (n : Nat) (c : Cfg) : Res :=
  match fs[0]? with
  | some f0 =>
    match childStart sevm c f0 with
    | some (e, cc) =>
      if decide (CoveredFork e.sta.benvStat.fork) ∧ e.sta.code.data.toList = code.data.toList
      then wrun fs e.sta n cc
      else .stuck
    | none => .stuck
  | none => .stuck

/-! ## `DELEGATECALL` up to its spawn -/

/-- The `.delegatecall` arm of `Xinst.step` up to its spawn (`Xinst.step_delegatecall_spawn`),
warm/cold on the address shadow `adrs`, the callee's code from the account shadow `acs`. -/
def dcallPrep (sevm : Sevm) (devm : Devm) (adrs : List Adr) (acs : AcctShadow) :
    Option CallPrep :=
  match devm.stack with
  | gw :: cw :: iiw :: isw :: oiw :: osw :: s =>
    if decide (CoveredFork sevm.benvStat.fork) ∧ sevm.depth ≠ 0 then
      let d0 := devm.setMach ⟨s, devm.memory, devm.gasLeft, devm.stateGas⟩
      let ext := d0.extCost [⟨iiw.toNat, isw.toNat⟩, ⟨oiw.toNat, osw.toNat⟩]
      let callee := cw.toAdr
      let dA := addAccessedAddress d0 callee
      let code := (lookupA acs callee).code
      match getDelegatedCodeAddress code with
      | some _ => none
      | none =>
        let acc := accessCostL callee adrs
        let r := calculateMsgCallGas 0 gw.toNat dA.gasLeft ext acc
        if r.1 + ext ≤ dA.gasLeft then
          let p := callSpawnParent dA (r.1 + ext) iiw.toNat isw.toNat oiw.toNat osw.toNat
          some ⟨Frame.ofCall (delegatecallSpawnMsg sevm p r.2 callee iiw.toNat isw.toNat code false),
            p, oiw.toNat, osw.toNat, callee :: adrs⟩
        else none
    else none
  | _ => none

/-! ## Value transfers that keep the storage shadow (Jaune `ca9f27d`)

A balance write deletes an emptied account with its storage, so a frame entry's value
transfer keeps the storage shadow only when no value moves or both endpoints have a nonzero
nonce in the account shadow. -/

end Blanc.Lift.Witness
