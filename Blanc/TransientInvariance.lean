import Blanc.CommonProofs

/-!
# `Devm.transientStorage` preservation

Contract-neutral `Hinv`/`Inv` machinery for the projection
`Devm.transientStorage`, mirroring the existing families for `Devm.getStor`,
`Devm.getCode`, `Devm.getBal`, `Devm.state` and `Devm.memory` in
`Blanc/CommonProofs.lean`. Before this module, no line of straight-line
`Func`/`Line` machinery could carry the transient-storage image of a fragment
across it, because no `Rinst.Hinv`/`Ninst.Hinv` instance existed for
`Devm.transientStorage` -- every generic-observable family the repository had
built stopped one projection short of it.

The shape is the mirror image of the `Devm.getStor` family: `SSTORE`
(`Rinst.sstore`) is the one register instruction that may move
`Devm.transientStorage`'s counterpart `Devm.state`, while `TSTORE`
(`Rinst.tstore`) is the one that may move `Devm.transientStorage` itself. So
where the `Devm.getStor` family case-splits on and excludes `Rinst.sstore`,
this family case-splits on and excludes `Rinst.tstore`, reusing exactly the
same two full-frame theorems (`Devm.StateWriteFrame` and
`Devm.InstructionFrame`) already proved in `Blanc/CommonProofs.lean`.

`Devm.transientStorage : Devm → Tra` is not curried over `Adr` the way
`Devm.getStor : Devm → Adr → Stor` is, so the equations here are plain `Tra`
equalities rather than `Adr`-indexed function equalities: no `funext`/
`congrArg` step over an address is needed anywhere in this file.
-/

namespace Blanc

open Jaune Jaune.List Jaune.Except _root_.List _root_.Nat
open Jaune.Ninst Ninst

/-! ## `Devm.WorldEq` and `chargeGas`/`Devm.push` projections -/

/-- The transient-storage component of `Devm.WorldEq`, projected out as its
own equation so the `chargeGas`/`Devm.push` frame lemmas below can consume it
directly, the same way `Devm.WorldEq.getStor` projects out the `state`
component for the `Devm.getStor` family. -/
lemma Devm.WorldEq.transientStorage {d d' : Devm} (h : Devm.WorldEq d d') :
    Devm.transientStorage d = Devm.transientStorage d' :=
  h.2

lemma chargeGas_transientStorage_eq {cost devm devm'}
    (h : chargeGas cost devm = .ok devm') :
    Devm.transientStorage devm = Devm.transientStorage devm' :=
  Devm.WorldEq.transientStorage (chargeGas_worldEq_of_ok h)

lemma Devm.push_transientStorage_eq {v devm devm'}
    (h : Devm.push v devm = .ok devm') :
    Devm.transientStorage devm = Devm.transientStorage devm' :=
  Devm.WorldEq.transientStorage
    (liftMachExecution_worldEq_of_ok (core := Mach.push v) h)

/-! ## The core `Rinst.Inv` lemma -/

/-- A regular instruction other than `TSTORE` preserves transient storage.

Mirrors `Rinst.preserves_stor`, but with the excluded constructor swapped:
`SSTORE` runs inside `Devm.StateWriteFrame`, which may move `state` but still
fixes `transientStorage` to `Eq` (only its `state` field is overridden away
from `Devm.Rels.instructionFrame`); every other non-`TSTORE` instruction runs
inside the fully generic `Devm.InstructionFrame`, which also fixes
`transientStorage` to `Eq`. Either frame's `transientStorage` field is
therefore already the equation this lemma needs, with no further unfolding. -/
lemma Rinst.preserves_transientStorage {r} (h_not_tstore : r ≠ Rinst.tstore) :
    Rinst.Inv Devm.transientStorage r := by
  intro pc sevm pre post hrun
  rcases eq_or_ne r .sstore with rfl | hs
  · have hf := Rinst.sstore_run_stateWriteFrame pc pre sevm; rw [hrun] at hf
    exact hf.transientStorage
  · have hf := Rinst.run_instructionFrame pc sevm pre r hs h_not_tstore
    rw [hrun] at hf
    exact hf.transientStorage

/-! ## The `show_hinv_trans` macro -/

/-- Discharges a `Rinst.Hinv Devm.transientStorage o` goal for a concrete
constructor `o` other than `Rinst.tstore`, via `Rinst.preserves_transientStorage`
and a `contradiction` on the excluded-constructor side condition. Mirrors
`show_hinv_stor`. -/
syntax "show_hinv_trans" : tactic
macro_rules
  | `(tactic| show_hinv_trans) =>
    `(tactic| exact ⟨Rinst.preserves_transientStorage (by intro; contradiction)⟩)

/-! ## `Rinst.Hinv Devm.transientStorage` instances

One instance per `Rinst` constructor except `Rinst.tstore`, the one
constructor that may move `Devm.transientStorage`. The generic
`Rinst.reg`-wrapping bridge in `Blanc/CommonProofs.lean` is polymorphic in the
observable, so `Ninst.Hinv Devm.transientStorage (Ninst.reg o)` follows from
each instance below with no further declaration. -/

instance : Rinst.Hinv Devm.transientStorage Rinst.add := by show_hinv_trans
instance : Rinst.Hinv Devm.transientStorage Rinst.mul := by show_hinv_trans
instance : Rinst.Hinv Devm.transientStorage Rinst.sub := by show_hinv_trans
instance : Rinst.Hinv Devm.transientStorage Rinst.div := by show_hinv_trans
instance : Rinst.Hinv Devm.transientStorage Rinst.sdiv := by show_hinv_trans
instance : Rinst.Hinv Devm.transientStorage Rinst.mod := by show_hinv_trans
instance : Rinst.Hinv Devm.transientStorage Rinst.smod := by show_hinv_trans
instance : Rinst.Hinv Devm.transientStorage Rinst.addmod := by show_hinv_trans
instance : Rinst.Hinv Devm.transientStorage Rinst.mulmod := by show_hinv_trans
instance : Rinst.Hinv Devm.transientStorage Rinst.exp := by show_hinv_trans
instance : Rinst.Hinv Devm.transientStorage Rinst.signextend := by show_hinv_trans
instance : Rinst.Hinv Devm.transientStorage Rinst.lt := by show_hinv_trans
instance : Rinst.Hinv Devm.transientStorage Rinst.gt := by show_hinv_trans
instance : Rinst.Hinv Devm.transientStorage Rinst.slt := by show_hinv_trans
instance : Rinst.Hinv Devm.transientStorage Rinst.sgt := by show_hinv_trans
instance : Rinst.Hinv Devm.transientStorage Rinst.eq := by show_hinv_trans
instance : Rinst.Hinv Devm.transientStorage Rinst.iszero := by show_hinv_trans
instance : Rinst.Hinv Devm.transientStorage Rinst.and := by show_hinv_trans
instance : Rinst.Hinv Devm.transientStorage Rinst.or := by show_hinv_trans
instance : Rinst.Hinv Devm.transientStorage Rinst.xor := by show_hinv_trans
instance : Rinst.Hinv Devm.transientStorage Rinst.not := by show_hinv_trans
instance : Rinst.Hinv Devm.transientStorage Rinst.byte := by show_hinv_trans
instance : Rinst.Hinv Devm.transientStorage Rinst.shr := by show_hinv_trans
instance : Rinst.Hinv Devm.transientStorage Rinst.shl := by show_hinv_trans
instance : Rinst.Hinv Devm.transientStorage Rinst.sar := by show_hinv_trans
instance : Rinst.Hinv Devm.transientStorage Rinst.clz := by show_hinv_trans
instance : Rinst.Hinv Devm.transientStorage Rinst.kec := by show_hinv_trans
instance : Rinst.Hinv Devm.transientStorage Rinst.address := by show_hinv_trans
instance : Rinst.Hinv Devm.transientStorage Rinst.balance := by show_hinv_trans
instance : Rinst.Hinv Devm.transientStorage Rinst.origin := by show_hinv_trans
instance : Rinst.Hinv Devm.transientStorage Rinst.caller := by show_hinv_trans
instance : Rinst.Hinv Devm.transientStorage Rinst.callvalue := by show_hinv_trans
instance : Rinst.Hinv Devm.transientStorage Rinst.calldataload := by show_hinv_trans
instance : Rinst.Hinv Devm.transientStorage Rinst.calldatasize := by show_hinv_trans
instance : Rinst.Hinv Devm.transientStorage Rinst.calldatacopy := by show_hinv_trans
instance : Rinst.Hinv Devm.transientStorage Rinst.codesize := by show_hinv_trans
instance : Rinst.Hinv Devm.transientStorage Rinst.codecopy := by show_hinv_trans
instance : Rinst.Hinv Devm.transientStorage Rinst.gasprice := by show_hinv_trans
instance : Rinst.Hinv Devm.transientStorage Rinst.extcodesize := by show_hinv_trans
instance : Rinst.Hinv Devm.transientStorage Rinst.extcodecopy := by show_hinv_trans
instance : Rinst.Hinv Devm.transientStorage Rinst.retdatasize := by show_hinv_trans
instance : Rinst.Hinv Devm.transientStorage Rinst.retdatacopy := by show_hinv_trans
instance : Rinst.Hinv Devm.transientStorage Rinst.extcodehash := by show_hinv_trans
instance : Rinst.Hinv Devm.transientStorage Rinst.blockhash := by show_hinv_trans
instance : Rinst.Hinv Devm.transientStorage Rinst.coinbase := by show_hinv_trans
instance : Rinst.Hinv Devm.transientStorage Rinst.timestamp := by show_hinv_trans
instance : Rinst.Hinv Devm.transientStorage Rinst.number := by show_hinv_trans
instance : Rinst.Hinv Devm.transientStorage Rinst.prevrandao := by show_hinv_trans
instance : Rinst.Hinv Devm.transientStorage Rinst.gaslimit := by show_hinv_trans
instance : Rinst.Hinv Devm.transientStorage Rinst.chainid := by show_hinv_trans
instance : Rinst.Hinv Devm.transientStorage Rinst.selfbalance := by show_hinv_trans
instance : Rinst.Hinv Devm.transientStorage Rinst.basefee := by show_hinv_trans
instance : Rinst.Hinv Devm.transientStorage Rinst.blobhash := by show_hinv_trans
instance : Rinst.Hinv Devm.transientStorage Rinst.blobbasefee := by show_hinv_trans
instance : Rinst.Hinv Devm.transientStorage Rinst.pop := by show_hinv_trans
instance : Rinst.Hinv Devm.transientStorage Rinst.mload := by show_hinv_trans
instance : Rinst.Hinv Devm.transientStorage Rinst.mstore := by show_hinv_trans
instance : Rinst.Hinv Devm.transientStorage Rinst.mstore8 := by show_hinv_trans
instance : Rinst.Hinv Devm.transientStorage Rinst.sload := by show_hinv_trans
instance : Rinst.Hinv Devm.transientStorage Rinst.sstore := by show_hinv_trans
instance : Rinst.Hinv Devm.transientStorage Rinst.tload := by show_hinv_trans
instance : Rinst.Hinv Devm.transientStorage Rinst.mcopy := by show_hinv_trans
instance : Rinst.Hinv Devm.transientStorage Rinst.pc := by show_hinv_trans
instance : Rinst.Hinv Devm.transientStorage Rinst.msize := by show_hinv_trans
instance : Rinst.Hinv Devm.transientStorage Rinst.gas := by show_hinv_trans
instance {n} : Rinst.Hinv Devm.transientStorage (Rinst.dup n) := by show_hinv_trans
instance {n} : Rinst.Hinv Devm.transientStorage (Rinst.swap n) := by show_hinv_trans
instance {n} : Rinst.Hinv Devm.transientStorage (Rinst.log n) := by show_hinv_trans

/-! ## `Ninst.Hinv Devm.transientStorage` instances for the push instructions

Mirrors the `Devm.getStor` versions of these two instances (in
`Blanc/CommonProofs.lean`). `Ninst.pushB256 x` unfolds to
`Ninst.push x.toBytes.sig _`, so `Ninst.run_push_eq` applies to it directly;
`Devm.pushBurn_of_run` turns the resulting `chargeGas`/`Devm.push` composite
into a `Devm.PushBurn`, whose `transientStorage` field is `Eq` (it is built
from `Devm.Rels.eq`), giving the equation with no further work. -/

instance {x} : Ninst.Hinv Devm.transientStorage (Ninst.pushB256 x) := ⟨by
  intros e s s' h
  have run := Ninst.run_push_eq h
  rcases hc : chargeGas
      (if (x.toBytes.sig) = [] then gBase else gVerylow) s with _ | s_gas
  · rw [hc] at run; dsimp [bind, Except.bind] at run; contradiction
  · rw [hc] at run; dsimp [bind, Except.bind] at run
    rcases hp : Devm.push x.toBytes.sig.toB256 s_gas with _ | s''
    · rw [hp] at run; contradiction
    · rw [hp] at run
      injection run with h_eq; subst h_eq
      exact (chargeGas_transientStorage_eq hc).trans
        (Devm.push_transientStorage_eq hp)
⟩

instance {xs} {p : xs.length ≤ 32} :
    Ninst.Hinv Devm.transientStorage (Ninst.push xs p) := ⟨by
  intros e s s' h
  have run := Ninst.run_push_eq h
  have h_pb := Devm.pushBurn_of_run run
  exact h_pb.transientStorage
⟩

/-! ## `PopBurn.Inv` / `Burn.Inv` for `Devm.transientStorage`

A `Func.branch` consumes its flag through `Devm.PopBurn`, and its taken arm
runs a further `Devm.Burn` before falling to the taken branch's body (see
`of_run_branch`); a later consumer that needs to carry the transient-storage
projection across a branch needs both instances to cross it. Both relations
are built from `Devm.Rels.eq`, so their `transientStorage` field is already
`Eq`, and both proofs are direct projections mirroring `Devm.Burn.getStor` /
`Devm.PopBurn.getStor`. -/

lemma Devm.Burn.transientStorage_eq {s s' : Devm} (h : Devm.Burn s s') :
    Devm.transientStorage s' = Devm.transientStorage s :=
  h.transientStorage.symm

lemma Devm.PopBurn.transientStorage_eq {xs} {s s' : Devm}
    (h : Devm.PopBurn xs s s') :
    Devm.transientStorage s' = Devm.transientStorage s :=
  h.transientStorage.symm

instance : PopBurn.Inv Devm.transientStorage := ⟨by
  intros xs s s' h
  exact (Devm.PopBurn.transientStorage_eq h).symm
⟩

instance : Burn.Inv Devm.transientStorage := ⟨by
  intros s s' h
  exact (Devm.Burn.transientStorage_eq h).symm
⟩

end Blanc
