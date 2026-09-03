-- StorageOnlySpec.lean : the ladder adapter for a storage-determined invariant.

import Blanc.Ladder
import Blanc.Tactics
import Blanc.StaticStorage

/-!
# Contract specs whose invariant reads only storage

`ContractSpec` carries an invariant over three arguments — the contract's
storage, the callvalue in flight, and the contract's ETH balance — because a
wrapped-native-token contract's solvency claim needs all three.  A contract
whose invariant is a property of its storage alone still has to answer the
record's eight balance obligations, and every one of those answers is the same:
none of `addBal`, `subBal` or a value transfer moves the storage at any
address, so the invariant is carried by a rewrite.

`ContractSpec.ofStorageOnly` packages that argument once.  It also declines the
`nof`-class side condition, which a storage-determined invariant never needs.

`Blanc/Conserved.lean`'s `fmintSpec` predates this module and states the same
eight answers inline for `Stor.Conserved`; folding it onto this adapter belongs
to the fmint family rather than to a consumer.
-/

namespace Blanc

open Jaune

/-- The storage at `ca` is blind to a credit. -/
theorem getStor_addBal (w : Jaune.State) (ca a : Adr) (val : B256) :
    (w.addBal a val).getStor ca = w.getStor ca := by
  show ((w.setBal a _).get ca).stor = (w.get ca).stor
  rw [State.setBal_get_stor]

/-- The storage at `ca` is blind to a debit followed by a credit. -/
theorem getStor_subBal_addBal {st st' : Jaune.State} {caller callee ca : Adr}
    {wad : B256} (h_sub : st.subBal caller wad = some st') :
    (st'.addBal callee wad).getStor ca = st.getStor ca := by
  rcases State.of_subBal h_sub with ⟨-, h_st'⟩
  show ((st'.setBal callee _).get ca).stor = (st.get ca).stor
  rw [State.setBal_get_stor, h_st', State.setBal_get_stor]

/-- A contract whose invariant is determined by its own storage, packaged for
the generic execution ladder.  The callvalue and balance arguments are
discarded, so the four monotonicity fields are `id`-shaped and the four
world-movement fields are one storage rewrite each. -/
def ContractSpec.ofStorageOnly (p : Prog) (P : Stor → Prop) : ContractSpec where
  prog := p
  Inv := fun s _ _ => P s
  Side := fun _ => True
  inv_forget := id
  inv_mono := fun h _ => h
  inv_recv := fun h _ => h
  side_le := fun _ _ => trivial
  side_transfer := fun _ _ => trivial
  side_addBal := fun _ _ => trivial
  inv_transfer := by
    intro st st' caller callee ca wad v h_sub _ _ h_inv
    show P _
    rw [getStor_subBal_addBal h_sub]
    exact h_inv
  inv_recv_transfer := by
    intro st st' caller ca wad h_sub _ _ h_inv
    show P _
    rw [getStor_subBal_addBal h_sub]
    exact h_inv
  inv_addBal := by
    intro w ca a val v _ _ h_inv
    show P _
    rw [getStor_addBal]
    exact h_inv

/-- The frame-entry invariant of a storage-determined spec carries no
callvalue case: both branches of `PreInv` are the same proposition, so the
conjunction collapses.  Hoisted from fmint's `fmintSpec_preInv_iff`, which is
now this lemma. -/
theorem ContractSpec.ofStorageOnly_preInv_iff {p : Prog} {P : Stor → Prop}
    {ca : Adr} {sevm : Sevm} {devm : Devm} :
    (ContractSpec.ofStorageOnly p P).PreInv devm ca sevm ↔
      P (Devm.getStor devm ca) := by
  constructor
  · intro h
    by_cases h_ct : sevm.currentTarget = ca
    · exact h.1 h_ct
    · exact h.2 h_ct
  · exact fun h => ⟨fun _ => h, fun _ => h⟩

/-- Reduce a storage-determined spec's per-target obligation to the bare
storage implication: `Side` is trivial, `PreInv` and `PostInv` are the storage
property, and the deeper-frame hypothesis is discarded.  A target that consumes
the deeper-frame hypothesis — a re-entrant one — proves `FuncSoundNoMem`
directly instead.

Hoisted from fmint's `fmintSpec_funcSound`; the second consumer is the
WETH-backed PRORATA vault. -/
theorem ContractSpec.ofStorageOnly_funcSound {p : Prog} {P : Stor → Prop}
    {ca : Adr} {aux : List Func} (f : Func)
    (h_cons : ∀ {sevm : Sevm} {s r : Devm},
      Func.Run (p.main :: aux) sevm s f r →
      P (Devm.getStor s sevm.currentTarget) →
      P (Devm.getStor r sevm.currentTarget)) :
    (ContractSpec.ofStorageOnly p P).FuncSoundNoMem ca aux f := by
  intro sevm s r h_ct h_pre _ h_run
  subst h_ct
  exact ⟨trivial, h_cons h_run (ofStorageOnly_preInv_iff.mp h_pre.inv)⟩

/-- Discharge a target that never writes storage: `func_inv` shows the walk
leaves `Devm.getStor` alone at every account, and the invariant is transported
along that equality by its own `of_eq`.

Generic in the invariant — `h.of_eq` resolves from the type of `h` — so this
serves any storage-determined property with an `of_eq` transport, which is
every consumer of `ContractSpec.ofStorageOnly`.  Hoisted from fmint's
`simple_conserved`, which is now this tactic.

The tactic names `h` and `run` in the caller's context, so it is written with
`hygiene` off and only applies where those are the invariant hypothesis and the
run.  That is the calling convention of every per-target obligation below
`ofStorageOnly_funcSound`. -/
syntax "storage_silent" : tactic
set_option hygiene false in
macro_rules
| `(tactic| storage_silent) =>
  `(tactic| exact h.of_eq
              (congr_fun (Func.of_inv Devm.getStor Devm.getStor (by func_inv) run)
                sevm.currentTarget))

/-- Discharge a target that writes no storage but *does* make a `STATICCALL`.

`func_inv` cannot synthesise `Ninst.Hinv Devm.getStor Ninst.staticcall`, and
should not: `Stor` is a tree whose raw equality distinguishes redundant zero
entries, so entering interpreted code preserves the storage *observation*
rather than the representation.  `Blanc/StaticStorage.lean` supplies the
instance at `Devm.storageView`, and the invariant is transported along the
resulting pointwise equality by its own `of_get_eq`.

Prefer `storage_silent`, which is cheaper; reach for this one when the target
reads another contract through a static call, as every live-quoting ERC-4626
view does. -/
syntax "storage_silent_static" : tactic
set_option hygiene false in
macro_rules
| `(tactic| storage_silent_static) =>
  `(tactic| exact h.of_get_eq (fun key =>
              congrFun (congrFun
                (Func.of_inv Devm.storageView Devm.storageView (by func_inv) run)
                sevm.currentTarget) key))

@[simp] theorem ContractSpec.ofStorageOnly_prog {p : Prog} {P : Stor → Prop} :
    (ContractSpec.ofStorageOnly p P).prog = p := rfl

@[simp] theorem ContractSpec.ofStorageOnly_inv {p : Prog} {P : Stor → Prop}
    {s : Stor} {v b : B256} :
    (ContractSpec.ofStorageOnly p P).Inv s v b = P s := rfl

end Blanc
