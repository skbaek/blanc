import Blanc.Lift.BeaconDeposit.BodySpec

/-!
# Beacon-lift re-pin bridge (unit-local, hoisting candidate)

Jaune `ca9f27d` prices `SSTORE` from the machine read `Devm.getOrigStorVal`
(`Blanc.sstoreCost` in `Blanc/ForwardCall.lean`), which is `0` at accounts
created in this transaction and the transaction-start snapshot otherwise.
The body's model costs in `BodySpec.lean` (`liveStoreCost`, `countStoreCost`)
still price from the static snapshot read `Jaune.getOrigStorVal`, so the
`SSTORE` congruences in `Body.lean` (`hcost`, `hcs5`) and
`Creation/Walk.lean` (`sstoreCost_congr`) need the machine read threaded
through.

Following the port-side precedent (`insertionFirstLiveStoreCostOf` /
`depositRuntimeSuccessGasOf` in `Blanc/BeaconDepositInsertFirstLiveCost.lean`
and neighboring `...Of` definitions), this module adds the `...Of` variants
priced from a supplied original word, with `rfl` links back to the static
defs and the machine-read connection under an explicit `horig` premise.
The transport across the SHA-256 call sites is `ShaCallPost.created`
(`Blanc/Lift/ExactWalkCutOps.lean`, master-authorized core-b CR1), carried by
`Keep.created` and `LoopBase.created`.

The body-level `...Of` costs (`bodyLiveCostOf`, `bodyInsertGasOf`, `bodyGasOf`)
price the two body `SSTORE`s from supplied original words; the restated P2
liveness headers supply the machine reads of the entry base (Option A, master
decision under blanc-repin-os-optionA-delegation-20261012).

Reuse note: `afterSload_createdAccounts`, `afterSstore_createdAccounts` and
`getOrigStorVal_congr_created` already exist in
`Blanc.BeaconDeposit.RepinBridge` (`Blanc/BeaconDepositRepinBridge.lean`)
and are reused, not re-derived here.
-/

namespace Blanc.Lift.BeaconDeposit

open Jaune

/-! ## `...Of` cost variants priced from a supplied original word -/

/-- The storing (live) iteration's `SSTORE`, priced from a supplied original
word (see `liveStoreCost`). -/
def liveStoreCostOf (orig : B256) (sevm : Sevm) (keys : KeySet) (stor : Stor)
    (n : Nat) (node : B256) : Nat :=
  (if (⟨sevm.currentTarget, solBranchSlot n⟩ : Adr × B256) ∈ keys then 0 else gasColdSload) +
    sstoreValueCost orig (stor.get (solBranchSlot n)) node

/-- `liveStoreCost` is the `liveStoreCostOf` at the static snapshot read. -/
theorem liveStoreCost_eq_of (sevm : Sevm) (keys : KeySet) (stor : Stor)
    (n : Nat) (node : B256) :
    liveStoreCost sevm keys stor n node =
      liveStoreCostOf (getOrigStorVal sevm sevm.currentTarget (solBranchSlot n))
        sevm keys stor n node := rfl

/-- The count's `SSTORE`, priced from a supplied original word
(see `countStoreCost`). -/
def countStoreCostOf (orig : B256) (w : B256) : Nat :=
  sstoreValueCost orig w (1 + w)

/-- `countStoreCost` is the `countStoreCostOf` at the static snapshot read. -/
theorem countStoreCost_eq_of (sevm : Sevm) (w : B256) :
    countStoreCost sevm w =
      countStoreCostOf (getOrigStorVal sevm sevm.currentTarget solCountSlot)
        w := rfl

/-- `liveStoreCostOf` depends only on the stored cell. -/
theorem liveStoreCostOf_congr {orig : B256} {sevm : Sevm} {keys : KeySet}
    {s t : Stor} {n : Nat} {nd : B256}
    (h : s.get (solBranchSlot n) = t.get (solBranchSlot n)) :
    liveStoreCostOf orig sevm keys s n nd =
      liveStoreCostOf orig sevm keys t n nd := by
  unfold liveStoreCostOf; rw [h]

/-! ## Body-level `...Of` costs -/

/-- The storing `SSTORE`'s charge (`bodyLiveCost`), priced from a supplied original word. -/
def bodyLiveCostOf (orig : B256) (sevm : Sevm) (b : Devm) : Nat :=
  liveStoreCostOf orig sevm b.accessedStorageKeys (Devm.getStor b sevm.currentTarget)
    (bodyDepth sevm b) (bodyNode sevm b)

/-- The insertion loop's gas (`bodyInsertGas`), its `SSTORE` priced from a supplied original
word. -/
def bodyInsertGasOf (orig : B256) (sevm : Sevm) (b : Devm) : Nat :=
  deadRun sevm.currentTarget b.accessedStorageKeys 0 (bodyDepth sevm b) +
    (143 + bodyLiveCostOf orig sevm b)

/-- The body's gas (`bodyGas`), the storing `SSTORE` priced from `origLive` and the count
`SSTORE` from `origCount`. -/
def bodyGasOf (origLive origCount : B256) (sevm : Sevm) (b : Devm) : Nat :=
  14551 + sloadCostOfKeys sevm.currentTarget b.accessedStorageKeys solCountSlot +
    countStoreCostOf origCount (bodyCount sevm b) + bodyInsertGasOf origLive sevm b

theorem bodyLiveCost_eq_of (sevm : Sevm) (b : Devm) :
    bodyLiveCost sevm b =
      bodyLiveCostOf (getOrigStorVal sevm sevm.currentTarget (solBranchSlot (bodyDepth sevm b)))
        sevm b := rfl

theorem bodyInsertGas_eq_of (sevm : Sevm) (b : Devm) :
    bodyInsertGas sevm b =
      bodyInsertGasOf
        (getOrigStorVal sevm sevm.currentTarget (solBranchSlot (bodyDepth sevm b))) sevm b := rfl

theorem bodyGas_eq_of (sevm : Sevm) (b : Devm) :
    bodyGas sevm b =
      bodyGasOf (getOrigStorVal sevm sevm.currentTarget (solBranchSlot (bodyDepth sevm b)))
        (getOrigStorVal sevm sevm.currentTarget solCountSlot) sevm b := rfl

/-! ## Machine-read connection -/

/-- `sstoreCost` is the `liveStoreCostOf` at the machine's own storage and key
set, with the machine original read. -/
theorem sstoreCost_eq_liveStoreCostOf_self {sevm : Sevm} {b : Devm}
    {n : Nat} {nd : B256} :
    sstoreCost sevm b (solBranchSlot n) nd =
      liveStoreCostOf (b.getOrigStorVal sevm sevm.currentTarget (solBranchSlot n))
        sevm b.accessedStorageKeys (Devm.getStor b sevm.currentTarget) n nd := by
  unfold sstoreCost liveStoreCostOf
  show (if (⟨sevm.currentTarget, solBranchSlot n⟩ : Adr × B256) ∈
      b.accessedStorageKeys then 0 else gasColdSload) +
      sstoreValueCost (b.getOrigStorVal sevm sevm.currentTarget (solBranchSlot n))
        (b.getStorVal sevm.currentTarget (solBranchSlot n)) nd = _
  show _ = _ + sstoreValueCost _ ((Devm.getStor b sevm.currentTarget).get _) _
  rfl

/-- `sstoreCost` for the count bump is the `countStoreCostOf` at the machine
original read, at a warm count key (the body `SLOAD`s the count first). -/
theorem sstoreCost_eq_countStoreCostOf {sevm : Sevm} {b : Devm} {w : B256}
    (hwarm : (⟨sevm.currentTarget, solCountSlot⟩ : Adr × B256) ∈
      b.accessedStorageKeys)
    (hw : b.getStorVal sevm.currentTarget solCountSlot = w) :
    sstoreCost sevm b solCountSlot (1 + w) =
      countStoreCostOf (b.getOrigStorVal sevm sevm.currentTarget solCountSlot)
        w := by
  unfold sstoreCost countStoreCostOf
  rw [ite_eq_left hwarm, hw, Nat.zero_add]

/-- At an account absent from `createdAccounts`, the machine original read is
the static snapshot read. -/
theorem getOrigStorVal_of_not_created {sevm : Sevm} {d : Devm} {adr : Adr}
    {key : B256} (h : adr ∉ d.createdAccounts) :
    d.getOrigStorVal sevm adr key = getOrigStorVal sevm adr key := by
  unfold Devm.getOrigStorVal
  rw [ite_eq_right h]

end Blanc.Lift.BeaconDeposit
