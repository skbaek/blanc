import Blanc.Lift.BeaconDeposit.Layout
import Blanc.CommonProofs

/-!
# Satisfiability of the Beacon deposit checkpoint premise

The Beacon history theorem carries `SolInv stor history` at its checkpoint.  This module shows
that the premise is inhabited over the empty history by an explicit concrete storage:
the zero-hash table written by the constructor (`zero_hashes[h] = zeroHash Bytes.sha256 h` at
slot `33 + h`), all branch slots and the deposit count left at their default `0`.

The table values are stated *symbolically* as `zeroHash Bytes.sha256 h`; nothing here evaluates
SHA-256.

This proves satisfiability of the checkpoint premise, not deployment: it says nothing about how
a real chain reaches such a storage.
-/

namespace Blanc.Lift.BeaconDeposit

open Jaune
open Blanc.BeaconDeposit

/-- The first `n` zero-hash table entries, written in order. -/
def beaconZeroStorUpTo : Nat → Stor
  | 0 => Stor.empty
  | n + 1 =>
      (beaconZeroStorUpTo n).set (solZeroHashSlot n) (zeroHash Bytes.sha256 n)

/-- The concrete storage of a freshly constructed deposit contract: the zero-hash table
`zero_hashes[h] = zeroHash Bytes.sha256 h` for `h < 32`, every branch slot and the count `0`. -/
def beaconZeroStor : Stor := beaconZeroStorUpTo 32

theorem solZeroHashSlot_toNat {h : Nat} (hh : h < 32) : (solZeroHashSlot h).toNat = 33 + h :=
  B256.toNat_toB256_of_lt (by omega)

theorem solZeroHashSlot_inj {h h' : Nat} (hh : h < 32) (hh' : h' < 32)
    (e : solZeroHashSlot h = solZeroHashSlot h') : h = h' := by
  have := congrArg B256.toNat e
  rw [solZeroHashSlot_toNat hh, solZeroHashSlot_toNat hh'] at this
  omega

theorem beaconZeroStorUpTo_get_table {n : Nat} (hn : n ≤ 32) {h : Nat} (hh : h < n) :
    (beaconZeroStorUpTo n).get (solZeroHashSlot h) = zeroHash Bytes.sha256 h := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [beaconZeroStorUpTo, Stor.get_set_ite]
    by_cases e : h = n
    · subst e; simp
    · have hne : solZeroHashSlot n ≠ solZeroHashSlot h := fun c =>
        e (solZeroHashSlot_inj (by omega) (by omega) c).symm
      simp only [hne, ↓reduceIte]
      exact ih (by omega) (by omega)

theorem beaconZeroStorUpTo_get_low {n : Nat} (hn : n ≤ 32) {x : B256} (hx : x.toNat < 33) :
    (beaconZeroStorUpTo n).get x = 0 := by
  induction n with
  | zero => simp [beaconZeroStorUpTo, Stor.get, Stor.empty]
  | succ n ih =>
    rw [beaconZeroStorUpTo, Stor.get_set_ite]
    have hne : solZeroHashSlot n ≠ x := fun c => by
      have := congrArg B256.toNat c
      rw [solZeroHashSlot_toNat (by omega)] at this
      omega
    simp only [hne, ↓reduceIte]
    exact ih (by omega)

/-- **The Beacon checkpoint premise is satisfiable.**  The concrete storage `beaconZeroStor`
satisfies `SolInv` for the empty deposit history. -/
theorem beacon_zero_init : SolInv beaconZeroStor [] := by
  have hbranch : ∀ h, h < 32 → beaconZeroStor.get (solBranchSlot h) = 0 := fun h hh =>
    beaconZeroStorUpTo_get_low (n := 32) (le_refl 32) (by
      rw [solBranchSlot, B256.toNat_toB256_of_lt (by omega)]; omega)
  have hcount : beaconZeroStor.get solCountSlot = 0 :=
    beaconZeroStorUpTo_get_low (n := 32) (le_refl 32) (by decide)
  have hbr : (fun h => if h < 32 then beaconZeroStor.get (solBranchSlot h) else 0) =
      fun _ => (0 : B256) := by
    funext h
    by_cases hh : h < 32
    · simp only [hh, ↓reduceIte, hbranch h hh]
    · simp only [hh, ↓reduceIte]
  have hacc : solAcc beaconZeroStor = Acc.empty :=
    congrArg₂ Acc.mk hbr (by rw [hcount]; rfl)
  refine ⟨fun h hh => beaconZeroStorUpTo_get_table (n := 32) (le_refl 32) hh, ?_⟩
  rw [hacc]
  exact empty_inv _

end Blanc.Lift.BeaconDeposit
