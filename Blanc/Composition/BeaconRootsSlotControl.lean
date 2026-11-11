import Blanc.Composition.Corpus.Proofs.RingHistory
import Batteries.Tactic.OpenPrivate

namespace Blanc.Composition.BeaconRootsSlotControl

open Jaune Blanc.Corpus.Freeze Blanc.Corpus.Freeze.BeaconRoots

open private Blanc.Corpus.Proofs.RingHistory.R.root_time_ne
  from Blanc.Composition.Corpus.Proofs.RingHistory

/-- On any positive slot grid, the write 8191 slots later replaces the original timestamp tag. -/
theorem slot_grid_control : Blanc.Corpus.Freeze.BeaconRoots.R_S8_slot_control := by
  intro s genesis d slot v v' positive fits duration
  let t := genesis + d * slot
  let u := genesis + d * (slot + 8191)
  let T := t.toB256
  let U := u.toB256
  have advance : u = t + d * 8191 := by
    dsimp only [t, u]
    simp only [Nat.mul_add, Nat.add_assoc]
  have later : t < u := by
    rw [advance]
    have increment : 0 < d * 8191 := Nat.mul_pos duration (by decide)
    omega
  have wordBound : 2 ^ 64 < 2 ^ 256 := by decide
  have tn : T.toNat = t := B256.toNat_toB256_of_lt (by omega)
  have un : U.toNat = u := B256.toNat_toB256_of_lt (by omega)
  have nonzero : T ≠ 0 := by
    intro zero
    have eq := congrArg B256.toNat zero
    rw [tn] at eq
    change t = 0 at eq
    omega
  have different : U ≠ T := by
    intro same
    have eq := congrArg B256.toNat same
    rw [un, tn] at eq
    omega
  have keys : timeKey U = timeKey T := by
    apply B256.toNat_inj
    rw [timeKey, timeKey, B256.toNat_mod (by decide), B256.toNat_mod (by decide),
      un, tn, show ring.toNat = 8191 from rfl, advance, Nat.add_mul_mod_self_right]
  have tag : writeAll s [(T, v), (U, v')] (timeKey T) = U := by
    change write (write s T v) U v' (timeKey T) = U
    unfold write
    rw [ite_eq_right (Blanc.Corpus.Proofs.RingHistory.R.root_time_ne U T).symm,
      ite_eq_left keys.symm]
  change Blanc.Corpus.Freeze.BeaconRoots.read (writeAll s [(T, v), (U, v')]) T = none
  rw [Blanc.Corpus.Freeze.BeaconRoots.read, tag]
  have guard : (T ≠ 0 ∧ U = T) ↔ U = T :=
    ⟨And.right, fun same => ⟨nonzero, same⟩⟩
  exact ite_eq_right (fun h => different (guard.mp h))

end Blanc.Composition.BeaconRootsSlotControl
