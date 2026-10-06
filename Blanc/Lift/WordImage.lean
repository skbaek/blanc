import Blanc.Lift.ExactWalk
import Blanc.Lift.ExactWalkMemory

/-!
# Whole-word byte images

Small facts about images built by successive whole-word writes (`MSTORE`):
a word write strictly before a window leaves it alone, and a word written right
after a window extends it. Also the low-byte mask (`AND 0xff`) as a `UInt8`.
Nothing here mentions a contract.
-/

namespace Blanc.Lift
open Jaune

theorem Bytes.sliceD_writeAt_word_after (img : Bytes) (n start len : Nat) (w : B256)
    (h : n + 32 ≤ start) :
    (Bytes.writeAt img n w.toBytes).sliceD start len 0 = img.sliceD start len 0 :=
  Bytes.sliceD_writeAt_after img w.toBytes start len n (by rw [B256.length_toBytes]; exact h)

/-- A word written at the end of a window appends to it. -/
theorem Bytes.sliceD_writeAt_word_last (img : Bytes) (start len n m : Nat) (w : B256)
    (h : start + len = n) (hm : len + 32 = m) :
    (Bytes.writeAt img n w.toBytes).sliceD start m 0 =
      img.sliceD start len 0 ++ w.toBytes := by
  rw [← hm, List.sliceD_split, Bytes.sliceD_writeAt_before _ _ start len n (Nat.le_of_eq h), h,
    sliceD_word_same]

/-- A short write at the start of a word window fills its head. -/
theorem Bytes.sliceD_writeAt_short (img t : Bytes) (n : Nat) (h : t.length ≤ 32) :
    (Bytes.writeAt img n t).sliceD n 32 0 =
      t ++ img.sliceD (n + t.length) (32 - t.length) 0 := by
  have split := List.sliceD_split (Bytes.writeAt img n t) 0 t.length n (32 - t.length)
  rw [show t.length + (32 - t.length) = 32 by omega] at split
  rw [split, Bytes.sliceD_writeAt,
    Bytes.sliceD_writeAt_after img t (n + t.length) (32 - t.length) n (Nat.le_refl _)]

/-- Any tail of the zero word reads zeros. -/
theorem B256.zero_toBytes_sliceD (k : Nat) :
    (0 : B256).toBytes.sliceD k (32 - k) 0 = List.replicate (32 - k) 0 := by
  rw [show (0 : B256).toBytes = List.replicate 32 0 from rfl]
  unfold List.sliceD
  rw [List.drop_replicate, List.takeD_eq_take _ (by rw [List.length_replicate]),
    List.take_replicate, Nat.min_self]

/-- `AND 0xff` keeps exactly the low byte. -/
theorem B256.and_ff_eq_toUInt8 (w : B256) :
    (w &&& Bytes.toB256 [0xff]) = (w.2.2.toUInt8).toB256 := by
  rcases w with ⟨⟨a, b⟩, ⟨c, d⟩⟩
  change ((a &&& 0, b &&& 0), (c &&& 0, d &&& 255)) =
    (((0 : UInt64), (0 : UInt64)), ((0 : UInt64), d.toUInt8.toUInt64))
  rw [UInt64.and_zero, UInt64.and_zero, UInt64.and_zero]
  congr 2
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_and, UInt8.toNat_toUInt64, UInt64.toNat_toUInt8]
  exact Nat.and_two_pow_sub_one_eq_mod d.toNat 8

/-- A byte word is fixed by the low-byte mask. -/
theorem UInt8.toB256_and_ff (u : UInt8) : (u.toB256 &&& Bytes.toB256 [0xff]) = u.toB256 := by
  rw [B256.and_ff_eq_toUInt8]
  change UInt8.toB256 u.toUInt64.toUInt8 = _
  rw [UInt8.toUInt8_toUInt64]

end Blanc.Lift
