import Blanc.CommonProofs

/-! # Contract-neutral byte-image write laws -/

namespace Blanc

open Jaune

/-- Writing a payload extends an image exactly to the larger of its old length
and the end of the write. -/
lemma Bytes.length_writeAt
    (bs : Bytes) (n : Nat) (xs : Bytes) :
    (Bytes.writeAt bs n xs).length = max bs.length (n + xs.length) := by
  simp only [Bytes.writeAt, List.length_append, List.takeD_length,
    List.length_drop]
  omega

/-- A write ending before a requested slice leaves that later slice
unchanged. -/
lemma Bytes.sliceD_writeAt_after
    (bs xs : Bytes) (start len n : Nat)
    (h : n + xs.length ≤ start) :
    (Bytes.writeAt bs n xs).sliceD start len 0 =
      bs.sliceD start len 0 := by
  rw [List.sliceD_eq_map, List.sliceD_eq_map]
  apply List.map_congr_left
  intro i hi
  rw [Bytes.getD_writeAt]
  split
  · rename_i hinside
    have hi' := List.mem_range.mp hi
    omega
  · rfl

/-- A padded slice of a sum of widths is the first padded slice followed by
the adjacent second padded slice. -/
theorem List.sliceD_add {ξ : Type} (xs : List ξ) (d : ξ) :
    ∀ (a m b : Nat),
      xs.sliceD m (a + b) d =
        xs.sliceD m a d ++ xs.sliceD (m + a) b d := by
  intro a
  induction a with
  | zero =>
      intro m b
      simp [List.sliceD, List.takeD]
  | succ a ih =>
      intro m b
      rw [show a + 1 + b = (a + b) + 1 by omega,
        List.sliceD_succ, ih (m + 1) b,
        List.sliceD_succ xs m a d]
      have hindex : m + (a + 1) = m + 1 + a := by omega
      rw [hindex]
      rfl

/-- Staging two words at offsets zero and 32 makes their concatenation the
exact 64-byte prefix, independently of the old image. -/
lemma Bytes.sliceD_stagedPair
    (image : Bytes) (left right : B256) :
    (Bytes.writeAt
      (Bytes.writeAt image 0 left.toBytes) 32 right.toBytes).sliceD
        0 64 0 = left.toBytes ++ right.toBytes := by
  rw [List.sliceD_eq_map]
  apply List.ext_get
  · simp only [List.length_map, List.length_range, List.length_append,
      B256.length_toBytes]
  · intro i hi₁ hi₂
    simp only [List.length_map, List.length_range] at hi₁
    simp only [List.get_eq_getElem, List.getElem_map, List.getElem_range,
      zero_add]
    by_cases hi : i < 32
    · rw [Bytes.getD_writeAt, if_neg (by omega),
        Bytes.getD_writeAt, if_pos (by
          simp only [B256.length_toBytes]
          omega)]
      rw [List.getElem_append_left (by
        simpa only [B256.length_toBytes] using hi)]
      rw [Nat.sub_zero, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by
          simpa only [B256.length_toBytes] using hi)]
      rfl
    · have hi32 : 32 ≤ i := Nat.not_lt.mp hi
      have hi64 : i < 64 := hi₁
      have hir : i - 32 < right.toBytes.length := by
        rw [B256.length_toBytes]
        omega
      rw [Bytes.getD_writeAt, if_pos (by
        simp only [B256.length_toBytes]
        omega)]
      rw [List.getElem_append_right (by
        simp only [B256.length_toBytes]
        omega)]
      rw [List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem hir]
      simp only [B256.length_toBytes]
      rfl

/-- Slicing an image from zero at its exact length returns the image. -/
lemma Bytes.sliceD_zero_length {bs : Bytes} {n : Nat}
    (h : bs.length = n) : bs.sliceD 0 n 0 = bs := by
  subst n
  unfold List.sliceD
  simp only [List.drop_zero]
  rw [List.takeD_eq_take _ (Nat.le_refl _)]
  exact List.take_length

/-- A padded slice selecting an exact middle segment of a concatenation
returns that segment. -/
lemma Bytes.sliceD_append_middle
    (pre middle post : Bytes) :
    (pre ++ middle ++ post).sliceD
      pre.length middle.length 0 = middle := by
  simp only [List.sliceD]
  rw [List.append_assoc,
    List.drop_length_append' rfl,
    List.takeD_eq_take _ (by simp),
    List.take_length_append' rfl]

/-- An in-range indexed read of a padded slice is the corresponding read of
the source image. -/
lemma Bytes.getD_sliceD_of_lt
    (bs : Bytes) (start len i : Nat) (hi : i < len) :
    (bs.sliceD start len 0).getD i 0 = bs.getD (start + i) 0 := by
  unfold List.sliceD
  rw [List.getD_takeD, if_pos hi, List.getD_drop]

/-- Slicing inside a padded slice agrees with slicing the same window from
the original image, provided the inner window fits within the outer one. -/
lemma Bytes.sliceD_sliceD_of_le
    (bs : Bytes) (outerStart outerLen innerStart innerLen : Nat)
    (hfit : innerStart + innerLen ≤ outerLen) :
    (bs.sliceD outerStart outerLen 0).sliceD innerStart innerLen 0 =
      bs.sliceD (outerStart + innerStart) innerLen 0 := by
  rw [List.sliceD_eq_map
      (bs.sliceD outerStart outerLen 0) 0 innerLen innerStart,
    List.sliceD_eq_map bs 0 innerLen (outerStart + innerStart)]
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.mp hi
  rw [Bytes.getD_sliceD_of_lt _ _ _ _ (by omega)]
  congr 1
  omega

/-- Equality of a padded region transfers to every window contained in that
region. -/
lemma Bytes.sliceD_of_sliceD_eq
    {image knownRegion : Bytes}
    {regionStart regionLen innerStart innerLen : Nat}
    (hregion : image.sliceD regionStart regionLen 0 = knownRegion)
    (hfit : innerStart + innerLen ≤ regionLen) :
    image.sliceD (regionStart + innerStart) innerLen 0 =
      knownRegion.sliceD innerStart innerLen 0 := by
  have h := congrArg
    (fun bs : Bytes => bs.sliceD innerStart innerLen 0) hregion
  rw [Bytes.sliceD_sliceD_of_le _ _ _ _ _ hfit] at h
  exact h

/-- Equality of a padded prefix transfers to every window contained in that
prefix. -/
lemma Bytes.sliceD_of_sliceD_zero_eq
    {image knownPrefix : Bytes} {total start len : Nat}
    (hprefix : image.sliceD 0 total 0 = knownPrefix)
    (hfit : start + len ≤ total) :
    image.sliceD start len 0 = knownPrefix.sliceD start len 0 := by
  simpa only [Nat.zero_add] using
    (Bytes.sliceD_of_sliceD_eq hprefix hfit)

/-- Replacing a middle segment by an equal-length payload preserves the exact
prefix and suffix. -/
lemma Bytes.writeAt_append_middle_at
    {pre old suffix replacement : Bytes} {offset : Nat}
    (hprefix : pre.length = offset)
    (hlen : old.length = replacement.length) :
    Bytes.writeAt (pre ++ old ++ suffix) offset replacement =
      pre ++ replacement ++ suffix := by
  subst offset
  unfold Bytes.writeAt
  rw [List.takeD_eq_take _ (by simp)]
  simp only [List.append_assoc]
  rw [List.take_left]
  simp [List.drop_append, hlen]

end Blanc
