-- CommonProofs/MemImage.lean : memory as a byte image: the read/write algebra behind `Mem.Wf`, `Mem.Reads` and `Bytes.writeAt`.

import Blanc.Tactics
import Blanc.ExecutionSettlement
import Jaune.DevmProjections

namespace Blanc

open Jaune Jaune.List Jaune.Except _root_.List _root_.Nat
open Jaune.Ninst Ninst
open DispatchTree

/-! ## Memory as a byte image

The read/write algebra behind `Mem.Wf`, `Mem.Reads` and `Bytes.writeAt`
(`CommonCore.lean`).  Jaune's `Array.writeD` and `Array.copyD` carry no lemmas
beyond `Array.size_copyD`, so this section starts from their definitions.

Everything here is EVM-generic: no Blanc program, no contract and no ABI shape
appears.  Its consumers are the instruction-level memory images below, and
through them any statement about the bytes a frame hands to an outgoing
`CALL`. -/

lemma Array.size_writeD {ξ : Type} :
    ∀ (ys : List ξ) (xs : Array ξ) (n : Nat),
      (Array.writeD xs n ys).size = xs.size := by
  intro ys
  induction ys with
  | nil => intro xs n; rfl
  | cons y ys ih =>
    intro xs n
    rw [Array.writeD]
    split
    · rw [ih]; simp only [Array.size_set]
    · rfl

lemma Array.getD_set {ξ : Type} (xs : Array ξ) (n : Nat) (y : ξ) (h : n < xs.size)
    (i : Nat) (d : ξ) :
    (xs.set n y h).getD i d = if i = n then y else xs.getD i d := by
  by_cases hi : i = n
  · subst hi; simp only [Array.getD, Array.size_set, h, ↓reduceDIte, Array.getInternal_eq_getElem,
    Array.getElem_set_self, ↓reduceIte]
  · simp only [Array.getD, Array.size_set, Array.getInternal_eq_getElem, Array.getElem_set,
    Ne.symm hi, ↓reduceIte, hi]

/-- Read-over-write for `Array.writeD`, the primitive behind `Mem.write`.

The hypothesis is what makes the write total: `writeD` silently stops at the end
of the array, and all three of `Mem.write`'s branches arrange for the whole
payload to fit before calling it. -/
lemma Array.getD_writeD {ξ : Type} (d : ξ) :
    ∀ (ys : List ξ) (xs : Array ξ) (n i : Nat), n + ys.length ≤ xs.size →
      (Array.writeD xs n ys).getD i d =
        if n ≤ i ∧ i < n + ys.length then ys.getD (i - n) d else xs.getD i d := by
  intro ys
  induction ys with
  | nil => intro xs n i _; simp only [Array.writeD, Array.getD_eq_getD_getElem?, length_nil,
    add_zero, getD_eq_getElem?_getD, _root_.not_lt_zero, not_false_eq_true, getElem?_neg,
    Option.getD_none, right_eq_ite_iff, isEmpty_Prop, not_and, not_lt, imp_self, IsEmpty.forall_iff]
  | cons y ys ih =>
    intro xs n i h
    simp only [List.length_cons] at h
    have hn : n < xs.size := by omega
    rw [Array.writeD, dite_eq_left hn]
    rw [ih (xs.set n y hn) (n + 1) i (by rw [Array.size_set]; omega)]
    rw [Array.getD_set]
    by_cases hi : i = n
    · subst hi
      rw [ite_eq_right (by omega), ite_eq_left rfl, ite_eq_left (by simp only [Std.le_refl, length_cons,
        lt_add_iff_pos_right, add_pos_iff, zero_lt_one, or_true, and_self]), Nat.sub_self]
      rfl
    · by_cases hlt : n ≤ i ∧ i < n + (y :: ys).length
      · have h1 : n + 1 ≤ i ∧ i < n + 1 + ys.length := by
          simp only [List.length_cons] at hlt; omega
        rw [ite_eq_left h1, ite_eq_left hlt]
        have : i - n = (i - (n + 1)) + 1 := by omega
        rw [this]; rfl
      · have h1 : ¬ (n + 1 ≤ i ∧ i < n + 1 + ys.length) := by
          simp only [List.length_cons] at hlt; omega
        rw [ite_eq_right h1, ite_eq_right hlt, ite_eq_right hi]

lemma Array.getD_setIfInBounds {ξ : Type} (a : Array ξ) (k : Nat) (x : ξ)
    (hk : k < a.size) (i : Nat) (d : ξ) :
    (a.setIfInBounds k x).getD i d = if i = k then x else a.getD i d := by
  simp only [Array.setIfInBounds, dite_eq_left hk]
  exact Array.getD_set a k x hk i d

lemma Array.foldl_setIfInBounds_getD {ξ : Type} (d : ξ) :
    ∀ (l : List ξ) (a : Array ξ) (k i : Nat), k + l.length ≤ a.size →
      (List.foldl (fun (ysn : Array ξ × Nat) x =>
        (ysn.fst.setIfInBounds ysn.snd x, ysn.snd + 1)) (a, k) l).fst.getD i d =
        if k ≤ i ∧ i < k + l.length then l.getD (i - k) d else a.getD i d := by
  intro l
  induction l with
  | nil => intro a k i _; simp only [foldl_nil, Array.getD_eq_getD_getElem?, length_nil, add_zero,
    getD_eq_getElem?_getD, _root_.not_lt_zero, not_false_eq_true, getElem?_neg, Option.getD_none,
    right_eq_ite_iff, isEmpty_Prop, not_and, not_lt, imp_self, IsEmpty.forall_iff]
  | cons x l ih =>
    intro a k i h
    simp only [List.length_cons] at h
    have hk : k < a.size := by omega
    simp only [List.foldl_cons]
    rw [ih (a.setIfInBounds k x) (k + 1) i
      (by rw [Array.size_setIfInBounds]; omega)]
    rw [Array.getD_setIfInBounds a k x hk]
    by_cases hi : i = k
    · subst hi
      rw [ite_eq_right (by omega), ite_eq_left rfl, ite_eq_left (by simp only [Std.le_refl, length_cons,
        lt_add_iff_pos_right, add_pos_iff, zero_lt_one, or_true, and_self]), Nat.sub_self]
      rfl
    · by_cases hlt : k ≤ i ∧ i < k + (x :: l).length
      · have h1 : k + 1 ≤ i ∧ i < k + 1 + l.length := by
          simp only [List.length_cons] at hlt; omega
        rw [ite_eq_left h1, ite_eq_left hlt]
        have hsub : i - k = (i - (k + 1)) + 1 := by omega
        rw [hsub]; rfl
      · have h1 : ¬ (k + 1 ≤ i ∧ i < k + 1 + l.length) := by
          simp only [List.length_cons] at hlt; omega
        rw [ite_eq_right h1, ite_eq_right hlt, ite_eq_right hi]

/-- Read-back for `Array.copyD`, whose contract is "overwrite the front of `ys`
with `xs`, keeping `ys`'s length".  With `xs` no longer than `ys` nothing is
dropped, which is the only case `Mem.write` ever creates. -/
lemma Array.getD_copyD {ξ : Type} (xs ys : Array ξ) (d : ξ) (h : xs.size ≤ ys.size)
    (i : Nat) :
    (Array.copyD xs ys).getD i d = if i < xs.size then xs.getD i d else ys.getD i d := by
  simp only [Array.copyD]
  rw [← Array.foldl_toList]
  rw [Array.foldl_setIfInBounds_getD d xs.toList ys 0 i (by simpa only [Array.length_toList,
    zero_add] using h)]
  by_cases hi : i < xs.size
  · rw [ite_eq_left (by simpa only [_root_.zero_le, Array.length_toList, zero_add, true_and] using hi), ite_eq_left hi, Nat.sub_zero]
    simp only [getD_eq_getElem?_getD, Array.length_toList, hi, getElem?_pos, Array.getElem_toList,
      Option.getD_some, Array.getD, ↓reduceDIte, Array.getInternal_eq_getElem]
  · rw [ite_eq_right (by simpa only [_root_.zero_le, Array.length_toList, zero_add, true_and,
    not_lt] using hi), ite_eq_right hi]

/-- Pointwise read-back for an in-bounds source byte copied into an in-bounds
target byte.  Unlike `Array.getD_copyD`, this does not require the whole source
to fit: raw `Mem` values may have a backing array longer than their logical
size, and `Mem.write` deliberately truncates that excess when it reallocates. -/
lemma Array.getD_copyD_of_lt {ξ : Type} (xs ys : Array ξ) (d : ξ) (i : Nat)
    (hxs : i < xs.size) (hys : i < ys.size) :
    (Array.copyD xs ys).getD i d = xs.getD i d := by
  unfold Array.copyD
  change (Array.foldl (fun (state : Array ξ × Nat) value =>
    (state.fst.setIfInBounds state.snd value, state.snd + 1))
    (ys, 0) xs).fst.getD i d = xs.getD i d
  rw [← Array.foldl_toList]
  have readsMember : ∀ (values : List ξ) (array : Array ξ)
      (offset index : Nat), index < array.size → offset ≤ index →
      index < offset + values.length →
      (List.foldl (fun (state : Array ξ × Nat) value =>
        (state.fst.setIfInBounds state.snd value, state.snd + 1))
        (array, offset) values).fst.getD index d =
          values.getD (index - offset) d := by
    intro values
    induction values with
    | nil => intro array offset index _ after before; simp only [length_nil, add_zero] at before; omega
    | cons value rest ih =>
      intro array offset index inBounds after before
      simp only [List.foldl_cons]
      by_cases atOffset : index = offset
      · subst index
        have preservesBefore : ∀ (values : List ξ) (array : Array ξ)
            (offset index : Nat), index < offset →
            (List.foldl (fun (state : Array ξ × Nat) value =>
              (state.fst.setIfInBounds state.snd value, state.snd + 1))
              (array, offset) values).fst.getD index d =
                array.getD index d := by
          intro values
          induction values with
          | nil => intro _ _ _ _; rfl
          | cons value rest ih' =>
            intro array offset index before
            simp only [List.foldl_cons]
            rw [ih' _ _ _ (by omega)]
            by_cases offsetInBounds : offset < array.size
            · rw [Array.getD_setIfInBounds _ _ _ offsetInBounds,
                ite_eq_right (by omega)]
            · simp only [Array.setIfInBounds, offsetInBounds, ↓reduceDIte,
              Array.getD_eq_getD_getElem?]
        rw [preservesBefore _ _ _ _ (by omega)]
        rw [Array.getD_setIfInBounds _ _ _ inBounds, ite_eq_left rfl]
        simp only [tsub_self, getD_eq_getElem?_getD, length_cons, add_pos_iff, zero_lt_one, or_true,
          getElem?_pos, getElem_cons_zero, Option.getD_some]
      · rw [ih _ _ _ (by rw [Array.size_setIfInBounds]; exact inBounds)
          (by omega) (by simp only [length_cons] at before ⊢; omega)]
        have hsub : index - offset = (index - (offset + 1)) + 1 := by omega
        rw [hsub]
        rfl
  rw [readsMember xs.toList ys 0 i hys (by omega) (by simpa only [Array.length_toList,
    zero_add] using hxs)]
  simp only [tsub_zero, getD_eq_getElem?_getD, Array.length_toList, hxs, getElem?_pos,
    Array.getElem_toList, Option.getD_some, Array.getD, ↓reduceDIte, Array.getInternal_eq_getElem]

/-- A copied array preserves a target byte at and after the end of the source.
This is the other pointwise half needed when the source is longer than the
target or their relative sizes are otherwise unknown. -/
lemma Array.getD_copyD_of_size_le {ξ : Type} (xs ys : Array ξ) (d : ξ)
    (i : Nat) (hxs : xs.size ≤ i) :
    (Array.copyD xs ys).getD i d = ys.getD i d := by
  unfold Array.copyD
  change (Array.foldl (fun (state : Array ξ × Nat) value =>
    (state.fst.setIfInBounds state.snd value, state.snd + 1))
    (ys, 0) xs).fst.getD i d = ys.getD i d
  rw [← Array.foldl_toList]
  have preservesAfter : ∀ (values : List ξ) (array : Array ξ)
      (offset index : Nat), offset + values.length ≤ index →
      (List.foldl (fun (state : Array ξ × Nat) value =>
        (state.fst.setIfInBounds state.snd value, state.snd + 1))
        (array, offset) values).fst.getD index d =
          array.getD index d := by
    intro values
    induction values with
    | nil => intro _ _ _ _; rfl
    | cons value rest ih =>
      intro array offset index after
      simp only [List.foldl_cons]
      rw [ih _ _ _ (by simp only [length_cons] at after ⊢; omega)]
      by_cases offsetInBounds : offset < array.size
      · rw [Array.getD_setIfInBounds _ _ _ offsetInBounds,
          ite_eq_right (by simp only [length_cons] at after; omega)]
      · simp only [Array.setIfInBounds, offsetInBounds, ↓reduceDIte, Array.getD_eq_getD_getElem?]
  exact preservesAfter xs.toList ys 0 i (by simpa only [Array.length_toList, zero_add] using hxs)

/-! ### The list side of `Bytes.writeAt` -/

lemma List.getD_append_left {ξ : Type} {l₁ l₂ : List ξ} {i : Nat} (d : ξ)
    (h : i < l₁.length) : (l₁ ++ l₂).getD i d = l₁.getD i d := by
  simp only [getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma List.getD_append_right {ξ : Type} {l₁ l₂ : List ξ} {i : Nat} (d : ξ)
    (h : l₁.length ≤ i) : (l₁ ++ l₂).getD i d = l₂.getD (i - l₁.length) d := by
  simp only [getD_eq_getElem?_getD, List.getElem?_append_right h]

lemma List.getD_drop {ξ : Type} (l : List ξ) (k j : Nat) (d : ξ) :
    (l.drop k).getD j d = l.getD (k + j) d := by
  simp only [getD_eq_getElem?_getD, getElem?_drop]

lemma List.getD_takeD {ξ : Type} (d : ξ) :
    ∀ (n : Nat) (l : List ξ) (i : Nat),
      (List.takeD n l d).getD i d = if i < n then l.getD i d else d := by
  intro n
  induction n with
  | zero => intro l i; simp only [takeD_zero, getD_eq_getElem?_getD, length_nil, _root_.not_lt_zero,
    not_false_eq_true, getElem?_neg, Option.getD_none, ↓reduceIte]
  | succ n ih =>
    intro l i
    rw [List.takeD_succ]
    cases i with
    | zero => cases l <;> simp only [head?_nil, Option.getD_none, tail_nil, takeD_nil, getD_eq_getElem?_getD, length_cons, length_replicate, lt_add_iff_pos_left, add_pos_iff, zero_lt_one, or_true, getElem?_pos, getElem_cons_zero, Option.getD_some, ↓reduceIte, length_nil, lt_self_iff_false, not_false_eq_true, getElem?_neg, head?_cons, tail_cons, takeD_length]
    | succ i =>
      rw [show ((l.head?.getD d :: List.takeD n l.tail d).getD (i + 1) d)
            = (List.takeD n l.tail d).getD i d from rfl, ih l.tail i]
      by_cases hi : i < n
      · rw [ite_eq_left hi, ite_eq_left (by omega)]
        cases l <;> simp only [tail_nil, getD_eq_getElem?_getD, length_nil, _root_.not_lt_zero, not_false_eq_true, getElem?_neg, Option.getD_none, tail_cons, getElem?_cons_succ]
      · rw [ite_eq_right hi, ite_eq_right (by omega)]

lemma List.takeD_nil_eq_replicate {ξ} (d : ξ) :
    ∀ n, List.takeD n ([] : List ξ) d = List.replicate n d := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    show ([] : List ξ).head?.getD d :: List.takeD n ([] : List ξ).tail d = _
    rw [show ([] : List ξ).tail = [] from rfl, ih]; rfl

/-- Taking *more* than there is pads with the default.

The half of `List.takeD` that `List.takeD_eq_take` does not cover, and the shape
a `CALL`'s argument window takes when it runs past the bytes the frame actually
wrote: `Mem.Reads` compares with `getD` on both sides, so those trailing
positions read as `0`, which is exactly `abiBytesTail`'s zero padding. -/
lemma List.takeD_of_length_le {ξ} (d : ξ) :
    ∀ (l : List ξ) (n : Nat), l.length ≤ n →
      List.takeD n l d = l ++ List.replicate (n - l.length) d := by
  intro l
  induction l with
  | nil => intro n _; rw [List.takeD_nil_eq_replicate]; simp only [length_nil, tsub_zero,
    nil_append]
  | cons a l ih =>
    intro n hn
    cases n with
    | zero => simp only [length_cons, nonpos_iff_eq_zero, Nat.add_eq_zero_iff, length_eq_zero_iff,
      one_ne_zero, and_false] at hn
    | succ m =>
      have hm : l.length ≤ m := by simp only [length_cons, add_le_add_iff_right] at hn; omega
      show (a :: l).head?.getD d :: List.takeD m ((a :: l).tail) d = _
      rw [show (a :: l).tail = l from rfl, ih m hm]
      simp only [head?_cons, Option.getD_some, length_cons, reduceSubDiff, cons_append]

/-- `Bytes.writeAt` read pointwise: inside the written range it is the payload,
outside it is the old image.  Every `Mem.Reads` step below is this equation
paired with `Array.getD_writeD`. -/
lemma Bytes.getD_writeAt (bs : Bytes) (n : Nat) (xs : Bytes) (i : Nat) :
    (Bytes.writeAt bs n xs).getD i 0 =
      if n ≤ i ∧ i < n + xs.length then xs.getD (i - n) 0 else bs.getD i 0 := by
  simp only [Bytes.writeAt, List.append_assoc]
  have hlen : (List.takeD n bs 0).length = n := List.takeD_length n bs 0
  by_cases h1 : i < n
  · rw [List.getD_append_left 0 (by omega), List.getD_takeD, ite_eq_left h1,
      ite_eq_right (by omega)]
  · rw [List.getD_append_right 0 (by omega), hlen]
    by_cases h2 : i < n + xs.length
    · rw [List.getD_append_left 0 (by omega), ite_eq_left ⟨by omega, h2⟩]
    · rw [List.getD_append_right 0 (by omega), ite_eq_right (by omega),
        List.getD_drop]
      congr 1
      omega

/-- Taking a padded slice from zero at the exact source length returns the
source unchanged. -/
lemma Bytes.sliceD_zero_length {bs : Bytes} {n : Nat}
    (h : bs.length = n) : bs.sliceD 0 n 0 = bs := by
  unfold List.sliceD
  simp only [List.drop_zero]
  rw [List.takeD_eq_take _ (by omega), ← h]
  exact List.take_length

/-- Split a padded slice at an arbitrary width.  This is the list-level
identity used when adjacent ABI words are proved separately and then
reassembled into one event or call-data window. -/
lemma List.sliceD_split {ξ : Type} (xs : List ξ) (d : ξ) :
    ∀ (a m b : Nat),
      xs.sliceD m (a + b) d =
        xs.sliceD m a d ++ xs.sliceD (m + a) b d := by
  intro a
  induction a with
  | zero => intro m b; simp only [sliceD, zero_add, takeD, add_zero, nil_append]
  | succ a ih =>
      intro m b
      rw [show a + 1 + b = (a + b) + 1 by omega, List.sliceD_succ,
        ih (m + 1) b, List.sliceD_succ xs m a d,
        show m + (a + 1) = m + 1 + a by omega]
      rfl

/-- Writing at the end of the image is an append.  The shape every store in a
frame that lays memory out once, upward and without gaps, takes. -/
lemma Bytes.writeAt_length (bs xs : Bytes) :
    Bytes.writeAt bs bs.length xs = bs ++ xs := by
  rw [Bytes.writeAt, List.takeD_eq_take _ (Nat.le_refl _), List.take_length,
    List.drop_eq_nil_of_le (Nat.le_add_right _ _), List.append_nil]

/-- `Bytes.writeAt_length` with the offset given as a numeral.  A walk meets the
append shape as `writeAt bs 96 xs`, never as `writeAt bs bs.length xs`, and
rewriting a numeral into a `length` first is what makes those two the same
step. -/
lemma Bytes.writeAt_of_length_eq {bs xs : Bytes} {n : Nat} (h : bs.length = n) :
    Bytes.writeAt bs n xs = bs ++ xs := by
  subst h; exact Bytes.writeAt_length bs xs

/-- Writing over the whole image from `0` replaces it.  The other shape: the
mint's `Transfer` data lands at `0`, and `storeCallbackHead`'s first store lands
on top of it. -/
lemma Bytes.writeAt_zero_of_le {bs xs : Bytes} (h : bs.length ≤ xs.length) :
    Bytes.writeAt bs 0 xs = xs := by
  rw [Bytes.writeAt, show List.takeD 0 bs 0 = [] from rfl, List.nil_append,
    List.drop_eq_nil_of_le (by omega), List.append_nil]

/-- Reading a write back at its own offset returns the payload.  The read-back
step of every store-then-load fragment: `checkReturnDataHead` clobbers a memory
word and immediately `MLOAD`s it. -/
lemma Bytes.sliceD_writeAt (bs xs : Bytes) (n : Nat) :
    (Bytes.writeAt bs n xs).sliceD n xs.length 0 = xs := by
  unfold List.sliceD
  rw [Bytes.writeAt, List.append_assoc,
    List.drop_append_of_le_length (by rw [List.takeD_length]),
    List.drop_eq_nil_of_le (by rw [List.takeD_length]), List.nil_append,
    List.takeD_eq_take _ (by simp only [length_append, length_drop, le_add_iff_nonneg_right,
      _root_.zero_le]), List.take_left]

/-! ### `Mem.Wf` and `Mem.Reads` -/

lemma Nat.le_mul_ceilDiv (n m : Nat) (hm : 0 < m) : n ≤ m * ceilDiv n m := by
  simp only [ceilDiv]
  have hdm := Nat.div_add_mod n m
  rcases Nat.eq_zero_or_pos (n % m) with h | h
  · rw [ite_eq_left h, Nat.add_zero]
    omega
  · rw [ite_eq_right (by omega), Nat.mul_add, Nat.mul_one]
    have := Nat.mod_lt n hm
    omega

lemma Mem.wf_empty : Mem.Wf Mem.empty := Nat.le_refl 0

lemma Mem.reads_empty : Mem.Reads Mem.empty [] := fun _ => rfl

lemma Mem.Wf.extend {μ : Mem} (h : Mem.Wf μ) (index size : Nat) :
    Mem.Wf (μ.extend index size) := by
  simp only [Mem.Wf, Mem.extend] at *
  simp only [memExtSize]
  split
  · exact h
  · have h1 : μ.size ≤ 32 * ceilDiv μ.size 32 :=
      Nat.le_mul_ceilDiv μ.size 32 (by omega)
    have hmax : 32 * ceilDiv μ.size 32
        ≤ 32 * max (ceilDiv μ.size 32) (ceilDiv (index + size) 32) :=
      Nat.mul_le_mul_left 32 (Nat.le_max_left _ _)
    omega

lemma Mem.Wf.extends : ∀ (pairs : List (Nat × Nat)) {μ : Mem},
    Mem.Wf μ → Mem.Wf (μ.extends pairs) := by
  intro pairs
  induction pairs with
  | nil => intro μ h; exact h
  | cons p ps ih =>
    rcases p with ⟨idx, sz⟩
    intro μ h
    exact ih (Mem.Wf.extend h idx sz)

lemma Mem.Reads.extend {μ : Mem} {bs : Bytes} (h : Mem.Reads μ bs)
    (index size : Nat) : Mem.Reads (μ.extend index size) bs := h

lemma Mem.Reads.extends : ∀ (pairs : List (Nat × Nat)) {μ : Mem} {bs : Bytes},
    Mem.Reads μ bs → Mem.Reads (μ.extends pairs) bs := by
  intro pairs
  induction pairs with
  | nil => intro μ bs h; exact h
  | cons p ps ih =>
    rcases p with ⟨idx, sz⟩
    intro μ bs h
    exact ih (Mem.Reads.extend h idx sz)

lemma Nat.le_ceil32 (n : Nat) : n ≤ ceil32 n := by
  unfold ceil32
  split
  · exact Nat.le_refl _
  · rename_i m hm
    have := Nat.mod_lt n (show 0 < 32 by omega)
    omega

lemma Array.getD_replicate_zero (k i : Nat) :
    (Array.replicate k (0 : UInt8)).getD i 0 = 0 := by
  simp only [Array.getD, Array.size_replicate, Array.getInternal_eq_getElem,
    Array.getElem_replicate, dite_eq_ite, ite_self]

lemma Array.getD_of_size_le {ξ : Type} {xs : Array ξ} {i : Nat} (d : ξ)
    (h : xs.size ≤ i) : xs.getD i d = d := by
  simp only [Array.getD, Nat.not_lt.mpr h, ↓reduceDIte]

/-- `Mem.write`'s three branches, factored.

Whichever branch it takes, the result is `Array.writeD` over an array that reads
exactly as the old one, is long enough to hold the whole payload, and does not
run past the new logical size.  The `Mem.Wf` hypothesis is precisely what rules
out the truncation `Array.copyD` would otherwise perform in the growth branch,
where the fresh array is `ceil32 (n + ys.length)` long. -/
lemma Mem.write_aux {μ : Mem} (hwf : Mem.Wf μ) (n : Nat) :
    ∀ {ys : Bytes}, ys ≠ [] →
      ∃ A : Array UInt8,
        (μ.write n ys).data = Array.writeD A n ys ∧
        n + ys.length ≤ A.size ∧
        A.size ≤ (μ.write n ys).size ∧
        ∀ i, A.getD i 0 = μ.data.getD i 0 := by
  intro ys hne
  cases ys with
  | nil => exact absurd rfl hne
  | cons y ys =>
    simp only [Mem.Wf] at hwf
    simp only [Mem.write]
    by_cases h1 : n + (y :: ys).length ≤ μ.size
    · rw [ite_eq_left h1]
      by_cases h2 : n + (y :: ys).length ≤ μ.data.size
      · rw [ite_eq_left h2]
        exact ⟨μ.data, rfl, h2, hwf, fun _ => rfl⟩
      · rw [ite_eq_right h2]
        refine ⟨Array.copyD μ.data
          (Array.replicate (n + (y :: ys).length) 0x00), rfl, ?_, ?_, ?_⟩
        · rw [Array.size_copyD, Array.size_replicate]
        · rw [Array.size_copyD, Array.size_replicate]; exact h1
        · intro i
          rw [Array.getD_copyD _ _ _ (by rw [Array.size_replicate]; omega)]
          by_cases hi : i < μ.data.size
          · rw [ite_eq_left hi]
          · rw [ite_eq_right hi, Array.getD_replicate_zero,
              Array.getD_of_size_le 0 (Nat.not_lt.mp hi)]
    · rw [ite_eq_right h1]
      have hle : n + (y :: ys).length ≤ ceil32 (n + (y :: ys).length) :=
        Nat.le_ceil32 _
      refine ⟨Array.copyD μ.data
        (Array.replicate (ceil32 (n + (y :: ys).length)) 0x00), rfl, ?_, ?_, ?_⟩
      · rw [Array.size_copyD, Array.size_replicate]; exact hle
      · rw [Array.size_copyD, Array.size_replicate]
      · intro i
        rw [Array.getD_copyD _ _ _ (by rw [Array.size_replicate]; omega)]
        by_cases hi : i < μ.data.size
        · rw [ite_eq_left hi]
        · rw [ite_eq_right hi, Array.getD_replicate_zero,
            Array.getD_of_size_le 0 (Nat.not_lt.mp hi)]

lemma Mem.Wf.write {μ : Mem} (h : Mem.Wf μ) (n : Nat) (ys : Bytes) :
    Mem.Wf (μ.write n ys) := by
  cases ys with
  | nil => exact h
  | cons y ys =>
    rcases Mem.write_aux h n (ys := y :: ys) (by simp only [ne_eq, reduceCtorEq, not_false_eq_true]) with ⟨A, hdata, _, hsz, _⟩
    simp only [Mem.Wf, hdata, Array.size_writeD]
    exact hsz

/-- Read-over-write for EVM memory, and the whole point of this section: the
image after a write is the image before it with the payload laid over it, and
everything the write did not touch — including the bytes past the payload inside
the word the machine rounds up to — still reads as it did. -/
lemma Mem.Reads.write {μ : Mem} {bs : Bytes} (hwf : Mem.Wf μ) (h : Mem.Reads μ bs)
    (n : Nat) (ys : Bytes) :
    Mem.Reads (μ.write n ys) (Bytes.writeAt bs n ys) := by
  cases ys with
  | nil =>
    intro i
    rw [Bytes.getD_writeAt]
    simp only [List.length_nil, Nat.add_zero]
    rw [ite_eq_right (by omega)]
    exact h i
  | cons y ys =>
    rcases Mem.write_aux hwf n (ys := y :: ys) (by simp only [ne_eq, reduceCtorEq,
      not_false_eq_true]) with
      ⟨A, hdata, hlen, _, hreads⟩
    intro i
    rw [hdata, Array.getD_writeD 0 _ A n i hlen, Bytes.getD_writeAt]
    by_cases hin : n ≤ i ∧ i < n + (y :: ys).length
    · rw [ite_eq_left hin, ite_eq_left hin]
    · rw [ite_eq_right hin, ite_eq_right hin, hreads i]
      exact h i

/-! ### Reading the image back

`Mem.read` slices the backing array with `Array.sliceD`, which accumulates from
the far end, while `List.sliceD` consumes from the near end.  Both are put in
the same `List.range` normal form, after which a pointwise `Mem.Reads` transfers
between them. -/

lemma Array.sliceD_aux_eq {ξ : Type} (xs : Array ξ) (d : ξ) :
    ∀ (n : Nat) (Acc : List ξ) (m : Nat),
      Array.sliceD.aux xs Acc m n d
        = (List.range n).map (fun j => xs.getD (m + j) d) ++ Acc := by
  intro n
  induction n with
  | zero => intro Acc m; rfl
  | succ n ih =>
    intro Acc m
    rw [show Array.sliceD.aux xs Acc m (n + 1) d
          = Array.sliceD.aux xs (xs.getD (m + n) d :: Acc) m n d from rfl,
      ih, List.range_succ]
    simp only [Array.getD_eq_getD_getElem?, map_append, map_cons, map_nil, append_assoc,
      cons_append, nil_append]

lemma Array.sliceD_eq_map {ξ : Type} (xs : Array ξ) (m n : Nat) (d : ξ) :
    Array.sliceD xs m n d = (List.range n).map (fun j => xs.getD (m + j) d) := by
  rw [show Array.sliceD xs m n d = Array.sliceD.aux xs [] m n d from rfl,
    Array.sliceD_aux_eq]
  simp only [Array.getD_eq_getD_getElem?, append_nil]

lemma List.sliceD_eq_map {ξ : Type} (ys : List ξ) (d : ξ) :
    ∀ (n m : Nat), List.sliceD ys m n d
      = (List.range n).map (fun j => ys.getD (m + j) d) := by
  intro n
  induction n with
  | zero => intro m; rfl
  | succ n ih =>
    intro m
    rw [List.sliceD_succ, ih (m + 1), List.range_succ_eq_map]
    simp only [List.map_cons, List.map_map, Nat.add_zero]
    congr 1
    apply List.map_congr_left
    intro j _
    show ys.getD (m + 1 + j) d = ys.getD (m + (j + 1)) d
    rw [show m + (j + 1) = m + 1 + j from by omega]

/-- Pointwise read inside a padded slice, while the requested index remains
inside that slice's declared width. -/
lemma Bytes.getD_sliceD_of_lt
    (bs : Bytes) (start len i : Nat) (hi : i < len) :
    (bs.sliceD start len 0).getD i 0 = bs.getD (start + i) 0 := by
  rw [List.sliceD_eq_map]
  simp only [getD_eq_getElem?_getD, length_map, length_range, hi, getElem?_pos, getElem_map,
    getElem_range, Option.getD_some]

/-- A subwindow wholly inside a padded slice is the corresponding slice of the
original image.  This is the word-projection rule for a multiword ABI copy. -/
lemma Bytes.sliceD_sliceD_of_le
    (bs : Bytes) (start width offset len : Nat)
    (h : offset + len ≤ width) :
    (bs.sliceD start width 0).sliceD offset len 0 =
      bs.sliceD (start + offset) len 0 := by
  rw [List.sliceD_eq_map (bs.sliceD start width 0) 0 len offset,
    List.sliceD_eq_map bs 0 len (start + offset)]
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.mp hi
  rw [Bytes.getD_sliceD_of_lt _ _ _ _ (by omega)]
  congr 1
  omega

/-- A write starting after a requested slice leaves that earlier slice
unchanged. -/
lemma Bytes.sliceD_writeAt_before
    (bs xs : Bytes) (start len n : Nat)
    (h : start + len ≤ n) :
    (Bytes.writeAt bs n xs).sliceD start len 0 =
      bs.sliceD start len 0 := by
  rw [List.sliceD_eq_map, List.sliceD_eq_map]
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.mp hi
  rw [Bytes.getD_writeAt]
  rw [ite_eq_right]
  omega

/-- The mirror of `Bytes.sliceD_writeAt_before`: a write that lands entirely
below the read window leaves it alone.  Scratch-word walks need both halves,
because later writes may sit on either side of an earlier word. -/
lemma Bytes.sliceD_writeAt_after
    (bs xs : Bytes) (start len n : Nat)
    (h : n + xs.length ≤ start) :
    (Bytes.writeAt bs n xs).sliceD start len 0 =
      bs.sliceD start len 0 := by
  rw [List.sliceD_eq_map, List.sliceD_eq_map]
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.mp hi
  rw [Bytes.getD_writeAt]
  rw [ite_eq_right]
  omega

/-- A padded read wholly inside a written window reads the corresponding
subwindow of the payload.  Constructor decoders use this after copying a
multiword ABI head and then loading its individual words. -/
lemma Bytes.sliceD_writeAt_inside
    (bs xs : Bytes) (n start len : Nat)
    (hstart : n ≤ start) (hend : start + len ≤ n + xs.length) :
    (Bytes.writeAt bs n xs).sliceD start len 0 =
      xs.sliceD (start - n) len 0 := by
  rw [List.sliceD_eq_map, List.sliceD_eq_map]
  apply List.map_congr_left
  intro i hi
  have hi' := List.mem_range.mp hi
  rw [Bytes.getD_writeAt, ite_eq_left (by omega)]
  congr 1
  omega

/-- Reading back the 32-byte word just written at `n`.  Scratch-word walks
store and reload whole words, so this is the shape they need rather than the
length-polymorphic `Bytes.sliceD_writeAt`. -/
lemma Bytes.readWord_writeAt_self (bs : Bytes) (n : Nat) (v : B256) :
    Bytes.toB256 ((Bytes.writeAt bs n v.toBytes).sliceD n 32 0) = v := by
  rw [show (32 : Nat) = v.toBytes.length from (B256.length_toBytes v).symm,
    Bytes.sliceD_writeAt]
  exact B256.toB256_toBytes v

/-- A 32-byte word write that misses the 32-byte read window entirely, on
either side, leaves it alone. -/
lemma Bytes.readWord_writeAt_of_disjoint (bs : Bytes) (start n : Nat)
    (v : B256) (h : start + 32 ≤ n ∨ n + 32 ≤ start) :
    (Bytes.writeAt bs n v.toBytes).sliceD start 32 0 =
      bs.sliceD start 32 0 := by
  rcases h with h | h
  · exact Bytes.sliceD_writeAt_before bs v.toBytes start 32 n h
  · exact Bytes.sliceD_writeAt_after bs v.toBytes start 32 n
      (by rw [B256.length_toBytes]; exact h)

/-- What a `CALL`, `LOG` or `MLOAD` reads out of a memory whose image is known:
exactly the corresponding slice of the image, zero-padded past its end. -/
lemma Mem.Reads.read {μ : Mem} {bs : Bytes} (h : Mem.Reads μ bs) (i n : Nat) :
    (μ.read i n).1 = bs.sliceD i n 0 := by
  show Array.sliceD μ.data i n 0 = _
  rw [Array.sliceD_eq_map, List.sliceD_eq_map]
  exact List.map_congr_left (fun j _ => h (i + j))

/-- Two adjacent whole-word writes determine their 64-byte image window. -/
lemma Bytes.read_two_word_writes_at (image : Bytes) (start : Nat)
    (left right : B256) :
    (Bytes.writeAt (Bytes.writeAt image start left.toBytes)
      (start + 32) right.toBytes).sliceD start 64 0 =
        left.toBytes ++ right.toBytes := by
  rw [show (64 : Nat) = 32 + 32 by omega, List.sliceD_split]
  congr 1
  · rw [Bytes.sliceD_writeAt_before _ _ start 32 (start + 32) (by omega),
      show (32 : Nat) = left.toBytes.length from
        (B256.length_toBytes left).symm,
      Bytes.sliceD_writeAt]
  · rw [show (32 : Nat) = right.toBytes.length from
        (B256.length_toBytes right).symm,
      Bytes.sliceD_writeAt]

/-- Two adjacent whole-word stores at an arbitrary memory offset determine the
complete 64-byte readback independently of the prior image.  `Mem.Wf` is
needed only to transport the reader image through the two writes. -/
lemma Mem.read_two_word_writes_at {μ : Mem} {image : Bytes}
    (hwf : Mem.Wf μ) (hreads : Mem.Reads μ image) (start : Nat)
    (left right : B256) :
    ((((μ.write start left.toBytes).write (start + 32) right.toBytes).read
      start 64).1) =
      left.toBytes ++ right.toBytes := by
  have hreadsLeft : Mem.Reads (μ.write start left.toBytes)
      (Bytes.writeAt image start left.toBytes) :=
    Mem.Reads.write hwf hreads start left.toBytes
  have hreadsRight :
      Mem.Reads
        ((μ.write start left.toBytes).write (start + 32) right.toBytes)
        (Bytes.writeAt (Bytes.writeAt image start left.toBytes)
          (start + 32) right.toBytes) :=
    Mem.Reads.write (Mem.Wf.write hwf start left.toBytes) hreadsLeft
      (start + 32) right.toBytes
  rw [Mem.Reads.read hreadsRight,
    Bytes.read_two_word_writes_at]

/-- Offset-zero specialization retained for existing event proofs. -/
lemma Mem.read_two_word_writes {μ : Mem} {image : Bytes}
    (hwf : Mem.Wf μ) (hreads : Mem.Reads μ image) (left right : B256) :
    ((((μ.write 0 left.toBytes).write 32 right.toBytes).read 0 64).1) =
      left.toBytes ++ right.toBytes := by
  simpa only [zero_add] using Mem.read_two_word_writes_at hwf hreads 0 left right

/-- Reading back a nonempty byte string immediately after writing it at offset
zero returns that byte string, independently of the old memory image.  Unlike
`Mem.Reads.write`, this self-window fact needs no well-formedness premise: each
branch of `Mem.write` allocates enough backing array for the payload itself. -/
lemma Mem.read_write_zero (μ : Mem) {ys : Bytes} (hne : ys ≠ []) :
    ((μ.write 0 ys).read 0 ys.length).1 = ys := by
  rcases ys with _ | ⟨b, bs⟩
  · exact absurd rfl hne
  · simp only [Mem.write]
    split
    · split
      · simp only [Mem.read, Array.sliceD_eq_map]
        apply List.ext_get
        · simp only [zero_add, Array.getD_eq_getD_getElem?, length_cons, length_map, length_range]
        · intro n h1 h2
          simp only [List.length_map, List.length_range] at h1
          simp only [List.get_eq_getElem, List.getElem_map,
            List.getElem_range, zero_add]
          rw [Array.getD_writeD 0 (b :: bs) μ.data 0 n (by omega),
            ite_eq_left (by omega)]
          simp only [tsub_zero, getD_eq_getElem?_getD, List.getElem?_eq_getElem h2,
            Option.getD_some]
      · simp only [Mem.read, Array.sliceD_eq_map]
        apply List.ext_get
        · simp only [length_cons, zero_add, Array.getD_eq_getD_getElem?, length_map, length_range]
        · intro n h1 h2
          simp only [List.length_map, List.length_range] at h1
          simp only [List.get_eq_getElem, List.getElem_map,
            List.getElem_range, zero_add]
          rw [Array.getD_writeD 0 (b :: bs)
            (Array.copyD μ.data (Array.replicate (b :: bs).length 0))
            0 n (by simp only [length_cons, zero_add, Array.size_copyD, Array.size_replicate,
              Std.le_refl]), ite_eq_left (by omega)]
          simp only [tsub_zero, getD_eq_getElem?_getD, List.getElem?_eq_getElem h2,
            Option.getD_some]
    · simp only [Mem.read, Array.sliceD_eq_map]
      apply List.ext_get
      · simp only [length_cons, zero_add, Array.getD_eq_getD_getElem?, length_map, length_range]
      · intro n h1 h2
        simp only [List.length_map, List.length_range] at h1
        simp only [List.get_eq_getElem, List.getElem_map,
          List.getElem_range, zero_add]
        rw [Array.getD_writeD 0 (b :: bs)
          (Array.copyD μ.data
            (Array.replicate (ceil32 (b :: bs).length) 0))
          0 n (by
            rw [Array.size_copyD, Array.size_replicate]
            simpa only [length_cons, zero_add] using Nat.le_ceil32 (b :: bs).length),
          ite_eq_left (by omega)]
        simp only [tsub_zero, getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some]

/-- Pointwise read-back below the allocated end of a nonempty memory write.
Inside the written interval the payload wins; below its start the old byte is
preserved.  The upper bound is what makes this true even for a malformed raw
`Mem` whose backing array is longer than its logical size: `Mem.write` may
truncate such an array, but never below the end it allocates for the payload. -/
lemma Mem.getD_write_below_end (μ : Mem) (start : Nat) {ys : Bytes}
    (hne : ys ≠ []) {i : Nat} (hi : i < start + ys.length) :
    (μ.write start ys).data.getD i 0 =
      if start ≤ i then ys.getD (i - start) 0 else μ.data.getD i 0 := by
  rcases ys with _ | ⟨b, bs⟩
  · exact absurd rfl hne
  · simp only [Mem.write]
    split
    · split
      · rw [Array.getD_writeD (0 : UInt8) (b :: bs) μ.data start i
          (by omega)]
        by_cases hstart : start ≤ i
        · rw [ite_eq_left (by omega), ite_eq_left hstart]
        · rw [ite_eq_right (by omega), ite_eq_right hstart]
      · rw [Array.getD_writeD (0 : UInt8) (b :: bs)
          (Array.copyD μ.data
            (Array.replicate (start + (b :: bs).length) (0 : UInt8)))
          start i (by simp only [length_cons, Array.size_copyD, Array.size_replicate, Std.le_refl])]
        by_cases hstart : start ≤ i
        · rw [ite_eq_left (by omega), ite_eq_left hstart]
        · rw [ite_eq_right (by omega), ite_eq_right hstart]
          by_cases hold : i < μ.data.size
          · rw [Array.getD_copyD_of_lt _ _ _ _ hold
              (by simp only [length_cons, Array.size_replicate]; omega)]
          · rw [Array.getD_copyD_of_size_le _ _ _ _ (Nat.le_of_not_gt hold),
              Array.getD_replicate_zero,
              Array.getD_of_size_le 0 (Nat.not_lt.mp hold)]
    · rw [Array.getD_writeD (0 : UInt8) (b :: bs)
        (Array.copyD μ.data
          (Array.replicate (ceil32 (start + (b :: bs).length))
            (0 : UInt8)))
        start i (by
          rw [Array.size_copyD, Array.size_replicate]
          exact Nat.le_ceil32 _)]
      by_cases hstart : start ≤ i
      · rw [ite_eq_left (by omega), ite_eq_left hstart]
      · rw [ite_eq_right (by omega), ite_eq_right hstart]
        by_cases hold : i < μ.data.size
        · rw [Array.getD_copyD_of_lt _ _ _ _ hold
            (by simp only [length_cons, Array.size_replicate]; exact lt_of_lt_of_le hi (Nat.le_ceil32 _))]
        · rw [Array.getD_copyD_of_size_le _ _ _ _ (Nat.le_of_not_gt hold),
            Array.getD_replicate_zero,
            Array.getD_of_size_le 0 (Nat.not_lt.mp hold)]

/-- A nonempty raw memory write always allocates backing data and logical size
through the end of its payload. -/
lemma Mem.write_end_le_data_size (μ : Mem) (start : Nat) {ys : Bytes}
    (hne : ys ≠ []) :
    start + ys.length ≤ (μ.write start ys).data.size := by
  rcases ys with _ | ⟨b, bs⟩
  · exact absurd rfl hne
  · simp only [Mem.write]
    split
    · split
      · simpa only [length_cons, Array.size_writeD]
      · simp only [length_cons, Array.size_writeD, Array.size_copyD, Array.size_replicate,
        Std.le_refl]
    · simp only [Array.size_writeD, Array.size_copyD, Array.size_replicate]
      exact Nat.le_ceil32 _

lemma Mem.write_end_le_size (μ : Mem) (start : Nat) {ys : Bytes}
    (hne : ys ≠ []) : start + ys.length ≤ (μ.write start ys).size := by
  rcases ys with _ | ⟨b, bs⟩
  · exact absurd rfl hne
  · simp only [Mem.write]
    split
    · split <;> assumption
    · exact Nat.le_ceil32 _

/-- Two adjacent whole-word writes determine their 64-byte read window even
for a raw, not-yet-certified memory value.  This is the exact scratch-memory
fact needed by nested mapping-key computations reached before a theorem has a
`Mem.Wf` premise available. -/
lemma Mem.read_two_word_writes_at_raw (μ : Mem) (start : Nat)
    (left right : B256) :
    ((((μ.write start left.toBytes).write (start + 32) right.toBytes).read
      start 64).1) = left.toBytes ++ right.toBytes := by
  simp only [Mem.read, Array.sliceD_eq_map]
  apply List.ext_get
  · simp only [Array.getD_eq_getD_getElem?, length_map, length_range, length_append,
    B256.length_toBytes, reduceAdd]
  · intro i hleft hright
    simp only [List.length_map, List.length_range] at hleft
    simp only [List.get_eq_getElem, List.getElem_map, List.getElem_range]
    rw [Mem.getD_write_below_end _ (start + 32)
      (by
        intro h
        have hlen := B256.length_toBytes right
        simp only [h, length_nil, OfNat.zero_ne_ofNat] at hlen)
      (by simp only [B256.length_toBytes]; omega)]
    by_cases hhalf : i < 32
    · rw [ite_eq_right (by omega), Mem.getD_write_below_end _ start
        (by
          intro h
          have hlen := B256.length_toBytes left
          simp only [h, length_nil, OfNat.zero_ne_ofNat] at hlen)
        (by simp only [B256.length_toBytes, add_lt_add_iff_left]; omega), ite_eq_left (by omega)]
      calc
        left.toBytes.getD (start + i - start) 0 =
            left.toBytes.getD i 0 := by congr 1 <;> omega
        _ = (left.toBytes ++ right.toBytes).getD i 0 :=
          (List.getD_append_left (d := (0 : UInt8))
            (by simpa only [B256.length_toBytes] using hhalf)).symm
        _ = (left.toBytes ++ right.toBytes)[i] := by
          rw [List.getD_eq_getElem?_getD,
            List.getElem?_eq_getElem hright]
          rfl
    · rw [ite_eq_left (by omega)]
      have hsub : start + i - (start + 32) = i - 32 := by omega
      rw [hsub]
      calc
        right.toBytes.getD (i - 32) 0 =
            (left.toBytes ++ right.toBytes).getD i 0 := by
          rw [List.getD_append_right (d := (0 : UInt8))
            (by simp only [B256.length_toBytes]; omega), B256.length_toBytes]
        _ = (left.toBytes ++ right.toBytes)[i] := by
          rw [List.getD_eq_getElem?_getD,
            List.getElem?_eq_getElem hright]
          rfl

/-- Right-first companion used by nested mapping-key helpers: storing the
right word first necessarily allocates the whole window, so the following
left-word store cannot truncate it even when the input `Mem` is malformed. -/
lemma Mem.read_two_word_writes_at_raw_right_first (μ : Mem) (start : Nat)
    (left right : B256) :
    ((((μ.write (start + 32) right.toBytes).write start left.toBytes).read
      start 64).1) = left.toBytes ++ right.toBytes := by
  have hright : right.toBytes ≠ [] := by
    intro h
    have hlen := B256.length_toBytes right
    simp only [h, length_nil, OfNat.zero_ne_ofNat] at hlen
  have hleft : left.toBytes ≠ [] := by
    intro h
    have hlen := B256.length_toBytes left
    simp only [h, length_nil, OfNat.zero_ne_ofNat] at hlen
  let μ' := μ.write (start + 32) right.toBytes
  have hdata : start + left.toBytes.length ≤ μ'.data.size := by
    dsimp only [μ']
    have h := Mem.write_end_le_data_size μ (start + 32) hright
    simp only [B256.length_toBytes] at h ⊢
    omega
  have hsize : start + left.toBytes.length ≤ μ'.size := by
    dsimp only [μ']
    have h := Mem.write_end_le_size μ (start + 32) hright
    simp only [B256.length_toBytes] at h ⊢
    omega
  have hlen : left.toBytes.length = 32 := B256.length_toBytes left
  generalize heq : left.toBytes = ys at hleft hdata hsize hlen ⊢
  rcases ys with _ | ⟨b, bs⟩
  · exact absurd rfl hleft
  change (((μ'.write start (b :: bs)).read start 64).1) = _
  simp only [Mem.write]
  rw [ite_eq_left hsize, ite_eq_left hdata]
  simp only [Mem.read, Array.sliceD_eq_map]
  apply List.ext_get
  · simp only [List.length_map, List.length_range, List.length_append,
      B256.length_toBytes, List.length_cons] at hlen ⊢
    omega
  · intro i hwindow hout
    simp only [List.length_map, List.length_range] at hwindow
    simp only [List.get_eq_getElem, List.getElem_map, List.getElem_range]
    rw [Array.getD_writeD (0 : UInt8) (b :: bs) μ'.data start
      (start + i) hdata]
    by_cases hhalf : i < 32
    · rw [ite_eq_left (by omega)]
      calc
        (b :: bs).getD (start + i - start) 0 =
            (b :: bs).getD i 0 := by congr 1 <;> omega
        _ = ((b :: bs) ++ right.toBytes).getD i 0 :=
          (List.getD_append_left (d := (0 : UInt8))
            (by omega)).symm
        _ = ((b :: bs) ++ right.toBytes)[i] := by
          rw [List.getD_eq_getElem?_getD,
            List.getElem?_eq_getElem hout]
          rfl
    · rw [ite_eq_right (by omega)]
      dsimp only [cons_append, μ']
      rw [Mem.getD_write_below_end μ (start + 32) hright
        (by simp only [B256.length_toBytes]; omega), ite_eq_left (by omega)]
      have hsub : start + i - (start + 32) = i - 32 := by omega
      rw [hsub]
      calc
        right.toBytes.getD (i - 32) 0 =
            ((b :: bs) ++ right.toBytes).getD i 0 := by
          rw [List.getD_append_right (d := (0 : UInt8))
            (by omega), hlen]
        _ = ((b :: bs) ++ right.toBytes)[i] := by
          rw [List.getD_eq_getElem?_getD,
            List.getElem?_eq_getElem hout]
          rfl

/-- Bitwise `and` distributes over a shift-and-or split of both sides, provided
the low halves fit below the shift.  The one bit-level fact the `B128`/`B256`
`toNat` homomorphisms need. -/
lemma Nat.and_or_shiftLeft {a b c d k : Nat} (hb : b < 2 ^ k) (hd : d < 2 ^ k) :
    ((a <<< k ||| b) &&& (c <<< k ||| d)) = ((a &&& c) <<< k) ||| (b &&& d) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft]
  by_cases hi : k ≤ i
  · have hpow : (2 : Nat) ^ k ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) hi
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb hpow),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hd hpow)]
    simp only [ge_iff_le, hi, decide_true, Bool.true_and, Bool.or_false, Bool.and_self]
  · simp only [ge_iff_le, hi, decide_false, Bool.false_and, Bool.false_or]

lemma B128.toNat_and (x y : B128) : (x &&& y).toNat = x.toNat &&& y.toNat := by
  show ((x.1 &&& y.1).toNat <<< 64) ||| (x.2 &&& y.2).toNat = _
  rw [UInt64.toNat_and, UInt64.toNat_and]
  exact (Nat.and_or_shiftLeft (UInt64.toNat_lt x.2) (UInt64.toNat_lt y.2)).symm

lemma B256.toNat_and (x y : B256) : (x &&& y).toNat = x.toNat &&& y.toNat := by
  show ((x.1 &&& y.1).toNat <<< 128) ||| (x.2 &&& y.2).toNat = _
  rw [B128.toNat_and, B128.toNat_and]
  exact (Nat.and_or_shiftLeft (B128.toNat_lt (x := x.2)) (B128.toNat_lt (x := y.2))).symm

/-- Masking off the low five bits is division by `32`.  `2 ^ 256 - 32` is
`(2 ^ 251 - 1) <<< 5`, so both sides agree bit by bit. -/
lemma Nat.and_mask32 {n : Nat} (h : n < 2 ^ 256) :
    n &&& (2 ^ 256 - 32) = 32 * (n / 32) := by
  have hm : (2 : Nat) ^ 256 - 32 = (2 ^ 251 - 1) <<< 5 := by
    rw [Nat.shiftLeft_eq, Nat.sub_mul, Nat.one_mul, ← Nat.pow_add]
  have hr : 32 * (n / 32) = (n >>> 5) <<< 5 := by
    rw [Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow, Nat.mul_comm]
  rw [hm, hr]
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft,
    Nat.testBit_two_pow_sub_one, Nat.testBit_shiftRight]
  by_cases hi : 5 ≤ i
  · rw [show 5 + (i - 5) = i from by omega]
    simp only [ge_iff_le, hi, decide_true, Bool.true_and]
    by_cases hi2 : i < 256
    · rw [decide_eq_true (by omega : i - 5 < 251), Bool.and_true]
    · rw [Nat.testBit_lt_two_pow
        (Nat.lt_of_lt_of_le h (Nat.pow_le_pow_right (by omega) (by omega)))]
      rw [Bool.false_and]
  · simp only [ge_iff_le, hi, decide_false, Bool.false_and, Bool.and_false]

lemma ceil32_eq_mul (len : Nat) : ceil32 len = 32 * ((31 + len) / 32) := by
  unfold ceil32
  rcases hm : len % 32 with _ | m
  · show len = _; omega
  · show len + 32 - (m + 1) = _; omega

end Blanc
