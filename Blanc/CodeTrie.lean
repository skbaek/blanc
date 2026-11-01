import Jaune.Machine

/-!
# Balanced tries over code bytes

`LTrie` is a complete binary tree over list positions: a lookup costs `O(log n)` kernel steps,
where `code.data.toList[pc]?` costs `O(pc)`.  `CodeTries` bundles the byte and instruction-start
tries of a code with their equalities to the list reads, `jumpdestOkT` decides an accepted jump
destination from the tries (`jumpdestOkT_eq`), and `windowT` reads the 33 bytes from a position,
which is every byte `ByteArray.getInst` reads there (`getInst_windowT`).

The names stay in `Blanc.Lift`, where these declarations were first written
(`Blanc/Lift/CheckFast.lean`); this module has no Lift dependency, so the stack-certificate
checker (`Blanc/AbstractStackCertificate.lean`) reads the same tries.
-/

namespace Blanc.Lift

open Jaune

/-- A complete binary tree over list positions: at depth `d + 1` the left subtree holds positions
below `2 ^ d`. -/
inductive LTrie (α : Type) : Type
  | leaf : Option α → LTrie α
  | node : LTrie α → LTrie α → LTrie α

/-- Build the depth-`d` trie of a list (positions `≥ 2 ^ d` are dropped). -/
def LTrie.ofList {α : Type} : Nat → List α → LTrie α
  | 0, l => .leaf l.head?
  | d + 1, l => .node (LTrie.ofList d (l.take (2 ^ d))) (LTrie.ofList d (l.drop (2 ^ d)))

/-- Lookup at position `i` in a depth-`d` trie. -/
def LTrie.get? {α : Type} : Nat → LTrie α → Nat → Option α
  | 0, .leaf a, i => if i = 0 then a else none
  | d + 1, .node l r, i => if i < 2 ^ d then LTrie.get? d l i else LTrie.get? d r (i - 2 ^ d)
  | _, _, _ => none

theorem LTrie.get?_ofList {α : Type} (d : Nat) (l : List α) (hl : l.length ≤ 2 ^ d) (i : Nat) :
    LTrie.get? d (LTrie.ofList d l) i = l[i]? := by
  induction d generalizing l i with
  | zero =>
    cases l with
    | nil => simp only [ofList, List.head?_nil, get?, ite_self, List.length_nil, not_lt_zero,
      not_false_eq_true, getElem?_neg]
    | cons x xs =>
      have hxs : xs.length = 0 := by simpa only [List.length_eq_zero_iff, List.length_cons,
        pow_zero, add_le_iff_nonpos_left, nonpos_iff_eq_zero] using hl
      have : xs = [] := List.eq_nil_of_length_eq_zero hxs
      subst xs
      cases i <;> simp only [ofList, List.head?_cons, get?, ↓reduceIte, List.length_cons, List.length_nil, zero_add, zero_lt_one, getElem?_pos, List.getElem_cons_zero, Nat.add_eq_zero_iff, one_ne_zero, and_false, add_lt_iff_neg_right, not_lt_zero, not_false_eq_true, getElem?_neg]
  | succ d ih =>
    simp only [LTrie.ofList, LTrie.get?]
    by_cases hi : i < 2 ^ d
    · rw [ite_eq_left hi]
      rw [ih (l := l.take (2 ^ d)) (i := i)]
      · simp only [hi, List.getElem?_take_of_lt]
      · have htake : (l.take (2 ^ d)).length ≤ 2 ^ d := by
          rw [List.length_take]
          exact min_le_left _ _
        exact htake
    · rw [ite_eq_right hi]
      rw [ih (l := l.drop (2 ^ d)) (i := i - 2 ^ d)]
      · have hdrop : ∀ (n : Nat) (xs : List α) (j : Nat), n ≤ j →
            (xs.drop n)[j - n]? = xs[j]? := by
          intro n
          induction n with
          | zero => intro xs j _; simp only [List.drop_zero, tsub_zero]
          | succ n ih =>
            intro xs j hj
            cases xs with
            | nil => simp only [List.drop_nil, List.length_nil, not_lt_zero, not_false_eq_true,
              getElem?_neg]
            | cons x xs =>
              cases j with
              | zero => omega
              | succ j =>
                simp only [List.drop, List.getElem?_cons_succ]
                rw [show j + 1 - (n + 1) = j - n by omega]
                apply ih
                omega
        exact hdrop (2 ^ d) l i (Nat.le_of_not_gt hi)
      · simp only [List.length_drop]
        omega

/-- The code bytes and instruction starts of `code`, as tries of depth `d`. -/
structure CodeTries (code : ByteArray) (d : Nat) : Type where
  bytes : LTrie UInt8
  starts : LTrie Bool
  bytes_eq : ∀ i, LTrie.get? d bytes i = code.data.toList[i]?
  starts_eq : ∀ i, (LTrie.get? d starts i).getD false = (instStarts code).getD i false

/-- The canonical tries (when `code` fits in depth `d`). -/
def CodeTries.ofCode (code : ByteArray) (d : Nat) (hd : code.data.toList.length ≤ 2 ^ d)
    (hs : (instStarts code).length ≤ 2 ^ d) : CodeTries code d :=
  { bytes := LTrie.ofList d code.data.toList
    starts := LTrie.ofList d (instStarts code)
    bytes_eq := fun i => LTrie.get?_ofList d _ hd i
    starts_eq := fun i => by rw [LTrie.get?_ofList d _ hs i]; rfl }

/-- `jumpdestOk`, reading the code byte and the instruction-start flag from the tries. -/
def jumpdestOkT (code : ByteArray) (d : Nat) (T : CodeTries code d) (k : Nat) : Bool :=
  LTrie.get? d T.bytes k == some (Jinst.toUInt8 .jumpdest) &&
    (LTrie.get? d T.starts k).getD false

theorem jumpdestOkT_eq {code : ByteArray} {d : Nat} (T : CodeTries code d) (k : Nat) :
    jumpdestOkT code d T k = jumpdestOk code k := by
  by_cases hk : k < code.size
  · have hlist : k < code.data.toList.length := by
      simpa only [Array.length_toList, ByteArray.size_data] using
        hk
    have hget : code.data.toList[k]? = some code[k] := by
      exact List.getElem?_eq_getElem hlist
    have hdata : code.data[k] = code[k] := by rfl
    have ha : code.data[k]? = some code[k] := by
      rw [← hdata]
      simp only [ByteArray.size_data, hk, getElem?_pos]
    have hbyte : (code.data[k]? == some (Jinst.toUInt8 .jumpdest)) =
        decide (code[k] = Jinst.toUInt8 .jumpdest) := by
      rw [ha]
      rfl
    have hbeq : (code[k] == Jinst.toUInt8 .jumpdest) =
        decide (code[k] = Jinst.toUInt8 .jumpdest) := by rfl
    simp only [jumpdestOkT, hk, T.bytes_eq, Array.length_toList, ByteArray.size_data,
      getElem?_pos, Array.getElem_toList, hdata, Option.some_beq_some, hbeq,
      T.starts_eq, List.getD_eq_getElem?_getD, jumpdestOk, ↓reduceDIte, instStartAt,
      Bool.decide_and, Bool.decide_eq_true]
  · have hlist : ¬ k < code.data.toList.length := by
      simpa only [Array.length_toList, ByteArray.size_data] using hk
    have hnone : LTrie.get? d T.bytes k = none := by
      rw [T.bytes_eq]
      exact getElem?_neg code.data.toList k hlist
    simp only [jumpdestOkT, hnone, Option.none_beq_some, Bool.false_and, jumpdestOk, hk,
      ↓reduceDIte]


/-- The 33 trie bytes from `pc` (zero past the trie). -/
def windowT (d : Nat) (t : LTrie UInt8) (pc : Nat) : Array UInt8 :=
  ((List.range 33).map fun i => (LTrie.get? d t (pc + i)).getD 0).toArray

/-- `sliceD` with fill byte zero is the list of `byteD` reads. -/
theorem sliceD_eq_map_byteD (xs : ByteArray) (m n : Nat) :
    xs.sliceD m n 0 = (List.range n).map fun i => xs.byteD (m + i) := by
  induction n generalizing m with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ_eq_map, List.map_cons, List.map_map]
    unfold ByteArray.sliceD
    by_cases hm : m < xs.size
    · rw [dite_eq_left hm, ih]
      simp only [ByteArray.byteD, hm, ↓reduceDIte, Nat.add_zero, List.cons.injEq, true_and]
      apply List.map_congr_left
      intro i _
      simp only [Function.comp, Nat.succ_eq_add_one]
      rw [show m + 1 + i = m + (i + 1) by omega]
    · rw [dite_eq_right hm]
      simp only [ByteArray.byteD, Nat.add_zero, hm, ↓reduceDIte, List.replicate_succ,
        List.cons.injEq, true_and]
      rw [List.map_congr_left (g := fun _ => (0 : UInt8))]
      · simp only [List.map_const', List.length_range]
      · intro i _
        simp only [Function.comp]
        rw [dite_eq_right (by omega)]

/-- The 33 bytes of `code` from `pc`, zero past its end. -/
def codeWindow (code : ByteArray) (pc : Nat) : ByteArray :=
  ⟨((List.range 33).map fun i => code.byteD (pc + i)).toArray⟩

theorem codeWindow_size (code : ByteArray) (pc : Nat) : (codeWindow code pc).size = 33 := by
  simp only [codeWindow, ByteArray.size, List.size_toArray, List.length_map, List.length_range]

theorem codeWindow_byteD (code : ByteArray) (pc : Nat) {k : Nat} (hk : k < 33) :
    (codeWindow code pc).byteD k = code.byteD (pc + k) := by
  have hs : k < (codeWindow code pc).size := by rw [codeWindow_size]; exact hk
  unfold ByteArray.byteD
  rw [dite_eq_left hs, ByteArray.getElem_eq_getElem_data]
  simp only [codeWindow, List.getElem_toArray, List.getElem_map, List.getElem_range]
  rfl

/-- In-range positions with equal bytes and equal next 32 bytes decode equally. -/
theorem getInst_congr {a b : ByteArray} {i j : Nat} (hi : i < a.size) (hj : j < b.size)
    (hr : ∀ k < 33, a.byteD (i + k) = b.byteD (j + k)) : a.getInst i = b.getInst j := by
  have hab : a[i] = b[j] := by
    have h := hr 0 (by omega)
    simpa only [ByteArray.byteD, Nat.add_zero, hi, hj, ↓reduceDIte] using h
  have hs : ∀ n ≤ 32, a.sliceD (i + 1) n 0 = b.sliceD (j + 1) n 0 := by
    intro n hn
    rw [sliceD_eq_map_byteD, sliceD_eq_map_byteD]
    apply List.map_congr_left
    intro k hk
    rw [List.mem_range] at hk
    rw [show i + 1 + k = i + (k + 1) by omega, show j + 1 + k = j + (k + 1) by omega]
    exact hr (k + 1) (by omega)
  have h1 : a.byteD (i + 1) = b.byteD (j + 1) := hr 1 (by omega)
  unfold ByteArray.getInst
  simp only [hi, hj, ↓reduceDIte, h1]
  split <;> rename_i h₁ <;> have h₂ := hab ▸ h₁
  · split <;> split <;> (try split) <;>
      simp_all +decide only [Nat.one_lt_ofNat, heq_eq_eq, reduceCtorEq, not_isEmpty_of_nonempty,
        IsEmpty.forall_iff, implies_true, imp_false]
  all_goals split <;> rename_i h₃ <;> (try (rw [h₂] at h₃; cases h₃))
  · simp only [hab]
  · simp only [hab]
  · simp only [hab]
  · have := le_of_toInstType_eq_p _ h₂
    simp only [hab, hs (b[j].toNat - 95) (by omega)]

/-- `getInst` reads only the 33 bytes from `pc`. -/
theorem getInst_codeWindow (code : ByteArray) (pc : Nat) :
    (codeWindow code pc).getInst 0 = code.getInst pc := by
  by_cases hpc : pc < code.size
  · exact getInst_congr (by rw [codeWindow_size]; omega) hpc (fun k hk => by
      rw [Nat.zero_add, codeWindow_byteD code pc hk])
  · have hw : codeWindow code pc = ⟨(List.replicate 33 (0 : UInt8)).toArray⟩ := by
      simp only [codeWindow, ByteArray.mk.injEq]
      congr 1
      rw [List.map_congr_left (g := fun _ => (0 : UInt8))]
      · simp only [List.map_const', List.length_range]
      · intro i _
        simp only [ByteArray.byteD]
        rw [dite_eq_right (by omega)]
    rw [hw]
    unfold ByteArray.getInst
    rw [dite_eq_right hpc]
    rfl

/-- The trie window is the code window. -/
theorem windowT_eq {code : ByteArray} {d : Nat} (T : CodeTries code d) (pc : Nat) :
    ByteArray.mk (windowT d T.bytes pc) = codeWindow code pc := by
  simp only [windowT, codeWindow, ByteArray.mk.injEq, T.bytes_eq]
  congr 1
  apply List.map_congr_left
  intro i _
  by_cases h : pc + i < code.size
  · have hl : pc + i < code.data.toList.length := by simpa only [Array.length_toList,
      ByteArray.size_data] using h
    simp only [ByteArray.byteD, h, ↓reduceDIte, List.getElem?_eq_getElem hl, Option.getD_some]
    rfl
  · have hl : ¬ pc + i < code.data.toList.length := by simpa only [Array.length_toList,
      ByteArray.size_data] using h
    simp only [ByteArray.byteD, h, ↓reduceDIte, List.getElem?_eq_none (Nat.le_of_not_gt hl),
      Option.getD_none]

/-- The instruction at `pc`, decoded from the trie window. -/
theorem getInst_windowT {code : ByteArray} {d : Nat} (T : CodeTries code d) (pc : Nat) :
    (ByteArray.mk (windowT d T.bytes pc)).getInst 0 = code.getInst pc := by
  rw [windowT_eq, getInst_codeWindow]

end Blanc.Lift
