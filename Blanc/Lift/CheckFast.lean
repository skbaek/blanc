import Blanc.Lift.Exact

/-!
# Kernel-economical certificate checking

`checkNode` and `jumpsOkNode` read code bytes through `code.data.toList` (`List.drop`, `[pc]?`) and
`jumpdestOk` rescans the whole code for instruction starts at every jump target.  Under `decide +kernel`
each read is linear in the code size and the kernel keeps every intermediate term, so large entries of
large contracts exhaust memory (a 1,474-node entry of the 6,358-byte deployed beacon deposit contract
passed 16 GiB).

This module adds a balanced binary trie over a list (`LTrie`), whose lookup costs `O(log n)` kernel
steps, and trie-reading copies of the two checkers.  `checkNodeT_eq` and `jumpsOkNodeT_eq` state that
the copies compute exactly the original checkers when the tries represent the code, so a per-entry
certificate decision can be made on the fast copy and rewritten back.  The trusted definitions in
`Check.lean` and `Exact.lean` are not changed.
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
    · rw [if_pos hi]
      rw [ih (l := l.take (2 ^ d)) (i := i)]
      · simp only [hi, List.getElem?_take_of_lt]
      · have htake : (l.take (2 ^ d)).length ≤ 2 ^ d := by
          rw [List.length_take]
          exact min_le_left _ _
        exact htake
    · rw [if_neg hi]
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

def bytesAtT (d : Nat) (t : LTrie UInt8) : Nat → Bytes → Bool
  | _, [] => true
  | pc, b :: bs => LTrie.get? d t pc == some b && bytesAtT d t (pc + 1) bs

/-- `checkNode`, reading bytes from the trie `t`.  Identical to `checkNode` arm by arm except that
`byteAt code pc` is `LTrie.get? d t pc` and `bytesAt code pc bs` is `bytesAtT d t pc bs`. -/
def checkNodeT (code : ByteArray) (d : Nat) (t : LTrie UInt8) (es : List Entry) (m : Nat) :
    Nat → List AVal → SFunc → Bool
  | pc, a, .next n f =>
    bytesAtT d t pc (Ninst.toBytes n) && Ninst.pcFree n &&
      match absNinst n a with
      | some a' => checkNodeT code d t es m (pc + n.size) a' f
      | none => false
  | pc, _, .last l => LTrie.get? d t pc == some l.toUInt8
  | pc, a, .dest f =>
    LTrie.get? d t pc == some (Jinst.toUInt8 .jumpdest) && checkNodeT code d t es m (pc + 1) a f
  | pc, a, .branch f g =>
    match a with
    | .const tg :: v :: a' =>
      LTrie.get? d t pc == some (Jinst.toUInt8 .jumpi) &&
        (v.jumps? == some true || checkNodeT code d t es m (pc + 1) a' f) &&
        (v.jumps? == some false || checkNodeT code d t es m tg.toNat a' g)
    | _ => false
  | pc, a, .branchTo f k =>
    match a, es[k]? with
    | .const tg :: v :: a', some e =>
      LTrie.get? d t pc == some (Jinst.toUInt8 .jumpi) && e.pc == tg.toNat &&
        e.rets == m && gotoCompat a' e.frame &&
        (v.jumps? == some true || checkNodeT code d t es m (pc + 1) a' f)
    | _, _ => false
  | pc, a, .jump k =>
    match a, es[k]? with
    | .const tg :: a', some e =>
      LTrie.get? d t pc == some (Jinst.toUInt8 .jump) && e.pc == tg.toNat &&
        e.rets == m && gotoCompat a' e.frame
    | _, _ => false
  | pc, a, .callNext k f =>
    match a, f, es[k]? with
    | .const tg :: a', .dest _, some e =>
      LTrie.get? d t pc == some (Jinst.toUInt8 .jump) && e.pc == tg.toNat &&
        decide (e.frame.length ≤ a'.length) &&
        (match e.frame.findIdx? (· == .ret) with
         | some i =>
           match a'[i]? with
           | some (.const r) =>
             callCompat r a' e.frame &&
               checkNodeT code d t es m r.toNat
                 (List.replicate e.rets .unk ++ a'.drop e.frame.length) f
           | _ => false
         | none => callCompat 0 a' e.frame)
    | _, _, _ => false
  | pc, a, .ret =>
    match a with
    | .ret :: a' => LTrie.get? d t pc == some (Jinst.toUInt8 .jump) && a'.length == m
    | _ => false
  | pc, a, .pcAt p f =>
    bytesAtT d t pc (Ninst.toBytes (.reg .pc)) && p == pc &&
      checkNodeT code d t es m (pc + 1) (.const (Nat.toB256 pc) :: a) f
  | pc, _, .undefined => (code.getInst pc).isNone

private lemma getElem?_eq_drop_head {α : Type} (xs : List α) (i : Nat) :
    xs[i]? = (xs.drop i).head? := by
  induction i generalizing xs with
  | zero => cases xs <;> rfl
  | succ i ih =>
    cases xs with
    | nil => simp only [List.length_nil, not_lt_zero, not_false_eq_true, getElem?_neg, List.drop_nil, List.head?_nil]
    | cons x xs => simpa only [List.getElem?_cons_succ, List.drop_succ_cons] using ih xs

private lemma bytesAtT_eq {code : ByteArray} {d : Nat} {t : LTrie UInt8}
    (ht : ∀ i, LTrie.get? d t i = code.data.toList[i]?) (pc : Nat) (bs : Bytes) :
    bytesAtT d t pc bs = bytesAt code pc bs := by
  induction bs generalizing pc with
  | nil => rfl
  | cons b bs ih =>
    rw [bytesAtT, ht, ih]
    simp only [bytesAt]
    rw [getElem?_eq_drop_head]
    cases h : code.data.toList.drop pc with
    | nil => simp only [List.head?_nil, Option.none_beq_some, Bool.false_and, List.length_cons,
      List.take_nil, List.nil_eq, reduceCtorEq, decide_false]
    | cons c cs =>
      have hnext : code.data.toList.drop (pc + 1) = cs := by
        rw [show pc + 1 = pc + 1 by rfl, ← List.drop_drop, h]
        rfl
      have hbeq : (c == b) = decide (c = b) := by
        rfl
      simp only [List.head?_cons, Option.some_beq_some, hbeq, hnext, List.length_cons,
        List.take_succ_cons, List.cons.injEq, Bool.decide_and]

theorem checkNodeT_eq {code : ByteArray} {d : Nat} (T : CodeTries code d) (es : List Entry)
    (m pc : Nat) (a : List AVal) (f : SFunc) :
    checkNodeT code d T.bytes es m pc a f = checkNode code es m pc a f := by
  let Q : SFunc → Prop := fun f =>
    ∀ (pc : Nat) (a : List AVal),
      checkNodeT code d T.bytes es m pc a f = checkNode code es m pc a f
  let P : SFunc → Prop := fun f =>
    Q f ∧ match f with
    | .dest g => Q g
    | _ => True
  have hall : ∀ f : SFunc, P f := by
    intro f
    induction f with
    | next n f ih =>
      constructor
      · intro pc a
        cases h : absNinst n a <;>
          simp only [checkNodeT, bytesAtT_eq T.bytes_eq, h, Bool.and_false, checkNode, Q, ih.1]
      · simp only
    | last l =>
      constructor
      · intro pc a
        simp only [checkNodeT, T.bytes_eq, Array.getElem?_toList, checkNode, byteAt]
      · simp only
    | dest f ih =>
      constructor
      · intro pc a
        simp only [checkNodeT, T.bytes_eq, Array.getElem?_toList, ih.1, checkNode, byteAt, Q]
      · exact ih.1
    | branch f g ihf ihg =>
      constructor
      · intro pc a
        cases a with
        | nil => rfl
        | cons av a =>
          cases av <;> cases a <;>
            simp only [checkNodeT, checkNode, Q, T.bytes_eq, Array.getElem?_toList, ihf.1, ihg.1, byteAt]
      · simp only
    | branchTo f k ih =>
      constructor
      · intro pc a
        cases a with
        | nil => rfl
        | cons av a =>
          cases av <;> cases a <;> cases h : es[k]? <;>
            simp only [checkNodeT, checkNode, Q, h, T.bytes_eq, Array.getElem?_toList, ih.1, byteAt]
      · simp only
    | jump k =>
      constructor
      · intro pc a
        cases a with
        | nil => rfl
        | cons av a =>
          cases av <;> cases h : es[k]? <;>
            simp only [checkNodeT, h, checkNode, T.bytes_eq, Array.getElem?_toList, byteAt]
      · simp only
    | callNext k f ih =>
      constructor
      · intro pc a
        cases a with
        | nil => rfl
        | cons av a =>
          cases av <;> cases f <;> cases h : es[k]? <;>
            simp only [checkNodeT, checkNode, Q, h, T.bytes_eq, Array.getElem?_toList, ih.2, byteAt] <;> rfl
      · simp only
    | ret =>
      constructor
      · intro pc a
        cases a with
        | nil => rfl
        | cons av a =>
          cases av <;> simp only [checkNodeT, checkNode, T.bytes_eq, Array.getElem?_toList, byteAt]
      · simp only
    | pcAt p f ih =>
      constructor
      · intro pc a
        simp only [checkNodeT, bytesAtT_eq T.bytes_eq, ih.1, checkNode, Q]
      · simp only
    | undefined =>
      constructor
      · intro pc a; rfl
      · simp only
  exact (hall f).1 pc a

/-- `jumpdestOk`, reading the code byte and the instruction-start flag from the tries. -/
def jumpdestOkT (code : ByteArray) (d : Nat) (T : CodeTries code d) (k : Nat) : Bool :=
  decide (k < code.size) && LTrie.get? d T.bytes k == some (Jinst.toUInt8 .jumpdest) &&
    (LTrie.get? d T.starts k).getD false

theorem jumpdestOkT_eq {code : ByteArray} {d : Nat} (T : CodeTries code d) (k : Nat) :
    jumpdestOkT code d T k = jumpdestOk code k := by
  by_cases hk : k < code.size
  · have hlist : k < code.data.toList.length := by
      simpa only [Array.length_toList, ByteArray.size_data, ByteArray.size_eq_length_toList] using
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
    simp only [jumpdestOkT, hk, decide_true, T.bytes_eq, Array.length_toList, ByteArray.size_data,
      getElem?_pos, Array.getElem_toList, hdata, Option.some_beq_some, hbeq, Bool.true_and,
      T.starts_eq, List.getD_eq_getElem?_getD, jumpdestOk, ↓reduceDIte, instStartAt,
      Bool.decide_and, Bool.decide_eq_true]
  · simp only [jumpdestOkT, hk, decide_false, Bool.false_and, jumpdestOk, ↓reduceDIte]

/-- `jumpsOkNode` with `jumpdestOk` replaced by `jumpdestOkT` (every other arm identical). -/
def jumpsOkNodeT (code : ByteArray) (d : Nat) (T : CodeTries code d) (es : List Entry) :
    SFunc → List AVal → Bool
  | .next n f, a =>
    match absNinst n a with
    | some a' => jumpsOkNodeT code d T es f a'
    | none => true
  | .last _, _ => true
  | .dest f, a => jumpsOkNodeT code d T es f a
  | .branch f g, a =>
    match a with
    | .const t :: v :: a' =>
      (v.jumps? == some true || jumpsOkNodeT code d T es f a') &&
        (v.jumps? == some false || (jumpdestOkT code d T t.toNat && jumpsOkNodeT code d T es g a'))
    | _ => false
  | .branchTo f k, a =>
    match a, es[k]? with
    | .const _ :: v :: a', some e =>
      jumpdestOkT code d T e.pc && (v.jumps? == some true || jumpsOkNodeT code d T es f a')
    | _, _ => false
  | .jump k, a =>
    match a, es[k]? with
    | .const _ :: _, some e => jumpdestOkT code d T e.pc
    | _, _ => false
  | .callNext k f, a =>
    match a, f, es[k]? with
    | .const _ :: a', .dest dd, some e =>
      jumpdestOkT code d T e.pc &&
        match e.frame.findIdx? (· == .ret) with
        | some i =>
          match a'[i]? with
          | some (.const r) =>
            jumpdestOkT code d T r.toNat &&
              jumpsOkNodeT code d T es dd
                (List.replicate e.rets .unk ++ a'.drop e.frame.length)
          | _ => false
        | none => true
    | _, _, _ => false
  | .ret, _ => true
  | .pcAt p f, a => jumpsOkNodeT code d T es f (.const (Nat.toB256 p) :: a)
  | .undefined, _ => true

theorem jumpsOkNodeT_eq {code : ByteArray} {d : Nat} (T : CodeTries code d) (es : List Entry)
    (f : SFunc) (a : List AVal) :
    jumpsOkNodeT code d T es f a = jumpsOkNode code es f a := by
  let Q : SFunc → Prop := fun f =>
    ∀ (a : List AVal),
      jumpsOkNodeT code d T es f a = jumpsOkNode code es f a
  let P : SFunc → Prop := fun f =>
    Q f ∧ match f with
    | .dest g => Q g
    | _ => True
  have hall : ∀ f : SFunc, P f := by
    intro f
    induction f with
    | next n f ih =>
      constructor
      · intro a
        cases h : absNinst n a <;>
          simp only [jumpsOkNodeT, h, jumpsOkNode, Q, ih.1]
      · simp only
    | last l =>
      constructor
      · intro a; rfl
      · simp only
    | dest f ih =>
      constructor
      · intro a
        simp only [jumpsOkNodeT, ih.1, jumpsOkNode, Q]
      · exact ih.1
    | branch f g ihf ihg =>
      constructor
      · intro a
        cases a with
        | nil => rfl
        | cons av a =>
          cases av <;> cases a <;>
            simp only [jumpsOkNodeT, jumpsOkNode, Q, ihf.1, jumpdestOkT_eq T, ihg.1]
      · simp only
    | branchTo f k ih =>
      constructor
      · intro a
        cases a with
        | nil => rfl
        | cons av a =>
          cases av <;> cases a <;> cases h : es[k]? <;>
            simp only [jumpsOkNodeT, jumpsOkNode, Q, h, jumpdestOkT_eq T, ih.1]
      · simp only
    | jump k =>
      constructor
      · intro a
        cases a with
        | nil => rfl
        | cons av a =>
          cases av <;> cases h : es[k]? <;>
            simp only [jumpsOkNodeT, h, jumpsOkNode, jumpdestOkT_eq T]
      · simp only
    | callNext k f ih =>
      constructor
      · intro a
        cases a with
        | nil => rfl
        | cons av a =>
          cases av <;> cases f <;> cases h : es[k]? <;>
            simp only [jumpsOkNodeT, jumpsOkNode, Q, List.cons.injEq, AVal.const.injEq, SFunc.dest.injEq, reduceCtorEq, imp_self, implies_true, h, Option.some.injEq, jumpdestOkT_eq T, ih.2] <;> rfl
      · simp only
    | ret =>
      constructor
      · intro a; rfl
      · simp only
    | pcAt p f ih =>
      constructor
      · intro a
        simp only [jumpsOkNodeT, ih.1, jumpsOkNode, Q]
      · simp only
    | undefined =>
      constructor
      · intro a; rfl
      · simp only
  exact (hall f).1 a

/-! ## The memory-tracking checkers, reading from tries -/

/-- `checkNodeM`, reading bytes from the trie `t` (arm by arm as `checkNodeT`). -/
def checkNodeMT (code : ByteArray) (d : Nat) (t : LTrie UInt8) (es : List Entry)
    (ms : List MemMap) (b : Bool) (m : Nat) : Nat → List AVal → MemMap → SFunc → Bool
  | pc, a, μ, .next n f =>
    bytesAtT d t pc (Ninst.toBytes n) && Ninst.pcFree n &&
      match absNinst n a with
      | some a' =>
        checkNodeMT code d t es ms b m (pc + n.size) (if b then memFold (memTop n a μ) a' else a')
          (if b then absMem n a μ else []) f
      | none => false
  | pc, _, _, .last l => LTrie.get? d t pc == some l.toUInt8
  | pc, a, μ, .dest f =>
    LTrie.get? d t pc == some (Jinst.toUInt8 .jumpdest) &&
      checkNodeMT code d t es ms b m (pc + 1) a μ f
  | pc, a, μ, .branch f g =>
    match a with
    | .const tg :: v :: a' =>
      LTrie.get? d t pc == some (Jinst.toUInt8 .jumpi) &&
        (v.jumps? == some true || checkNodeMT code d t es ms b m (pc + 1) a' μ f) &&
        (v.jumps? == some false || checkNodeMT code d t es ms b m tg.toNat a' μ g)
    | _ => false
  | pc, a, μ, .branchTo f k =>
    match a, es[k]? with
    | .const tg :: v :: a', some e =>
      LTrie.get? d t pc == some (Jinst.toUInt8 .jumpi) && e.pc == tg.toNat &&
        e.rets == m && gotoCompat a' e.frame && memCompat μ (ms.getD k []) &&
        (v.jumps? == some true || checkNodeMT code d t es ms b m (pc + 1) a' μ f)
    | _, _ => false
  | pc, a, μ, .jump k =>
    match a, es[k]? with
    | .const tg :: a', some e =>
      LTrie.get? d t pc == some (Jinst.toUInt8 .jump) && e.pc == tg.toNat &&
        e.rets == m && gotoCompat a' e.frame && memCompat μ (ms.getD k [])
    | _, _ => false
  | pc, a, _, .callNext k f =>
    match a, f, es[k]? with
    | .const tg :: a', .dest _, some e =>
      LTrie.get? d t pc == some (Jinst.toUInt8 .jump) && e.pc == tg.toNat &&
        decide (e.frame.length ≤ a'.length) && (ms.getD k []).isEmpty &&
        (match e.frame.findIdx? (· == .ret) with
         | some i =>
           match a'[i]? with
           | some (.const r) =>
             callCompat r a' e.frame &&
               checkNodeMT code d t es ms b m r.toNat
                 (List.replicate e.rets .unk ++ a'.drop e.frame.length) [] f
           | _ => false
         | none => callCompat 0 a' e.frame)
    | _, _, _ => false
  | pc, a, _, .ret =>
    match a with
    | .ret :: a' => LTrie.get? d t pc == some (Jinst.toUInt8 .jump) && a'.length == m
    | _ => false
  | pc, a, μ, .pcAt p f =>
    bytesAtT d t pc (Ninst.toBytes (.reg .pc)) && p == pc &&
      checkNodeMT code d t es ms b m (pc + 1) (.const (Nat.toB256 pc) :: a) μ f
  | pc, _, _, .undefined => (code.getInst pc).isNone

theorem checkNodeMT_eq {code : ByteArray} {d : Nat} (T : CodeTries code d) (es : List Entry)
    (ms : List MemMap) (b : Bool) (m pc : Nat) (a : List AVal) (μ : MemMap) (f : SFunc) :
    checkNodeMT code d T.bytes es ms b m pc a μ f = checkNodeM code es ms b m pc a μ f := by
  let Q : SFunc → Prop := fun f =>
    ∀ (pc : Nat) (a : List AVal) (μ : MemMap),
      checkNodeMT code d T.bytes es ms b m pc a μ f = checkNodeM code es ms b m pc a μ f
  let P : SFunc → Prop := fun f =>
    Q f ∧ match f with
    | .dest g => Q g
    | _ => True
  have hall : ∀ f : SFunc, P f := by
    intro f
    induction f with
    | next n f ih =>
      refine ⟨fun pc a μ => ?_, by simp only⟩
      cases h : absNinst n a <;>
        simp only [checkNodeMT, bytesAtT_eq T.bytes_eq, h, Bool.and_false, checkNodeM, Q, ih.1]
    | last l => exact ⟨fun pc a μ => by simp only [checkNodeMT, T.bytes_eq,
      Array.getElem?_toList, checkNodeM, byteAt],
        by simp only⟩
    | dest f ih =>
      exact ⟨fun pc a μ => by simp only [checkNodeMT, T.bytes_eq, Array.getElem?_toList, ih.1,
        checkNodeM, byteAt, Q], ih.1⟩
    | branch f g ihf ihg =>
      refine ⟨fun pc a μ => ?_, by simp only⟩
      rcases a with _ | ⟨_ | _ | _, _ | ⟨_, a⟩⟩ <;>
        simp only [checkNodeMT, checkNodeM, Q, T.bytes_eq, Array.getElem?_toList, ihf.1, ihg.1, byteAt]
    | branchTo f k ih =>
      refine ⟨fun pc a μ => ?_, by simp only⟩
      rcases a with _ | ⟨_ | _ | _, _ | ⟨_, a⟩⟩ <;> cases h : es[k]? <;>
        simp only [checkNodeMT, checkNodeM, Q, h, T.bytes_eq, Array.getElem?_toList, List.getD_eq_getElem?_getD, ih.1, byteAt]
    | jump k =>
      refine ⟨fun pc a μ => ?_, by simp only⟩
      rcases a with _ | ⟨_ | _ | _, a⟩ <;> cases h : es[k]? <;>
        simp only [checkNodeMT, checkNodeM, h, T.bytes_eq, Array.getElem?_toList, List.getD_eq_getElem?_getD, byteAt]
    | callNext k f ih =>
      refine ⟨fun pc a μ => ?_, by simp only⟩
      rcases a with _ | ⟨_ | _ | _, a⟩ <;> cases f <;> cases h : es[k]? <;>
        simp only [checkNodeMT, checkNodeM, Q, h, T.bytes_eq, Array.getElem?_toList, List.getD_eq_getElem?_getD, ih.2, byteAt] <;> rfl
    | ret =>
      exact ⟨fun pc a μ => by
        rcases a with _ | ⟨_ | _ | _, a⟩ <;> simp only [checkNodeMT, checkNodeM, T.bytes_eq, Array.getElem?_toList, byteAt],
        by simp only⟩
    | pcAt p f ih =>
      exact ⟨fun pc a μ => by
        simp only [checkNodeMT, bytesAtT_eq T.bytes_eq, ih.1, checkNodeM, Q], by simp only⟩
    | undefined => exact ⟨fun pc a μ => rfl, by simp only⟩
  exact (hall f).1 pc a μ

/-- `jumpsOkNodeM` with `jumpdestOk` replaced by `jumpdestOkT`. -/
def jumpsOkNodeMT (code : ByteArray) (d : Nat) (T : CodeTries code d) (es : List Entry)
    (b : Bool) : SFunc → List AVal → MemMap → Bool
  | .next n f, a, μ =>
    match absNinst n a with
    | some a' => jumpsOkNodeMT code d T es b f (if b then memFold (memTop n a μ) a' else a')
        (if b then absMem n a μ else [])
    | none => true
  | .last _, _, _ => true
  | .dest f, a, μ => jumpsOkNodeMT code d T es b f a μ
  | .branch f g, a, μ =>
    match a with
    | .const t :: v :: a' =>
      (v.jumps? == some true || jumpsOkNodeMT code d T es b f a' μ) &&
        (v.jumps? == some false ||
          (jumpdestOkT code d T t.toNat && jumpsOkNodeMT code d T es b g a' μ))
    | _ => false
  | .branchTo f k, a, μ =>
    match a, es[k]? with
    | .const _ :: v :: a', some e =>
      jumpdestOkT code d T e.pc && (v.jumps? == some true || jumpsOkNodeMT code d T es b f a' μ)
    | _, _ => false
  | .jump k, a, _ =>
    match a, es[k]? with
    | .const _ :: _, some e => jumpdestOkT code d T e.pc
    | _, _ => false
  | .callNext k f, a, _ =>
    match a, f, es[k]? with
    | .const _ :: a', .dest dd, some e =>
      jumpdestOkT code d T e.pc &&
        match e.frame.findIdx? (· == .ret) with
        | some i =>
          match a'[i]? with
          | some (.const r) =>
            jumpdestOkT code d T r.toNat &&
              jumpsOkNodeMT code d T es b dd
                (List.replicate e.rets .unk ++ a'.drop e.frame.length) []
          | _ => false
        | none => true
    | _, _, _ => false
  | .ret, _, _ => true
  | .pcAt p f, a, μ => jumpsOkNodeMT code d T es b f (.const (Nat.toB256 p) :: a) μ
  | .undefined, _, _ => true

theorem jumpsOkNodeMT_eq {code : ByteArray} {d : Nat} (T : CodeTries code d) (es : List Entry)
    (b : Bool) (f : SFunc) (a : List AVal) (μ : MemMap) :
    jumpsOkNodeMT code d T es b f a μ = jumpsOkNodeM code es b f a μ := by
  let Q : SFunc → Prop := fun f =>
    ∀ (a : List AVal) (μ : MemMap), jumpsOkNodeMT code d T es b f a μ = jumpsOkNodeM code es b f a μ
  let P : SFunc → Prop := fun f =>
    Q f ∧ match f with
    | .dest g => Q g
    | _ => True
  have hall : ∀ f : SFunc, P f := by
    intro f
    induction f with
    | next n f ih =>
      refine ⟨fun a μ => ?_, by simp only⟩
      cases h : absNinst n a <;> simp only [jumpsOkNodeMT, h, jumpsOkNodeM, Q, ih.1]
    | last l => exact ⟨fun a μ => rfl, by simp only⟩
    | dest f ih => exact ⟨fun a μ => by simp only [jumpsOkNodeMT, ih.1, jumpsOkNodeM, Q], ih.1⟩
    | branch f g ihf ihg =>
      refine ⟨fun a μ => ?_, by simp only⟩
      rcases a with _ | ⟨_ | _ | _, _ | ⟨_, a⟩⟩ <;>
        simp only [jumpsOkNodeMT, jumpsOkNodeM, Q, ihf.1, jumpdestOkT_eq T, ihg.1]
    | branchTo f k ih =>
      refine ⟨fun a μ => ?_, by simp only⟩
      rcases a with _ | ⟨_ | _ | _, _ | ⟨_, a⟩⟩ <;> cases h : es[k]? <;>
        simp only [jumpsOkNodeMT, jumpsOkNodeM, Q, h, jumpdestOkT_eq T, ih.1]
    | jump k =>
      refine ⟨fun a μ => ?_, by simp only⟩
      rcases a with _ | ⟨_ | _ | _, a⟩ <;> cases h : es[k]? <;>
        simp only [jumpsOkNodeMT, jumpsOkNodeM, h, jumpdestOkT_eq T]
    | callNext k f ih =>
      refine ⟨fun a μ => ?_, by simp only⟩
      rcases a with _ | ⟨_ | _ | _, a⟩ <;> cases f <;> cases h : es[k]? <;>
        simp only [jumpsOkNodeMT, jumpsOkNodeM, Q, List.cons.injEq, AVal.const.injEq, SFunc.dest.injEq, reduceCtorEq, imp_self, implies_true, h, Option.some.injEq, jumpdestOkT_eq T, ih.2] <;> rfl
    | ret => exact ⟨fun a μ => rfl, by simp only⟩
    | pcAt p f ih =>
      exact ⟨fun a μ => by simp only [jumpsOkNodeMT, ih.1, jumpsOkNodeM, Q], by simp only⟩
    | undefined => exact ⟨fun a μ => rfl, by simp only⟩
  exact (hall f).1 a μ

/-! ## Assembling a memory-tracking certificate from per-entry decisions -/

/-- One step of a chain proof of `Cert.checkEntriesM` over the tails of a long certificate. -/
theorem Cert.checkEntriesM_drop {code : ByteArray} {es : List Entry} {ms : List MemMap}
    {b : Bool} (c : Cert) (k : Nat) (hk : k < c.length)
    (h : checkNodeM code es ms b (c[k]'hk).1.rets (c[k]'hk).1.pc (c[k]'hk).1.frame
      (ms.getD k []) (c[k]'hk).2 = true)
    (hrest : Cert.checkEntriesM code es ms b (k + 1) (c.drop (k + 1)) = true) :
    Cert.checkEntriesM code es ms b k (c.drop k) = true := by
  rw [List.drop_eq_getElem_cons hk]
  simp only [Cert.checkEntriesM, Bool.and_eq_true]
  exact ⟨h, hrest⟩

/-- One step of a chain proof of `Cert.jumpsEntriesM`. -/
theorem Cert.jumpsEntriesM_drop {code : ByteArray} {es : List Entry} {ms : List MemMap}
    {b : Bool} (c : Cert) (k : Nat) (hk : k < c.length)
    (h : jumpsOkNodeM code es b (c[k]'hk).2 (c[k]'hk).1.frame (ms.getD k []) = true)
    (hrest : Cert.jumpsEntriesM code es ms b (k + 1) (c.drop (k + 1)) = true) :
    Cert.jumpsEntriesM code es ms b k (c.drop k) = true := by
  rw [List.drop_eq_getElem_cons hk]
  simp only [Cert.jumpsEntriesM, Bool.and_eq_true]
  exact ⟨h, hrest⟩

end Blanc.Lift
