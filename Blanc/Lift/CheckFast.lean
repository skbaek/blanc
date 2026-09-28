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
    | nil => simp [LTrie.ofList, LTrie.get?]
    | cons x xs =>
      have hxs : xs.length = 0 := by simpa using hl
      have : xs = [] := List.eq_nil_of_length_eq_zero hxs
      subst xs
      cases i <;> simp [LTrie.ofList, LTrie.get?]
  | succ d ih =>
    simp only [LTrie.ofList, LTrie.get?]
    by_cases hi : i < 2 ^ d
    · rw [if_pos hi]
      rw [ih (l := l.take (2 ^ d)) (i := i)]
      · simp [hi]
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
          | zero => intro xs j _; simp
          | succ n ih =>
            intro xs j hj
            cases xs with
            | nil => simp
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
    | nil => simp
    | cons x xs => simpa using ih xs

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
    | nil => simp [h]
    | cons c cs =>
      have hnext : code.data.toList.drop (pc + 1) = cs := by
        rw [show pc + 1 = pc + 1 by rfl, ← List.drop_drop, h]
        rfl
      have hbeq : (c == b) = decide (c = b) := by
        rfl
      simp [h, hnext, hbeq]

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
          simp [Q, checkNodeT, checkNode, byteAt, bytesAtT_eq T.bytes_eq, ih.1, h]
      · simp [P]
    | last l =>
      constructor
      · intro pc a
        simp [Q, checkNodeT, checkNode, byteAt, T.bytes_eq]
      · simp [P]
    | dest f ih =>
      constructor
      · intro pc a
        simp [Q, checkNodeT, checkNode, byteAt, T.bytes_eq, ih.1]
      · exact ih.1
    | branch f g ihf ihg =>
      constructor
      · intro pc a
        cases a with
        | nil => rfl
        | cons av a =>
          cases av <;> cases a <;>
            simp [Q, checkNodeT, checkNode, byteAt, T.bytes_eq, ihf.1, ihg.1]
      · simp [P]
    | branchTo f k ih =>
      constructor
      · intro pc a
        cases a with
        | nil => rfl
        | cons av a =>
          cases av <;> cases a <;> cases h : es[k]? <;>
            simp [Q, checkNodeT, checkNode, byteAt, T.bytes_eq, ih.1, h]
      · simp [P]
    | jump k =>
      constructor
      · intro pc a
        cases a with
        | nil => rfl
        | cons av a =>
          cases av <;> cases h : es[k]? <;>
            simp [Q, checkNodeT, checkNode, byteAt, T.bytes_eq, h]
      · simp [P]
    | callNext k f ih =>
      constructor
      · intro pc a
        cases a with
        | nil => rfl
        | cons av a =>
          cases av <;> cases f <;> cases h : es[k]? <;>
            simp [Q, checkNodeT, checkNode, byteAt, T.bytes_eq, ih.1, ih.2, h, *] <;> rfl
      · simp [P]
    | ret =>
      constructor
      · intro pc a
        cases a with
        | nil => rfl
        | cons av a =>
          cases av <;> simp [Q, checkNodeT, checkNode, byteAt, T.bytes_eq]
      · simp [P]
    | pcAt p f ih =>
      constructor
      · intro pc a
        simp [Q, checkNodeT, checkNode, bytesAtT_eq T.bytes_eq, ih.1]
      · simp [P]
    | undefined =>
      constructor
      · intro pc a; rfl
      · simp [P]
  exact (hall f).1 pc a

/-- `jumpdestOk`, reading the code byte and the instruction-start flag from the tries. -/
def jumpdestOkT (code : ByteArray) (d : Nat) (T : CodeTries code d) (k : Nat) : Bool :=
  decide (k < code.size) && LTrie.get? d T.bytes k == some (Jinst.toUInt8 .jumpdest) &&
    (LTrie.get? d T.starts k).getD false

theorem jumpdestOkT_eq {code : ByteArray} {d : Nat} (T : CodeTries code d) (k : Nat) :
    jumpdestOkT code d T k = jumpdestOk code k := by
  by_cases hk : k < code.size
  · have hlist : k < code.data.toList.length := by
      simpa [ByteArray.size_eq_length_toList] using hk
    have hget : code.data.toList[k]? = some code[k] := by
      exact List.getElem?_eq_getElem hlist
    have hdata : code.data[k] = code[k] := by rfl
    have ha : code.data[k]? = some code[k] := by
      rw [← hdata]
      simp [hk]
    have hbyte : (code.data[k]? == some (Jinst.toUInt8 .jumpdest)) =
        decide (code[k] = Jinst.toUInt8 .jumpdest) := by
      rw [ha]
      rfl
    have hbeq : (code[k] == Jinst.toUInt8 .jumpdest) =
        decide (code[k] = Jinst.toUInt8 .jumpdest) := by rfl
    simp [jumpdestOkT, jumpdestOk, instStartAt, hk, T.bytes_eq, T.starts_eq,
      hget, hlist, hdata, ha, hbyte, hbeq]
  · simp [jumpdestOkT, jumpdestOk, hk]

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
          simp [Q, jumpsOkNodeT, jumpsOkNode, ih.1, h]
      · simp [P]
    | last l =>
      constructor
      · intro a; rfl
      · simp [P]
    | dest f ih =>
      constructor
      · intro a
        simp [Q, jumpsOkNodeT, jumpsOkNode, ih.1]
      · exact ih.1
    | branch f g ihf ihg =>
      constructor
      · intro a
        cases a with
        | nil => rfl
        | cons av a =>
          cases av <;> cases a <;>
            simp [Q, jumpsOkNodeT, jumpsOkNode, jumpdestOkT_eq T,
              ihf.1, ihg.1]
      · simp [P]
    | branchTo f k ih =>
      constructor
      · intro a
        cases a with
        | nil => rfl
        | cons av a =>
          cases av <;> cases a <;> cases h : es[k]? <;>
            simp [Q, jumpsOkNodeT, jumpsOkNode, jumpdestOkT_eq T, ih.1, h]
      · simp [P]
    | jump k =>
      constructor
      · intro a
        cases a with
        | nil => rfl
        | cons av a =>
          cases av <;> cases h : es[k]? <;>
            simp [Q, jumpsOkNodeT, jumpsOkNode, jumpdestOkT_eq T, h]
      · simp [P]
    | callNext k f ih =>
      constructor
      · intro a
        cases a with
        | nil => rfl
        | cons av a =>
          cases av <;> cases f <;> cases h : es[k]? <;>
            simp [Q, jumpsOkNodeT, jumpsOkNode, jumpdestOkT_eq T,
              ih.1, ih.2, h, *] <;> rfl
      · simp [P]
    | ret =>
      constructor
      · intro a; rfl
      · simp [P]
    | pcAt p f ih =>
      constructor
      · intro a
        simp [Q, jumpsOkNodeT, jumpsOkNode, ih.1]
      · simp [P]
    | undefined =>
      constructor
      · intro a; rfl
      · simp [P]
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
      refine ⟨fun pc a μ => ?_, by simp [P]⟩
      cases h : absNinst n a <;>
        simp [Q, checkNodeMT, checkNodeM, byteAt, bytesAtT_eq T.bytes_eq, ih.1, h]
    | last l => exact ⟨fun pc a μ => by simp [Q, checkNodeMT, checkNodeM, byteAt, T.bytes_eq],
        by simp [P]⟩
    | dest f ih =>
      exact ⟨fun pc a μ => by simp [Q, checkNodeMT, checkNodeM, byteAt, T.bytes_eq, ih.1], ih.1⟩
    | branch f g ihf ihg =>
      refine ⟨fun pc a μ => ?_, by simp [P]⟩
      rcases a with _ | ⟨_ | _ | _, _ | ⟨_, a⟩⟩ <;>
        simp [Q, checkNodeMT, checkNodeM, byteAt, T.bytes_eq, ihf.1, ihg.1]
    | branchTo f k ih =>
      refine ⟨fun pc a μ => ?_, by simp [P]⟩
      rcases a with _ | ⟨_ | _ | _, _ | ⟨_, a⟩⟩ <;> cases h : es[k]? <;>
        simp [Q, checkNodeMT, checkNodeM, byteAt, T.bytes_eq, ih.1, h]
    | jump k =>
      refine ⟨fun pc a μ => ?_, by simp [P]⟩
      rcases a with _ | ⟨_ | _ | _, a⟩ <;> cases h : es[k]? <;>
        simp [Q, checkNodeMT, checkNodeM, byteAt, T.bytes_eq, h]
    | callNext k f ih =>
      refine ⟨fun pc a μ => ?_, by simp [P]⟩
      rcases a with _ | ⟨_ | _ | _, a⟩ <;> cases f <;> cases h : es[k]? <;>
        simp [Q, checkNodeMT, checkNodeM, byteAt, T.bytes_eq, ih.1, ih.2, h, *] <;> rfl
    | ret =>
      exact ⟨fun pc a μ => by
        rcases a with _ | ⟨_ | _ | _, a⟩ <;> simp [Q, checkNodeMT, checkNodeM, byteAt, T.bytes_eq],
        by simp [P]⟩
    | pcAt p f ih =>
      exact ⟨fun pc a μ => by
        simp [Q, checkNodeMT, checkNodeM, bytesAtT_eq T.bytes_eq, ih.1], by simp [P]⟩
    | undefined => exact ⟨fun pc a μ => rfl, by simp [P]⟩
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
      refine ⟨fun a μ => ?_, by simp [P]⟩
      cases h : absNinst n a <;> simp [Q, jumpsOkNodeMT, jumpsOkNodeM, ih.1, h]
    | last l => exact ⟨fun a μ => rfl, by simp [P]⟩
    | dest f ih => exact ⟨fun a μ => by simp [Q, jumpsOkNodeMT, jumpsOkNodeM, ih.1], ih.1⟩
    | branch f g ihf ihg =>
      refine ⟨fun a μ => ?_, by simp [P]⟩
      rcases a with _ | ⟨_ | _ | _, _ | ⟨_, a⟩⟩ <;>
        simp [Q, jumpsOkNodeMT, jumpsOkNodeM, jumpdestOkT_eq T, ihf.1, ihg.1]
    | branchTo f k ih =>
      refine ⟨fun a μ => ?_, by simp [P]⟩
      rcases a with _ | ⟨_ | _ | _, _ | ⟨_, a⟩⟩ <;> cases h : es[k]? <;>
        simp [Q, jumpsOkNodeMT, jumpsOkNodeM, jumpdestOkT_eq T, ih.1, h]
    | jump k =>
      refine ⟨fun a μ => ?_, by simp [P]⟩
      rcases a with _ | ⟨_ | _ | _, a⟩ <;> cases h : es[k]? <;>
        simp [Q, jumpsOkNodeMT, jumpsOkNodeM, jumpdestOkT_eq T, h]
    | callNext k f ih =>
      refine ⟨fun a μ => ?_, by simp [P]⟩
      rcases a with _ | ⟨_ | _ | _, a⟩ <;> cases f <;> cases h : es[k]? <;>
        simp [Q, jumpsOkNodeMT, jumpsOkNodeM, jumpdestOkT_eq T, ih.1, ih.2, h, *] <;> rfl
    | ret => exact ⟨fun a μ => rfl, by simp [P]⟩
    | pcAt p f ih =>
      exact ⟨fun a μ => by simp [Q, jumpsOkNodeMT, jumpsOkNodeM, ih.1], by simp [P]⟩
    | undefined => exact ⟨fun a μ => rfl, by simp [P]⟩
  exact (hall f).1 a μ

/-! ## Splitting one node check at an unknown-condition branch -/

/-- `checkNode` at `.branch` with an unknown condition is the byte check and both
sub-tree checks. Each sub-tree can then be its own `decide +kernel` theorem and
the entry composed without re-deciding the whole tree. -/
theorem checkNode_branch_unk {code : ByteArray} (es : List Entry) (m pc : Nat)
    (tgt : B256) (v : AVal) (a' : List AVal) (f g : SFunc) (hv : v.jumps? = none) :
    checkNode code es m pc (.const tgt :: v :: a') (.branch f g) =
      (byteAt code pc == some (Jinst.toUInt8 .jumpi) &&
        checkNode code es m (pc + 1) a' f && checkNode code es m tgt.toNat a' g) := by
  simp [checkNode, hv]

/-- Trie-reading copy of `checkNode_branch_unk`. -/
theorem checkNodeT_branch_unk {code : ByteArray} {d : Nat} (t : LTrie UInt8)
    (es : List Entry) (m pc : Nat) (tgt : B256) (v : AVal) (a' : List AVal)
    (f g : SFunc) (hv : v.jumps? = none) :
    checkNodeT code d t es m pc (.const tgt :: v :: a') (.branch f g) =
      (LTrie.get? d t pc == some (Jinst.toUInt8 .jumpi) &&
        checkNodeT code d t es m (pc + 1) a' f &&
        checkNodeT code d t es m tgt.toNat a' g) := by
  simp [checkNodeT, hv]

/-- `jumpsOkNode` at `.branch` with an unknown condition needs both sub-trees
(and the taken target to be a jump destination). -/
theorem jumpsOkNode_branch_unk {code : ByteArray} (es : List Entry)
    (tgt : B256) (v : AVal) (a' : List AVal) (f g : SFunc) (hv : v.jumps? = none) :
    jumpsOkNode code es (.branch f g) (.const tgt :: v :: a') =
      (jumpsOkNode code es f a' && (jumpdestOk code tgt.toNat && jumpsOkNode code es g a')) := by
  simp [jumpsOkNode, hv]

/-- Trie-reading copy of `jumpsOkNode_branch_unk`. -/
theorem jumpsOkNodeT_branch_unk {code : ByteArray} {d : Nat} (T : CodeTries code d)
    (es : List Entry) (tgt : B256) (v : AVal) (a' : List AVal) (f g : SFunc)
    (hv : v.jumps? = none) :
    jumpsOkNodeT code d T es (.branch f g) (.const tgt :: v :: a') =
      (jumpsOkNodeT code d T es f a' &&
        (jumpdestOkT code d T tgt.toNat && jumpsOkNodeT code d T es g a')) := by
  simp [jumpsOkNodeT, hv]

/-- Trie-reading memory-tracking copy of the branch-split equation. -/
theorem checkNodeMT_branch_unk {code : ByteArray} {d : Nat} (t : LTrie UInt8)
    (es : List Entry) (ms : List MemMap) (b : Bool) (m pc : Nat)
    (tgt : B256) (v : AVal) (a' : List AVal) (μ : MemMap) (f g : SFunc)
    (hv : v.jumps? = none) :
    checkNodeMT code d t es ms b m pc (.const tgt :: v :: a') μ (.branch f g) =
      (LTrie.get? d t pc == some (Jinst.toUInt8 .jumpi) &&
        checkNodeMT code d t es ms b m (pc + 1) a' μ f &&
        checkNodeMT code d t es ms b m tgt.toNat a' μ g) := by
  simp [checkNodeMT, hv]

/-- Trie-reading memory-tracking copy of the jumps branch-split equation. -/
theorem jumpsOkNodeMT_branch_unk {code : ByteArray} {d : Nat} (T : CodeTries code d)
    (es : List Entry) (b : Bool)
    (tgt : B256) (v : AVal) (a' : List AVal) (μ : MemMap) (f g : SFunc)
    (hv : v.jumps? = none) :
    jumpsOkNodeMT code d T es b (.branch f g) (.const tgt :: v :: a') μ =
      (jumpsOkNodeMT code d T es b f a' μ &&
        (jumpdestOkT code d T tgt.toNat && jumpsOkNodeMT code d T es b g a' μ)) := by
  simp [jumpsOkNodeMT, hv]

/-! ## Assembling a memory-tracking certificate from per-entry decisions -/

/-- The entries of a certificate with their indices, from `k`. -/
def Cert.indexedFrom : Nat → Cert → List (Nat × (Entry × SFunc))
  | _, [] => []
  | k, p :: c => (k, p) :: Cert.indexedFrom (k + 1) c

def Cert.indexed (c : Cert) : List (Nat × (Entry × SFunc)) := Cert.indexedFrom 0 c

theorem Cert.checkEntriesM_of_indexedFrom {code : ByteArray} {es : List Entry}
    {ms : List MemMap} {b : Bool} : ∀ (c : Cert) (k : Nat),
    (∀ j p, (j, p) ∈ Cert.indexedFrom k c →
      checkNodeM code es ms b p.1.rets p.1.pc p.1.frame (ms.getD j []) p.2 = true) →
    Cert.checkEntriesM code es ms b k c = true
  | [], _, _ => rfl
  | (e, f) :: c, k, h => by
    simp only [Cert.checkEntriesM, Bool.and_eq_true]
    exact ⟨h k (e, f) (by simp [Cert.indexedFrom]),
      Cert.checkEntriesM_of_indexedFrom c (k + 1)
        (fun j p hp => h j p (by simp [Cert.indexedFrom, hp]))⟩

theorem Cert.jumpsEntriesM_of_indexedFrom {code : ByteArray} {es : List Entry}
    {ms : List MemMap} {b : Bool} : ∀ (c : Cert) (k : Nat),
    (∀ j p, (j, p) ∈ Cert.indexedFrom k c →
      jumpsOkNodeM code es b p.2 p.1.frame (ms.getD j []) = true) →
    Cert.jumpsEntriesM code es ms b k c = true
  | [], _, _ => rfl
  | (e, f) :: c, k, h => by
    simp only [Cert.jumpsEntriesM, Bool.and_eq_true]
    exact ⟨h k (e, f) (by simp [Cert.indexedFrom]),
      Cert.jumpsEntriesM_of_indexedFrom c (k + 1)
        (fun j p hp => h j p (by simp [Cert.indexedFrom, hp]))⟩

theorem Cert.jumpsOkM_of_indexed {code : ByteArray} {c : Cert} {ms : List MemMap} {b : Bool}
    (hall : ∀ k p, (k, p) ∈ Cert.indexed c →
      jumpsOkNodeM code c.entries b p.2 p.1.frame (ms.getD k []) = true) :
    Cert.jumpsOkM code c ms b = true :=
  Cert.jumpsEntriesM_of_indexedFrom c 0 hall

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
