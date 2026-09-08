import Blanc.Forward
import Mathlib.Tactic.IntervalCases

namespace Blanc

open Jaune

namespace CompiledShape

/-! Shared structural facts for inspecting compiled `Func` byte shapes. -/

def prefixByteSize : Line → Nat
  | [] => 0
  | inst :: rest => inst.size + prefixByteSize rest

theorem byteAt_prepend_eq_prefix
    (locations : List Nat) (n : Nat) (l : Line) (p0 p : Func)
    (i : Nat) (d : UInt8) (hi : i < prefixByteSize l) :
    Func.byteAtByShape locations n (l +++ p0).compileShape
        (l +++ p) i d =
      Func.byteAtByShape locations n (l +++ p0).compileShape
        (l +++ p0) i d := by
  induction l generalizing n i with
  | nil => simp [prefixByteSize] at hi
  | cons inst rest ih =>
      change
        Func.byteAtByShape locations n
            (.next inst.size (rest +++ p0).compileShape)
            (inst ::: (rest +++ p)) i d =
          Func.byteAtByShape locations n
            (.next inst.size (rest +++ p0).compileShape)
            (inst ::: (rest +++ p0)) i d
      by_cases hinst : i < inst.size
      · conv_lhs => rw [Func.byteAtByShape, if_pos hinst]
        conv_rhs => rw [Func.byteAtByShape, if_pos hinst]
      · conv_lhs => rw [Func.byteAtByShape, if_neg hinst]
        conv_rhs => rw [Func.byteAtByShape, if_neg hinst]
        apply ih
        simp only [prefixByteSize] at hi
        omega

theorem byteAt_prepend_to_tail
    (locations : List Nat) (n : Nat) (l : Line) (p0 p : Func)
    (i : Nat) (d : UInt8) (hlo : prefixByteSize l ≤ i) :
    Func.byteAtByShape locations n (l +++ p0).compileShape
        (l +++ p) i d =
      Func.byteAtByShape locations (n + prefixByteSize l) p0.compileShape
        p (i - prefixByteSize l) d := by
  induction l generalizing n i with
  | nil => simp [prefixByteSize, prepend]
  | cons inst rest ih =>
      have hinst : inst.size ≤ i := by
        simp only [prefixByteSize] at hlo
        omega
      change
        Func.byteAtByShape locations n
            (.next inst.size (rest +++ p0).compileShape)
            (inst ::: (rest +++ p)) i d = _
      conv_lhs => rw [Func.byteAtByShape, if_neg (Nat.not_lt_of_ge hinst)]
      rw [ih (n := n + inst.size) (i := i - inst.size) (by
        simp only [prefixByteSize] at hlo
        omega)]
      simp only [prefixByteSize, Nat.add_assoc, Nat.sub_sub]

/-- Once the byte index is past a reference instruction, continue in the
tail even when the executed instruction has a different value or width. The
caller remains responsible for relating the supplied shape to serialized
instruction bytes where that matters. -/
theorem byteAt_next_to_tail
    (locations : List Nat) (n : Nat) (inst0 inst : Ninst) (p0 p : Func)
    (i : Nat) (d : UInt8) (hlo : inst0.size ≤ i) :
    Func.byteAtByShape locations n (inst0 ::: p0).compileShape
        (inst ::: p) i d =
      Func.byteAtByShape locations (n + inst0.size) p0.compileShape
        p (i - inst0.size) d := by
  rw [Func.compileShape, Func.byteAtByShape,
    if_neg (Nat.not_lt_of_ge hlo)]

theorem byteAt_branch_eq_header
    (locations : List Nat) (n : Nat)
    (left0 right0 left right : Func) (i : Nat) (d : UInt8)
    (hi : i < 4) :
    Func.byteAtByShape locations n
        (.branch left0.compileShape right0.compileShape)
        (.branch left right) i d =
      Func.byteAtByShape locations n
        (.branch left0.compileShape right0.compileShape)
        (.branch left0 right0) i d := by
  conv_lhs => rw [Func.byteAtByShape, if_pos (by
    simpa only [List.length_cons, List.length_nil, Nat.reduceAdd] using hi)]
  conv_rhs => rw [Func.byteAtByShape, if_pos (by
    simpa only [List.length_cons, List.length_nil, Nat.reduceAdd] using hi)]
theorem byteAt_branch_to_left
    (locations : List Nat) (n : Nat)
    (left0 right0 left right : Func) (i : Nat) (d : UInt8)
    (hlo : 4 ≤ i) (hinside : i - 4 < left0.compileShape.byteSize) :
    Func.byteAtByShape locations n
        (.branch left0.compileShape right0.compileShape)
        (.branch left right) i d =
      Func.byteAtByShape locations (n + 4) left0.compileShape left
        (i - 4) d := by
  conv_lhs => rw [Func.byteAtByShape]
  conv_lhs => rw [if_neg (by
    simp only [List.length_cons, List.length_nil]
    omega)]
  dsimp only
  conv_lhs => rw [if_pos (by
    simpa only [List.length_cons, List.length_nil, Nat.reduceAdd] using
      hinside)]
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd]
lemma byteAt_branch_jumpdest
    (locations : List Nat) (n : Nat)
    (left0 right0 left right : Func) (d : UInt8) :
    Func.byteAtByShape locations n
        (.branch left0.compileShape right0.compileShape)
        (.branch left right) (4 + left0.compileShape.byteSize) d =
      Jinst.jumpdest.toUInt8 := by
  conv_lhs => rw [Func.byteAtByShape]
  conv_lhs => rw [if_neg (by
    simp only [List.length_cons, List.length_nil]
    omega)]
  dsimp only
  conv_lhs => rw [if_neg (by
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd]
    omega)]
  conv_lhs => rw [if_pos (by
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd]
    omega)]
  have hi0 :
      4 + left0.compileShape.byteSize - 4 -
        left0.compileShape.byteSize = 0 := by
    omega
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd]
  rw [hi0]
  rfl
theorem byteAt_branch_eq_before_right
    (locations : List Nat) (n : Nat)
    (left0 right0 right : Func) (i : Nat) (d : UInt8)
    (hi : i < 5 + left0.compileShape.byteSize) :
    Func.byteAtByShape locations n
        (.branch left0.compileShape right0.compileShape)
        (.branch left0 right) i d =
      Func.byteAtByShape locations n
        (.branch left0.compileShape right0.compileShape)
        (.branch left0 right0) i d := by
  by_cases hheader : i < 4
  · exact byteAt_branch_eq_header locations n left0 right0 left0 right
      i d hheader
  · by_cases hleft : i - 4 < left0.compileShape.byteSize
    · rw [byteAt_branch_to_left locations n left0 right0 left0 right i d
          (by omega) hleft,
        byteAt_branch_to_left locations n left0 right0 left0 right0 i d
          (by omega) hleft]
    · have hjump : i = 4 + left0.compileShape.byteSize := by omega
      subst i
      rw [byteAt_branch_jumpdest locations n left0 right0 left0 right,
        byteAt_branch_jumpdest locations n left0 right0 left0 right0]
theorem byteAt_branch_to_right
    (locations : List Nat) (n : Nat)
    (left0 right0 left right : Func) (i : Nat) (d : UInt8)
    (hlo : 5 + left0.compileShape.byteSize ≤ i) :
    Func.byteAtByShape locations n
        (.branch left0.compileShape right0.compileShape)
        (.branch left right) i d =
      Func.byteAtByShape locations
        (n + 5 + left0.compileShape.byteSize) right0.compileShape right
        (i - (5 + left0.compileShape.byteSize)) d := by
  conv_lhs => rw [Func.byteAtByShape]
  conv_lhs => rw [if_neg (by
    simp only [List.length_cons, List.length_nil]
    omega)]
  dsimp only
  conv_lhs => rw [if_neg (by
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd]
    omega)]
  conv_lhs => rw [if_neg (by
    simp only [List.length_cons, List.length_nil, Nat.reduceAdd]
    omega)]
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd]
  congr 1 <;> omega
theorem pushFullWord_opcode_eq
    (locations : List Nat) (n : Nat) (p0 p : Func) (w : B256) :
    Func.byteAtByShape locations n
        (Ninst.push (0 : B256).toBytes (by rw [B256.length_toBytes]) :::
          p0).compileShape
        (Ninst.push w.toBytes (by rw [B256.length_toBytes]) ::: p) 0 0 =
      Func.byteAtByShape locations n
        (Ninst.push (0 : B256).toBytes (by rw [B256.length_toBytes]) :::
          p0).compileShape
        (Ninst.push (0 : B256).toBytes (by rw [B256.length_toBytes]) :::
          p0) 0 0 := by
  simp [Func.byteAtByShape, Func.compileShape,
    Ninst.toBytes, Ninst.size, pushToB8L, pushToB8, B256.length_toBytes]
theorem byteAt_pushFullWord_data
    (locations : List Nat) (n : Nat) (p0 p : Func) (w : B256)
    (j : Nat) (hj : j < 32) :
    Func.byteAtByShape locations n
        (Ninst.push (0 : B256).toBytes (by rw [B256.length_toBytes]) :::
          p0).compileShape
        (Ninst.push w.toBytes (by rw [B256.length_toBytes]) ::: p)
        (j + 1) 0 =
      w.toBytes.getD j 0 := by
  rw [Func.compileShape, Func.byteAtByShape]
  rw [if_pos (by
    simp only [Ninst.size, B256.length_toBytes]
    omega)]
  rw [List.getD_takeD]
  rw [if_pos (by
    simp only [Ninst.size, B256.length_toBytes]
    omega)]
  simp only [Ninst.toBytes, pushToB8L, List.getD_cons_succ]
def dispatchNode (selector : B256) (offPath onPath : Func) : Func :=
  Ninst.dup 0 ::: Ninst.pushB256 selector ::: Ninst.gt :::
    (offPath <?> onPath)
lemma dispatchNodeByteAt_to_onPath
    (locations : List Nat) (n : Nat) (selector : B256)
    (off0 on0 off on : Func) (i : Nat) (d : UInt8)
    (hpush : (Ninst.pushB256 selector).size = 5)
    (hlo : 11 ≤ i)
    (hinside : i - 11 < on0.compileShape.byteSize) :
    Func.byteAtByShape locations n
        (dispatchNode selector off0 on0).compileShape
        (dispatchNode selector off on) i d =
      Func.byteAtByShape locations (n + 11) on0.compileShape on
        (i - 11) d := by
  have hdup : (Ninst.dup 0).size = 1 := by decide +kernel
  have hgt : Ninst.gt.size = 1 := by decide +kernel
  have hiEq : i - 1 - 5 - 1 - 4 = i - 11 := by omega
  change
    Func.byteAtByShape locations n
      (.next (Ninst.dup 0).size
        (.next (Ninst.pushB256 selector).size
          (.next Ninst.gt.size
            (.branch on0.compileShape off0.compileShape))))
      (Ninst.dup 0 ::: Ninst.pushB256 selector ::: Ninst.gt :::
        (off <?> on)) i d = _
  conv_lhs => rw [Func.byteAtByShape, if_neg (by omega)]
  conv_lhs => rw [Func.byteAtByShape, if_neg (by omega)]
  conv_lhs => rw [Func.byteAtByShape, if_neg (by omega)]
  conv_lhs => rw [Func.byteAtByShape]
  conv_lhs => rw [if_neg (by
    simp only [List.length_cons, List.length_nil]
    omega)]
  dsimp only
  conv_lhs => rw [if_pos (by
    simpa only [hdup, hpush, hgt, List.length_cons, List.length_nil,
      Nat.reduceAdd, hiEq] using hinside)]
  simp only [hdup, hpush, hgt, List.length_cons, List.length_nil,
    Nat.reduceAdd, hiEq]
lemma dispatchNodeByteAt_to_offPath
    (locations : List Nat) (n : Nat) (selector : B256)
    (off0 on0 off on : Func) (i : Nat) (d : UInt8)
    (hpush : (Ninst.pushB256 selector).size = 5)
    (hlo : 12 + on0.compileShape.byteSize ≤ i) :
    Func.byteAtByShape locations n
        (dispatchNode selector off0 on0).compileShape
        (dispatchNode selector off on) i d =
      Func.byteAtByShape locations
        (n + 12 + on0.compileShape.byteSize) off0.compileShape off
        (i - (12 + on0.compileShape.byteSize)) d := by
  have hdup : (Ninst.dup 0).size = 1 := by decide +kernel
  have hgt : Ninst.gt.size = 1 := by decide +kernel
  change
    Func.byteAtByShape locations n
      (.next (Ninst.dup 0).size
        (.next (Ninst.pushB256 selector).size
          (.next Ninst.gt.size
            (.branch on0.compileShape off0.compileShape))))
      (Ninst.dup 0 ::: Ninst.pushB256 selector ::: Ninst.gt :::
        (off <?> on)) i d = _
  conv_lhs => rw [Func.byteAtByShape, if_neg (by omega)]
  conv_lhs => rw [Func.byteAtByShape, if_neg (by omega)]
  conv_lhs => rw [Func.byteAtByShape, if_neg (by omega)]
  conv_lhs => rw [Func.byteAtByShape]
  conv_lhs => rw [if_neg (by
    simp only [List.length_cons, List.length_nil]
    omega)]
  dsimp only
  conv_lhs => rw [if_neg (by
    simp only [hdup, hpush, hgt, List.length_cons, List.length_nil,
      Nat.reduceAdd]
    omega)]
  conv_lhs => rw [if_neg (by
    simp only [hdup, hpush, hgt, List.length_cons, List.length_nil,
      Nat.reduceAdd]
    omega)]
  simp only [hdup, hpush, hgt, List.length_cons, List.length_nil,
    Nat.reduceAdd]
  congr 1 <;> omega
theorem dispatchNode_size (s : B256) (off on : Func)
    (hpush : (Ninst.pushB256 s).size = 5) :
    (dispatchNode s off on).compileShape.byteSize =
      12 + on.compileShape.byteSize + off.compileShape.byteSize := by
  have hpushBytes : (Ninst.toBytes (Ninst.pushB256 s)).length = 5 := by
    rw [← Ninst.size_eq_length_toBytes]
    exact hpush
  have hdup : (Ninst.toBytes (Ninst.dup 0)).length = 1 := rfl
  have hgt : (Ninst.toBytes Ninst.gt).length = 1 := rfl
  simp only [Func.CompileShape.byteSize_compileShape, dispatchNode, compsize,
    hpushBytes, hdup, hgt]
  omega
theorem dispatchNodeByteAt_eq_prefix
    (locations : List Nat) (n : Nat) (selector : B256)
    (off0 on0 off on : Func)
    (hpush : (Ninst.pushB256 selector).size = 5)
    (i : Nat) (hi : i < 11) :
    Func.byteAtByShape locations n
        (dispatchNode selector off0 on0).compileShape
        (dispatchNode selector off on) i 0 =
      Func.byteAtByShape locations n
        (dispatchNode selector off0 on0).compileShape
        (dispatchNode selector off0 on0) i 0 := by
  have hdup : (Ninst.dup 0).size = 1 := by decide +kernel
  have hgt : Ninst.gt.size = 1 := by decide +kernel
  interval_cases i <;>
    simp [dispatchNode, Func.byteAtByShape, Func.compileShape,
      hdup, hgt, hpush]
lemma dispatchNodeByteAt_jumpdest
    (locations : List Nat) (n : Nat) (selector : B256)
    (off0 on0 off on : Func)
    (hpush : (Ninst.pushB256 selector).size = 5) (d : UInt8) :
    Func.byteAtByShape locations n
        (dispatchNode selector off0 on0).compileShape
        (dispatchNode selector off on) (11 + on0.compileShape.byteSize) d =
      Jinst.jumpdest.toUInt8 := by
  have hdup : (Ninst.dup 0).size = 1 := by decide +kernel
  have hgt : Ninst.gt.size = 1 := by decide +kernel
  change
    Func.byteAtByShape locations n
      (.next (Ninst.dup 0).size
        (.next (Ninst.pushB256 selector).size
          (.next Ninst.gt.size
            (.branch on0.compileShape off0.compileShape))))
      (Ninst.dup 0 ::: Ninst.pushB256 selector ::: Ninst.gt :::
        (off <?> on)) (11 + on0.compileShape.byteSize) d = _
  conv_lhs => rw [Func.byteAtByShape, if_neg (by
    simp only [hdup]
    omega)]
  conv_lhs => rw [Func.byteAtByShape, if_neg (by
    simp only [hdup, hpush]
    omega)]
  conv_lhs => rw [Func.byteAtByShape, if_neg (by
    simp only [hdup, hpush, hgt]
    omega)]
  conv_lhs => rw [Func.byteAtByShape]
  conv_lhs => rw [if_neg (by
    simp only [hdup, hpush, hgt, List.length_cons, List.length_nil]
    omega)]
  dsimp only
  conv_lhs => rw [if_neg (by
    simp only [hdup, hpush, hgt, List.length_cons, List.length_nil,
      Nat.reduceAdd]
    omega)]
  conv_lhs => rw [if_pos (by
    simp only [hdup, hpush, hgt, List.length_cons, List.length_nil,
      Nat.reduceAdd]
    omega)]
  have hi0 :
      11 + on0.compileShape.byteSize - 1 - 5 - 1 - 4 -
        on0.compileShape.byteSize = 0 := by
    omega
  simp only [hdup, hpush, hgt, List.length_cons, List.length_nil,
    Nat.reduceAdd]
  rw [hi0]
  rfl
theorem dispatchNodeByteAt_eq_jumpdest
    (locations : List Nat) (n : Nat) (selector : B256)
    (off0 on0 off on : Func)
    (hpush : (Ninst.pushB256 selector).size = 5) :
    Func.byteAtByShape locations n
        (dispatchNode selector off0 on0).compileShape
        (dispatchNode selector off on) (11 + on0.compileShape.byteSize) 0 =
      Func.byteAtByShape locations n
        (dispatchNode selector off0 on0).compileShape
        (dispatchNode selector off0 on0)
        (11 + on0.compileShape.byteSize) 0 := by
  rw [dispatchNodeByteAt_jumpdest locations n selector off0 on0 off on hpush,
    dispatchNodeByteAt_jumpdest locations n selector off0 on0 off0 on0 hpush]

end CompiledShape
end Blanc
