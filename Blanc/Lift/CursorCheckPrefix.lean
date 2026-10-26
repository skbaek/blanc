import Blanc.Lift.Cursor
import Blanc.BytePattern

/-! Read a literal linear prefix from the same checked certificate cursor. -/

namespace Blanc.Lift

open Jaune

/-- Consecutive checked byte slices join without changing their starting pc. -/
theorem bytesAt_append {code : ByteArray} {pc : Nat} {xs ys : Bytes}
    (left : bytesAt code pc xs = true)
    (right : bytesAt code (pc + xs.length) ys = true) :
    bytesAt code pc (xs ++ ys) = true := by
  unfold bytesAt at *
  apply decide_eq_true
  have hleft := of_decide_eq_true left
  have hright := of_decide_eq_true right
  rw [List.length_append, List.take_add, hleft, List.drop_drop, hright]

/-- A successful check contains every byte of its literal next-node prefix. -/
theorem checkNode_nexts {code : ByteArray} {es : List Entry} {m pc : Nat}
    {a : List AVal} (ns : List Ninst) (tail : SFunc)
    (checked : checkNode code es m pc a (ns.foldr SFunc.next tail) = true) :
    bytesAt code pc (ns.flatMap Ninst.toBytes) = true ∧
      ∃ a', checkNode code es m (pc + (ns.map Ninst.size).sum) a' tail = true := by
  induction ns generalizing pc a with
  | nil =>
    exact ⟨rfl, a, by simpa only [List.map_nil, List.sum_nil, Nat.add_zero, List.foldr] using checked⟩
  | cons n ns ih =>
    change checkNode code es m pc a (.next n (ns.foldr SFunc.next tail)) = true at checked
    simp only [checkNode, Bool.and_eq_true] at checked
    obtain ⟨⟨bytes, _⟩, checked⟩ := checked
    cases transfer : absNinst n a with
    | none => simp only [transfer, Bool.false_eq_true] at checked
    | some a' =>
      obtain ⟨later, finalA, finalCheck⟩ := ih (pc := pc + n.size) (a := a')
        (by simpa only [transfer] using checked)
      refine ⟨?_, finalA, ?_⟩
      · change bytesAt code pc (Ninst.toBytes n ++ ns.flatMap Ninst.toBytes) = true
        exact bytesAt_append bytes (by simpa only [Ninst.size_eq_length_toBytes] using later)
      · simpa only [List.map_cons, List.sum_cons, Nat.add_assoc] using finalCheck

theorem checkNode_bytesAt_prefix {code : ByteArray} {es : List Entry} {m pc : Nat}
    {a : List AVal} (ns : List Ninst) (tail : SFunc)
    (checked : checkNode code es m pc a (ns.foldr SFunc.next tail) = true) :
    bytesAt code pc (ns.flatMap Ninst.toBytes) = true :=
  (checkNode_nexts ns tail checked).1

/-- The literal prefix is read from this cursor's existing final check. -/
theorem CursorOK.bytesAt_of_prefix {code : ByteArray} {c : Cert}
    {F : Exec.Deriv} {κ : Cursor} (ok : CursorOK code c F κ)
    (ns : List Ninst) (tail : SFunc) (tree : κ.f = ns.foldr SFunc.next tail) :
    bytesAt code F.pc (ns.flatMap Ninst.toBytes) = true := by
  rw [ok.pc_eq]
  apply checkNode_bytesAt_prefix ns tail
  simpa only [tree] using ok.check

/-- A checked byte prefix and exact singleton scan identify its start. -/
theorem bytesAt_eq_of_prefix_singleton {code : ByteArray} {pc only : Nat}
    {pattern suffix : Bytes} (bytes : bytesAt code pc (pattern ++ suffix) = true)
    (nonempty : pattern ≠ []) (single : BytePattern.occurrences pattern code.toList = [only]) :
    pc = only := by
  have matched := of_decide_eq_true bytes
  have shorter := congrArg (List.take pattern.length) matched
  have bound : pattern.length ≤ (pattern ++ suffix).length := by
    simp only [List.length_append]; omega
  simp only [List.take_take, Nat.min_eq_left bound, List.take_append_length] at shorter
  apply BytePattern.eq_of_singleton nonempty single
  rw [ByteArray.toList_eq_toList_data]
  exact shorter

/-- A unique byte prefix identifies this same cursor's pc, with no pc bound premise. -/
theorem CursorOK.pc_eq_of_prefix_singleton {code : ByteArray} {c : Cert}
    {F : Exec.Deriv} {κ : Cursor} (ok : CursorOK code c F κ)
    (ns : List Ninst) (tail : SFunc) (tree : κ.f = ns.foldr SFunc.next tail)
    {pattern suffix : Bytes} {only : Nat}
    (hprefix : ns.flatMap Ninst.toBytes = pattern ++ suffix)
    (nonempty : pattern ≠ [])
    (single : BytePattern.occurrences pattern code.toList = [only]) :
    F.pc = only := by
  have bytes := ok.bytesAt_of_prefix ns tail tree
  rw [hprefix] at bytes
  exact bytesAt_eq_of_prefix_singleton bytes nonempty single

/-- Read the anchor after a literal prefix from this same check, without advancing execution. -/
theorem CursorOK.pc_add_eq_of_prefix_singleton {code : ByteArray} {c : Cert}
    {F : Exec.Deriv} {κ : Cursor} (ok : CursorOK code c F κ)
    (lead anchor : List Ninst) (tail : SFunc)
    (tree : κ.f = lead.foldr SFunc.next (anchor.foldr SFunc.next tail))
    {pattern suffix : Bytes} {only : Nat}
    (hprefix : anchor.flatMap Ninst.toBytes = pattern ++ suffix)
    (nonempty : pattern ≠ [])
    (single : BytePattern.occurrences pattern code.toList = [only]) :
    F.pc + (lead.map Ninst.size).sum = only := by
  have checked := ok.check
  rw [tree] at checked
  obtain ⟨_, a', later⟩ := checkNode_nexts lead (anchor.foldr SFunc.next tail) checked
  have bytes := checkNode_bytesAt_prefix anchor tail later
  rw [hprefix] at bytes
  have fixed := bytesAt_eq_of_prefix_singleton bytes nonempty single
  simpa only [ok.pc_eq] using fixed

end Blanc.Lift
