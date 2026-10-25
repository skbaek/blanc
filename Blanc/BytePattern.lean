import Blanc.Basic

/-!
Exact byte-pattern occurrences. The scan visits every byte offset, including
bytes inside instruction immediates; it makes no parsing or execution claim.
-/

namespace Blanc.BytePattern

/-- Scan successive suffixes, carrying their absolute starting offset. -/
def scan (pattern : List UInt8) : List UInt8 → Nat → List Nat
  | [], _ => []
  | byte :: rest, offset =>
    if (byte :: rest).take pattern.length = pattern then
      offset :: scan pattern rest (offset + 1)
    else scan pattern rest (offset + 1)

/-- All matching byte offsets, in increasing order. Empty patterns yield no offsets. -/
def occurrences (pattern code : List UInt8) : List Nat :=
  if pattern = [] then [] else scan pattern code 0

theorem mem_scan_iff {pattern code : List UInt8} {offset pc : Nat} :
    pc ∈ scan pattern code offset ↔
      ∃ k, pc = offset + k ∧ k < code.length ∧
        (code.drop k).take pattern.length = pattern := by
  induction code generalizing offset with
  | nil => simp only [scan, List.not_mem_nil, List.length_nil, Nat.not_lt_zero,
      false_and, and_false, exists_false]
  | cons byte rest ih =>
    rw [scan]
    split
    · rename_i matched
      rw [List.mem_cons, ih]
      constructor
      · intro member
        rcases member with equal | ⟨k, equal, bound, hprefix⟩
        · exact ⟨0, by omega, by simp only [List.length_cons]; omega,
            by simpa only [List.drop_zero] using matched⟩
        · exact ⟨k + 1, by omega, by simp only [List.length_cons]; omega,
            by simpa only [List.drop_succ_cons] using hprefix⟩
      · rintro ⟨k, equal, bound, hprefix⟩
        cases k with
        | zero => exact Or.inl (by omega)
        | succ k =>
          exact Or.inr ⟨k, by omega, by simp only [List.length_cons] at bound; omega,
            by simpa only [List.drop_succ_cons] using hprefix⟩
    · rename_i unmatched
      rw [ih]
      constructor
      · rintro ⟨k, equal, bound, hprefix⟩
        exact ⟨k + 1, by omega, by simp only [List.length_cons]; omega,
          by simpa only [List.drop_succ_cons] using hprefix⟩
      · rintro ⟨k, equal, bound, hprefix⟩
        cases k with
        | zero => exact False.elim (unmatched (by simpa only [List.drop_zero] using hprefix))
        | succ k =>
          exact ⟨k, by omega, by simp only [List.length_cons] at bound; omega,
            by simpa only [List.drop_succ_cons] using hprefix⟩

/-- A nonempty matching slice fits inside the code, even for an arbitrary natural offset. -/
theorem bounds_of_match {pattern code : List UInt8} {pc : Nat}
    (nonempty : pattern ≠ [])
    (matched : (code.drop pc).take pattern.length = pattern) :
    pc < code.length ∧ pc + pattern.length ≤ code.length := by
  have positive := List.length_pos_iff.mpr nonempty
  have lengths := congrArg List.length matched
  simp only [List.length_take, List.length_drop] at lengths
  omega

/-- Exact occurrence membership, with no caller-supplied bound on the offset. -/
theorem mem_occurrences_iff {pattern code : List UInt8} {pc : Nat}
    (nonempty : pattern ≠ []) :
    pc ∈ occurrences pattern code ↔
      (code.drop pc).take pattern.length = pattern := by
  rw [occurrences, ite_eq_right nonempty, mem_scan_iff]
  simp only [Nat.zero_add]
  constructor
  · rintro ⟨k, equal, _, matched⟩
    rw [equal]
    exact matched
  · intro matched
    exact ⟨pc, rfl, (bounds_of_match nonempty matched).1, matched⟩

theorem scan_increasing (pattern code : List UInt8) (offset : Nat) :
    (scan pattern code offset).Pairwise (· < ·) := by
  induction code generalizing offset with
  | nil => exact List.Pairwise.nil
  | cons byte rest ih =>
    rw [scan]
    split
    · apply List.pairwise_cons.mpr
      refine ⟨?_, ih (offset + 1)⟩
      intro pc member
      obtain ⟨k, equal, _, _⟩ := mem_scan_iff.mp member
      omega
    · exact ih (offset + 1)

/-- Each offset is visited once, in strictly increasing order. -/
theorem occurrences_increasing (pattern code : List UInt8) :
    (occurrences pattern code).Pairwise (· < ·) := by
  unfold occurrences
  split
  · exact List.Pairwise.nil
  · exact scan_increasing pattern code 0

/-- A singleton scan identifies the unique matching offset, including its existence. -/
theorem match_iff_eq_of_singleton {pattern code : List UInt8} {only pc : Nat}
    (nonempty : pattern ≠ []) (single : occurrences pattern code = [only]) :
    (code.drop pc).take pattern.length = pattern ↔ pc = only := by
  rw [← mem_occurrences_iff nonempty, single, List.mem_singleton]

theorem eq_of_singleton {pattern code : List UInt8} {only pc : Nat}
    (nonempty : pattern ≠ []) (single : occurrences pattern code = [only])
    (matched : (code.drop pc).take pattern.length = pattern) : pc = only :=
  (match_iff_eq_of_singleton nonempty single).mp matched

end Blanc.BytePattern
