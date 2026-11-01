import Blanc.Lift.CheckFast

/-!
# Range-batched certificate checking

A generated `Check` module used to state one `checkNodeM`/`jumpsOkNodeM` theorem per certificate
entry, each over `cert[i]'(by decide +kernel)`, and then assemble `Cert.checkM`/`Cert.jumpsOkM`
with one chain theorem per entry.  Here one kernel decision covers a contiguous range of entries:
`Cert.rangeOk` fuses the node check and (with `j`) the jump check of every entry of a tail, and
`Cert.rangeOkT` computes the same through the code tries (`Cert.rangeOkT_eq`).  A range is stated
over `(c.drop k).take n`, so neither the elaborator nor a chain step ever indexes into the
certificate; `Cert.rangeOk_drop_take` chains consecutive ranges and `Cert.checkM_of_rangeOk`,
`Cert.jumpsOkM_of_rangeOk`, `Cert.check_of_rangeOk` and `Cert.jumpsOk_of_rangeOk` assemble the
unchanged checkers.  A non-memory certificate is checked with no maps and tracking off
(`checkNode_eq_checkNodeM`, `jumpsOkNode_eq_jumpsOkNodeM`).

The kernel work per entry is the per-entry decision's; what goes is the per-entry statement, its
index proofs and its chain step.  The generator (`scripts/lift/lift.py`, `--check-ranges`) bounds
each range by summed tree nodes, so the memory of one declaration stays bounded.
-/

namespace Blanc.Lift

open Jaune

/-- The node check, and with `j` the jump check, of every entry of the tail `c` whose first entry
is the certificate's `k`-th (its memory map is `ms.getD k []`). -/
def Cert.rangeOk (code : ByteArray) (es : List Entry) (ms : List MemMap) (b j : Bool) :
    Nat → Cert → Bool
  | _, [] => true
  | k, (e, f) :: c =>
    checkNodeM code es ms b e.rets e.pc e.frame (ms.getD k []) f &&
      (!j || jumpsOkNodeM code es b f e.frame (ms.getD k [])) &&
      Cert.rangeOk code es ms b j (k + 1) c

/-- `Cert.rangeOk` reading the code through its tries: the form a range is decided in. -/
def Cert.rangeOkT (code : ByteArray) (d : Nat) (T : CodeTries code d) (es : List Entry)
    (ms : List MemMap) (b j : Bool) : Nat → Cert → Bool
  | _, [] => true
  | k, (e, f) :: c =>
    checkNodeMT code d T.bytes es ms b e.rets e.pc e.frame (ms.getD k []) f &&
      (!j || jumpsOkNodeMT code d T es b f e.frame (ms.getD k [])) &&
      Cert.rangeOkT code d T es ms b j (k + 1) c

theorem Cert.rangeOkT_eq {code : ByteArray} {d : Nat} (T : CodeTries code d) (es : List Entry)
    (ms : List MemMap) (b j : Bool) (k : Nat) (c : Cert) :
    Cert.rangeOkT code d T es ms b j k c = Cert.rangeOk code es ms b j k c := by
  induction c generalizing k with
  | nil => rfl
  | cons p c ih =>
    obtain ⟨e, f⟩ := p
    simp only [Cert.rangeOkT, Cert.rangeOk, checkNodeMT_eq, jumpsOkNodeMT_eq, ih]

theorem Cert.rangeOk_append (code : ByteArray) (es : List Entry) (ms : List MemMap) (b j : Bool)
    (k : Nat) (c₁ c₂ : Cert) :
    Cert.rangeOk code es ms b j k (c₁ ++ c₂) =
      (Cert.rangeOk code es ms b j k c₁ && Cert.rangeOk code es ms b j (k + c₁.length) c₂) := by
  induction c₁ generalizing k with
  | nil => simp only [List.nil_append, Cert.rangeOk, List.length_nil, Nat.add_zero, Bool.true_and]
  | cons p c ih =>
    obtain ⟨e, f⟩ := p
    simp only [List.cons_append, Cert.rangeOk, ih, List.length_cons, Bool.and_assoc,
      Nat.add_assoc, Nat.add_comm 1]

/-- One link of a range chain: the range `[k, k + n)` and the tail from `k + n` give the tail
from `k`.  A range past the end is shorter; the tail after it is then empty. -/
theorem Cert.rangeOk_drop_take {code : ByteArray} {es : List Entry} {ms : List MemMap}
    {b j : Bool} (c : Cert) (k n : Nat)
    (h : Cert.rangeOk code es ms b j k ((c.drop k).take n) = true)
    (hrest : Cert.rangeOk code es ms b j (k + n) (c.drop (k + n)) = true) :
    Cert.rangeOk code es ms b j k (c.drop k) = true := by
  rw [← List.take_append_drop n (c.drop k), Cert.rangeOk_append, h, Bool.true_and,
    List.drop_drop]
  by_cases hn : n ≤ (c.drop k).length
  · rwa [List.length_take, Nat.min_eq_left hn]
  · have hnil : c.drop (k + n) = [] :=
      List.drop_eq_nil_of_le (by simp only [List.length_drop] at hn; omega)
    rw [hnil]
    rfl

/-- The chain's end: past the last entry nothing is left to check. -/
theorem Cert.rangeOk_drop_of_le {code : ByteArray} {es : List Entry} {ms : List MemMap}
    {b j : Bool} (c : Cert) (k : Nat) (hk : c.length ≤ k) :
    Cert.rangeOk code es ms b j k (c.drop k) = true := by
  rw [List.drop_eq_nil_of_le hk]
  rfl

theorem Cert.rangeOk_eq (code : ByteArray) (es : List Entry) (ms : List MemMap) (b j : Bool)
    (k : Nat) (c : Cert) :
    Cert.rangeOk code es ms b j k c =
      (Cert.checkEntriesM code es ms b k c && (!j || Cert.jumpsEntriesM code es ms b k c)) := by
  induction c generalizing k with
  | nil => cases j <;> rfl
  | cons p c ih =>
    obtain ⟨e, f⟩ := p
    cases j <;>
      simp only [Cert.rangeOk, Cert.checkEntriesM, Cert.jumpsEntriesM, ih, Bool.not_true,
        Bool.not_false, Bool.true_or, Bool.false_or, Bool.and_true, Bool.and_assoc,
        Bool.and_left_comm]

/-- Assemble the memory-tracking checker from its startup conditions and a range chain. -/
theorem Cert.checkM_of_rangeOk {code : ByteArray} {c : Cert} {ms : List MemMap} {b j : Bool}
    (hstart : (match c with
      | (e, _) :: _ => e.pc == 0 && e.frame == []
      | [] => false) = true)
    (hm : (ms.getD 0 []).isEmpty = true)
    (h : Cert.rangeOk code c.entries ms b j 0 (c.drop 0) = true) :
    Cert.checkM code c ms b = true := by
  rw [List.drop_zero, Cert.rangeOk_eq, Bool.and_eq_true] at h
  unfold Cert.checkM
  rw [Bool.and_eq_true, Bool.and_eq_true]
  exact ⟨⟨hstart, hm⟩, h.1⟩

/-- Assemble the memory-tracking jump checker from a range chain run with jumps on. -/
theorem Cert.jumpsOkM_of_rangeOk {code : ByteArray} {c : Cert} {ms : List MemMap} {b : Bool}
    (h : Cert.rangeOk code c.entries ms b true 0 (c.drop 0) = true) :
    Cert.jumpsOkM code c ms b = true := by
  rw [List.drop_zero, Cert.rangeOk_eq, Bool.and_eq_true, Bool.not_true, Bool.false_or] at h
  exact h.2

/-- A tail check with no maps and tracking off is the plain checker's tail. -/
theorem Cert.checkEntriesM_nil_false (code : ByteArray) (es : List Entry) (k : Nat) (c : Cert) :
    Cert.checkEntriesM code es [] false k c =
      c.all fun (e, f) => checkNode code es e.rets e.pc e.frame f := by
  induction c generalizing k with
  | nil => rfl
  | cons p c ih =>
    obtain ⟨e, f⟩ := p
    simp only [Cert.checkEntriesM, ih, List.all_cons, checkNode_eq_checkNodeM, List.getD_nil]

/-- A jump tail check with no maps and tracking off is the plain jump checker's tail. -/
theorem Cert.jumpsEntriesM_nil_false (code : ByteArray) (es : List Entry) (k : Nat) (c : Cert) :
    Cert.jumpsEntriesM code es [] false k c =
      c.all fun (e, f) => jumpsOkNode code es f e.frame := by
  induction c generalizing k with
  | nil => rfl
  | cons p c ih =>
    obtain ⟨e, f⟩ := p
    simp only [Cert.jumpsEntriesM, ih, List.all_cons, jumpsOkNode_eq_jumpsOkNodeM, List.getD_nil]

/-- Assemble the plain checker from its startup condition and a range chain run with no maps
and tracking off. -/
theorem Cert.check_of_rangeOk {code : ByteArray} {c : Cert} {j : Bool}
    (hstart : (match c with
      | (e, _) :: _ => e.pc == 0 && e.frame == []
      | [] => false) = true)
    (h : Cert.rangeOk code c.entries [] false j 0 (c.drop 0) = true) :
    Cert.check code c = true := by
  rw [List.drop_zero, Cert.rangeOk_eq, Bool.and_eq_true, Cert.checkEntriesM_nil_false] at h
  unfold Cert.check
  rw [Bool.and_eq_true]
  exact ⟨hstart, h.1⟩

/-- Assemble the plain jump checker from a range chain run with jumps on. -/
theorem Cert.jumpsOk_of_rangeOk {code : ByteArray} {c : Cert}
    (h : Cert.rangeOk code c.entries [] false true 0 (c.drop 0) = true) :
    Cert.jumpsOk code c = true := by
  rw [List.drop_zero, Cert.rangeOk_eq, Bool.and_eq_true, Bool.not_true, Bool.false_or,
    Cert.jumpsEntriesM_nil_false] at h
  exact h.2

/-- The node check of the `i`-th entry of a checked range, for a consumer that names one entry. -/
theorem Cert.checkNodeM_of_rangeOk {code : ByteArray} {es : List Entry} {ms : List MemMap}
    {b j : Bool} (c : Cert) (k n i : Nat)
    (h : Cert.rangeOk code es ms b j k ((c.drop k).take n) = true)
    (hi : i < c.length) (hk : k ≤ i) (hn : i < k + n) :
    checkNodeM code es ms b (c[i]'hi).1.rets (c[i]'hi).1.pc (c[i]'hi).1.frame (ms.getD i [])
      (c[i]'hi).2 = true := by
  have key : ∀ (k : Nat) (l : Cert) (t : Nat) (ht : t < l.length),
      Cert.rangeOk code es ms b j k l = true →
        checkNodeM code es ms b (l[t]'ht).1.rets (l[t]'ht).1.pc (l[t]'ht).1.frame
          (ms.getD (k + t) []) (l[t]'ht).2 = true := by
    intro k l
    induction l generalizing k with
    | nil => intro t ht; exact absurd ht (Nat.not_lt_zero t)
    | cons p l ih =>
      obtain ⟨e, f⟩ := p
      intro t ht hl
      simp only [Cert.rangeOk, Bool.and_eq_true] at hl
      cases t with
      | zero => exact hl.1.1
      | succ t =>
        have := ih (k + 1) t (by simp only [List.length_cons] at ht; omega) hl.2
        rwa [Nat.add_assoc, Nat.add_comm 1 t] at this
  have hlen : i - k < ((c.drop k).take n).length := by
    simp only [List.length_take, List.length_drop]; omega
  have := key k _ (i - k) hlen h
  simp only [List.getElem_take, List.getElem_drop, Nat.add_sub_cancel' hk] at this
  exact this

end Blanc.Lift
