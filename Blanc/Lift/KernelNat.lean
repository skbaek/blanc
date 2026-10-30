/-!
# Natural-number equality for kernel decisions over free variables

The kernel evaluates `Nat` arithmetic on literals with GMP only when the whole term is closed.
A kernel decision stated over free variables (a free world, free bookkeeping, a free original
state) can carry a value that is closed after evaluation inside a term that still mentions those
variables; `decide (a = b)` on such a term then runs `Nat.beq` one successor at a time, which
costs millions of steps for a gas value. `natEqW` matches each side against `n + 1` first, so the
kernel evaluates both to literals before the closed `Nat.beq` that remains. Nothing here is
contract-specific.
-/

namespace Blanc.KernelNat

/-- `decide (a = b)`, evaluated by the kernel on literals (`natEqW_eq`). -/
def natEqW (a b : Nat) : Bool :=
  match a, b with
  | 0, 0 => true
  | 0, _ + 1 => false
  | _ + 1, 0 => false
  | n + 1, m + 1 => Nat.beq n m

theorem natEqW_eq (a b : Nat) : natEqW a b = decide (a = b) := by
  cases a with
  | zero => cases b <;> rfl
  | succ n =>
    cases b with
    | zero => rfl
    | succ m =>
      show Nat.beq n m = decide (n + 1 = m + 1)
      by_cases h : n = m
      · subst h
        rw [Nat.beq_refl, decide_eq_true rfl]
      · have hb : Nat.beq n m = false := by
          cases hc : Nat.beq n m
          · rfl
          · exact absurd (Nat.eq_of_beq_eq_true hc) h
        rw [hb, decide_eq_false (fun h' => h (Nat.succ.inj h'))]

/-- A kernel decision of `natEqW a b` gives `decide (a = b) = true`. -/
theorem decide_eq_of_natEqW {a b : Nat} (h : natEqW a b = true) : decide (a = b) = true :=
  (natEqW_eq a b) ▸ h

/-- A kernel decision of `natEqW a b` gives `a = b`. -/
theorem eq_of_natEqW {a b : Nat} (h : natEqW a b = true) : a = b :=
  of_decide_eq_true (decide_eq_of_natEqW h)

end Blanc.KernelNat
