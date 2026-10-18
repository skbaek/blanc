import Blanc.Lift.Usdc.Model

/-!
# Pure laws of one USDC step

The per-call facts the token interface's signature laws (`BookLawsS`) read off `Ledger.step`, so
that `usdcBook_lawsS` is assembly over the decoder:

* `step_good`: a good ledger stays good (balances below `2 ^ 255`, initialized, version 3);
* `step_holder_only`: only the holder, a spender it approved, or a call it signed lowers its
  balance;
* `step_allow_owner`: only the owner, or a call it signed, raises its allowances;
* `step_transfer_debit`, `step_transfer_exact`, `step_transfer_allow`, `step_view`: the holder-safe
  calls (`balanceOf` decodes to `view`, `transfer` to `transfer`).
-/

namespace Blanc.Lift.Usdc

open Jaune Blanc

namespace Ledger

/-! ## The guarded writes -/

theorem setBalance_eq_some {l l' : Ledger} {a : Adr} {x : Nat} (h : l.setBalance a x = some l') :
    x < 2 ^ 255 ∧ l.frozen a = false ∧ l' = l.setBal a x := by
  unfold setBalance at h
  split_ifs at h with c
  cases h
  simp only [not_or, not_le, Bool.not_eq_true] at c
  exact ⟨c.1, c.2, rfl⟩

theorem approveOf_eq_some {l l' : Ledger} {o s : Adr} {x : Nat}
    (h : l.approveOf o s x = some l') : l' = l.setAllow o s x := by
  unfold approveOf at h
  split_ifs at h
  cases h
  rfl

/-- The balances after a committed move. -/
def moveBal (b : Adr → Nat) (src dst : Adr) (v : Nat) : Adr → Nat :=
  Function.update (Function.update b src (b src - v)) dst
    (Function.update b src (b src - v) dst + v)

theorem move_eq_some {l l' : Ledger} {src dst : Adr} {v : Nat} (h : l.move src dst v = some l') :
    v ≤ l.bal src ∧ l.bal src - v < 2 ^ 255 ∧ moveBal l.bal src dst v dst < 2 ^ 255 ∧
      l' = { l with bal := moveBal l.bal src dst v } := by
  unfold move at h
  split_ifs at h with c
  simp only [not_or, not_lt] at c
  obtain ⟨l₁, h₁, h₂⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨cap₁, -, rfl⟩ := setBalance_eq_some h₁
  obtain ⟨cap₂, -, rfl⟩ := setBalance_eq_some h₂
  refine ⟨c.2.2, cap₁, ?_, rfl⟩
  unfold moveBal
  rw [Function.update_self]
  exact cap₂

/-! ## Balances under a move -/

theorem moveBal_lt {b : Adr → Nat} {src dst h : Adr} {v : Nat} (le : v ≤ b src)
    (lt : moveBal b src dst v h < b h) : h = src ∧ dst ≠ src ∧ 0 < v := by
  unfold moveBal at lt
  by_cases hd : h = dst
  · subst hd
    rw [Function.update_self] at lt
    by_cases hs : h = src
    · subst hs
      rw [Function.update_self] at lt
      omega
    · rw [Function.update_of_ne hs] at lt
      omega
  · rw [Function.update_of_ne hd] at lt
    by_cases hs : h = src
    · subst hs
      rw [Function.update_self] at lt
      exact ⟨rfl, Ne.symm hd, by omega⟩
    · rw [Function.update_of_ne hs] at lt
      omega

theorem moveBal_src_le {b : Adr → Nat} {src dst : Adr} {v : Nat} (le : v ≤ b src) :
    b src ≤ moveBal b src dst v src + v := by
  unfold moveBal
  by_cases hd : src = dst
  · subst hd
    rw [Function.update_self, Function.update_self]
    omega
  · rw [Function.update_of_ne hd, Function.update_self]
    omega

theorem moveBal_src_exact {b : Adr → Nat} {src dst : Adr} {v : Nat} (le : v ≤ b src)
    (ne : dst ≠ src) : moveBal b src dst v src + v = b src := by
  unfold moveBal
  rw [Function.update_of_ne (Ne.symm ne), Function.update_self]
  omega

theorem moveBal_cap {b : Adr → Nat} {src dst : Adr} {v : Nat} (cap : ∀ a, b a < 2 ^ 255)
    (dstCap : moveBal b src dst v dst < 2 ^ 255) : ∀ a, moveBal b src dst v a < 2 ^ 255 := by
  intro a
  by_cases hd : a = dst
  · subst hd; exact dstCap
  · unfold moveBal
    rw [Function.update_of_ne hd]
    by_cases hs : a = src
    · subst hs
      rw [Function.update_self]
      have := cap a
      omega
    · rw [Function.update_of_ne hs]
      exact cap a

/-! ## A good ledger stays good -/

theorem update_cap {b : Adr → Nat} {k : Adr} {x : Nat} (cap : ∀ a, b a < 2 ^ 255)
    (hx : x < 2 ^ 255) : ∀ a, Function.update b k x a < 2 ^ 255 := by
  intro a
  by_cases ha : a = k
  · subst ha; rw [Function.update_self]; exact hx
  · rw [Function.update_of_ne ha]; exact cap a

theorem good_of {l l' : Ledger} (good : l.Good) (bal : ∀ a, l'.bal a < 2 ^ 255)
    (init : l'.initialized = l.initialized) (ver : l'.version = l.version) : l'.Good :=
  ⟨bal, init.trans good.initialized, ver.trans good.version⟩

/-- **A good ledger stays good** along any committed call. -/
theorem step_good {l l' : Ledger} {self caller : Adr} {c : Call} (good : l.Good)
    (h : l.step self caller c = some l') : l'.Good := by
  have v3 := good.version
  cases c <;> simp only [step] at h <;> (try split_ifs at h) <;> (try cases h) <;>
    (try exact good_of good good.bal_lt rfl rfl) <;> (try (exfalso; omega))
  all_goals first
    | (obtain ⟨-, -, cap, rfl⟩ := move_eq_some h
       exact good_of good (moveBal_cap good.bal_lt cap) rfl rfl)
    | (obtain ⟨l₁, h₁, rfl⟩ := Option.map_eq_some_iff.mp h
       obtain ⟨-, -, cap, rfl⟩ := move_eq_some h₁
       exact good_of good (moveBal_cap good.bal_lt cap) rfl rfl)
    | (obtain rfl := approveOf_eq_some h
       exact good_of good good.bal_lt rfl rfl)
    | (obtain ⟨l₁, h₁, rfl⟩ := Option.map_eq_some_iff.mp h
       obtain ⟨cap, -, rfl⟩ := setBalance_eq_some h₁
       exact good_of good (update_cap good.bal_lt cap) rfl rfl)
    | (obtain ⟨cap, -, rfl⟩ := setBalance_eq_some h
       exact good_of good (update_cap good.bal_lt cap) rfl rfl)

/-! ## Who lowers a balance -/

theorem update_lt {b : Adr → Nat} {k a : Adr} {x : Nat} (lt : Function.update b k x a < b a) :
    a = k := by
  by_contra ha
  rw [Function.update_of_ne ha] at lt
  exact lt_irrefl _ lt

theorem update_add_not_lt {b : Adr → Nat} {k a : Adr} {v : Nat} :
    ¬ Function.update b k (b k + v) a < b a := by
  intro lt
  have ha := update_lt lt
  subst ha
  rw [Function.update_self] at lt
  omega

/-- **Only the holder, a spender it approved, or a call it signed lowers its balance.** -/
theorem step_holder_only {l l' : Ledger} {self caller : Adr} {c : Call} {hd : Adr}
    (good : l.Good) (h : l.step self caller c = some l') (lt : l'.bal hd < l.bal hd) :
    caller = hd ∨ 0 < l.allow hd caller ∨ c.signer = some hd := by
  have v3 := good.version
  cases c <;> simp only [step] at h <;> (try split_ifs at h with g) <;> (try cases h) <;>
    (try exact absurd lt (lt_irrefl _)) <;> (try (exfalso; omega))
  all_goals first
    | (obtain ⟨le, -, -, rfl⟩ := move_eq_some h
       exact Or.inl (moveBal_lt le lt).1.symm)
    | (obtain ⟨l₁, h₁, rfl⟩ := Option.map_eq_some_iff.mp h
       obtain ⟨le, -, -, rfl⟩ := move_eq_some h₁
       obtain ⟨rfl, -, pos⟩ := moveBal_lt le lt
       simp only [not_or, not_lt] at g
       exact Or.inr (Or.inl (lt_of_lt_of_le pos g.2.2.2.2)))
    | (obtain rfl := approveOf_eq_some h
       exact absurd lt (lt_irrefl _))
    | (obtain ⟨le, -, -, rfl⟩ := move_eq_some h
       obtain ⟨rfl, -, -⟩ := moveBal_lt le lt
       exact Or.inr (Or.inr rfl))
    | (obtain ⟨l₁, h₁, rfl⟩ := Option.map_eq_some_iff.mp h
       obtain ⟨-, -, rfl⟩ := setBalance_eq_some h₁
       exact absurd lt update_add_not_lt)
    | (obtain ⟨-, -, rfl⟩ := setBalance_eq_some h
       exact Or.inl (update_lt lt).symm)

/-! ## Who raises an allowance -/

theorem setAllow_lt {l : Ledger} {o s p q : Adr} {x : Nat}
    (lt : l.allow p q < (l.setAllow o s x).allow p q) : p = o := by
  by_contra hp
  simp only [setAllow, hp, false_and, ↓reduceIte, lt_irrefl] at lt

theorem setAllow_sub_not_lt {l : Ledger} {o s p q : Adr} {v : Nat} :
    ¬ l.allow p q < (l.setAllow o s (l.allow o s - v)).allow p q := by
  intro lt
  simp only [setAllow] at lt
  split_ifs at lt with hpq
  · obtain ⟨rfl, rfl⟩ := hpq
    omega
  · exact lt_irrefl _ lt

/-- **Only the owner, or a call it signed, raises its allowances.** -/
theorem step_allow_owner {l l' : Ledger} {self caller : Adr} {c : Call} {hd g : Adr}
    (good : l.Good) (h : l.step self caller c = some l') (lt : l.allow hd g < l'.allow hd g) :
    caller = hd ∨ c.signer = some hd := by
  have v3 := good.version
  cases c <;> simp only [step] at h <;> (try split_ifs at h) <;> (try cases h) <;>
    (try exact absurd lt (lt_irrefl _)) <;> (try (exfalso; omega))
  all_goals first
    | (obtain ⟨-, -, -, rfl⟩ := move_eq_some h
       exact absurd lt (lt_irrefl _))
    | (obtain ⟨l₁, h₁, rfl⟩ := Option.map_eq_some_iff.mp h
       obtain ⟨-, -, -, rfl⟩ := move_eq_some h₁
       exact absurd lt setAllow_sub_not_lt)
    | (obtain rfl := approveOf_eq_some h
       first
         | exact Or.inl (setAllow_lt lt).symm
         | exact Or.inr (congrArg some (setAllow_lt lt).symm))
    | (obtain ⟨l₁, h₁, rfl⟩ := Option.map_eq_some_iff.mp h
       obtain ⟨-, -, rfl⟩ := setBalance_eq_some h₁
       exact absurd lt (lt_irrefl _))
    | (obtain ⟨-, -, rfl⟩ := setBalance_eq_some h
       exact absurd lt (lt_irrefl _))

/-! ## The holder-safe calls -/

/-- A good ledger's balances are words. -/
theorem Good.bal_lt_word {l : Ledger} (good : l.Good) (a : Adr) : l.bal a < 2 ^ 256 :=
  lt_trans (good.bal_lt a) (by decide)

/-- A view changes nothing. -/
theorem step_view {l l' : Ledger} {self caller : Adr} (h : l.step self caller .view = some l') :
    l' = l := by
  simp only [step, Option.some.injEq] at h
  exact h.symm

theorem step_transfer_move {l l' : Ledger} {self caller dst : Adr} {v : Nat}
    (h : l.step self caller (.transfer dst v) = some l') : l.move caller dst v = some l' := by
  simp only [step] at h
  split_ifs at h
  exact h

/-- A committed `transfer` debits its caller by at most its amount. -/
theorem step_transfer_debit {l l' : Ledger} {self caller dst : Adr} {v : Nat}
    (h : l.step self caller (.transfer dst v) = some l') : l.bal caller ≤ l'.bal caller + v := by
  obtain ⟨le, -, -, rfl⟩ := move_eq_some (step_transfer_move h)
  exact moveBal_src_le le

/-- A committed `transfer` to someone else debits its caller exactly. -/
theorem step_transfer_exact {l l' : Ledger} {self caller dst : Adr} {v : Nat}
    (h : l.step self caller (.transfer dst v) = some l') (ne : dst ≠ caller) :
    l'.bal caller + v = l.bal caller := by
  obtain ⟨le, -, -, rfl⟩ := move_eq_some (step_transfer_move h)
  exact moveBal_src_exact le ne

/-- A committed `transfer` touches no allowance. -/
theorem step_transfer_allow {l l' : Ledger} {self caller dst : Adr} {v : Nat}
    (h : l.step self caller (.transfer dst v) = some l') : l'.allow = l.allow := by
  obtain ⟨-, -, -, rfl⟩ := move_eq_some (step_transfer_move h)
  rfl

end Ledger

end Blanc.Lift.Usdc
