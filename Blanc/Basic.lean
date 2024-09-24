-- Basic.lean : generically useful definitions not specific to Blanc

import Mathlib.Data.Nat.Defs
import Mathlib.Util.Notation3



-- Boolean lemmas --

instance : @Zero Bool := ⟨false⟩
instance : @One Bool := ⟨true⟩

def Bool.toChar : Bool → Char
  | 0 => '0'
  | 1 => '1'

lemma Bool.zero_toNat : (0 : Bool).toNat = 0 := rfl
lemma Bool.one_toNat : (1 : Bool).toNat = 1 := rfl

lemma false_toNat : (false : Bool).toNat = 0 := rfl
lemma true_toNat : (true : Bool).toNat = 1 := rfl

lemma true_eq_one : true = 1 := rfl
lemma false_eq_zero : false = 0 := rfl

lemma Bool.zero_or_one (x : Bool) : x = 0 ∨ x = 1 := by
  cases x
  · left; rfl
  · right; rfl

lemma not_true_lt_false : ¬ true < false := by simp [LT.lt]
lemma not_true_lt {b} : ¬ true < b := by simp [LT.lt]
lemma not_true_le_false : ¬ true ≤ false := by simp [LE.le]
lemma false_lt_true : false < true := by simp [LT.lt]
lemma false_le {b : Bool} : false ≤ b := by cases b <;> simp [LE.le]
lemma Bool.le_one {b : Bool} : b ≤ 1 := by cases b <;> simp [LE.le]; rfl
lemma Bool.zero : 0 = false := rfl
lemma Bool.one : 1 = true := rfl

def Split {α} [HAppend α α α] : α → α → α → Prop
  | a, ab, b => ab = a ++ b

notation x " <++ " xy " ++> " y => Split x xy y

def Pref {ξ} [HAppend ξ ξ ξ] (x : ξ) (xy : ξ) : Prop :=
  ∃ y : ξ, x <++ xy ++> y

infix:45 " <<+ " => Pref

lemma pref_append {ξ} [HAppend ξ ξ ξ] (xs ys : ξ) : xs <<+ xs ++ ys := ⟨ys, rfl⟩

def Frel {A B} (a : A) (r : B → B → Prop) (f g : A → B) : Prop :=
  ∀ a', (a = a' → r (f a') (g a')) ∧ (a ≠ a' → f a' = g a')

def Overwrite {A B} (x : A) (y : B) : (A → B) → (A → B) → Prop := Frel x (λ _ y' => y = y')

lemma List.of_cons_pref_of_cons_pref {ξ} {x y : ξ} {xs ys zs} :
    (x :: xs <<+ zs) → (y :: ys <<+ zs) →
      x = y ∧ ∃ zs', (xs <<+ zs') ∧ (ys <<+ zs') := by
  intros h0 h1
  rcases h0 with ⟨sfx, h0⟩
  rcases h1 with ⟨sfx', h1⟩
  rcases List.cons_eq_cons.mp (Eq.trans h0.symm h1) with ⟨h_head, h_tail⟩
  refine ⟨h_head, xs ++ sfx, pref_append _ _, sfx', h_tail⟩

lemma pref_head_unique {ξ} {x y : ξ} {xs ys zs} :
    (x :: xs <<+ zs) → (y :: ys <<+ zs) → x = y := by
  intros hx hy; apply (List.of_cons_pref_of_cons_pref hx hy).left

lemma List.pref_unique {ξ} {xs ys zs : List ξ}
    (h_len : xs.length = ys.length) (h : xs <<+ zs) (h' : ys <<+ zs) : xs = ys := by
  rcases h with ⟨sfx, h⟩; rcases h' with ⟨sfx', h'⟩
  apply List.append_inj_left (Eq.trans h.symm h') h_len

lemma pref_of_split {X} {x xy y : List X} : (x <++ xy ++> y) → (x <<+ xy) := λ h => ⟨y, h⟩

def List.repeat {ξ} (x : ξ) : Nat → List ξ
  | 0 => []
  | n + 1 => x :: List.repeat x n

lemma List.of_cons_split_cons {X} {x y : X} {xs ys zs} :
    ((x :: xs) <++ y :: ys ++> zs) → (x = y ∧ (xs <++ ys ++> zs)) := by
  simp [Split]; intros h h'; simp [h, h']

lemma List.of_cons_split {X} {x : X} {xs ys zs} (h : (x :: xs) <++ ys ++> zs) :
    ∃ ys', (ys = x :: ys' ∧ (xs <++ ys' ++> zs)) := by
  cases ys with
  | nil => cases h
  | cons y ys =>
    rcases of_cons_split_cons h with ⟨⟨_⟩, h'⟩
    refine' ⟨_, rfl, h'⟩

lemma List.of_nil_split {X} {p p' : List X} : ([] <++ p ++> p') → p = p' := by simp [Split]

universe u

lemma ite_cases {ξ : Sort u} (r : ξ → Prop) (c : Prop) [h : Decidable c] (x y : ξ) :
    (c → r x) → (¬ c → r y) → r (if c then x else y) := by
  have h : (if c then x else y) = (if c then x else y) := rfl
  intros hx hy; rw [ite_eq_iff'] at h; rcases h with ⟨hx', hy'⟩
  cases em c with
  | inl h => rw [← hx' h]; apply hx h
  | inr h => rw [← hy' h]; apply hy h

lemma Nat.forall_lt_succ_iff_forall_le {n : ℕ} {p : ℕ → Prop} :
    (∀ m < (n + 1), p m) ↔ (∀ m ≤ n, p m) := by
  constructor <;> intros h m h' <;> apply h
  · rw [Nat.lt_succ_iff]; apply h'
  · rw [← Nat.lt_succ_iff]; apply h'

lemma Nat.forall_le_succ {n : ℕ} {p : ℕ → Prop} :
    (∀ m ≤ n + 1, p m) ↔ (∀ m ≤ n, p m) ∧ p (n + 1) := by
  rw [← Nat.forall_lt_succ_iff_forall_le, ← Nat.forall_lt_succ_iff_forall_le]
  apply Nat.forall_lt_succ

syntax "asm" : term
macro_rules
  | `(term| asm) => `(term| by assumption)

syntax "cst" : term
macro_rules
  | `(term| cst) => `(term| by constructor)

lemma split_of_prefix {X} {x xy: List X} : (x <<+ xy) → ∃ y, (x <++ xy ++> y) := id

lemma pref_iff_isPrefix {ξ} {xs ys : List ξ} : xs <<+ ys ↔ xs <+: ys := by
  constructor <;> intro h <;> rcases h with ⟨zs, h⟩ <;> refine' ⟨zs, h.symm⟩

lemma pref_trans {X} {x xy xyz : List X} : (x <<+ xy) → (xy <<+ xyz) → (x <<+ xyz) := by
  simp [pref_iff_isPrefix]; apply List.IsPrefix.trans

lemma append_split {X} {x y z yz xyz : List X} (h : x <++ xyz ++> yz)
    (h' : y <++ yz ++> z) : (x ++ y) <++ xyz ++> z := by
  simp [Split] at *; rw [h, h']

lemma of_append_split {X} {x y z yz xyz : List X}
    (h : x <++ xyz ++> yz) (h' : (x ++ y) <++ xyz ++> z) : (y <++ yz ++> z) := by
  simp [Split] at *; apply List.append_inj_right (Eq.trans h.symm h') rfl

lemma of_append_pref {X} {x y yz xyz : List X} :
    (x <++ xyz ++> yz) → (x ++ y <<+ xyz) → (y <<+ yz) := by
  intros h0 h1; rcases h1 with ⟨z, h1⟩
  refine ⟨z, of_append_split h0 h1⟩

lemma append_pref {X} {x y yz xyz : List X} :
    (x <++ xyz ++> yz) → (y <<+ yz) → (x ++ y <<+ xyz) := by
  intros h0 h1; rcases split_of_prefix h1 with ⟨z, h2⟩
  refine ⟨z, append_split h0 h2⟩

lemma nil_pref {X} {xs : List X} : ([] <<+ xs) := ⟨xs, rfl⟩

lemma cons_pref_cons {X} {x y : X} {p pq} :
    x = y → (p <<+ pq) → (x :: p <<+ y :: pq) := by
  intros h0 h1; rw [h0]; rcases h1 with ⟨q, h2⟩; rw [h2]; refine ⟨q, rfl⟩

syntax "show_pref" : tactic
macro_rules
  | `(tactic| show_pref) =>
    `(tactic| first | apply nil_pref
                    | apply cons_pref_cons; rfl; show_pref )

lemma of_cons_cons_pref_of_cons_cons_pref {X} {x y x' y' : X} {xs xs' ys} :
    (x :: y :: xs <<+ ys) → (x' :: y' :: xs' <<+ ys) →
    x = x' ∧ y = y' ∧ ∃ ys', (xs <<+ ys') ∧ (xs' <<+ ys') := by
  intros h0 h1
  rcases List.of_cons_pref_of_cons_pref h0 h1 with ⟨hx, ys', h3, h4⟩;
  rcases List.of_cons_pref_of_cons_pref h3 h4 with ⟨hy, ys'', h5⟩;
  refine ⟨hx, hy, ys'', h5⟩

open Lean.Elab.Tactic

def Lean.Expr.apply (x : Lean.Expr) : Lean.Elab.Tactic.TacticM Unit := do
  withMainContext do
    let mut val ← Lean.instantiateMVars x
    if val.isMVar then
      Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
      val ← Lean.instantiateMVars val
    let mvarIds' ← Lean.MVarId.apply (← getMainGoal) val {allowSynthFailures := true}
    Lean.Elab.Term.synthesizeSyntheticMVarsNoPostponing
    replaceMainGoal mvarIds'

inductive Bits : ℕ → Type
  | nil : Bits 0
  | cons : ∀ {n : ℕ}, Bits n → Bool → Bits (n + 1)

abbrev Addr := Bits 160
abbrev Word := Bits 256

notation "⦃⦄" => Bits.nil

infixl:70 " +> " => Bits.cons

syntax "⦃" withoutPosition(term,*,?) "⦄"  : term
macro_rules | `(⦃$l,*⦄) => `(expand_foldl% (h t => Bits.cons h t) Bits.nil [$(.ofElems l),*])

abbrev Byte := Bits 8

inductive Bytes : Type
  | nil : Bytes
  | cons : Bytes → Byte → Bytes

infixl:70 " :> " => Bytes.cons

syntax "⟪" withoutPosition(term,*,?) "⟫"  : term
macro_rules | `(⟪$l,*⟫) => `(expand_foldl% (h t => Bytes.cons h t) Bytes.nil [$(.ofElems l),*])

def Bits.toString : ∀ {n}, String → Bits n → String
  | 0, acc, ⦃⦄ => acc
  | _, acc, (xs +> x) => Bits.toString ⟨Bool.toChar x :: acc.data⟩ xs

instance {n} : Repr (Bits n) := ⟨λ bs _ => Bits.toString "" bs⟩

def Bits.not : ∀ {n}, Bits n → Bits n
  | 0, ⦃⦄ => ⦃⦄
  | _, (xs +> x) => xs.not +> x.not

notation "~" => Bits.not

def Bits.zipWith (f : Bool → Bool → Bool) : ∀ {n}, Bits n → Bits n → Bits n
  | 0, ⦃⦄, ⦃⦄ => ⦃⦄
  | _, xs +> x, ys +> y => (zipWith f xs ys) +> f x y


def Bits.and {n} : Bits n → Bits n → Bits n := zipWith Bool.and
def Bits.or {n} : Bits n → Bits n → Bits n := zipWith Bool.or
def Bits.xor {n} : Bits n → Bits n → Bits n := zipWith Bool.xor

lemma Bits.cons_and_cons {n} {xs ys : Bits n} {x y} :
  and (xs +> x) (ys +> y) = and xs ys +> Bool.and x y := rfl

def Bits.lt : ∀ {n : ℕ}, Bits n → Bits n → Prop
  | 0, ⦃⦄, ⦃⦄ => False
  | _, xs +> x, ys +> y => lt xs ys ∨ (xs = ys ∧ x < y)

instance {n} : @LT (Bits n) := ⟨Bits.lt⟩

def Bits.le : ∀ {n : ℕ}, Bits n → Bits n → Prop
  | 0, ⦃⦄, ⦃⦄ => True
  | _, xs +> x, ys +> y => lt xs ys ∨ (xs = ys ∧ x ≤ y)

instance {n} : @LE (Bits n) := ⟨Bits.le⟩

lemma Bits.cons_lt_cons {n} {xs ys : Bits n} {x y} :
    xs +> x < ys +> y ↔ (xs < ys ∨ (xs = ys ∧ x < y)) := Iff.refl _

lemma Bits.cons_lt_cons' {n} {xs ys : Bits n} {x} :
    xs +> x < ys +> x ↔ xs < ys := by simp [cons_lt_cons]

lemma Bits.cons_eq_cons {n} {xs ys : Bits n} {x y} :
    xs +> x = ys +> y ↔ (xs = ys ∧ x = y) := by simp

lemma Bits.cons_le_cons {n} {xs ys : Bits n} {x y} :
    xs +> x ≤ ys +> y ↔ (xs < ys ∨ (xs = ys ∧ x ≤ y)) := Iff.refl _

instance {n : ℕ} (xs ys : Bits n) : Decidable (xs = ys) := by
  induction n with
  | zero => cases xs; cases ys; apply Decidable.isTrue rfl
  | succ n ih =>
    match xs, ys with
    | xs +> x, ys +> y =>
      rw [Bits.cons_eq_cons]; apply instDecidableAnd

instance {n} {xs ys : Bits n} : Decidable (xs < ys) := by
  induction n with
  | zero =>
    cases xs; cases ys; simp [LT.lt, Bits.lt]
    apply Decidable.isFalse not_false
  | succ n ih =>
    match xs, ys with
    | xs +> x, ys +> y =>
      cases x <;> cases y <;>
      simp [Bits.cons_lt_cons, false_lt_true, not_true_lt] <;>
      try {apply ih}; apply instDecidableOr

instance {n : ℕ} (xs ys : Bits n) : Decidable (xs ≤ ys) := by
  cases n with
  | zero =>
    cases xs; cases ys;
    apply Decidable.isTrue; constructor
  | succ n =>
    match xs, ys with
    | xs +> x, ys +> y =>
      rw [Bits.cons_le_cons]; apply instDecidableOr

def Bits.slt : ∀ {n : ℕ}, Bits n → Bits n → Prop
  | 0, ⦃⦄, ⦃⦄ => False
  | 1, ⦃1⦄, ⦃0⦄ => True
  | 1, ⦃_⦄, ⦃_⦄ => False
  | _ + 2, xs +> x, ys +> y => slt xs ys ∨ (x < y ∧ xs = ys)

infix:70 " ±< " => Bits.slt

lemma Bits.singleton_slt_singleton {x y : Bool} :
    ⦃x⦄ ±< ⦃y⦄ ↔ (x = 1 ∧ y = 0) := by
  cases x <;> cases y <;> simp [Bool.zero, Bool.one] <;>
  try {intro hc; cases hc}; constructor

def Bits.sgt {n : ℕ} (xs ys : Bits n) : Prop := slt ys xs

infix:70 " ±> " => Bits.sgt

def Bits.toNat : ∀ {n : ℕ}, Bits n → Nat
  | 0, ⦃⦄ => 0
  | _ + 1, xs +> x => 2 * xs.toNat + x.toNat

def Bits.zero : ∀ n : ℕ, Bits n
  | 0 => ⦃⦄
  | n + 1 => zero n +> 0

instance {n} : @Zero (Bits n) := ⟨Bits.zero n⟩
instance : @Zero Byte := ⟨Bits.zero 8⟩

def Bits.max : ∀ n : ℕ, Bits n
  | 0 => ⦃⦄
  | n + 1 => max n +> 1

def Bits.one : ∀ n : ℕ, Bits n
  | 0 => ⦃⦄
  | n + 1 => 0 +> 1

instance {n} : @One (Bits n) := ⟨Bits.one n⟩

def Bits.succ : ∀ {n}, Bits n → Bits n
  | 0, ⦃⦄ => ⦃⦄
  | _ + 1, xs +> 0 => xs +> 1
  | _ + 1, xs +> 1 => xs.succ +> 0

def Bits.succs {n} : Nat → Bits n → Bits n
  | 0, xs => xs
  | n + 1, xs => succs n xs.succ

def Bits.incr {n} : Bool → Bits n → Bits n
  | false => id
  | true => Bits.succ

def Bits.add : ∀ {n}, Bits n → Bits n → Bits n
  | 0, ⦃⦄, ⦃⦄ => ⦃⦄
  | _ + 1, xs +> x, ys +> y => incr x (add xs ys +> y)

def Overflow {n : ℕ} (xs ys : Bits n) : Prop := 2 ^ n ≤ xs.toNat + ys.toNat

infix:55 " ↟ " => Overflow

lemma Nat.mul_le_mul_iff {a b c : ℕ} (h : 0 < c) : c * a ≤ c * b ↔ a ≤ b := by
  constructor <;> intro h'
  · apply Nat.le_of_mul_le_mul_left h' h
  · apply Nat.mul_le_mul_left _ h'

lemma Nat.lt_floor_left {a b c d : ℕ} (h : d < c) : c * a + d < c * b ↔ c * a < c * b := by
  constructor <;> intro h'
  · apply lt_of_le_of_lt (Nat.le_add_right _ _) h'
  · have hc : 0 < c := Nat.lt_of_le_of_lt (Nat.zero_le _) h
    have h'' : c * a + d < c * a + c := by
      rw [Nat.add_lt_add_iff_left]; exact h
    apply lt_of_lt_of_le h''
    rw [← Nat.mul_succ, Nat.mul_le_mul_iff hc, Nat.succ_le]
    rw [Nat.mul_lt_mul_left hc] at h'; exact h'

lemma Nat.eq_floor {a b c d e : ℕ} (hd : d < c) (he : e < c)
    (h : c * a + d = c * b + e) : a = b ∧ d = e := by
  have hc : 0 < c := Nat.lt_of_le_of_lt (Nat.zero_le _) hd
  rcases Nat.lt_trichotomy a b with h' | h' | h'
  · apply False.elim <| Nat.lt_irrefl (c * b) _
    apply lt_of_le_of_lt (Nat.le_add_right (c * b) e)
    rw [← h, Nat.lt_floor_left hd]
    apply Nat.mul_lt_mul_of_pos_left h' hc
  · simp [h'] at h; refine ⟨h', h⟩
  · apply False.elim <| Nat.lt_irrefl (c * a) _
    apply lt_of_le_of_lt (Nat.le_add_right (c * a) d)
    rw [h, Nat.lt_floor_left he]
    apply Nat.mul_lt_mul_of_pos_left h' hc

def NoOverflow {n : ℕ} (xs ys : Bits n) : Prop := xs.toNat + ys.toNat < 2 ^ n

def Bits.nof_iff_not_Overflow {n : ℕ} (xs ys : Bits n) : NoOverflow xs ys ↔ ¬ xs ↟ ys := by
  simp [Overflow, NoOverflow]

def Bits.pred : ∀ {n}, Bits n → Bits n
  | 0, ⦃⦄ => ⦃⦄
  | _ + 1, xs +> 0 => xs.pred +> 1
  | _ + 1, xs +> 1 => xs +> 0

def Bits.decr {n} : Bool → Bits n → Bits n
  | false, xs => xs
  | true, xs => xs.pred

def Bits.sub : ∀ {n}, Bits n → Bits n → Bits n
  | 0, ⦃⦄, ⦃⦄ => ⦃⦄
  | _ + 1, xs +> x, ys +> y => decr y (sub xs ys +> x)

instance {n} : HAdd (Bits n) (Bits n) (Bits n) := ⟨Bits.add⟩

lemma Bits.cons_add_cons {n} {xs ys : Bits n} {x y} :
    xs +> x + ys +> y = incr x ((xs + ys) +> y) := rfl

lemma Bits.cons_zero_add_cons {n} {xs ys : Bits n} {y} :
    xs +> 0 + ys +> y = ((xs + ys) +> y) := rfl

lemma Bits.cons_add_cons_zero {n} {xs ys : Bits n} {x} :
    xs +> x + ys +> 0 = ((xs + ys) +> x) := by
  rw [cons_add_cons]; cases x <;> simp [incr] <;> rfl

lemma Bits.cons_add_cons_one {n} {xs ys : Bits n} {x} :
    xs +> x + ys +> 1 = ((xs + ys) +> x).succ := by
  rw [cons_add_cons]; cases x <;> simp [incr] <;> rfl

lemma Bits.cons_false_add_cons {n} {xs ys : Bits n} {y} :
    xs +> false + ys +> y = ((xs + ys) +> y) := cons_zero_add_cons

lemma Bits.cons_true_add_cons {n} {xs ys : Bits n} {y} :
    xs +> true + ys +> y = ((xs + ys) +> y).succ := rfl

lemma Bits.cons_add_cons_false {n} {xs ys : Bits n} {x} :
    xs +> x + ys +> false = ((xs + ys) +> x) := cons_add_cons_zero

lemma Bits.cons_add_cons_true {n} {xs ys : Bits n} {x} :
    xs +> x + ys +> true = ((xs + ys) +> x).succ := cons_add_cons_one

instance {n} : HSub (Bits n) (Bits n) (Bits n) := ⟨Bits.sub⟩

lemma Bits.cons_sub_cons_true {n} {xs ys : Bits n} {x} :
    xs +> x - ys +> true = ((xs - ys) +> x).pred := rfl

lemma Bits.cons_sub_cons_false {n} {xs ys : Bits n} {x} :
    xs +> x - ys +> false = (xs - ys) +> x := rfl

lemma Bits.cons_sub_cons {n} {xs ys : Bits n} {x y} :
    xs +> x - ys +> y = decr y ((xs - ys) +> x) := rfl

lemma Bits.cons_sub_cons' {n} {xs ys : Bits n} {x} :
    xs +> x - ys +> x = (xs - ys) +> 0 := by cases x <;> rfl

def Bits.shlo : ∀ {n}, Bits n → Bool → Bits n
  | 0, ⦃⦄, _ => ⦃⦄
  | _ + 1, xs +> x, y => shlo xs x +> y

def Bits.shl : Nat → ∀ {n}, Bits n → Bits n
  | 0, _, xs => xs
  | k + 1, _, xs => shl k (shlo xs 0)

def Bits.snoc (x : Bool) : ∀ {n}, Bits n → Bits (n + 1)
  | 0, ⦃⦄ =>⦃x⦄
  | _ + 1, ys +> y => snoc x ys +> y

def Bits.shro (x : Bool) : ∀ {n}, Bits n → Bits n
  | 0, ⦃⦄ => ⦃⦄
  | _ + 1, ys +> _ => snoc x ys

def Bits.shr : Nat → ∀ {n}, Bits n → Bits n
  | 0, _, xs => xs
  | k + 1, _, xs => shro 0 (shr k xs)

def Bits.is_neg : ∀ {n : ℕ}, Bits n → Bool
  | 0, _ => false
  | 1,⦃x⦄ => x
  | _ + 2, xs +> _ => is_neg xs

def Bits.neg {n : ℕ} (xs : Bits n) : Bits n := (~ xs).succ

def Bits.sar (m : Nat) {n} (xs : Bits n) : Bits n :=
  if is_neg xs
  then neg (shr m (neg xs))
  else shr m xs

def Bits.append : ∀ {m n}, Bits m → Bits n → Bits (m + n)
  | _, 0, xs, ⦃⦄ => xs
  | _, _ + 1, xs, ys +> y => append xs ys +> y

instance {m n} : HAppend (Bits m) (Bits n) (Bits (m + n)) := ⟨Bits.append⟩

lemma Bits.append_nil {n} {xs : Bits n} : xs ++ ⦃⦄ = xs := rfl

lemma Bits.append_cons {m n} {xs : Bits m} {ys : Bits n} {y} :
    xs ++ (ys +> y) = (xs ++ ys) +> y := by simp [HAppend.hAppend, append]

lemma Bits.append_and_append {m n} {xs₀ ys₀ : Bits m} {xs₁ ys₁ : Bits n} :
    and (xs₀ ++ xs₁) (ys₀ ++ ys₁) = and xs₀ ys₀ ++ and xs₁ ys₁ := by
  induction n with
  | zero => cases xs₁; cases ys₁; rfl
  | succ n ih =>
    match xs₁, ys₁ with
    | xs₁ +> x,  ys₁ +> y =>
      simp [append_cons, cons_and_cons, ih]

def Bits.mul : ∀ {n}, Bits n → Bits n → Bits n
  | 0, ⦃⦄, ⦃⦄ => ⦃⦄
  | _ + 1, xs +> x, ys +> 0 => mul (shlo xs x) ys +> 0
  | _ + 1, xs +> x, ys +> 1 => (mul (shlo xs x) ys +> 0) + (xs +> x)

instance {n} : HMul (Bits n) (Bits n) (Bits n) := ⟨Bits.mul⟩

def Bits.div_mod : ∀ {n}, Bits n → Bits n → (Bits n × Bits n)
  | 0, ⦃⦄, ⦃⦄ => (⦃⦄, ⦃⦄)
  | _ + 1, xs +> x, ys +> y =>
  if xs +> x < ys +> y
  then (0, xs +> x)
  else let (zs, xs') := div_mod xs (shlo ys y)
       if xs' +> x < ys +> y
       then (zs +> 0, xs' +> x)
       else (zs +> 1, xs' +> x - ys +> y)

def Bits.div {n} (xs ys : Bits n) : Bits n := (div_mod xs ys).fst

instance {n} : HDiv (Bits n) (Bits n) (Bits n) := ⟨Bits.div⟩

def Bits.mod {n} (xs ys : Bits n) : Bits n := (div_mod xs ys).snd

instance {n} : HMod (Bits n) (Bits n) (Bits n) := ⟨Bits.mod⟩

def Bits.smin : ∀ {n : ℕ}, Bits n
  | 0 => ⦃⦄
  | 1 =>⦃1⦄
  | _ + 2 => smin +> 0

def Bits.neg_one {n : ℕ} : Bits n := max _

def Bits.sdiv {n : ℕ} (xs ys : Bits n) : Bits n :=
  if ys = 0
  then 0
  else if xs = smin ∧ ys = neg_one
       then smin
       else match (is_neg xs, is_neg ys) with
            | (0, 0) => xs / ys
            | (1, 0) => neg ((neg xs) / ys)
            | (0, 1) => neg (xs / (neg ys))
            | (1, 1) => (neg xs) / (neg ys)

def Bits.abs {n : ℕ} (xs : Bits n) : Bits n :=
  if is_neg xs then neg xs else xs

def Bits.smod {n : ℕ} (xs ys : Bits n) : Bits n :=
  if ys = 0
  then 0
  else let mod := (abs xs) % (abs ys)
       if is_neg xs then neg mod else mod

def Bits.addmod {n : ℕ} (x y z : Bits n) : Bits n :=
  if z = 0 then 0 else (x + y) % z

def Bits.mulmod {n : ℕ} (x y z : Bits n) : Bits n :=
  if z = 0 then 0 else (x * y) % z

def Bits.iter {α : Type} (f : α → α) : α → ∀ {n}, Bits n → α
  | a, 0, ⦃⦄ => a
  | a, _ + 1, xs +> 0 => iter f (iter f a xs) xs
  | a, _ + 1, xs +> 1 => iter f (iter f (f a) xs) xs

def Bits.exp {n : ℕ} (x y : Bits n) : Bits n :=
  iter (· * x) 1 y

instance {n} : HPow (Bits n) (Bits n) (Bits n) := ⟨Bits.exp⟩

def Bits.signextend_core : Nat → ∀ {n : Nat}, Bits n → Bits n
  | _, 0, ⦃⦄ => ⦃⦄
  | 0, _ + 1, _ +> 0  => 0
  | 0, _ + 1, _ +> 1 => Bits.max _
  | n + 1, _ + 1, xs +> x => signextend_core n xs +> x

def Bits.signextend {n} (x y : Bits n) : Bits n :=
  signextend_core (8 * (Bits.toNat x + 1)) y

def Bits.suffix : ∀ {m n}, Bits m → Bits n → Prop
  | _, 0, _, ⦃⦄ => true
  | 0, _ + 1, ⦃⦄, _ => false
  | _ + 1, _ + 1, xs +> x, ys +> y => suffix xs ys ∧ x = y

def Bits.getSuff : ∀ {m n}, Bits (m + n) → Bits n
  | _, 0, _ => ⦃⦄
  | _, n + 1, xs +> x => getSuff xs +> x

inductive Bits.prefix : ∀ {m n}, Bits m → Bits n → Prop
  | refl : ∀ {m} (xs : Bits m), Bits.prefix xs xs
  | cons : ∀ {m n} (xs : Bits m) (ys : Bits n) y, Bits.prefix xs ys → Bits.prefix xs (ys +> y)

lemma Bits.nil_eq_nil {x y : Bits 0} : x = y := by cases x; cases y; rfl

lemma Bits.append_inj {m n} {xs₁ ys₁ : Bits m} {xs₂ ys₂ : Bits n} :
     xs₁ ++ xs₂ = ys₁ ++ ys₂ → xs₁ = ys₁ ∧ xs₂ = ys₂ := by
  induction n generalizing xs₁ ys₁ m with
  | zero => cases xs₂; cases ys₂; intro h; refine' ⟨h, nil_eq_nil⟩
  | succ n ih =>
    match xs₂, ys₂ with
    | xs₂' +> x, ys₂' +> y =>
      simp [Bits.append_cons]; intro h h'
      refine ⟨(ih h).left, (ih h).right, h'⟩

def Addr.toWord (a : Addr) : Bits 256 := (0 : Bits 96) ++ a

lemma Addr.toWord_inj {a a' : Addr} :
    Addr.toWord a = Addr.toWord a' → a = a' := And.right ∘ Bits.append_inj

def Nat.toBits (k) : Nat → Bits k
  | 0 => 0
  | n + 1 => (Nat.toBits k n).succ

instance {m n} : OfNat (Bits m) n := ⟨Nat.toBits _ n⟩

def Nat.toByte : Nat → Bits 8 := Nat.toBits _

def toAddr : Bits 256 → Bits 160 := @Bits.getSuff 96 160

def getSuff_append {m n} {xs : Bits m} {ys : Bits n} :
    Bits.getSuff (xs ++ ys) = ys := by
  induction n with
  | zero => cases ys; rfl
  | succ n ih =>
    cases ys with
    | cons ys y => simp [Bits.getSuff]; apply ih

lemma toWord_toAddr_eq (a : Addr) : toAddr (Addr.toWord a) = a := getSuff_append

def Bits.head {m} : ∀ {n}, Bits (m + n) → Bits m
  | 0, xs => xs
  | n + 1, xs +> _ => head xs

def Bits.tail {m} : ∀ {n}, Bits (m + n) → Bits n
  | 0, _ => ⦃⦄
  | n + 1, xs +> x => tail xs +> x
lemma Bits.head_append_tail {m n} : ∀ xs : Bits (m + n), head xs ++ tail xs = xs := by
  induction n with
  | zero => intro xs; rfl
  | succ n ih =>
    intro xs; match xs with
    | xs' +> x => simp [head, tail, append_cons, ih]

def Bits.toBytes : ∀ {n}, Bits (8 * n) → Bytes
  | 0, ⦃⦄ => ⟪⟫
  | _ + 1, (bs +> b0 +> b1 +> b2 +> b3 +> b4 +> b5 +> b6 +> b7) =>
    toBytes bs :> ⦃b0, b1, b2, b3, b4, b5, b6, b7⦄

def Bits.min {n} (x y : Bits n) : Bits n :=
if x ≤ y then x else y

def Bytes.toBits : ∀ (n : Nat), Bytes → Bits (8 * n)
  | 0, _ => ⦃⦄
  | n + 1, ⟪⟫ => ⟪⟫.toBits n ++ (0 : Byte)
  | n + 1, bs :> b => bs.toBits n ++ b

lemma Bits.zero_eq_cons {n} : (0 : Bits (n + 1)) = (0 : Bits n) +> 0 := rfl

lemma Bits.zero_eq_append {m n} : (0 : Bits (m + n)) = (0 : Bits m) ++ (0 : Bits n) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [zero_eq_cons, zero_eq_cons, append_cons, ih]

lemma Bits.zero_toNat : ∀ {k}, (0 : Bits k).toNat = 0
  | 0 => rfl
  | (k + 1) => by simp [zero_eq_cons]; unfold Bits.toNat; simp [zero_toNat]; rfl

lemma Bits.cons_eq_zero {n x} {xs : Bits n} :
  xs +> x = 0 ↔ (xs = 0 ∧ x = 0) := by rw [zero_eq_cons]; simp

lemma Bits.of_toNat_eq_zero {k} (xs : Bits k) (h : xs.toNat = 0) : xs = 0 := by
  induction k with
  | zero => apply nil_eq_nil
  | succ k ih =>
    rcases xs with _ | ⟨xs, _ | _⟩ <;>
    (simp [cons_eq_zero]; simp [toNat, Nat.mul_eq_zero] at h)
    · refine ⟨ih _ h, false_eq_zero⟩

lemma Bits.nonzero_toNat {k} (xs : Bits k) : xs ≠ 0 → xs.toNat ≠ 0 :=
  mt <| of_toNat_eq_zero xs

lemma Bits.succ_toNat_assoc {k} : (xs : Bits k) → xs ≠ max _ → xs.succ.toNat = xs.toNat.succ := by
  apply @Nat.rec (λ k => (xs : Bits k) → xs ≠ max _ → xs.succ.toNat = xs.toNat.succ)
  · intros xs h; cases h nil_eq_nil
  · intros k ih xs h; rcases xs with _ | ⟨xs, _ | _⟩
    · simp [succ, toNat, false_toNat, true_toNat, Bool.zero_toNat, Bool.one_toNat]
    · simp [succ, toNat, false_toNat, true_toNat, Bool.zero_toNat, Bool.one_toNat]
      have h_ne : xs ≠ max _ := by
        intro hc; simp [max, hc] at h
      rw [ih _ h_ne]; simp [Nat.mul_succ]

lemma Bits.incr_toNat_assoc {k} (x) (xs : Bits k) (h : xs ≠ max _) :
    (incr x xs).toNat = xs.toNat + x.toNat := by
  cases x <;> simp [incr]; apply succ_toNat_assoc _ h

lemma Bits.nil_toNat (xs : Bits 0) : xs.toNat = 0 := by cases xs; rfl

lemma Bits.pred_toNat_assoc {k} (xs : Bits k) (h : xs ≠ 0) : xs.pred.toNat = xs.toNat.pred := by
  induction k with
  | zero => simp [nil_toNat]
  | succ k ih =>
    rcases xs with _ | ⟨xs, _ | _⟩ <;>
    simp [pred, toNat, Bool.one_toNat]
    · simp [Ne, cons_eq_zero, false_eq_zero] at h; rw [ih xs h];
      rcases Nat.exists_eq_succ_of_ne_zero <| nonzero_toNat _ h with ⟨n, hn⟩
      rw [hn, Nat.mul_succ]; simp [Nat.pred]
    · rfl

lemma Bits.decr_toNat_assoc {k} (x) (xs : Bits k) (h : xs ≠ 0) :
    (decr x xs).toNat = xs.toNat - x.toNat := by
  cases x <;> simp [decr]; apply pred_toNat_assoc _ h

lemma Bits.max_toNat_succ : ∀ {n : Nat}, (max n : Bits n).toNat.succ = 2 ^ n := by
  apply Nat.rec
  · rfl
  · intros n ih
    simp [toNat, Nat.pow_succ, Bool.one_toNat]
    rw [← ih]; omega

lemma Bits.succ_pred : ∀ {n} {xs : Bits n}, succ (pred xs) = xs := by
  apply Nat.rec
  · intros _; apply nil_eq_nil
  · intros n ih xs; rcases xs with _ | ⟨xs, _ | _⟩ <;> simp [pred, succ]
    · simp [ih]; rfl
    · rfl

lemma Bits.pred_succ : ∀ {n} {xs : Bits n}, pred (succ xs) = xs := by
  apply Nat.rec
  · intros _; apply nil_eq_nil
  · intros n ih xs; rcases xs with _ | ⟨xs, _ | _⟩ <;> simp [pred, succ]
    · rfl
    · simp [ih]; rfl

lemma Bits.add_comm : ∀ {n} {xs ys : Bits n}, xs + ys = ys + xs := by
  apply Nat.rec
  · intros _ _; apply nil_eq_nil
  · intros n ih xs ys;
    rcases xs with _ | ⟨xs, x⟩
    rcases ys with _ | ⟨ys, y⟩
    rw [cons_add_cons, cons_add_cons, ih];
    cases x <;> cases y <;> rfl

lemma Bits.succ_add : ∀ {n} {xs ys : Bits n}, succ (xs + ys) = xs.succ + ys := by
  apply Nat.rec
  · intros _ _; apply nil_eq_nil
  · intros n ih xs ys;
    rcases xs with _ | ⟨xs, _ | _⟩ <;>
    rcases ys with _ | ⟨ys, _ | _⟩
    · rfl
    · rfl
    · rw [cons_add_cons_false]; simp [succ];
      rw [cons_add_cons_false, ih]
    · rw [cons_true_add_cons]; simp [succ];
      rw [cons_add_cons_true]; simp [succ, ih]

lemma Bits.pred_add_eq_add_pred : ∀ {n} {xs ys : Bits n}, xs.pred + ys = xs + ys.pred := by
  apply Nat.rec
  · intros _ _; apply nil_eq_nil
  · intros n ih xs ys;
    rcases xs with _ | ⟨xs, _ | _⟩ <;>
    rcases ys with _ | ⟨ys, _ | _⟩
    · simp [cons_false_add_cons, pred, cons_add_cons_false]; apply ih
    · simp [pred, cons_add_cons, incr, succ];
      rw [succ_add]; simp [succ_pred]
    · simp [pred]; rw [cons_add_cons_false, cons_true_add_cons];
      simp [succ]; rw [← ih, succ_add, succ_pred];
    · rfl

lemma Bits.pred_add : ∀ {n} {xs ys : Bits n}, pred (xs + ys) = xs.pred + ys := by
  apply Nat.rec
  · intros _ _; apply nil_eq_nil
  · intros n ih xs ys;
    rcases xs with _ | ⟨xs, _ | _⟩ <;>
    rcases ys with _ | ⟨ys, _ | _⟩
    · simp [cons_false_add_cons, pred, cons_add_cons_false]; apply ih
    · rw [cons_false_add_cons, pred_add_eq_add_pred]
      simp [pred]; rfl
    · rfl
    · rw [cons_true_add_cons]; simp [pred];
      rw [cons_add_cons_true]; simp [succ, pred_succ]

lemma Bits.pred_sub : ∀ {n} {xs ys : Bits n}, pred (xs - ys) = xs.pred - ys := by
  apply Nat.rec
  · intros _ _; apply nil_eq_nil
  · intros n ih xs ys;
    rcases xs with _ | ⟨xs, _ | _⟩ <;>
    rcases ys with _ | ⟨ys, _ | _⟩
    · rw [cons_sub_cons_false]; simp [pred]; rw [cons_sub_cons_false, ih]
    · rw [cons_sub_cons_true]; simp [pred]; rw [cons_sub_cons_true]; simp [pred, ih]
    · rfl
    · rfl

lemma Bits.succ_sub : ∀ {n} {xs ys : Bits n}, succ (xs - ys) = xs.succ - ys := by
  apply Nat.rec
  · intros _ _; apply nil_eq_nil
  · intros n ih xs ys;
    rcases xs with _ | ⟨xs, _ | _⟩ <;>
    rcases ys with _ | ⟨ys, _ | _⟩
    · rw [cons_sub_cons_false]; simp [succ]; rw [cons_sub_cons_false]
    · simp [succ]; rw [succ_pred]; rfl
    · rw [cons_sub_cons_false]; simp [succ]; rw [cons_sub_cons_false, ih]
    · simp [succ]; rw [cons_sub_cons_true]; simp [pred];
      rw [pred_sub, pred_succ]; rfl

lemma Bits.pred_add' {n} {xs ys : Bits n} : pred (xs + ys) = xs + ys.pred := by
  rw [@add_comm _ _ ys, pred_add, add_comm]

lemma Bits.add_sub_assoc : ∀ {n} {xs ys zs : Bits n}, xs + ys - zs = xs + (ys - zs) := by
  apply Nat.rec
  · intros _ _ _; apply nil_eq_nil
  · intros m ih xs ys zs
    rcases xs with _ | ⟨xs, _ | _⟩ <;>
    rcases ys with _ | ⟨ys, _ | _⟩ <;>
    rcases zs with _ | ⟨zs, _ | _⟩ <;>
    simp [cons_add_cons, cons_sub_cons, decr, incr]
    · rw [ih]
    · rw [← pred_add', cons_false_add_cons, ih]
    · rw [ih]
    · rw [← pred_add', cons_false_add_cons, ih]
    · simp [succ]; rw [cons_sub_cons_false, ih]
    · simp [succ]; rw [← pred_add_eq_add_pred];
      simp [pred]; rw [cons_zero_add_cons, ← ih]; rfl
    · simp [succ]; rw [cons_sub_cons_false];
      rw [← ih, succ_sub]
    · simp [succ, pred]; rw [cons_sub_cons_true, cons_true_add_cons]
      simp [succ, pred]; rw [pred_sub, pred_succ, ih]

lemma Bits.sub_self : ∀ {n} {x : Bits n}, x - x = 0 := by
  apply Nat.rec
  · intros _; apply nil_eq_nil
  · intros m ih xs; rcases xs with _ | ⟨xs, x⟩
    rw [cons_sub_cons', ih]; rfl

lemma Bits.add_zero : ∀ {n} (xs : Bits n), xs + 0 = xs := by
  apply Nat.rec
  · intros _; apply nil_eq_nil
  · intros m ih xs; rcases xs with _ | ⟨xs, x⟩
    rw [zero_eq_cons, cons_add_cons_zero, ih]

lemma Bits.add_sub_cancel {n} {x y : Bits n} : x + y - y = x :=
 by rw [add_sub_assoc, sub_self, add_zero]

lemma Bits.add_sub_comm {n} {xs ys zs : Bits n} : xs + ys - zs = xs - zs + ys := by
  rw [add_comm, add_sub_assoc, add_comm]

lemma Bits.sub_add_cancel {n} {x y : Bits n} : x - y + y = x :=
 by rw [← add_sub_comm, add_sub_cancel]

lemma Bits.zero_add {n} (xs : Bits n) : 0 + xs = xs := by rw [add_comm, add_zero]

lemma Bits.add_right_inj {n} {x y z : Bits n} : x + z = y + z → x = y := by
  intro h; have h' : x + z - z = y + z - z := by rw [h]
  rw [add_sub_assoc, add_sub_assoc, sub_self, add_zero, add_zero] at h'; exact h'

lemma Bits.add_left_inj {n} {x y z : Bits n} : z + x = z + y → x = y := by
 rw [add_comm, @add_comm _ z]; apply add_right_inj

lemma toBits_toNat {k} : ∀ n, n < 2 ^ k → (@Nat.toBits k n).toNat = n := by
  apply Nat.rec
  · simp [Nat.toBits, Bits.toNat, Bits.zero_toNat]
  · intros n ih h_lt
    have h_lt' : n < 2 ^ k := Nat.lt_trans (Nat.lt_succ_self _) h_lt
    have ih' := ih h_lt'
    unfold Nat.toBits; rw [Bits.succ_toNat_assoc, ih']
    intro hc; rw [hc] at ih'
    rw [← ih', Bits.max_toNat_succ] at h_lt
    apply Nat.lt_irrefl _ h_lt

lemma Bits.nil_le_nil {xs ys : Bits 0} : xs ≤ ys := by cases xs; cases ys; constructor

lemma Bits.lt_succ_self {n} {xs : Bits n} (h : xs < max n) : xs < xs.succ := by
  induction n with
  | zero => cases xs; simp [max] at h; cases h
  | succ n ih =>
    match xs with
    | xs +> x =>
      simp [max] at h; rw [cons_lt_cons] at h
      cases x <;> simp [succ, cons_lt_cons]
      · right; constructor
      · cases h with
        | inl h' => left; apply ih h'
        | inr h' => cases h'.right

lemma Bits.lt_trans {n} {xs ys zs : Bits n} (h : xs < ys) (h' : ys < zs) : xs < zs := by
  induction n with
  | zero => cases xs; cases ys; cases h
  | succ n ih =>
    match xs, ys, zs with
    | xs +> x, ys +> y, zs +> z =>
      cases x <;> cases y <;> cases z <;>
      simp [cons_lt_cons, false_lt_true, not_true_lt_false] at * <;>
      try {apply ih h h'}
      · left; rcases h' with h' | h'; exact ih h h'; rw [← h']; exact h
      · rcases h with h | h; exact ih h h'; rw [h]; exact h'
      · left; rcases h with h | h; exact ih h h'; rw [h]; exact h'
      · rcases h' with h' | h';  exact ih h h'; rw [← h']; exact h

lemma Bits.le_refl {n} {xs : Bits n} : xs ≤ xs := by
  cases xs with
  | nil => apply nil_le_nil
  | cons xs x => simp [cons_le_cons]

lemma Bits.le_of_eq {n : Nat} {xs ys : Bits n} (h : xs = ys) : xs ≤ ys := by
  cases h; apply le_refl

lemma Bits.le_of_lt {n : Nat} {xs ys : Bits n} (h : xs < ys) : xs ≤ ys := by
  cases n with
  | zero => cases xs; cases ys; constructor
  | succ n =>
    match xs, ys with
    | xs +> x, ys +> y =>
      rw [cons_lt_cons] at h
      rcases h with h | ⟨h, h'⟩
      · left; exact h
      · right; refine' ⟨h, Bool.le_of_lt h'⟩

lemma Bits.le_of_lt_or_eq {n : Nat} {xs ys : Bits n}
    (h : xs < ys ∨ xs = ys) : xs ≤ ys := by
  cases h; apply le_of_lt asm; apply le_of_eq asm

lemma Bits.lt_or_eq_of_le {n : Nat} {xs ys : Bits n} (h : xs ≤ ys) : xs < ys ∨ xs = ys := by
  cases n with
  | zero => right; apply nil_eq_nil
  | succ n  =>
  match xs, ys with
  | xs +> x, ys +> y =>
    cases h with
    | inl h' => left; left; apply h'
    | inr h' =>
      match x, y with
      | 0, 0 => right; rw [h'.left]
      | 0, 1 => left; right; simp [h'.left]; constructor
      | 1, 0 => simp [LE.le] at h'
      | 1, 1 => right; rw [h'.left]


lemma Bits.le_iff_lt_or_eq {n : Nat} {xs ys : Bits n} : xs ≤ ys ↔ (xs < ys ∨ xs = ys) :=
  ⟨lt_or_eq_of_le, le_of_lt_or_eq⟩

lemma Bits.cons_lt_cons_of_le_of_lt {n} {xs ys : Bits n} {x y} :
    xs ≤ ys → x < y → xs +> x < ys +> y := by
  intros hs h; cases lt_or_eq_of_le hs with
  | inl h_lt => left; apply h_lt
  | inr h_eq => right; refine ⟨h_eq, h⟩

lemma Bits.le_max {n} : ∀ {xs : Bits n}, xs ≤ max _ := by
  induction n with
  | zero => intro _; apply nil_le_nil
  | succ n ih =>
    intro xs
    cases xs with
    | cons xs x =>
      cases lt_or_eq_of_le ih with
      | inl h => left; apply h
      | inr h => right; refine' ⟨h, Bool.le_one⟩

lemma Bits.zero_le {n} : ∀ xs : Bits n, 0 ≤ xs := by
  induction n with
  | zero => intro xs; cases xs; constructor
  | succ n ih =>
    intro xs; match xs with
    | xs +> x =>
      rw [zero_eq_cons, cons_le_cons]
      cases lt_or_eq_of_le <| ih xs
      · left; assumption
      · right; refine' ⟨asm, by simp [LE.le]⟩

lemma Bits.lt_irrefl {n} {xs : Bits n} : ¬ xs < xs := by
  induction n with
  | zero => cases xs; simp [LT.lt, lt]
  | succ n ih => rcases xs with _ | ⟨xs, x⟩; rw [cons_lt_cons']; apply ih

lemma Bits.lt_of_le_of_lt {n} {xs ys zs : Bits n} (h : xs ≤ ys) (h' : ys < zs) : xs < zs := by
  cases lt_or_eq_of_le h with
  | inl h'' => apply lt_trans h'' h'
  | inr h'' => rw [h'']; exact h'

lemma Bits.lt_of_lt_of_le {n} {xs ys zs : Bits n} (h : xs < ys) (h' : ys ≤ zs) : xs < zs := by
  cases lt_or_eq_of_le h' with
  | inl h'' => apply lt_trans h h''
  | inr h'' => rw [← h'']; exact h

lemma Bits.le_trans {n} {xs ys zs : Bits n} (h : xs ≤ ys) (h' : ys ≤ zs) : xs ≤ zs := by
  induction n with
  | zero => cases xs; cases zs; constructor
  | succ n ih =>
    match xs, ys, zs with
    | xs +> x, ys +> y, zs +> z =>
      cases x <;> cases y <;> cases z <;>
      simp [cons_le_cons, false_le, not_true_le_false] at * <;>
      try {apply lt_or_eq_of_le (ih (le_of_lt_or_eq h) (le_of_lt_or_eq h'))}
      · left; apply lt_of_le_of_lt (le_of_lt_or_eq h) h'
      · apply lt_of_lt_of_le h <| le_of_lt_or_eq h'
      · apply lt_or_eq_of_le <| ih (le_of_lt h) <| le_of_lt_or_eq h'
      · apply lt_of_le_of_lt (le_of_lt_or_eq h) h'

lemma Bits.lt_max_of_ne_max {n} {xs : Bits n} : xs ≠ max _ → xs < max _ := by
  induction n with
  | zero => intro h; cases h nil_eq_nil
  | succ n ih =>
    rcases xs with _ | ⟨xs, _ | _⟩ <;> unfold max
    · simp; apply cons_lt_cons_of_le_of_lt le_max cst
    · rw [true_eq_one]; simp; intro h; left; apply ih h

lemma Bits.lt_max_iff_ne_max {n} {xs : Bits n} : xs < max _ ↔ xs ≠ max _ := by
  refine' ⟨λ h_lt h_eq => _, lt_max_of_ne_max⟩
  cases h_eq; apply lt_irrefl h_lt

lemma toBits_le_toBits {k m n : Nat} :
     m ≤ n → n < 2 ^ k → (@Nat.toBits k m) ≤ (@Nat.toBits k n) := by
  revert m
  induction n with
  | zero => intros m h_le h_lt; cases m; apply Bits.zero_le; cases h_le
  | succ n ih =>
    intros m h_le h_lt;
    cases Nat.lt_or_eq_of_le h_le with
    | inl h_lt' =>
      apply
        Bits.le_trans
          (ih (Nat.le_of_lt_succ h_lt') (Nat.lt_trans (Nat.lt_succ_self _) h_lt))
      apply Bits.le_of_lt; apply Bits.lt_succ_self
      rw [Bits.lt_max_iff_ne_max]; intro h_eq
      have h_eq' : n + 1 = 2 ^ k := by
        apply Eq.trans _ Bits.max_toNat_succ; simp
        rw [← h_eq, toBits_toNat]
        apply Nat.lt_trans _ h_lt; simp
      rw [h_eq'] at h_lt; apply Nat.lt_irrefl _ h_lt
    | inr h_eq => rw [← h_eq]; apply Bits.le_refl

abbrev Hex : Type := Bits 4

def Hex.toChar : Hex → Char
  | ⦃0, 0, 0, 0⦄ => '0'
  | ⦃0, 0, 0, 1⦄ => '1'
  | ⦃0, 0, 1, 0⦄ => '2'
  | ⦃0, 0, 1, 1⦄ => '3'
  | ⦃0, 1, 0, 0⦄ => '4'
  | ⦃0, 1, 0, 1⦄ => '5'
  | ⦃0, 1, 1, 0⦄ => '6'
  | ⦃0, 1, 1, 1⦄ => '7'
  | ⦃1, 0, 0, 0⦄ => '8'
  | ⦃1, 0, 0, 1⦄ => '9'
  | ⦃1, 0, 1, 0⦄ => 'A'
  | ⦃1, 0, 1, 1⦄ => 'B'
  | ⦃1, 1, 0, 0⦄ => 'C'
  | ⦃1, 1, 0, 1⦄ => 'D'
  | ⦃1, 1, 1, 0⦄ => 'E'
  | ⦃1, 1, 1, 1⦄ => 'F'

def Byte.hex0 : Byte → Hex
  | ⦃w, x, y, z, _, _, _, _⦄ => ⦃w, x, y, z⦄

def Byte.hex1 : Byte → Hex
  | ⦃_, _, _, _, w, x, y, z⦄ => ⦃w, x, y, z⦄

def Byte.toString (b : Byte) : String :=
⟨['x', Hex.toChar b.hex0, Hex.toChar b.hex1]⟩

def Byte.toString' (b : Byte) : String :=
⟨[b.hex0.toChar, b.hex1.toChar]⟩

def Bytes.toString : Bytes → String
  | ⟪⟫ => ""
  | ⟪b⟫ => b.toString
  | bs :> b => bs.toString ++ " " ++ Byte.toString b

def Bytes.toString' : Bytes → String
  | ⟪⟫ => "0x"
  | bs :> b => bs.toString' ++ Byte.toString' b

instance : Repr Bytes := ⟨λ b _ => b.toString⟩

def Ox (hx hx' : Hex) : Byte := hx ++ hx'

lemma hex0_eq : ∀ {x y : Hex}, (Ox x y).hex0 = x
| ⦃_, _, _, _⦄, ⦃_, _, _, _⦄ => rfl

def x0 : Hex := ⦃0, 0, 0, 0⦄
def x1 : Hex := ⦃0, 0, 0, 1⦄
def x2 : Hex := ⦃0, 0, 1, 0⦄
def x3 : Hex := ⦃0, 0, 1, 1⦄
def x4 : Hex := ⦃0, 1, 0, 0⦄
def x5 : Hex := ⦃0, 1, 0, 1⦄
def x6 : Hex := ⦃0, 1, 1, 0⦄
def x7 : Hex := ⦃0, 1, 1, 1⦄
def x8 : Hex := ⦃1, 0, 0, 0⦄
def x9 : Hex := ⦃1, 0, 0, 1⦄
def xA : Hex := ⦃1, 0, 1, 0⦄
def xB : Hex := ⦃1, 0, 1, 1⦄
def xC : Hex := ⦃1, 1, 0, 0⦄
def xD : Hex := ⦃1, 1, 0, 1⦄
def xE : Hex := ⦃1, 1, 1, 0⦄
def xF : Hex := ⦃1, 1, 1, 1⦄

def Bytes.length : Bytes → Nat
  | ⟪⟫ => 0
  | bs :> _ => bs.length + 1

def Bytes.sig : Bytes → Bytes
  | ⟪⟫ => ⟪⟫
  | bs :> b =>
  match bs.sig with
  | ⟪⟫ => if b = 0 then ⟪⟫ else ⟪b⟫
  | bs'@(_ :> _) => bs' :> b

lemma Bytes.sig_length_le (bs : Bytes) : bs.sig.length ≤ bs.length := by
  induction bs with
  | nil => simp [Bytes.length]
  | cons bs b ih =>
    unfold Bytes.sig; revert ih
    cases bs.sig with
    | nil =>
      simp; intro _
      apply ite_cases (λ bs' : Bytes => bs'.length ≤ (bs :> b).length) <;>
      intro _ <;> simp [Bytes.length]
    | cons bs' b' =>
      simp; intro h; simp [Bytes.length]; apply h

lemma eq_nil_or_eq_cons (bs : Bytes) : bs = ⟪⟫ ∨ ∃ bs' b, bs = (bs' :> b) := by
  cases bs; left; rfl; right; refine ⟨_, _, rfl⟩

lemma Bits.cons_eq_max {n} (xs : Bits n) (x) : xs +> x = max _ ↔ (xs = max _ ∧ x = 1) := by
  cases x
  · apply iff_of_false <;> intro h
    · cases h
    · cases h.right
  · cases em (xs = max _) with
    | inl h => rw [h]; apply iff_of_true; rfl; simp; rfl
    | inr h =>
      apply iff_of_false <;> intro h'
      · cases h'; cases h rfl
      · cases h h'.left

lemma Bits.lt_or_ge {n : ℕ} : ∀ xs ys : Bits n, xs < ys ∨ xs ≥ ys := by
  induction n with
  | zero => intros _ _; right; apply nil_le_nil
  | succ n ih =>
    intros xs ys
    match xs, ys with
    | xs +> x, ys +> y =>
      rcases ih xs ys with h | h
      · left; left; exact h
      · simp only [GE.ge] at h
        rw [le_iff_lt_or_eq] at h
        rcases h with h | h
        · right; left; exact h
        · rw [h]; cases x
          · cases y
            · right; right; simp
            · left; right; simp; constructor
          · right; right; simp

lemma Bits.not_lt {n : ℕ} (xs ys : Bits n) : ¬ xs < ys ↔ ys ≤ xs := by
  constructor
  · rw [← or_iff_not_imp_left]; apply lt_or_ge
  · intros h h'; cases lt_irrefl <| lt_of_le_of_lt h h'

lemma Bits.exists_eq_cons {n} (xs : Bits (n + 1)) : ∃ xs' x, xs = xs' +> x :=
  by cases xs; refine ⟨_, _, rfl⟩

lemma Bits.toNat_lt_pow {n} : ∀ xs : Bits n, xs.toNat < 2 ^ n := by
  induction n with
  | zero => intro xs; cases xs; simp [Bits.toNat]
  | succ n ih =>
    intro xs
    rcases exists_eq_cons xs with ⟨xs', x, h_eq⟩
    cases h_eq; simp [Bits.toNat, Nat.pow_succ]
    apply @Nat.lt_of_lt_of_le _ (2 * (xs'.toNat + 1))
    · cases x <;> simp [Nat.mul_succ]
    · rw [Nat.mul_comm]; apply Nat.mul_le_mul_right
      rw [Nat.succ_le]; apply ih

lemma Bits.toNat_lt_toNat {k} (xs ys : Bits k) (h : xs < ys) : xs.toNat < ys.toNat := by
  induction k with
  | zero => cases xs; cases ys; cases h
  | succ k ih =>
    match xs, ys with
    | xs +> x, ys +> y =>
      rw [cons_lt_cons] at h
      rcases h with h | ⟨h_eq, h_lt⟩
      · simp [toNat]
        apply @Nat.lt_of_lt_of_le _ (2 * xs.toNat + 2 * 1)
        · apply Nat.add_lt_add_left; cases x <;> simp [Bool.toNat]
        · rw [← Nat.mul_add]
          apply @Nat.le_trans _ (2 * ys.toNat)
          · apply Nat.mul_le_mul_left _ <| Nat.succ_le_of_lt <| ih _ _ h
          · apply Nat.le_add_right
      · cases x <;> cases y <;>
        try {simp [LT.lt] at h_lt; done}
        simp [h_eq, toNat]

lemma Bits.lt_succ_of_le  {k} {xs ys : Bits k}
    (h : ys ≠ max k) (h' : xs ≤ ys) : xs < ys.succ := by
  induction k with
  | zero => cases h nil_eq_nil
  | succ k ih =>
    match xs, ys with
    | xs +> x, ys +> y =>
      rw [cons_le_cons] at h'
      simp [Ne, cons_eq_max] at h; cases y
      · simp [succ]; rcases h' with h' | h'
        · rw [cons_lt_cons]; left; apply h'
        · rw [cons_lt_cons, Bool.eq_false_of_le_false h'.right]
          right; refine ⟨h'.left, cst⟩
      · simp [true_eq_one] at h; simp [succ]
        rw [cons_lt_cons]; left; apply ih h
        apply le_of_lt_or_eq; rcases h' with h' | h'
        · left; exact h'
        · right; exact h'.left

lemma Bits.toNat_le_toNat {k} (xs ys : Bits k) (h : xs ≤ ys) : xs.toNat ≤ ys.toNat := by
  by_cases h' : ys = max k
  · apply Nat.le_of_lt_succ; rw [h', max_toNat_succ]; apply toNat_lt_pow
  · apply Nat.le_of_lt_succ; rw [← succ_toNat_assoc _ h']
    apply toNat_lt_toNat _ _ <| lt_succ_of_le h' h

lemma Bits.nof_of_add_eq_max {k} (xs ys : Bits k) (h : xs + ys = max _) :
    NoOverflow xs ys := by
  induction k with
  | zero => cases xs; cases ys; simp [NoOverflow]; rfl
  | succ k ih =>
    match xs, ys with
    | xs +> x, ys +> y =>
      have h' : xs + ys = max _ ∧ y = !x := by
        cases x <;> cases y
        · simp [cons_add_cons, incr] at h;
          rw [cons_eq_max] at h; simp [true_eq_one] at h
        · simp [cons_add_cons, incr] at h;
          rw [cons_eq_max] at h; refine' ⟨h.left, rfl⟩
        · simp [cons_add_cons, incr, succ] at h;
          rw [cons_eq_max] at h; refine' ⟨h.left, rfl⟩
        · simp [cons_add_cons, incr, succ] at h;
          rw [cons_eq_max] at h; simp at h
      rw [h'.right, nof_iff_not_Overflow]
      unfold Overflow
      simp only [Bits.toNat]
      rw [not_le]
      have hrw :
        2 * toNat xs + x.toNat + (2 * toNat ys + (!x).toNat) =
          2 * (toNat xs + toNat ys) + 1 := by
        rw [Nat.mul_add, Nat.add_assoc, Nat.add_assoc]
        simp; rw [Nat.add_comm, Nat.add_assoc]
        cases x <;> rfl
      rw [hrw, Nat.pow_succ, Nat.mul_comm (_ ^ _), Nat.lt_floor_left (by simp)]
      apply Nat.mul_lt_mul_of_pos_left _ (by simp)
      apply ih  _ _ h'.left

lemma Bits.cons_Overflow_cons {k} {xs ys : Bits k} {x y} (h : xs ↟ ys) : (xs +> x) ↟ (ys +> y) := by
  simp [Overflow, Bits.toNat, Nat.pow_succ, Nat.mul_comm]
  apply Nat.le_trans <| Nat.mul_le_mul_left 2 h
  simp [Nat.mul_add]; rw [Nat.add_assoc, Nat.mul_comm]
  simp; apply Nat.le_trans _ <| Nat.le_add_left _ _
  rw [Nat.mul_comm]; apply Nat.le_add_right

lemma Bits.of_cons_nof_cons {k} {xs ys : Bits k} {x y} :
    NoOverflow (xs +> x) (ys +> y) → NoOverflow xs ys := by
  simp [nof_iff_not_Overflow]; apply mt cons_Overflow_cons

lemma Bits.add_toNat {k} (xs ys : Bits k) (h : NoOverflow xs ys) :
    (xs + ys).toNat = xs.toNat + ys.toNat := by
  induction k with
  | zero => simp [nil_toNat]
  | succ k ih =>
    match xs, ys with
    | xs +> x, ys +> y =>
      by_cases h_eq : (xs + ys) +> y = max _
      · rw [cons_eq_max] at h_eq
        cases x
        · rw [cons_add_cons]
          simp only [incr, id, toNat]
          rw [ih _ _ <| nof_of_add_eq_max _ _ h_eq.left]
          rw [h_eq.right]
          simp [Bool.one_toNat]
          rw [Nat.mul_add, Nat.add_assoc]
        · cases h_eq.right
          simp [NoOverflow, toNat, Bool.one_toNat] at h
          have h_rw : 2 * xs.toNat + 1 + (2 * ys.toNat + 1) = 2 ^ k * 2 := by
            rw [Nat.mul_comm _ 2, ← max_toNat_succ, ← h_eq.left]
            rw [ih _ _ <| nof_of_add_eq_max _ _ h_eq.left]; omega
          rw [h_rw, Nat.pow_succ] at h; simp [lt_irrefl] at h
      · simp [cons_add_cons]
        rw [incr_toNat_assoc _ _ h_eq]; simp [toNat]
        rw [ih _ _ <| of_cons_nof_cons h, Nat.mul_add]
        rw [Nat.add_assoc, Nat.add_assoc, Nat.add_assoc]
        apply congr_arg (2 * xs.toNat + ·)
        rw [← Nat.add_assoc, Nat.add_comm]

lemma Bits.sub_toNat {k} (xs ys : Bits k) (h : ys ≤ xs) :
    (xs - ys).toNat = xs.toNat - ys.toNat := by
  induction k with
  | zero => simp [nil_toNat]
  | succ k ih =>
    match xs, ys with
    | xs +> x, ys +> y =>
      by_cases hd : (xs - ys) +> x = 0
      · rw [cons_eq_zero] at hd
        have h_eq : xs = ys := by
          have h := congr_arg (λ zs => zs + ys) hd.left
          simp [sub_add_cancel, zero_add] at h; exact h
        have h_eq' : y = 0 := by
          rw [h_eq, hd.right, cons_le_cons] at h
          simp [Bits.lt_irrefl] at h
          cases y
          · apply false_eq_zero
          · simp [LE.le] at h
        rw [h_eq, h_eq', hd.right, sub_self, Nat.sub_self, zero_toNat]
      · rw [cons_sub_cons]
        rw [decr_toNat_assoc _ _ hd]
        simp only [toNat]; rw [cons_le_cons] at h
        rcases h with h | h
        · rw [ih _ _ <| Bits.le_of_lt h]
          rw [Nat.mul_sub_left_distrib, Nat.sub_add_eq]
          apply congr_arg₂ _ _ rfl
          rw [← Nat.sub_add_comm]
          rw [Nat.mul_le_mul_iff (by simp)]
          apply Nat.le_of_lt <| toNat_lt_toNat _ _ h
        · rw [h.left, sub_self, zero_toNat, Nat.mul_zero, Nat.zero_add]
          rw [Nat.add_comm, Nat.sub_add_eq]
          rw [Nat.add_sub_assoc <| Nat.le_refl _]
          rw [Nat.sub_self, Nat.add_zero]

lemma Bits.append_eq_append_iff {m n} {xs ys : Bits m} {xs' ys' : Bits n} :
    xs ++ xs' = ys ++ ys' ↔ (xs = ys ∧ xs' = ys') := by
  revert xs xs' ys ys' m
  induction n with
  | zero =>
    intros m xs ys xs' ys'
    cases xs'; cases ys'
    simp [Bits.append_nil]
  | succ n ih =>
    intros m xs ys xs' ys'
    rcases xs' with _ | ⟨xs', x⟩
    rcases ys' with _ | ⟨ys', y⟩
    simp [Bits.append_cons]
    rw [ih]; simp [and_assoc]

lemma Bits.toBytes_length {n} (xs : Bits (8 * n)) : xs.toBytes.length = n := by
  induction n with
  | zero => cases xs; rfl
  | succ n ih =>
    match xs with
    | bs +> _ +> _ +> _ +> _ +> _ +> _ +> _ +> _ =>
      simp [toBytes, Bytes.length]; apply ih

lemma Bits.toBytes_toBits {n} (xs : Bits (8 * n)) : Bytes.toBits n (toBytes xs) = xs := by
  induction n with
  | zero => cases xs; rfl
  | succ n ih =>
    match xs with
    | _ +> _ +> _ +> _ +> _ +> _ +> _ +> _ +> _ =>
      simp [toBytes, Bytes.toBits]; rw [ih]; rfl

lemma Bits.succ_append {m n} (xs : Bits m) (ys : Bits n) :
    (xs ++ ys).succ = incr (if ys = max _ then 1 else 0) xs ++ ys.succ := by
  induction ys with
  | nil => rw [if_pos nil_eq_nil]; rfl
  | cons ys y ih =>
    cases y <;> simp only [succ]
    · rw [if_neg]; rfl; simp [cons_eq_max]
    · apply congrArg₂ _ (Eq.trans ih _) rfl
      by_cases h : ys = max _
      · rw [if_pos h, if_pos]; rfl
        simp [cons_eq_max, h, Bool.one]
      · rw [if_neg h, if_neg]; rfl
        simp [cons_eq_max, h]

lemma Bits.succ_append_eq_of_ne {m n} (xs : Bits m) (ys : Bits n) (h : ys ≠ max _) :
    (xs ++ ys).succ = xs ++ ys.succ := by rw [succ_append, if_neg h]; rfl

lemma Bits.toBytes_append {n} {xs : Bits (8 * n)} :
    ∀ {ys : Byte}, @toBytes (n + 1) (xs ++ ys) = toBytes xs :> ys
  | ⦃_, _, _, _, _, _, _, _⦄ => rfl

lemma Bits.max_eq_cons {n} : (max _ : Bits (n + 1)) = (max _ : Bits n) +> 1 := rfl

lemma Bits.append_eq_max {m n} {xs : Bits m} {ys : Bits n} :
    xs ++ ys = max (m + n) ↔ xs = max m ∧ ys = max n := by
  induction ys with
  | nil => constructor <;> intro h; refine ⟨h, rfl⟩; apply h.left
  | cons ys y ih =>
    rename Nat => k; rw [append_cons, max_eq_cons]
    conv => lhs; rhs; apply (@max_eq_cons (m + k)).symm
    simp [max_eq_cons]; rw [ih, and_assoc]

def Bytes.append : Bytes → Bytes → Bytes
  | xs, ⟪⟫ => xs
  | xs, ys :> y => append xs ys :> y

instance : HAppend Bytes Bytes Bytes := ⟨Bytes.append⟩

def Bytes.mem : Bytes → Byte → Prop
  | ⟪⟫, _ => False
  | bs :> b, b' => mem bs b' ∨ b = b'

instance : Membership Byte Bytes := ⟨Bytes.mem⟩

def Bytes.zero : Bytes → Prop
  | ⟪⟫ => True
  | xs :> x => zero xs ∧ x = 0

lemma Bytes.zero_of_sig_eq_nil {bs : Bytes} : bs.sig = ⟪⟫ → bs.zero := by
  induction bs with
  | nil => intro _; constructor
  | cons bs b ih =>
    simp [sig]
    rcases eq_nil_or_eq_cons bs.sig with h_nil | h_cons
    · simp [h_nil]; intro h; refine ⟨ih h_nil, h⟩
    · rcases h_cons with ⟨bs', b, h⟩; simp [h]

lemma Bytes.append_cons {xs ys : Bytes} {y} : xs ++ (ys :> y) = ((xs ++ ys) :> y) := by
  simp [HAppend.hAppend, append]

lemma Bytes.append_inj' {xs₁ xs₂ ys₁ ys₂ : Bytes} :
    xs₁ ++ xs₂ = ys₁ ++ ys₂ →
    xs₂.length = ys₂.length →
    xs₁ = ys₁ ∧ xs₂ = ys₂ := by
  revert ys₂
  induction xs₂ with
  | nil =>
    intros ys₂ h_eq h_len
    cases ys₂ with
    | nil => refine' ⟨h_eq, rfl⟩
    | cons _ _ => cases h_len
  | cons xs₂ x ih =>
    intros ys₂ h_eq h_len
    cases ys₂ with
    | nil => cases h_len
    | cons ys₂ y =>
      simp [append_cons] at h_eq
      rcases h_eq with ⟨h_eq, ⟨_⟩⟩
      simp [length] at h_len
      simp; apply ih h_eq h_len

lemma Bytes.length_append (xs ys : Bytes) : (xs ++ ys).length = xs.length + ys.length := by
  induction ys with
  | nil => rfl
  | cons ys y ih =>
    simp [append_cons, length]
    rw [← Nat.add_assoc, ← ih]; rfl

lemma Bytes.append_inj {xs₁ xs₂ ys₁ ys₂ : Bytes}
    (h_eq : xs₁ ++ xs₂ = ys₁ ++ ys₂)
    (h_len : xs₁.length = ys₁.length) : xs₁ = ys₁ ∧ xs₂ = ys₂ := by
  apply append_inj' h_eq
  apply @Nat.add_left_cancel ys₁.length
  have h := congrArg length h_eq
  simp [length_append, h_len] at h; rw [h]

lemma Bytes.prefix_unique {xs ys zs : Bytes}
    (h_len : xs.length = ys.length)
    (h_xs : xs <<+ zs)
    (h_ys : ys <<+ zs) : xs = ys := by
  rcases h_xs with ⟨sfx, h⟩
  rcases h_ys with ⟨sfx', h'⟩
  apply And.left <| append_inj (Eq.trans h.symm h') h_len

lemma Bytes.singleton_inj {x y} (h : ⟪x⟫ = ⟪y⟫) : x = y := by cases h; rfl

lemma Bytes.append_assoc (as bs cs : Bytes) : as ++ bs ++ cs = as ++ (bs ++ cs) := by
  induction cs with
  | nil => rfl
  | cons cs c ih => simp [append_cons, ih]

lemma Bytes.prefix_trans {xs ys zs : Bytes}
    (h : xs <<+ ys) (h' : ys <<+ zs) : xs <<+ zs := by
  rcases h with ⟨sfx, h_sfx⟩
  rcases h' with ⟨sfx', h_sfx'⟩
  refine' ⟨sfx ++ sfx', _⟩
  rw [h_sfx', h_sfx]
  apply append_assoc

lemma Bytes.length_eq_zero {xs : Bytes} : xs.length = 0 ↔ xs = ⟪⟫ := by
cases xs <;> simp [length]

lemma Bytes.split_nil {xs ys : Bytes} : (xs <++ ⟪⟫ ++> ys) ↔ (xs = ⟪⟫ ∧ ys = ⟪⟫) := by
  match xs with
  | ⟪⟫ =>
    match ys with
    | ⟪⟫ => simp; rfl
    | ys :> y => simp; intro h; cases h
  | xs :> x => cases ys <;> {simp; intro h; cases h}

lemma Bytes.prefix_nil {xs : Bytes} : xs <<+ ⟪⟫ ↔ xs = ⟪⟫ := by
  constructor <;> intro h
  · rcases h with ⟨ys, h⟩; rw [split_nil] at h; apply h.left
  · rw [h]; refine ⟨⟪⟫, rfl⟩

lemma Bytes.length_snoc {xs x} : length (⟪x⟫ ++ xs) = xs.length + 1 := by
  simp [length_append, Nat.add_comm, length]

def Bytes.succ : Bytes → Bytes
  | ⟪⟫ => ⟪⟫
  | xs :> x =>
    if x = Ox xF xF
    then succ xs :> 0
    else xs :> x.succ

lemma Bytes.succ_cons_max_eq {xs} : (xs :> Ox xF xF).succ = succ xs :> 0 := by
  simp only [Bytes.succ]; rw [if_pos cst]

lemma Bytes.succ_cons_eq_of_ne {xs x} (h : x ≠ Ox xF xF) : (xs :> x).succ = xs :> x.succ := by
  unfold Bytes.succ; rw [if_neg h]

def Bytes.max : Bytes → Prop
  | ⟪⟫ => True
  | xs :> x => max xs ∧ x = Ox xF xF

lemma Bytes.toBits_eq_zero {n} : ∀ {xs}, zero xs → toBits n xs = 0 := by
  induction n with
  | zero => intros _ _; rfl
  | succ n ih =>
    intro xs h; match xs with
    | ⟪⟫ => simp [toBits]; rw [ih (by constructor)]; rfl
    | xs :> x => simp [h.right, toBits]; rw [ih h.left]; rfl

lemma Bytes.of_toBits_succ_eq_toBits_succ {n} {bs bs' : Bytes} :
    toBits (n + 1) bs = toBits (n + 1) bs' → toBits n bs = toBits n bs' := by
  induction n generalizing bs bs' with
  | zero => intro _; rfl
  | succ n ih =>
    match bs, bs' with
    | nil, nil => simp [toBits]
    | nil, cons bs' b' =>
      simp [toBits]; intro h
      rw [Bits.append_eq_append_iff] at h
      rw [@ih nil bs' h.left, h.right]
    | cons bs b, nil =>
      simp [toBits]; intro h
      rw [Bits.append_eq_append_iff] at h
      rw [@ih nil bs h.left.symm, h.right]
    | cons bs b, cons bs' b' =>
      simp [toBits]; intro h
      rw [Bits.append_eq_append_iff] at h
      rw [ih h.left, h.right]

lemma Bytes.sig_toBits {n} (bs : Bytes) : bs.sig.toBits n = bs.toBits n := by
  induction bs with
  | nil => rfl
  | cons bs b ih =>
    rcases eq_nil_or_eq_cons bs.sig with h_nil | h_cons
    · simp [sig]; simp [h_nil]
      by_cases hb : b = 0
      · rw [if_pos hb]
        rw [@toBits_eq_zero n (bs :> b) ⟨zero_of_sig_eq_nil h_nil, hb⟩]
        apply toBits_eq_zero; constructor
      · rw [if_neg hb]
        cases n with
        | zero => rfl
        | succ n =>
          simp [toBits]
          rw [← of_toBits_succ_eq_toBits_succ ih, h_nil]
    · rcases h_cons with ⟨bs', b', h_sig⟩
      simp [sig]; simp [h_sig]
      cases n with
      | zero => rfl
      | succ n =>
        simp [toBits]
        rw [← of_toBits_succ_eq_toBits_succ ih, h_sig]

lemma Bytes.nil_append {xs} : ⟪⟫ ++ xs = xs := by
  induction xs with
  | nil => rfl
  | cons xs x ih => rw [append_cons, ih]

lemma Bytes.append_eq_nil {xs ys} : xs ++ ys = ⟪⟫ ↔ (xs = ⟪⟫ ∧ ys = ⟪⟫) := by
  rw [@Eq.comm _ _ ⟪⟫]; apply Bytes.split_nil

lemma Bytes.toBits_succ {n} {xs : Bytes} :
    ¬ xs.max → Bytes.toBits n xs.succ = (Bytes.toBits n xs).succ := by
  revert xs
  induction n with
  | zero => intros _ _; simp [Bytes.toBits]; rfl
  | succ n ih =>
    intro xs h
    match xs with
    | ⟪⟫ => cases h (by constructor)
    | xs :> x =>
      cases em (x = Ox xF xF) with
      | inl hx =>
        rw [hx]; simp [Bytes.succ, Bytes.toBits, Bits.succ]
        rw [ih _]; rfl; intro hc; apply h; refine ⟨hc, hx⟩
      | inr hx =>
        rw [Bytes.succ_cons_eq_of_ne hx]; simp [Bytes.toBits]
        rw [Bits.succ_append_eq_of_ne _]; apply hx

lemma Bits.toBytes_succ {n} {xs : Bits (8 * n)} :
    xs.succ.toBytes = Bytes.succ xs.toBytes := by
  revert xs
  induction n with
  | zero => simp [Nat.mul_zero]; intro xs; cases xs; rfl
  | succ n ih =>
    simp [Nat.mul_succ]; intro xs
    rw [← @Bits.head_append_tail (8 * n) 8 xs]
    cases em (xs.tail = Ox xF xF) with
    | inl h =>
      rw [h]; simp only [Bits.toBytes]
      apply Eq.trans _ <| Eq.symm Bytes.succ_cons_max_eq
      rw [ih]; rfl
    | inr h =>
      rw [Bits.succ_append_eq_of_ne _]
      simp [Bits.toBytes_append]
      rw [Bytes.succ_cons_eq_of_ne h]
      apply h

def slice (bs : Bytes) (loc : Nat) (sc : Bytes) : Prop :=
  ∃ pfx sfx, (pfx <++ bs ++> sfx) ∧ (sc <<+ sfx) ∧ pfx.length = loc

lemma slice_refl (bs : Bytes) : slice bs 0 bs := by
  refine' ⟨⟪⟫, bs, Eq.symm Bytes.nil_append, ⟨⟪⟫, rfl⟩, rfl⟩

def sliceFill (bs : Bytes) (loc sz : Nat) (sc : Bytes) : Prop :=
  (slice bs loc sc ∧ sc.length = sz) ∨
  ∃ pfx sfx zrs,
    (pfx <++ bs ++> sfx) ∧
    (sfx <++ sc ++> zrs) ∧
    pfx.length = loc ∧
    sc.length = sz ∧
    Bytes.zero zrs

lemma slice_unique {xs ys zs : Bytes} {k}
    (h_eq : ys.length = zs.length)
    (h_ys : slice xs k ys)
    (h_zs : slice xs k zs) : ys = zs := by
  simp [slice] at h_ys
  rcases h_ys with ⟨pfx, sfx, h_split, h_pfx, h_len⟩
  rcases h_zs with ⟨pfx', sfx', h_split', h_pfx', h_len'⟩
  cases
    And.right <|
      Bytes.append_inj
        (Eq.trans h_split.symm h_split')
          (Eq.trans h_len h_len'.symm)
  apply Bytes.prefix_unique h_eq h_pfx h_pfx'

lemma slice_singleton_unique {xs : Bytes} {k} {x y}
    (h : slice xs k ⟪x⟫) (h' : slice xs k ⟪y⟫) : x = y := by
  apply Bytes.singleton_inj <| slice_unique _ h h'; rfl

lemma slice_prefix {xs ys zs : Bytes} {k} (h : slice xs k (ys ++ zs)) :
    slice xs k ys := by
  rcases h with ⟨pfx, sfx, h_xs, h_sfx, h_len⟩
  refine' ⟨pfx, sfx, h_xs, _, h_len⟩
  apply Bytes.prefix_trans (pref_append _ _) h_sfx

lemma slice_suffix {xs ys zs : Bytes} {k} (h : slice xs k (ys ++ zs)) :
    slice xs (k + ys.length) zs := by
  rcases h with ⟨pfx, sfx, h_xs, h_sfx, h_len⟩
  rcases h_sfx with ⟨sfx', h_sfx⟩
  refine' ⟨pfx ++ ys, zs ++ sfx', _, pref_append _ _, _⟩
  · rw [h_xs, h_sfx]; unfold Split; simp [← Bytes.append_assoc]
  · rw [← h_len]; apply Bytes.length_append

lemma append_slice_suffix {xs ys} : slice (xs ++ ys) xs.length ys := by
  have h := slice_suffix <| slice_refl <| xs ++ ys
  rw [Nat.zero_add] at h; exact h

lemma zero_toBytes_zero {n} : (@Bits.toBytes n 0).zero := by
  induction n with
  | zero => constructor
  | succ n ih => simp [Bits.toBytes, Bytes.zero]; refine ⟨ih, rfl⟩

lemma Bits.zero_ne_one : ∀ {n}, (0 : Bits (n + 1)) ≠ (1 : Bits (n + 1))
  | 0, h => by cases h
  | n + 1, h => by cases h

lemma Bits.invert_zero_eq_max {n} : ~ (0 : Bits n) = max _ := by
  induction n with
  | zero => apply nil_eq_nil
  | succ n ih => rw [zero_eq_cons]; simp only [max, not]; rw [ih]; rfl

lemma Bits.max_and {n} {xs : Bits n} : and (max n) xs = xs := by
  induction n with
  | zero => apply nil_eq_nil
  | succ n ih =>
    cases xs with
    | cons xs x =>
      simp [max]
      rw [cons_and_cons]
      simp [Nat.add] at ih
      rw [@ih xs]
      cases x <;> rfl

lemma Bits.zero_and {n} {xs : Bits n} : and (0 : Bits n) xs = 0 := by
  induction n with
  | zero => apply nil_eq_nil
  | succ n ih =>
    cases xs with
    | cons xs x =>
      rw [zero_eq_cons, cons_and_cons, ih]
      cases x <;> rfl

lemma Bits.zipWith_comm (f : Bool → Bool → Bool)
    (hf : ∀ x y, f x y = f y x) (n) :
    ∀ x y : Bits n, zipWith f x y = zipWith f y x := by
  induction n with
  | zero => intro xs ys; apply nil_eq_nil
  | succ n ih =>
    intros xs ys
    match xs, ys with
    | xs +> x, ys +> y =>
      simp [zipWith, ih xs ys, hf x y]

lemma Bits.and_comm {n} : ∀ (x y : Bits n), and x y = and y x := by
  apply zipWith_comm; apply Bool.and_comm

lemma Bool.toNat_inj (x y : Bool) : x.toNat = y.toNat → x = y := by
  cases x <;> cases y <;> simp

lemma Bits.toNat_inj {k} (xs ys : Bits k) (h : xs.toNat = ys.toNat) : xs = ys := by
  induction k with
  | zero => apply Bits.nil_eq_nil
  | succ k ih =>
    match xs, ys with
    | xs +> x, ys +> y =>
      simp [Bits.toNat] at h
      cases Nat.eq_floor (Bool.toNat_lt _) (Bool.toNat_lt _) h
      rw [ih xs ys asm, Bool.toNat_inj x y asm]

lemma toNat_toBits {k : ℕ} {xs : Bits k} : (Nat.toBits k <| Bits.toNat xs) = xs := by
  apply Bits.toNat_inj; rw [toBits_toNat _ (Bits.toNat_lt_pow _)]

lemma Bits.of_toNat_le_toNat {k : ℕ} {xs ys : Bits k}
    (h : xs.toNat ≤ ys.toNat) : xs ≤ ys := by
  have h' := toBits_le_toBits h (toNat_lt_pow _)
  rw [toNat_toBits, toNat_toBits] at h'; exact h'

lemma Bits.le_add_right {n} {xs ys : Bits n} (h : NoOverflow xs ys) : xs ≤ xs + ys := by
  apply of_toNat_le_toNat; rw [add_toNat _ _ h]; apply Nat.le_add_right
