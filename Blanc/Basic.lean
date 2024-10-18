


-- Basic.lean : generic definitions and lemmas (e.g. for Booleans, lists,
-- bit vectors and bytes) that are useful for but not specific to Blanc

import Mathlib.Data.Nat.Defs
import Mathlib.Data.List.Lemmas
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

lemma cond_elim {ξ : Type u} (π : ξ → Prop) (b : Bool) (x y : ξ)
    (h : b = true → π x) (h' : b = false → π y) : π (cond b x y) := by
  cases b; apply h' rfl; apply h rfl

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
  | cons : ∀ {n : ℕ}, Bool → Bits n → Bits (n + 1)

abbrev Addr := Bits 160
abbrev Word := Bits 256

notation "⦃⦄" => Bits.nil

infixr:70 " +> " => Bits.cons

syntax "⦃" withoutPosition(term,*,?) "⦄"  : term
macro_rules
  | `(⦃$l,*⦄) => `(expand_foldr% (h t => Bits.cons h t) Bits.nil [$(.ofElems l),*])

abbrev Byte := Bits 8

abbrev Bytes : Type := List Byte
-- inductive Bytes : Type
--   | nil : Bytes
--   | cons : Bytes → Byte → Bytes

-- infixl:70 " :> " => Bytes.cons
--
-- syntax "[" withoutPosition(term,*,?) "]"  : term
-- macro_rules | `([$l,*]) => `(expand_foldl% (h t => Bytes.cons h t) Bytes.nil [$(.ofElems l),*])

def Bits.toChars : ∀ {n}, Bits n → List Char
  | 0, ⦃⦄ => []
  | _ + 1, x +> xs => x.toChar :: xs.toChars

def Bits.toString {n} (bs : Bits n) : String := ⟨bs.toChars⟩

instance {n} : Repr (Bits n) := ⟨λ bs _ => Bits.toString bs⟩

def Bits.not : ∀ {n}, Bits n → Bits n
  | 0, ⦃⦄ => ⦃⦄
  | _, (x +> xs) => x.not +> xs.not

notation "~" => Bits.not

def Bits.zipWith (f : Bool → Bool → Bool) : ∀ {n}, Bits n → Bits n → Bits n
  | 0, ⦃⦄, ⦃⦄ => ⦃⦄
  | _, x +> xs, y +> ys => f x y +> (zipWith f xs ys)

def Bits.and {n} : Bits n → Bits n → Bits n := zipWith Bool.and
def Bits.or {n} : Bits n → Bits n → Bits n := zipWith Bool.or
def Bits.xor {n} : Bits n → Bits n → Bits n := zipWith Bool.xor

lemma Bits.cons_and_cons {n} {xs ys : Bits n} {x y} :
  and (x +> xs) (y +> ys) = .and x y +> and xs ys := rfl

def Bits.lt : ∀ {n : ℕ}, Bits n → Bits n → Prop
  | 0, ⦃⦄, ⦃⦄ => False
  | _, x +> xs, y +> ys => x < y ∨ (x = y ∧ lt xs ys)

def Bits.lt' : ∀ {n : ℕ}, Bits n → Bits n → Bool
  | 0, ⦃⦄, ⦃⦄ => false
  | _, x +> xs, y +> ys => (!x && y) || (x == y && lt' xs ys)

instance {n} : @LT (Bits n) := ⟨Bits.lt⟩

def Bits.le : ∀ {n : ℕ}, Bits n → Bits n → Prop
  | 0, ⦃⦄, ⦃⦄ => True
  | _, x +> xs, y +> ys => x < y ∨ (x = y ∧ le xs ys)

instance {n} : @LE (Bits n) := ⟨Bits.le⟩

lemma Bits.cons_lt_cons {n} {x y} {xs ys : Bits n} :
    x +> xs < y +> ys ↔ (x < y ∨ (x = y ∧ xs < ys)) := Iff.refl _

-- lemma Bits.cons_lt_cons' {n} {xs ys : Bits n} {x} :
--     x +> xs < ys +> x ↔ xs < ys := by simp [cons_lt_cons]
--
lemma Bits.cons_eq_cons {n} {x y} {xs ys : Bits n} :
    x +> xs = y +> ys ↔ (x = y ∧ xs = ys) := by simp

lemma Bits.cons_le_cons {n} {xs ys : Bits n} {x y} :
    x +> xs ≤ y +> ys ↔ (x < y ∨ (x = y ∧ xs ≤ ys)) := Iff.refl _

instance {n : ℕ} (xs ys : Bits n) : Decidable (xs = ys) := by
  induction n with
  | zero => cases xs; cases ys; apply Decidable.isTrue rfl
  | succ n ih =>
    match xs, ys with
    | x +> xs, y +> ys =>
      rw [Bits.cons_eq_cons]; apply instDecidableAnd

instance {n} {xs ys : Bits n} : Decidable (xs < ys) := by
  induction n with
  | zero =>
    cases xs; cases ys; simp [LT.lt, Bits.lt]
    apply Decidable.isFalse not_false
  | succ n ih =>
    match xs, ys with
    | x +> xs, y +> ys =>
      cases x <;> cases y <;>
      simp [Bits.cons_lt_cons, false_lt_true, not_true_lt] <;>
      try {apply ih}; apply instDecidableTrue; apply instDecidableFalse

instance {n : ℕ} (xs ys : Bits n) : Decidable (xs ≤ ys) := by
  induction n with
  | zero =>
    cases xs; cases ys;
    apply Decidable.isTrue; constructor
  | succ n =>
    match xs, ys with
    | x +> xs, y +> ys =>
      rw [Bits.cons_le_cons]; apply instDecidableOr

def Bits.slt : ∀ {n : ℕ}, Bits n → Bits n → Prop
  | 0, ⦃⦄, ⦃⦄ => False
  | _ + 1, x +> xs, y +> ys => y < x ∨ (x = y ∧ xs < ys)

infix:70 " ±< " => Bits.slt

lemma Bits.singleton_slt_singleton {x y : Bool} :
    ⦃x⦄ ±< ⦃y⦄ ↔ (x = 1 ∧ y = 0) := by
  cases x <;> cases y <;>
  simp [Bool.zero, Bool.one, Bits.slt] <;>
  try {intro hc; cases hc}

def Bits.sgt {n : ℕ} (xs ys : Bits n) : Prop := slt ys xs

infix:70 " ±> " => Bits.sgt

def Bits.toNat : ∀ {n : ℕ}, Bits n → Nat
  | 0, ⦃⦄ => 0
  | n + 1, x +> xs => (cond x (2 ^ n) 0) + xs.toNat

def Bits.zero : ∀ n : ℕ, Bits n
  | 0 => ⦃⦄
  | n + 1 => 0 +> zero n

instance {n} : @Zero (Bits n) := ⟨Bits.zero n⟩

instance : @Zero Byte := ⟨Bits.zero 8⟩

def Bits.max : ∀ n : ℕ, Bits n
  | 0 => ⦃⦄
  | n + 1 => 1 +> max n

def Bits.one : ∀ n : ℕ, Bits n
  | 0 => ⦃⦄
  | n + 1 => 0 +> one n

instance {n} : @One (Bits n) := ⟨Bits.one n⟩

def Bits.rec2 {μ : ∀ n, Bits n → Bits n → Sort u}
    (nil : μ 0 ⦃⦄ ⦃⦄)
    (cons : ∀ {n} x xs y ys, μ n xs ys → μ (n + 1) (x +> xs) (y +> ys))
    {n} (xs ys : Bits n) : μ n xs ys := by
  induction n with
  | zero => cases xs; cases ys; exact nil
  | succ n ih =>
    match xs, ys with
    | x +> xs, y +> ys => apply cons; apply ih

  --| succ n =>
-- def Bits.carrySucc : ∀ {n}, Bits n → (Bool × Bits n)
--   | 0, ⦃⦄ => (1, ⦃⦄)
--   | _ + 1, x +> xs =>
--     let (y, ys) := xs.carrySucc
--     (x && y, (x != y) +> ys)
--
def Bits.isMax : ∀ {n}, Bits n → Bool
  | 0, ⦃⦄ => true
  | _ + 1, x +> xs => x && xs.isMax

def Bits.succ : ∀ {n}, Bits n →  Bits n
  | 0, ⦃⦄ => ⦃⦄
  | _ + 1, x +> xs => (x != xs.isMax) +> xs.succ

lemma Bits.succ_inj {n} {xs ys : Bits n} : xs.succ = ys.succ → xs = ys := by
  apply @Bits.rec2 (λ _ xs ys => xs.succ = ys.succ → xs = ys) (λ _ => rfl)
  intro n x xs y ys ih h; simp only [succ, cons_eq_cons] at h
  rcases h with ⟨h, h'⟩; cases ih h';
  rw [Bool.xor_right_inj] at h; cases h; rfl

def Bits.succs {n} : Nat → Bits n → Bits n
  | 0, xs => xs
  | n + 1, xs => succs n xs.succ

def Bits.incr {n} : Bool → Bits n → Bits n
  | false => id
  | true => Bits.succ

def Bits.carryAdd : ∀ {n}, Bits n → Bits n → (Bool × Bits n)
  | 0, ⦃⦄, ⦃⦄ => (0, ⦃⦄)
  | _ + 1, x +> xs, y +> ys =>
    let (z, zs) := carryAdd xs ys
    ((x && y) || (x && z) || (y && z), ((x != y) != z) +> zs)

---def Bits.add {n} (xs ys : Bits n) : Bits n := (carryAdd xs ys).snd


def Overflow {n : ℕ} (xs ys : Bits n) : Prop := 2 ^ n ≤ xs.toNat + ys.toNat

def overflow : ∀ {n : ℕ}, Bits n → Bits n → Bool
| 0, ⦃⦄, ⦃⦄ => false
| _ + 1, x +> xs, y +> ys => (x && y) || ((x != y) && overflow xs ys)


def Bits.add : ∀ {n : ℕ}, Bits n → Bits n → Bits n
  | 0, ⦃⦄, ⦃⦄ => ⦃⦄
  | _ + 1, x +> xs, y +> ys =>
    ((x != y) != overflow xs ys) +> (add xs ys)
    --let (z, zs) := carryAdd xs ys
    --((x && y) || (x && z) || (y && z), ((x != y) != z) +> zs)


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

def Nof {n : ℕ} (xs ys : Bits n) : Prop := xs.toNat + ys.toNat < 2 ^ n

def Bits.nof_iff_not_overflow {n : ℕ} (xs ys : Bits n) : Nof xs ys ↔ ¬ xs ↟ ys := by
  simp [Overflow, Nof]

--def Bits.pred : ∀ {n}, Bits n → Bits n
--  | 0, ⦃⦄ => ⦃⦄
--  | _ + 1, xs +> 0 => xs.pred +> 1
--  | _ + 1, xs +> 1 => xs +> 0
--
--def Bits.decr {n} : Bool → Bits n → Bits n
--  | false, xs => xs
--  | true, xs => xs.pred

def Bits.carrySub : ∀ {n}, Bits n → Bits n → (Bool × Bits n)
  | 0, ⦃⦄, ⦃⦄ => (0, ⦃⦄)
  | n + 1, x +> xs, y +> ys =>
    let (z, zs) := carrySub xs ys
    ((!x && (y != z)) || (y && z), ((x != y) != z) +> zs)

lemma Bits.cons_carrySub_cons {n} (x y) (xs ys : Bits n) :
  carrySub (x +> xs) (y +> ys) =
    ((!x && (y != (carrySub xs ys).fst)) || (y && (carrySub xs ys).fst), ((x != y) != (carrySub xs ys).fst) +> (carrySub xs ys).snd) := rfl

-- def Bits.sub {n} : Bits n → Bits n → Bits n --:= (carrySub xs ys).snd
--   | ⦃⦄, ⦃⦄ => ⦃⦄
--   | x +> xs, y +> ys => ((x != y) != decide (xs < ys)) +> sub xs ys

def Bits.sub {n} : Bits n → Bits n → Bits n --:= (carrySub xs ys).snd
  | ⦃⦄, ⦃⦄ => ⦃⦄
  | x +> xs, y +> ys => ((x != y) != lt' xs ys) +> sub xs ys

-- def Bits.sub {n} (xs ys : Bits n) : Bits n := (carrySub xs ys).snd

instance {n} : HAdd (Bits n) (Bits n) (Bits n) := ⟨Bits.add⟩

instance {n} : HSub (Bits n) (Bits n) (Bits n) := ⟨Bits.sub⟩


lemma Bits.lt_irrefl {n} {xs : Bits n} : ¬ xs < xs := by
  intro h;
  induction n with
  | zero => cases xs; cases h  --simp [LT.lt, lt]
  | succ n ih =>
    match xs with
    | x +> xs =>
      rcases h with h | h
      · apply Bool.lt_irrefl _ h
      · apply ih h.right

lemma Bits.nil_eq_nil {x y : Bits 0} : x = y := by cases x; cases y; rfl

lemma Bits.cons_sub_cons {n} {x y} {xs ys : Bits n} :
  (x +> xs) - (y +> ys) = ((x != y) != lt' xs ys) +> (xs - ys) := rfl

lemma Bits.cons_add_cons {n} {x y} {xs ys : Bits n} :
    (x +> xs) + (y +> ys) = ((x != y) != overflow xs ys) +> (xs + ys) := rfl

-- #exit
-- lemma Bits.cons_sub_cons {n} {x y} {xs ys : Bits n} :
--     carrySub (x +> xs) (y +> ys) =
--       ⟨(!x && (y != (xs < ys))) || (y && (xs < ys)), ((x != y) != (xs < ys)) +> (xs - ys)⟩ := by
--   induction n generalizing x y with
--   | zero =>
--     cases xs; cases ys
--     simp [carrySub, Bool.zero, lt_irrefl]
--     apply nil_eq_nil
--   | succ n ih =>
--     match xs, ys with
--     | x' +> xs, y' +> ys =>
--       rw [cons_carrySub_cons x y, ih]
--       apply congr_arg₂
--       · apply congr_arg₂
--         · apply congr_arg₂
--           · rfl
--           · simp;
--
































--     x +> xs - y +> ys = decr y ((xs - ys) +> x) := rfl


-- lemma Bits.cons_add_cons {n} {xs ys : Bits n} {x y} :
--     x +> xs + y +> ys = incr x ((xs + ys) +> y) := rfl
--
-- lemma Bits.cons_zero_add_cons {n} {xs ys : Bits n} {y} :
--     xs +> 0 + y +> ys = ((xs + ys) +> y) := rfl
--
-- lemma Bits.cons_add_cons_zero {n} {xs ys : Bits n} {x} :
--     x +> xs + ys +> 0 = ((xs + ys) +> x) := by
--   rw [cons_add_cons]; cases x <;> simp [incr] <;> rfl
--
-- lemma Bits.cons_add_cons_one {n} {xs ys : Bits n} {x} :
--     x +> xs + ys +> 1 = ((xs + ys) +> x).succ := by
--   rw [cons_add_cons]; cases x <;> simp [incr] <;> rfl
--
-- lemma Bits.cons_false_add_cons {n} {xs ys : Bits n} {y} :
--     xs +> false + y +> ys = ((xs + ys) +> y) := cons_zero_add_cons
--
-- lemma Bits.cons_true_add_cons {n} {xs ys : Bits n} {y} :
--     xs +> true + y +> ys = ((xs + ys) +> y).succ := rfl
--
-- lemma Bits.cons_add_cons_false {n} {xs ys : Bits n} {x} :
--     x +> xs + ys +> false = ((xs + ys) +> x) := cons_add_cons_zero
--
-- lemma Bits.cons_add_cons_true {n} {xs ys : Bits n} {x} :
--     x +> xs + ys +> true = ((xs + ys) +> x).succ := cons_add_cons_one

-- lemma Bits.cons_sub_cons_true {n} {xs ys : Bits n} {x} :
--     x +> xs - ys +> true = ((xs - ys) +> x).pred := rfl
--
-- lemma Bits.cons_sub_cons_false {n} {xs ys : Bits n} {x} :
--     x +> xs - ys +> false = (xs - ys) +> x := rfl
--
-- lemma Bits.cons_sub_cons {n} {xs ys : Bits n} {x y} :
--     x +> xs - y +> ys = decr y ((xs - ys) +> x) := rfl
--
-- lemma Bits.cons_sub_cons' {n} {xs ys : Bits n} {x} :
--     x +> xs - ys +> x = (xs - ys) +> 0 := by cases x <;> rfl

def Bits.carryShlo : ∀ {n}, Bits n → Bool → (Bool × Bits n)
  | 0, ⦃⦄, y => (y, ⦃⦄)
  | _ + 1, x +> xs, y =>
    let (z, zs) := carryShlo xs y
    (x, z +> zs)

def Bits.shlo {n} (xs : Bits n) (x : Bool) : Bits n := (carryShlo xs x).snd

-- def Bits.shlo : ∀ {n}, Bits n → Bool → (Bits n
--   | 0, ⦃⦄, _ => ⦃⦄
--   | _ + 1, x +> xs, y => shlo xs x +> y

def Bits.shl : Nat → ∀ {n}, Bits n → Bits n
  | 0, _, xs => xs
  | k + 1, _, xs => shl k <| shlo xs 0

-- def Bits.snoc (x : Bool) : ∀ {n}, Bits n → Bits (n + 1)
--   | 0, ⦃⦄ =>⦃x⦄
--   | _ + 1, y +> ys => snoc x y +> ys

def Bits.shro : ∀ {n}, Bool → Bits n → Bits n
  | 0, _, ⦃⦄ => ⦃⦄
  | n + 1, x, y +> ys =>  x +> shro y ys

def Bits.shr : Nat → ∀ {n}, Bits n → Bits n
  | 0, _, xs => xs
  | k + 1, _, xs => --shro 0 (shr k xs)
    shr k (shro 0 xs)

def Bits.isNeg : ∀ {n : ℕ}, Bits n → Bool
  | 0, _ => false
  | _ + 1, x +> _ => x

def Bits.neg {n : ℕ} (xs : Bits n) : Bits n := (~ xs).succ

def Bits.sar (m : Nat) {n} (xs : Bits n) : Bits n :=
  if isNeg xs
  then neg (shr m (neg xs))
  else shr m xs

def Bits.append : ∀ {m n}, Bits m → Bits n → Bits (n + m)
  | 0, _, ⦃⦄, ys => ys
  | m + 1, n, x +> xs, ys => x +> append xs ys

instance {m n} : HAppend (Bits m) (Bits n) (Bits (n + m)) := ⟨Bits.append⟩

-- lemma Bits.append_nil {n} {xs : Bits n} : xs ++ ⦃⦄ = xs :=
--
lemma Bits.cons_append {m n} {x} {xs : Bits m} {ys : Bits n} :
    (x +> xs) ++ ys = x +> (xs ++ ys) := by rfl

lemma Bits.append_and_append {m n} {xs₀ ys₀ : Bits m} {xs₁ ys₁ : Bits n} :
    and (xs₀ ++ xs₁) (ys₀ ++ ys₁) = and xs₀ ys₀ ++ and xs₁ ys₁ := by
  induction m with
  | zero => cases xs₀; cases ys₀; rfl
  | succ n ih =>
    match xs₀, ys₀ with
    | _ +> _, _ +> _ => simp [cons_append, cons_and_cons, ih]

def Bits.mulCore {m} : ∀ {n}, Bits m → Bits n → Bits m
  | 0, _, ⦃⦄ => 0
  | _ + 1, xs, 0 +> ys => mulCore xs ys
  | n + 1, xs, 1 +> ys => shl n xs + mulCore xs ys

def Bits.mul {n} (xs ys : Bits n) : Bits n := mulCore xs ys

instance {n} : HMul (Bits n) (Bits n) (Bits n) := ⟨Bits.mul⟩

def Bits.snoc : ∀ {n}, Bits n → Bool → Bits (n + 1)
  | 0, ⦃⦄, y => ⦃y⦄
  | n + 1, x +> xs, y => x +> snoc xs y

-- divMod acc pfx xs ys
-- assumes: pfx < ys
def divMod : ∀ {m n : ℕ}, Bits n → Bits m → Bits n → (Bits m × Bits n)
  | 0, _, pfx, ⦃⦄, _ => (0, pfx)
  | _ + 1, _, pfx, x +> xs, ys =>
    let pfx' := .shlo pfx x
    if ys ≤ pfx'
    then let (div, mod) := divMod (pfx' - ys) xs ys
         (1 +> div, mod)
    else let (div, mod) := divMod pfx' xs ys
         (0 +> div, mod)

def Bits.div {n} (xs ys : Bits n) : Bits n :=
  if ys = 0 then 0 else (divMod 0 xs ys).fst

instance {n} : HDiv (Bits n) (Bits n) (Bits n) := ⟨Bits.div⟩

def Bits.mod {n} (xs ys : Bits n) : Bits n := (divMod 0 xs ys).snd

instance {n} : HMod (Bits n) (Bits n) (Bits n) := ⟨Bits.mod⟩

-- minimum possible value in 2's complement
def Bits.smin : ∀ {n : ℕ}, Bits n
  | 0 => ⦃⦄
  | _ + 1 => 1 +> 0

def Bits.negOne {n : ℕ} : Bits n := max _

def Bits.sdiv {n : ℕ} (xs ys : Bits n) : Bits n :=
  if ys = 0
  then 0
  else if xs = smin ∧ ys = negOne
       then smin
       else match (isNeg xs, isNeg ys) with
            | (0, 0) => xs / ys
            | (1, 0) => neg ((neg xs) / ys)
            | (0, 1) => neg (xs / (neg ys))
            | (1, 1) => (neg xs) / (neg ys)

def Bits.abs {n : ℕ} (xs : Bits n) : Bits n :=
  if isNeg xs then neg xs else xs

def Bits.smod {n : ℕ} (xs ys : Bits n) : Bits n :=
  if ys = 0
  then 0
  else let mod := (abs xs) % (abs ys)
       if isNeg xs then neg mod else mod

def Bits.addmod {n : ℕ} (x y z : Bits n) : Bits n :=
  if z = 0 then 0 else (x + y) % z

def Bits.mulmod {n : ℕ} (x y z : Bits n) : Bits n :=
  if z = 0 then 0 else (x * y) % z

-- def Bits.iter {α : Type} (f : α → α) : α → ∀ {n}, Bits n → α
--   | a, 0, ⦃⦄ => a
--   | a, _ + 1, xs +> 0 => iter f (iter f a xs) xs
--   | a, _ + 1, xs +> 1 => iter f (iter f (f a) xs) xs

def Bits.expNat {n : ℕ} (x : Bits n) : Nat → Bits n
  | 0 => 1
  | k + 1 => x * x.expNat k

def Bits.exp {n : ℕ} (x y : Bits n) : Bits n := expNat x y.toNat

instance {n} : HPow (Bits n) (Bits n) (Bits n) := ⟨Bits.exp⟩

inductive Bits.Signext' : Nat → Bool → ∀ {n}, Bits n → Bits n → Prop
  | zero : ∀ n x (xs : Bits n), Signext' 0 x (x +> xs) (x +> xs)
  | succ :
    ∀ m n x y (xs ys : Bits n),
      Signext' m y xs ys →
      Signext' (m + 1) y (x +> xs) (y +> ys)

def Bits.Signext (x y y' : Word) : Prop :=
  ∃ b, Signext' (256 - (8 * (x.toNat + 1))) b y y'

-- def Bits.suffix : ∀ {m n}, Bits m → Bits n → Prop
--   | _, 0, _, ⦃⦄ => true
--   | 0, _ + 1, ⦃⦄, _ => false
--   | _ + 1, _ + 1, x +> xs, y +> ys => suffix xs ys ∧ x = y

def Bits.prefix {m} : ∀ {n}, Bits (m + n) → Bits n
  | 0, _ => ⦃⦄
  | n + 1, x +> xs => x +> xs.prefix

def Bits.suffix : ∀ {m n}, Bits (m + n) → Bits m
  | _, 0, xs => xs
  | _, n + 1, _ +> xs => xs.suffix

lemma Bits.prefix_append {m n} (xs : Bits m) (ys : Bits n) :
    (xs ++ ys).prefix = xs := by
  induction m with
  | zero => apply nil_eq_nil
  | succ m ih =>
    match xs with
    | x +> xs => rw [cons_append]; simp [Bits.prefix, ih]

lemma Bits.suffix_append {m n} (xs : Bits m) (ys : Bits n) :
    (xs ++ ys).suffix = ys := by
  induction m with
  | zero => cases xs; rfl
  | succ m ih =>
    match xs with
    | x +> xs => rw [cons_append]; simp [Bits.suffix, ih]

lemma Bits.append_inj {m n} {xs₁ ys₁ : Bits m} {xs₂ ys₂ : Bits n} :
     xs₁ ++ xs₂ = ys₁ ++ ys₂ → xs₁ = ys₁ ∧ xs₂ = ys₂ := by
  induction m generalizing xs₂ ys₂ n with
  | zero => cases xs₁; cases ys₁; intro h; refine' ⟨nil_eq_nil, h⟩
  | succ n ih =>
    match xs₁, ys₁ with
    | x +> xs, y +> ys =>
      simp [Bits.cons_append]; intro h h'
      let ⟨ih₁, ih₂⟩ := ih h'
      refine ⟨⟨h, ih₁⟩, ih₂⟩

def Addr.toWord (a : Addr) : Bits 256 := (0 : Bits 96) ++ a

lemma Addr.toWord_inj {a a' : Addr} :
    Addr.toWord a = Addr.toWord a' → a = a' := And.right ∘ Bits.append_inj

def Nat.toBits (k) : Nat → Bits k
  | 0 => 0
  | n + 1 => (Nat.toBits k n).succ

lemma Bits.zero_eq_cons {n} : (0 : Bits (n + 1)) = 0 +> (0 : Bits n) := rfl
lemma Bits.max_eq_cons {n} : max (n + 1) = 1 +> max n := rfl

lemma Bits.eq_max_iff_isMax {k : ℕ} (xs : Bits k) : xs = max k ↔ xs.isMax = true := by
  induction xs with
  | nil => apply iff_of_true <;> rfl
  | cons x xs ih =>
    rw [max_eq_cons, cons_eq_cons, ih]
    simp only [isMax, Bool.and_eq_true]; rfl

lemma Bits.max_isMax {n : ℕ} : (max n).isMax = true := by
  rw [← eq_max_iff_isMax]

lemma Bits.eq_max_iff_succ_eq_zero {k : ℕ} (xs : Bits k) :
    xs = max k ↔ xs.succ = 0 := by
  induction xs with
  | nil => apply iff_of_true <;> rfl
  | cons x xs ih =>
    rw [succ, zero_eq_cons, max_eq_cons, cons_eq_cons, cons_eq_cons, ih]
    simp; intro h; rw [← ih, eq_max_iff_isMax] at h
    rw [h]; cases x <;> simp [Bool.one, Bool.zero]

lemma Bits.succ_toNat_max_eq_pow {n : Nat} : (max n).toNat.succ = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [toNat, Nat.two_pow_succ]; rw [← ih]; rfl

lemma Bits.toNat_max_add_one_eq_pow {n : Nat} : (max n).toNat + 1 = 2 ^ n :=
  succ_toNat_max_eq_pow

lemma Bits.toNat_succ {k : ℕ} (xs : Bits k) :
    xs.succ.toNat = cond xs.isMax 0 xs.toNat.succ := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases h : xs = max _
    · have h' := (eq_max_iff_isMax xs).mp h
      simp [h'] at ih; simp only [succ, isMax, toNat, h', ih]
      cases x <;> simp; rw [← succ_toNat_max_eq_pow, h]
    · have h' := mt (eq_max_iff_isMax xs).mpr h
      simp [h'] at ih
      simp only [succ, toNat, isMax, h']
      rw [← Nat.add_succ]; simp [ih]

-- lemma Nat.toBits_inj {k m n : ℕ} (hm : m < 2 ^ k) (hn : n < 2 ^ k)
--     (h : toBits k m = toBits k n) : m = n := by
--   -- | 0, m, n, hm, hn, h => by
--   --   match m, n with
--   --   | succ _, _ =>
--   have foo : ∀ {k m : Nat}, m + 1 < 2 ^ k → (toBits k 0) ≠ (toBits k (m + 1)) := by
--     clear hm hn h k m n
--     intro k m h h'
--     simp only [toBits] at h'
--     rw [Eq.comm, ← Bits.eq_max_iff_succ_eq_zero] at h'
--
--     sorry
--   induction m generalizing n with
--   | zero =>
--     match n with
--     | 0 => rfl
--     | n + 1 =>
--       simp [toBits] at h
--       sorry
--   | succ m ih =>
--     match n with
--     | 0 => sorry
--     | n + 1 =>
--       have hm' := lt_trans (Nat.lt_succ_self m) hm
--       have hn' := lt_trans (Nat.lt_succ_self n) hn
--       rw [ih hm' hn' <| Bits.succ_inj h]







instance {m n} : OfNat (Bits m) n := ⟨Nat.toBits _ n⟩

def Nat.toByte : Nat → Bits 8 := Nat.toBits _

def toAddr : Bits 256 → Bits 160 := @Bits.suffix 160 96

def suffix_append {m n} {xs : Bits m} {ys : Bits n} :
    Bits.suffix (xs ++ ys) = ys := by
  induction m with
  | zero => cases xs; rfl
  | succ m ih =>
    match xs with
    | x +> xs' => simp [Bits.suffix]; apply ih

lemma toAddr_toWord (a : Addr) : toAddr (Addr.toWord a) = a := suffix_append

lemma Bits.prefix_append_suffix {m n} :
    ∀ xs : Bits (m + n), xs.prefix ++ xs.suffix = xs := by
  induction n with
  | zero => intro xs; rfl
  | succ n ih =>
    intro xs; match xs with
    | x +> xs' => simp [Bits.prefix, suffix, cons_append, ih]

def Bits.toBytes : ∀ {n}, Bits (8 * n) → Bytes
  | 0, ⦃⦄ => []
  | _ + 1, b0 +> b1 +> b2 +> b3 +> b4 +> b5 +> b6 +> b7 +> bs =>
    ⦃b0, b1, b2, b3, b4, b5, b6, b7⦄ :: bs.toBytes

def Bits.min {n} (x y : Bits n) : Bits n := if x ≤ y then x else y

-- #check List.takeD
-- def Bytes.ekatD' : Nat → Bytes → Byte → (Nat × Bytes)
--   | k, [], _ => (k, [])
--   | k, b :: bs, c =>
--     match ekatD' k bs c with
--     | (0, bs') => (0, bs')
--     | (k' + 1, bs') => (k', b :: bs')
--
def Bytes.toBits' : ∀ (n : Nat), Bytes → Bits (8 * n)
  | 0, _ => ⦃⦄
  | n + 1, [] => (0 : Byte) ++ toBits' n []
  | n + 1, b :: bs => b ++ toBits' n bs

def Bytes.toBits (n : Nat) (bs : Bytes) : Bits (8 * n) :=
  --have h : bs'.length = n := by
  --  rw [List.length_reverse]; apply List.takeD_length
  --by rw [← h]; exact
  Bytes.toBits' n <| List.reverse <| List.takeD n (List.reverse bs) 0


lemma Bits.cons_eq_zero_iff {n x} {xs : Bits n} :
   x +> xs = 0 ↔ (x = 0 ∧ xs = 0) := by rw [zero_eq_cons]; simp

lemma Bits.zero_append_zero {m n} :
    (0 : Bits n) ++ (0 : Bits m) = (0 : Bits (m + n)) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [zero_eq_cons, zero_eq_cons, cons_append, ih]

lemma Bits.toNat_zero : ∀ {k}, (0 : Bits k).toNat = 0
  | 0 => rfl
  | k + 1 => by rw [zero_eq_cons]; simp [toNat, @toNat_zero k]; rfl
--
--
-- lemma Bits.of_toNat_eq_zero {k} (xs : Bits k) (h : xs.toNat = 0) : xs = 0 := by
--   induction k with
--   | zero => apply nil_eq_nil
--   | succ k ih =>
--     rcases xs with _ | ⟨xs, _ | _⟩ <;>
--     (simp [cons_eq_zero_iff]; simp [toNat, Nat.mul_eq_zero] at h)
--     · refine ⟨ih _ h, false_eq_zero⟩
--
-- lemma Bits.nonzero_toNat {k} (xs : Bits k) : xs ≠ 0 → xs.toNat ≠ 0 :=
--   mt <| of_toNat_eq_zero xs
--
-- lemma Bits.succ_toNat_assoc {k} : (xs : Bits k) → xs ≠ max _ → xs.succ.toNat = xs.toNat.succ := by
--   apply @Nat.rec (λ k => (xs : Bits k) → xs ≠ max _ → xs.succ.toNat = xs.toNat.succ)
--   · intros xs h; cases h nil_eq_nil
--   · intros k ih xs h; rcases xs with _ | ⟨xs, _ | _⟩
--     · simp [succ, toNat, false_toNat, true_toNat, Bool.zero_toNat, Bool.one_toNat]
--     · simp [succ, toNat, false_toNat, true_toNat, Bool.zero_toNat, Bool.one_toNat]
--       have h_ne : xs ≠ max _ := by
--         intro hc; simp [max, hc] at h
--       rw [ih _ h_ne]; simp [Nat.mul_succ]
--
-- lemma Bits.incr_toNat_assoc {k} (x) (xs : Bits k) (h : xs ≠ max _) :
--     (incr x xs).toNat = xs.toNat + x.toNat := by
--   cases x <;> simp [incr]; apply succ_toNat_assoc _ h
--
lemma Bits.nil_toNat (xs : Bits 0) : xs.toNat = 0 := by cases xs; rfl
--
-- lemma Bits.pred_toNat_assoc {k} (xs : Bits k) (h : xs ≠ 0) : xs.pred.toNat = xs.toNat.pred := by
--   induction k with
--   | zero => simp [nil_toNat]
--   | succ k ih =>
--     rcases xs with _ | ⟨xs, _ | _⟩ <;>
--     simp [pred, toNat, Bool.one_toNat]
--     · simp [Ne, cons_eq_zero_iff, false_eq_zero] at h; rw [ih xs h];
--       rcases Nat.exists_eq_succ_of_ne_zero <| nonzero_toNat _ h with ⟨n, hn⟩
--       rw [hn, Nat.mul_succ]; simp [Nat.pred]
--     · rfl
--
-- lemma Bits.decr_toNat_assoc {k} (x) (xs : Bits k) (h : xs ≠ 0) :
--     (decr x xs).toNat = xs.toNat - x.toNat := by
--   cases x <;> simp [decr]; apply pred_toNat_assoc _ h
--

-- lemma Bits.succ_pred : ∀ {n} {xs : Bits n}, succ (pred xs) = xs := by
--   apply Nat.rec
--   · intros _; apply nil_eq_nil
--   · intros n ih xs; rcases xs with _ | ⟨xs, _ | _⟩ <;> simp [pred, succ]
--     · simp [ih]; rfl
--     · rfl
--
-- lemma Bits.pred_succ : ∀ {n} {xs : Bits n}, pred (succ xs) = xs := by
--   apply Nat.rec
--   · intros _; apply nil_eq_nil
--   · intros n ih xs; rcases xs with _ | ⟨xs, _ | _⟩ <;> simp [pred, succ]
--     · rfl
--     · simp [ih]; rfl
--
-- lemma Bits.add_comm : ∀ {n} {xs ys : Bits n}, xs + ys = ys + xs := by
--   apply Nat.rec
--   · intros _ _; apply nil_eq_nil
--   · intros n ih xs ys;
--     rcases xs with _ | ⟨xs, x⟩
--     rcases ys with _ | ⟨ys, y⟩
--     rw [cons_add_cons, cons_add_cons, ih];
--     cases x <;> cases y <;> rfl
--
-- lemma Bits.succ_add : ∀ {n} {xs ys : Bits n}, succ (xs + ys) = xs.succ + ys := by
--   apply Nat.rec
--   · intros _ _; apply nil_eq_nil
--   · intros n ih xs ys;
--     rcases xs with _ | ⟨xs, _ | _⟩ <;>
--     rcases ys with _ | ⟨ys, _ | _⟩
--     · rfl
--     · rfl
--     · rw [cons_add_cons_false]; simp [succ];
--       rw [cons_add_cons_false, ih]
--     · rw [cons_true_add_cons]; simp [succ];
--       rw [cons_add_cons_true]; simp [succ, ih]
--
-- lemma Bits.pred_add_eq_add_pred : ∀ {n} {xs ys : Bits n}, xs.pred + ys = xs + ys.pred := by
--   apply Nat.rec
--   · intros _ _; apply nil_eq_nil
--   · intros n ih xs ys;
--     rcases xs with _ | ⟨xs, _ | _⟩ <;>
--     rcases ys with _ | ⟨ys, _ | _⟩
--     · simp [cons_false_add_cons, pred, cons_add_cons_false]; apply ih
--     · simp [pred, cons_add_cons, incr, succ];
--       rw [succ_add]; simp [succ_pred]
--     · simp [pred]; rw [cons_add_cons_false, cons_true_add_cons];
--       simp [succ]; rw [← ih, succ_add, succ_pred];
--     · rfl
--
-- lemma Bits.pred_add : ∀ {n} {xs ys : Bits n}, pred (xs + ys) = xs.pred + ys := by
--   apply Nat.rec
--   · intros _ _; apply nil_eq_nil
--   · intros n ih xs ys;
--     rcases xs with _ | ⟨xs, _ | _⟩ <;>
--     rcases ys with _ | ⟨ys, _ | _⟩
--     · simp [cons_false_add_cons, pred, cons_add_cons_false]; apply ih
--     · rw [cons_false_add_cons, pred_add_eq_add_pred]
--       simp [pred]; rfl
--     · rfl
--     · rw [cons_true_add_cons]; simp [pred];
--       rw [cons_add_cons_true]; simp [succ, pred_succ]
--
-- lemma Bits.pred_sub : ∀ {n} {xs ys : Bits n}, pred (xs - ys) = xs.pred - ys := by
--   apply Nat.rec
--   · intros _ _; apply nil_eq_nil
--   · intros n ih xs ys;
--     rcases xs with _ | ⟨xs, _ | _⟩ <;>
--     rcases ys with _ | ⟨ys, _ | _⟩
--     · rw [cons_sub_cons_false]; simp [pred]; rw [cons_sub_cons_false, ih]
--     · rw [cons_sub_cons_true]; simp [pred]; rw [cons_sub_cons_true]; simp [pred, ih]
--     · rfl
--     · rfl
--
-- lemma Bits.succ_sub : ∀ {n} {xs ys : Bits n}, succ (xs - ys) = xs.succ - ys := by
--   apply Nat.rec
--   · intros _ _; apply nil_eq_nil
--   · intros n ih xs ys;
--     rcases xs with _ | ⟨xs, _ | _⟩ <;>
--     rcases ys with _ | ⟨ys, _ | _⟩
--     · rw [cons_sub_cons_false]; simp [succ]; rw [cons_sub_cons_false]
--     · simp [succ]; rw [succ_pred]; rfl
--     · rw [cons_sub_cons_false]; simp [succ]; rw [cons_sub_cons_false, ih]
--     · simp [succ]; rw [cons_sub_cons_true]; simp [pred];
--       rw [pred_sub, pred_succ]; rfl
--
-- lemma Bits.pred_add' {n} {xs ys : Bits n} : pred (xs + ys) = xs + ys.pred := by
--   rw [@add_comm _ _ ys, pred_add, add_comm]
--
-- lemma Bits.add_sub_assoc : ∀ {n} {xs ys zs : Bits n}, xs + ys - zs = xs + (ys - zs) := by
--   apply Nat.rec
--   · intros _ _ _; apply nil_eq_nil
--   · intros m ih xs ys zs
--     rcases xs with _ | ⟨xs, _ | _⟩ <;>
--     rcases ys with _ | ⟨ys, _ | _⟩ <;>
--     rcases zs with _ | ⟨zs, _ | _⟩ <;>
--     simp [cons_add_cons, cons_sub_cons, decr, incr]
--     · rw [ih]
--     · rw [← pred_add', cons_false_add_cons, ih]
--     · rw [ih]
--     · rw [← pred_add', cons_false_add_cons, ih]
--     · simp [succ]; rw [cons_sub_cons_false, ih]
--     · simp [succ]; rw [← pred_add_eq_add_pred];
--       simp [pred]; rw [cons_zero_add_cons, ← ih]; rfl
--     · simp [succ]; rw [cons_sub_cons_false];
--       rw [← ih, succ_sub]
--     · simp [succ, pred]; rw [cons_sub_cons_true, cons_true_add_cons]
--       simp [succ, pred]; rw [pred_sub, pred_succ, ih]


 -- apply Nat.rec
 -- · intros _; apply nil_eq_nil
 -- · intros m ih xs; rcases xs with _ | ⟨xs, x⟩
 --   rw [cons_sub_cons', ih]; rfl
--
-- lemma Bits.add_zero : ∀ {n} (xs : Bits n), xs + 0 = xs := by
--   apply Nat.rec
--   · intros _; apply nil_eq_nil
--   · intros m ih xs; rcases xs with _ | ⟨xs, x⟩
--     rw [zero_eq_cons, cons_add_cons_zero, ih]
--
-- lemma Bits.add_sub_cancel {n} {x y : Bits n} : x + y - y = x :=
--  by rw [add_sub_assoc, sub_self, add_zero]
--
-- lemma Bits.add_sub_comm {n} {xs ys zs : Bits n} : xs + ys - zs = xs - zs + ys := by
--   rw [add_comm, add_sub_assoc, add_comm]
--
-- lemma Bits.sub_add_cancel {n} {x y : Bits n} : x - y + y = x :=
--  by rw [← add_sub_comm, add_sub_cancel]
--
-- lemma Bits.zero_add {n} (xs : Bits n) : 0 + xs = xs := by rw [add_comm, add_zero]
--
-- lemma Bits.add_right_inj {n} {x y z : Bits n} : x + z = y + z → x = y := by
--   intro h; have h' : x + z - z = y + z - z := by rw [h]
--   rw [add_sub_assoc, add_sub_assoc, sub_self, add_zero, add_zero] at h'; exact h'
--
-- lemma Bits.add_left_inj {n} {x y z : Bits n} : z + x = z + y → x = y := by
--  rw [add_comm, @add_comm _ z]; apply add_right_inj

lemma Bits.add_left_inj {n} :
    ∀ {xs ys zs : Bits n}, xs + ys = xs + zs → ys = zs := by
  induction n with
  | zero => intro _ _ _ _; apply nil_eq_nil
  | succ n ih =>
    intro xs ys zs h
    match xs, ys, zs with
    | x +> xs, y +> ys, z +> zs =>
      simp [cons_add_cons] at h
      simp [ih h.right] at *; assumption

lemma Bits.toNat_lt_pow {n} (xs : Bits n) : xs.toNat < 2 ^ n := by
  induction xs with
  | nil => simp [toNat]
  | cons x xs ih =>
    simp only [toNat]; rw [Nat.two_pow_succ]
    apply Nat.add_lt_add_of_le_of_lt _ <| ih
    cases x <;> simp

lemma Bits.toNat_inj :
    ∀ {k} (xs ys : Bits k), xs.toNat = ys.toNat → xs = ys := by
  apply rec2
  · intro _; rfl
  · intro n x xs y ys ih h; simp only [toNat] at h
    cases x <;> cases y <;> simp at h <;> try {rw [ih h]}
    · apply (Nat.ne_of_lt (lt_of_lt_of_le (toNat_lt_pow _) _) h).elim
      apply Nat.le_add_right
    · apply (Nat.ne_of_lt (lt_of_lt_of_le (toNat_lt_pow _) _) h.symm).elim
      apply Nat.le_add_right

lemma toNat_toBits {k n} (h : n < 2 ^ k) : (Nat.toBits k n).toNat = n := by
  induction n with
  | zero => simp [Nat.toBits, Bits.toNat, Bits.toNat_zero]
  | succ n ih =>
    simp only [Nat.toBits]
    rw [Bits.toNat_succ]
    have ih' := ih <| lt_trans (Nat.lt_succ_self n) h
    by_cases h' : Nat.toBits k n = Bits.max k
    · have h_eq := @Bits.succ_toNat_max_eq_pow k
      rw [← h', ih'] at h_eq; rw [← h_eq] at h; cases Nat.lt_irrefl _ h
    · simp [mt (Bits.eq_max_iff_isMax (Nat.toBits k n)).mpr h', ih']

lemma Nat.toBits_inj {k m n : ℕ} (hm : m < 2 ^ k) (hn : n < 2 ^ k)
    (h : toBits k m = toBits k n) : m = n := by
  rw [← toNat_toBits hm, ← toNat_toBits hn, h]











-- lemma toBits_toNat {k} : ∀ n, n < 2 ^ k → (@Nat.toBits k n).toNat = n := by
--   apply Nat.rec
--   · simp [Nat.toBits, Bits.toNat, Bits.zero_toNat]
--   · intros n ih h_lt
--     have h_lt' : n < 2 ^ k := Nat.lt_trans (Nat.lt_succ_self _) h_lt
--     have ih' := ih h_lt'
--     unfold Nat.toBits; rw [Bits.succ_toNat_assoc, ih']
--     intro hc; rw [hc] at ih'
--     rw [← ih', Bits.max_toNat_succ] at h_lt
--     apply Nat.lt_irrefl _ h_lt
--
lemma Bits.nil_le_nil {xs ys : Bits 0} : xs ≤ ys := by
  cases xs; cases ys; constructor
--
-- lemma Bits.lt_succ_self {n} {xs : Bits n} (h : xs < max n) : xs < xs.succ := by
--   induction n with
--   | zero => cases xs; simp [max] at h; cases h
--   | succ n ih =>
--     match xs with
--     | x +> xs =>
--       simp [max] at h; rw [cons_lt_cons] at h
--       cases x <;> simp [succ, cons_lt_cons]
--       · right; constructor
--       · cases h with
--         | inl h' => left; apply ih h'
--         | inr h' => cases h'.right

lemma Bits.lt_trans {n} {xs ys zs : Bits n} (h : xs < ys) (h' : ys < zs) : xs < zs := by
  induction n with
  | zero => cases xs; cases ys; cases h
  | succ n ih =>
    match xs, ys, zs with
    | x +> xs, y +> ys, z +> zs =>
      rcases h with h | ⟨⟨_⟩, h⟩ <;> rcases h' with h' | ⟨⟨_⟩, h'⟩
      · left; apply Bool.lt_trans h h'
      · left; apply h
      · left; apply h'
      · right; refine ⟨rfl, ih h h'⟩

lemma Bits.le_refl {n} {xs : Bits n} : xs ≤ xs := by
  induction xs with
  | nil => apply nil_le_nil
  | cons x xs ih => simp [cons_le_cons]; exact ih

-- lemma Bits.le_of_eq {n : Nat} {xs ys : Bits n} (h : xs = ys) : xs ≤ ys := by
--   cases h; apply le_refl
--

lemma Bits.le_of_lt {n : Nat} {xs ys : Bits n} (h : xs < ys) : xs ≤ ys := by
  induction n with
  | zero => cases xs; cases ys; cases h
  | succ n ih =>
    match xs, ys with
    | x +> xs, y +> ys =>
      rw [cons_lt_cons] at h
      rcases h with h | ⟨h, h'⟩
      · left; exact h
      · right; refine ⟨h, ih h'⟩


-- lemma Bits.le_of_lt_or_eq {n : Nat} {xs ys : Bits n}
--     (h : xs < ys ∨ xs = ys) : xs ≤ ys := by
--   cases h; apply le_of_lt asm; apply le_of_eq asm

lemma Bits.lt_or_eq_of_le {n : Nat} {xs ys : Bits n} (h : xs ≤ ys) :
    xs < ys ∨ xs = ys := by
  induction n with
  | zero => cases xs; cases ys; simp
  | succ n ih =>
    match xs, ys with
    | x +> xs, y +> ys =>
      rcases h with h | ⟨⟨_⟩, h⟩
      · left; left; exact h
      · rcases ih h with h | ⟨⟨_⟩⟩
        · left; right; refine ⟨rfl, h⟩
        · right; rfl

-- lemma Bits.lt_or_eq_of_le {n : Nat} {xs ys : Bits n} (h : xs ≤ ys) : xs < ys ∨ xs = ys := by
--   cases n with
--   | zero => right; apply nil_eq_nil
--   | succ n  =>
--   match xs, ys with
--   | x +> xs, y +> ys =>
--     cases h with
--     | inl h' => left; left; apply h'
--     | inr h' =>
--       match x, y with
--       | 0, 0 => right; rw [h'.left]
--       | 0, 1 => left; right; simp [h'.left]; constructor
--       | 1, 0 => simp [LE.le] at h'
--       | 1, 1 => right; rw [h'.left]
--
--
-- lemma Bits.le_iff_lt_or_eq {n : Nat} {xs ys : Bits n} : xs ≤ ys ↔ (xs < ys ∨ xs = ys) :=
--   ⟨lt_or_eq_of_le, le_of_lt_or_eq⟩
--
-- lemma Bits.cons_lt_cons_of_le_of_lt {n} {xs ys : Bits n} {x y} :
--     xs ≤ ys → x < y → x +> xs < y +> ys := by
--   intros hs h; cases lt_or_eq_of_le hs with
--   | inl h_lt => left; apply h_lt
--   | inr h_eq => right; refine ⟨h_eq, h⟩
--
-- lemma Bits.le_max {n} : ∀ {xs : Bits n}, xs ≤ max _ := by
--   induction n with
--   | zero => intro _; apply nil_le_nil
--   | succ n ih =>
--     intro xs
--     cases xs with
--     | cons xs x =>
--       cases lt_or_eq_of_le ih with
--       | inl h => left; apply h
--       | inr h => right; refine' ⟨h, Bool.le_one⟩
--
-- lemma Bits.zero_le {n} : ∀ xs : Bits n, 0 ≤ xs := by
--   induction n with
--   | zero => intro xs; cases xs; constructor
--   | succ n ih =>
--     intro xs; match xs with
--     | x +> xs =>
--       rw [zero_eq_cons, cons_le_cons]
--       cases lt_or_eq_of_le <| ih xs
--       · left; assumption
--       · right; refine' ⟨asm, by simp [LE.le]⟩
--

lemma Bits.lt_of_le_of_lt {n} {xs ys zs : Bits n} (h : xs ≤ ys) (h' : ys < zs) : xs < zs := by
  cases lt_or_eq_of_le h with
  | inl h'' => apply lt_trans h'' h'
  | inr h'' => rw [h'']; exact h'

-- lemma Bits.lt_of_lt_of_le {n} {xs ys zs : Bits n} (h : xs < ys) (h' : ys ≤ zs) : xs < zs := by
--   cases lt_or_eq_of_le h' with
--   | inl h'' => apply lt_trans h h''
--   | inr h'' => rw [← h'']; exact h
--
-- lemma Bits.le_trans {n} {xs ys zs : Bits n} (h : xs ≤ ys) (h' : ys ≤ zs) : xs ≤ zs := by
--   induction n with
--   | zero => cases xs; cases zs; constructor
--   | succ n ih =>
--     match xs, ys, zs with
--     | x +> xs, y +> ys, zs +> z =>
--       cases x <;> cases y <;> cases z <;>
--       simp [cons_le_cons, false_le, not_true_le_false] at * <;>
--       try {apply lt_or_eq_of_le (ih (le_of_lt_or_eq h) (le_of_lt_or_eq h'))}
--       · left; apply lt_of_le_of_lt (le_of_lt_or_eq h) h'
--       · apply lt_of_lt_of_le h <| le_of_lt_or_eq h'
--       · apply lt_or_eq_of_le <| ih (le_of_lt h) <| le_of_lt_or_eq h'
--       · apply lt_of_le_of_lt (le_of_lt_or_eq h) h'
--
-- lemma Bits.lt_max_of_ne_max {n} {xs : Bits n} : xs ≠ max _ → xs < max _ := by
--   induction n with
--   | zero => intro h; cases h nil_eq_nil
--   | succ n ih =>
--     rcases xs with _ | ⟨xs, _ | _⟩ <;> unfold max
--     · simp; apply cons_lt_cons_of_le_of_lt le_max cst
--     · rw [true_eq_one]; simp; intro h; left; apply ih h
--
-- lemma Bits.lt_max_iff_ne_max {n} {xs : Bits n} : xs < max _ ↔ xs ≠ max _ := by
--   refine' ⟨λ h_lt h_eq => _, lt_max_of_ne_max⟩
--   cases h_eq; apply lt_irrefl h_lt
--
-- lemma toBits_le_toBits {k m n : Nat} :
--      m ≤ n → n < 2 ^ k → (@Nat.toBits k m) ≤ (@Nat.toBits k n) := by
--   revert m
--   induction n with
--   | zero => intros m h_le h_lt; cases m; apply Bits.zero_le; cases h_le
--   | succ n ih =>
--     intros m h_le h_lt;
--     cases Nat.lt_or_eq_of_le h_le with
--     | inl h_lt' =>
--       apply
--         Bits.le_trans
--           (ih (Nat.le_of_lt_succ h_lt') (Nat.lt_trans (Nat.lt_succ_self _) h_lt))
--       apply Bits.le_of_lt; apply Bits.lt_succ_self
--       rw [Bits.lt_max_iff_ne_max]; intro h_eq
--       have h_eq' : n + 1 = 2 ^ k := by
--         apply Eq.trans _ Bits.max_toNat_succ; simp
--         rw [← h_eq, toBits_toNat]
--         apply Nat.lt_trans _ h_lt; simp
--       rw [h_eq'] at h_lt; apply Nat.lt_irrefl _ h_lt
--     | inr h_eq => rw [← h_eq]; apply Bits.le_refl
--

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
  | [] => ""
  | [b] => b.toString
  | b :: bs => b.toString ++ " " ++ toString bs

def Bytes.toString' (bs : Bytes) : String :=
  "0x" ++ List.foldr (λ b s => b.toString ++ s) "" bs

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

--def Bytes.length : Bytes → Nat
--  | [] => 0
--  | bs :> _ => bs.length + 1

lemma List.length_dropWhile_le {ξ : Type u} (xs : List ξ) (f : ξ → Bool) :
    (dropWhile f xs ).length ≤ xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    by_cases h : f x
    · rw [List.dropWhile_cons_of_pos h]
      apply le_trans ih; simp
    · rw [List.dropWhile_cons_of_neg h]

def Bytes.sig (bs : Bytes) : Bytes :=
  List.dropWhile (· = 0) bs

-- def Bytes.sig : Bytes → Bytes
--   | [] => []
--   | bs :> b =>
--   match bs.sig with
--   | [] => if b = 0 then [] else [b]
--   | bs'@(_ :> _) => bs' :> b
--
-- lemma Bytes.sig_length_le (bs : Bytes) : bs.sig.length ≤ bs.length := by
--   induction bs with
--   | nil => simp [Bytes.length]
--   | cons bs b ih =>
--     unfold Bytes.sig; revert ih
--     cases bs.sig with
--     | nil =>
--       simp; intro _
--       apply ite_cases (λ bs' : Bytes => bs'.length ≤ (bs :> b).length) <;>
--       intro _ <;> simp [Bytes.length]
--     | cons bs' b' =>
--       simp; intro h; simp [Bytes.length]; apply h

-- lemma eq_nil_or_eq_cons (bs : Bytes) : bs = [] ∨ ∃ bs' b, bs = (bs' :> b) := by
--   cases bs; left; rfl; right; refine ⟨_, _, rfl⟩

-- lemma Bits.cons_eq_max {n} (xs : Bits n) (x) :
--     x +> xs = max _ ↔ (xs = max _ ∧ x = 1) := by
--   cases x
--   · apply iff_of_false <;> intro h
--     · cases h
--     · cases h.right
--   · cases em (xs = max _) with
--     | inl h => rw [h]; apply iff_of_true; rfl; simp; rfl
--     | inr h =>
--       apply iff_of_false <;> intro h'
--       · cases h'; cases h rfl
--       · cases h h'.left
--

lemma Bool.lt_or_ge (x y : Bool) : x < y ∨ x ≥ y := by
  cases x <;> cases y <;> simp

lemma Bool.lt_or_eq_of_le {x y : Bool} : x ≤ y → (x < y ∨ x = y) := by
  cases x <;> cases y <;> simp

lemma Bits.lt_or_ge {n : ℕ} : ∀ xs ys : Bits n, xs < ys ∨ xs ≥ ys := by
  induction n with
  | zero =>
    intros xs ys; cases xs; cases ys
    right; constructor
  | succ n ih =>
    intros xs ys
    match xs, ys with
    | x +> xs, y +> ys =>
      rcases Bool.lt_or_ge x y with h | h
      · left; left; exact h
      · rcases Bool.lt_or_eq_of_le h  with h' | h'
        · right; left; exact h'
        · rcases ih xs ys with h'' | h''
          · left; right; refine ⟨h'.symm, h''⟩
          · right; right; refine ⟨h', h''⟩

-- lemma Bits.lt_or_ge {n : ℕ} : ∀ xs ys : Bits n, xs < ys ∨ xs ≥ ys := by
--   induction n with
--   | zero => intros _ _; right; apply nil_le_nil
--   | succ n ih =>
--     intros xs ys
--     match xs, ys with
--     | x +> xs, y +> ys =>
--       rcases ih xs ys with h | h
--       · left; left; exact h
--       · simp only [GE.ge] at h
--         rw [le_iff_lt_or_eq] at h
--         rcases h with h | h
--         · right; left; exact h
--         · rw [h]; cases x
--           · cases y
--             · right; right; simp
--             · left; right; simp; constructor
--           · right; right; simp

lemma Bits.not_lt {n : ℕ} (xs ys : Bits n) : ¬ xs < ys ↔ ys ≤ xs := by
  constructor
  · rw [← or_iff_not_imp_left]; apply lt_or_ge
  · intros h h'; cases lt_irrefl <| lt_of_le_of_lt h h'

lemma Bits.exists_eq_cons {n} (xs : Bits (n + 1)) : ∃ xs' x, xs = xs' +> x :=
  by cases xs; refine ⟨_, _, rfl⟩


lemma overflow_iff_overflow_eq_true :
    ∀ {n : ℕ} (xs ys : Bits n), Overflow xs ys ↔ overflow xs ys = true := by
  apply @Bits.rec2 (λ n xs ys => Overflow xs ys ↔ overflow xs ys = true)
  · apply iff_of_false
    · simp [Overflow]; rfl
    · simp [overflow]
  · intro n x xs y ys ih
    simp only [Overflow, Bits.toNat, overflow, Nat.two_pow_succ]
    cases x <;> cases y <;> simp
    · apply Nat.add_lt_add <;> apply Bits.toNat_lt_pow
    · rw [← ih, Nat.add_comm _ ys.toNat]
      rw [← Nat.add_assoc, Nat.add_le_add_iff_right]
      simp [Overflow]
    · rw [Nat.add_assoc, Nat.add_le_add_iff_left, ← ih]
      simp [Overflow]
    · omega













-- lemma Bits.toNat_lt_toNat {k} (xs ys : Bits k) (h : xs < ys) : xs.toNat < ys.toNat := by
--   induction k with
--   | zero => cases xs; cases ys; cases h
--   | succ k ih =>
--     match xs, ys with
--     | x +> xs, y +> ys =>
--       rw [cons_lt_cons] at h
--       rcases h with h | ⟨h_eq, h_lt⟩
--       · simp [toNat]
--         apply @Nat.lt_of_lt_of_le _ (2 * xs.toNat + 2 * 1)
--         · apply Nat.add_lt_add_left; cases x <;> simp [Bool.toNat]
--         · rw [← Nat.mul_add]
--           apply @Nat.le_trans _ (2 * ys.toNat)
--           · apply Nat.mul_le_mul_left _ <| Nat.succ_le_of_lt <| ih _ _ h
--           · apply Nat.le_add_right
--       · cases x <;> cases y <;>
--         try {simp [LT.lt] at h_lt; done}
--         simp [h_eq, toNat]
--
-- lemma Bits.lt_succ_of_le  {k} {xs ys : Bits k}
--     (h : ys ≠ max k) (h' : xs ≤ ys) : xs < ys.succ := by
--   induction k with
--   | zero => cases h nil_eq_nil
--   | succ k ih =>
--     match xs, ys with
--     | x +> xs, y +> ys =>
--       rw [cons_le_cons] at h'
--       simp [Ne, cons_eq_max] at h; cases y
--       · simp [succ]; rcases h' with h' | h'
--         · rw [cons_lt_cons]; left; apply h'
--         · rw [cons_lt_cons, Bool.eq_false_of_le_false h'.right]
--           right; refine ⟨h'.left, cst⟩
--       · simp [true_eq_one] at h; simp [succ]
--         rw [cons_lt_cons]; left; apply ih h
--         apply le_of_lt_or_eq; rcases h' with h' | h'
--         · left; exact h'
--         · right; exact h'.left
--

lemma Bits.toNat_lt_toNat :
    ∀ {k} (xs ys : Bits k), xs < ys → xs.toNat < ys.toNat := by
  apply rec2
  · intro h; cases h
  · intro k x xs y ys ih h
    rcases h with h | h
    · rw [Bool.lt_iff] at h; rcases h with ⟨⟨_⟩, ⟨_⟩⟩;simp [toNat]
      apply le_trans (toNat_lt_pow xs) <| Nat.le_add_right _ _
    · rcases h with ⟨⟨_⟩, h⟩; simp [toNat]; apply ih h

lemma Bits.toNat_le_toNat {k} (xs ys : Bits k) (h : xs ≤ ys) :
    xs.toNat ≤ ys.toNat := by
  rcases lt_or_eq_of_le h with h | ⟨⟨_⟩⟩
  · apply Nat.le_of_lt <| toNat_lt_toNat _ _ h
  · apply Nat.le_refl

-- lemma Bits.toNat_le_toNat {k} (xs ys : Bits k) (h : xs ≤ ys) : xs.toNat ≤ ys.toNat := by
--   by_cases h' : ys = max k
--   · apply Nat.le_of_lt_succ; rw [h', max_toNat_succ]; apply toNat_lt_pow
--   · apply Nat.le_of_lt_succ; rw [← succ_toNat_assoc _ h']
--     apply toNat_lt_toNat _ _ <| lt_succ_of_le h' h
--
-- lemma Bits.nof_of_add_eq_max {k} (xs ys : Bits k) (h : xs + ys = max _) :
--     Nof xs ys := by
--   induction k with
--   | zero => cases xs; cases ys; simp [Nof]; rfl
--   | succ k ih =>
--     match xs, ys with
--     | x +> xs, y +> ys =>
--       have h' : xs + ys = max _ ∧ y = !x := by
--         cases x <;> cases y
--         · simp [cons_add_cons, incr] at h;
--           rw [cons_eq_max] at h; simp [true_eq_one] at h
--         · simp [cons_add_cons, incr] at h;
--           rw [cons_eq_max] at h; refine' ⟨h.left, rfl⟩
--         · simp [cons_add_cons, incr, succ] at h;
--           rw [cons_eq_max] at h; refine' ⟨h.left, rfl⟩
--         · simp [cons_add_cons, incr, succ] at h;
--           rw [cons_eq_max] at h; simp at h
--       rw [h'.right, nof_iff_not_overflow]
--       unfold Overflow
--       simp only [Bits.toNat]
--       rw [not_le]
--       have hrw :
--         2 * toNat xs + x.toNat + (2 * toNat ys + (!x).toNat) =
--           2 * (toNat xs + toNat ys) + 1 := by
--         rw [Nat.mul_add, Nat.add_assoc, Nat.add_assoc]
--         simp; rw [Nat.add_comm, Nat.add_assoc]
--         cases x <;> rfl
--       rw [hrw, Nat.pow_succ, Nat.mul_comm (_ ^ _), Nat.lt_floor_left (by simp)]
--       apply Nat.mul_lt_mul_of_pos_left _ (by simp)
--       apply ih  _ _ h'.left
--
-- lemma Bits.cons_Overflow_cons {k} {xs ys : Bits k} {x y} (h : xs ↟ ys) : (x +> xs) ↟ (y +> ys) := by
--   simp [Overflow, Bits.toNat, Nat.pow_succ, Nat.mul_comm]
--   apply Nat.le_trans <| Nat.mul_le_mul_left 2 h
--   simp [Nat.mul_add]; rw [Nat.add_assoc, Nat.mul_comm]
--   simp; apply Nat.le_trans _ <| Nat.le_add_left _ _
--   rw [Nat.mul_comm]; apply Nat.le_add_right
--
-- lemma Bits.of_cons_nof_cons {k} {xs ys : Bits k} {x y} :
--     Nof (x +> xs) (y +> ys) → Nof xs ys := by
--   simp [nof_iff_not_overflow]; apply mt cons_Overflow_cons
--
-- lemma Bits.add_toNat {k} (xs ys : Bits k) (h : Nof xs ys) :
--     (xs + ys).toNat = xs.toNat + ys.toNat := by
--   induction k with
--   | zero => simp [nil_toNat]
--   | succ k ih =>
--     match xs, ys with
--     | x +> xs, y +> ys =>
--       by_cases h_eq : (xs + ys) +> y = max _
--       · rw [cons_eq_max] at h_eq
--         cases x
--         · rw [cons_add_cons]
--           simp only [incr, id, toNat]
--           rw [ih _ _ <| nof_of_add_eq_max _ _ h_eq.left]
--           rw [h_eq.right]
--           simp [Bool.one_toNat]
--           rw [Nat.mul_add, Nat.add_assoc]
--         · cases h_eq.right
--           simp [Nof, toNat, Bool.one_toNat] at h
--           have h_rw : 2 * xs.toNat + 1 + (2 * ys.toNat + 1) = 2 ^ k * 2 := by
--             rw [Nat.mul_comm _ 2, ← max_toNat_succ, ← h_eq.left]
--             rw [ih _ _ <| nof_of_add_eq_max _ _ h_eq.left]; omega
--           rw [h_rw, Nat.pow_succ] at h; simp [lt_irrefl] at h
--       · simp [cons_add_cons]
--         rw [incr_toNat_assoc _ _ h_eq]; simp [toNat]
--         rw [ih _ _ <| of_cons_nof_cons h, Nat.mul_add]
--         rw [Nat.add_assoc, Nat.add_assoc, Nat.add_assoc]
--         apply congr_arg (2 * xs.toNat + ·)
--         rw [← Nat.add_assoc, Nat.add_comm]
--

lemma Bool.beq_eq_true (a b : Bool) : ((a == b) = true) = (a = b) := by
  cases a <;> cases b <;> simp

lemma Bits.lt_iff_lt' {k} (xs ys : Bits k) :
    xs < ys ↔ lt' xs ys = true := by
  induction k with
  | zero =>
    cases xs; cases ys
    apply iff_of_false <;> {intro h; cases h}
  | succ k ih =>
    match xs, ys with
    | x +> xs, y +> ys =>
     simp only [lt']
     rw [cons_lt_cons, Bool.or_eq_true, Bool.and_eq_true (_ == _)]
     rw [← ih, Bool.beq_eq_true]; simp only [LT.lt]

lemma Bits.sub_self {n} {xs : Bits n} : xs - xs = 0 := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [cons_sub_cons]; cases x <;>
    simp [ih, mt (lt_iff_lt' _ _).mpr <| @Bits.lt_irrefl _ xs] <;> rfl

lemma Bits.toNat_add {k} (xs ys : Bits k) :
    (xs + ys).toNat = xs.toNat + ys.toNat - (cond (overflow xs ys) (2 ^ k) 0) := by
  apply @Bits.rec2
    (λ k xs ys => (xs + ys).toNat = xs.toNat + ys.toNat - (cond (overflow xs ys) (2 ^ k) 0))
  · simp [toNat]
  · intro k x xs y ys ih
    rw [cons_add_cons]; simp only [overflow, toNat]; rw [ih]
    rcases Bool.eq_false_or_eq_true (overflow xs ys) with h'' | h'' <;>
      rw [h''] <;> cases x <;> cases y <;> simp <;>
      try {rw [Nat.two_pow_succ]} <;> try {omega}
    · rw [← Nat.add_sub_assoc, Nat.add_sub_cancel_left]
      rw [← overflow_iff_overflow_eq_true] at h''; exact h''
    · have h_rw : 2 ^ k + xs.toNat + (2 ^ k + ys.toNat) =
                    xs.toNat + ys.toNat + (2 ^ k + 2 ^ k) := by omega
      rw [← Nat.add_sub_assoc, Nat.add_sub_cancel_left, h_rw]; omega
      rw [← overflow_iff_overflow_eq_true] at h''; exact h''

lemma Bits.toNat_add_eq_of_nof {k} (xs ys : Bits k) (h : Nof xs ys) :
    (xs + ys).toNat = xs.toNat + ys.toNat := by
  rw [nof_iff_not_overflow, overflow_iff_overflow_eq_true] at h
  rw [toNat_add]; simp [h]

lemma Bits.toNat_sub {k} (xs ys : Bits k) :
    (xs - ys).toNat = (cond (lt' xs ys) (2 ^ k) 0) + xs.toNat - ys.toNat := by
  induction k with
  | zero => cases xs; cases ys; simp [lt', toNat]
  | succ k ih =>
    match xs, ys with
    | x +> xs, y +> ys =>
      have h : ys.toNat ≤ 2 ^ k + xs.toNat :=
        le_trans (Nat.le_of_lt <| toNat_lt_pow _) <| Nat.le_add_right _ _
      have h' : lt' xs ys = false → ys.toNat ≤ xs.toNat := by
        intro h; apply toNat_le_toNat; rw [← not_lt, lt_iff_lt', h]; simp
      rw [cons_sub_cons]; simp only [toNat, lt']; rw [ih]
      rcases Bool.eq_false_or_eq_true (lt' xs ys) with h'' | h'' <;>
        rw [h''] <;> cases x <;> cases y <;> simp <;> try rw [Nat.two_pow_succ]
      · rw [← Nat.add_sub_assoc h, Nat.add_assoc]
      · omega
      · rw [Nat.sub_add_eq, ← Nat.add_sub_assoc h]; omega
      · rw [Nat.sub_add_eq, ← Nat.add_sub_assoc (h' h'')]; omega
      · rw [Nat.add_sub_assoc (h' h'')]
      · rw [Nat.sub_add_eq, Nat.add_sub_cancel_left]

lemma Bits.toNat_sub_eq_of_le {k} (xs ys : Bits k) (h : ys ≤ xs) :
    (xs - ys).toNat = xs.toNat - ys.toNat := by
  rw [toNat_sub]; rw [← not_lt, lt_iff_lt'] at h; simp [h]

-- lemma Bits.sub_toNat {k} (xs ys : Bits k) (h : ys ≤ xs) :
--     (xs - ys).toNat = xs.toNat - ys.toNat := by
--   induction k with
--   | zero => simp [nil_toNat]
--   | succ k ih =>
--     match xs, ys with
--     | x +> xs, y +> ys =>
--       by_cases hd : (xs - ys) +> x = 0
--       · rw [cons_eq_zero_iff] at hd
--         have h_eq : xs = ys := by
--           have h := congr_arg (λ zs => zs + ys) hd.left
--           simp [sub_add_cancel, zero_add] at h; exact h
--         have h_eq' : y = 0 := by
--           rw [h_eq, hd.right, cons_le_cons] at h
--           simp [Bits.lt_irrefl] at h
--           cases y
--           · apply false_eq_zero
--           · simp [LE.le] at h
--         rw [h_eq, h_eq', hd.right, sub_self, Nat.sub_self, zero_toNat]
--       · rw [cons_sub_cons]
--         rw [decr_toNat_assoc _ _ hd]
--         simp only [toNat]; rw [cons_le_cons] at h
--         rcases h with h | h
--         · rw [ih _ _ <| Bits.le_of_lt h]
--           rw [Nat.mul_sub_left_distrib, Nat.sub_add_eq]
--           apply congr_arg₂ _ _ rfl
--           rw [← Nat.sub_add_comm]
--           rw [Nat.mul_le_mul_iff (by simp)]
--           apply Nat.le_of_lt <| toNat_lt_toNat _ _ h
--         · rw [h.left, sub_self, zero_toNat, Nat.mul_zero, Nat.zero_add]
--           rw [Nat.add_comm, Nat.sub_add_eq]
--           rw [Nat.add_sub_assoc <| Nat.le_refl _]
--           rw [Nat.sub_self, Nat.add_zero]
--

lemma Bits.append_eq_append_iff {m n} {xs ys : Bits m} {xs' ys' : Bits n} :
    xs ++ xs' = ys ++ ys' ↔ (xs = ys ∧ xs' = ys') := by
  revert xs xs' ys ys' n
  induction m with
  | zero =>
    intros n xs ys xs' ys'
    cases xs; cases ys; simp; rfl
  | succ m ih =>
    intros n xs ys xs' ys'
    rcases xs with _ | ⟨x, xs⟩
    rcases ys with _ | ⟨y, ys⟩
    simp [Bits.cons_append]
    rw [ih]; simp [and_assoc]

lemma Bits.length_toBytes {n} (xs : Bits (8 * n)) : xs.toBytes.length = n := by
  induction n with
  | zero => cases xs; rfl
  | succ n ih =>
    match xs with
    | _ +> _ +> _ +> _ +> _ +> _ +> _ +> _ +> _ =>
      simp [toBytes, List.length]; apply ih

lemma List.takeD_eq_self {ξ : Type u} {n : ℕ} {xs : List ξ} (x : ξ)
    (h : n = xs.length) : List.takeD n xs x = xs := by
  rw [takeD_eq_take x <| le_of_eq h, take_of_length_le <| le_of_eq h.symm]

lemma toBits'_toBytes {n} (xs : Bits (8 * n)) :
    Bytes.toBits' n (Bits.toBytes xs) = xs := by
  induction n with
  | zero => cases xs; rfl
  | succ n ih =>
    match xs with
    | _ +> _ +> _ +> _ +> _ +> _ +> _ +> _ +> xs' =>
      simp only [Bytes.toBits']; rw [ih]; rfl

lemma toBits_toBytes {n} (xs : Bits (8 * n)) :
    Bytes.toBits n (Bits.toBytes xs) = xs := by
  simp only [Bits.toBytes, Bytes.toBits];
  rw [List.takeD_eq_self, List.reverse_reverse]
  · apply toBits'_toBytes
  · rw [List.length_reverse, Bits.length_toBytes]







--def Bits.succ : ∀ {n}, Bits n →  Bits n
--  | 0, ⦃⦄ => ⦃⦄
--  | _ + 1, x +> xs => (x != xs.isMax) +> xs.succ

lemma Bits.succ_cons {n} (x) (xs : Bits n) :
     (x +> xs).succ = (x != xs.isMax) +> xs.succ := rfl

lemma Bits.append_eq_max_iff {m n} (xs : Bits m) (ys : Bits n) :
    (xs ++ ys) = max (n + m) ↔ (xs = max m ∧ ys = max n) := by
  induction xs with
  | nil => simp [@nil_eq_nil ⦃⦄ (max 0)]; rfl
  | cons x xs ih =>
    rw [cons_append]; conv => lhs; rhs; apply (@max_eq_cons (n + _))
    rw [cons_eq_cons, ih, max_eq_cons, cons_eq_cons, and_assoc]

-- lemma Bits.zero_append_zero {m n} :
--     (0 : Bits m) ++ (0 : Bits n) = (0 : Bits (n + m)) := by
--   induction m with
--   | zero => rfl
--   | succ m ih =>
--     rw [zero_eq_append]
--     --simp [zero]; rw [cons_append, ih]


lemma Bits.max_append_max {m n} :
    max m ++ max n = max (n + m) := by
  induction m with
  | zero => rfl
  | succ m ih => simp [max]; rw [cons_append, ih]

lemma Bits.succ_append {m n} (xs : Bits m) (ys : Bits n) :
    (xs ++ ys).succ = (if ys = max n then xs.succ else xs) ++ ys.succ := by
  induction xs with
  | nil => split <;> rfl
  | cons x xs ih =>
    rename Nat => m
    have h_rw : (xs = max m ∧ ys = max n) ↔ (xs ++ ys).isMax = true := by
      rw [← append_eq_max_iff, eq_max_iff_isMax]
    rw [cons_append]; simp only [succ_cons]; rw [ih]
    by_cases h : xs = max _ <;> by_cases h' : ys = max n <;>
      simp [h, h'] <;> simp [h, h'] at h_rw
    · simp [h_rw, max_isMax, cons_append]
    · simp [h_rw, cons_append]
    · simp [h_rw, mt (eq_max_iff_isMax _).mpr h, cons_append]
    · simp [h_rw, cons_append]

-- lemma Bits.succ_append {m n} (xs : Bits m) (ys : Bits n) :
--     (xs ++ ys).succ = incr (if ys = max _ then 1 else 0) xs ++ ys.succ := by
--   induction ys with
--   | nil => rw [if_pos nil_eq_nil]; rfl
--   | cons ys y ih =>
--     cases y <;> simp only [succ]
--     · rw [if_neg]; rfl; simp [cons_eq_max]
--     · apply congrArg₂ _ (Eq.trans ih _) rfl
--       by_cases h : ys = max _
--       · rw [if_pos h, if_pos]; rfl
--         simp [cons_eq_max, h, Bool.one]
--       · rw [if_neg h, if_neg]; rfl
--         simp [cons_eq_max, h]
--
-- lemma Bits.succ_append_eq_of_ne {m n} (xs : Bits m) (ys : Bits n) (h : ys ≠ max _) :
--     (xs ++ ys).succ = xs ++ ys.succ := by rw [succ_append, if_neg h]; rfl

lemma Bits.toBytes_eq_cons {n} (b : Byte) {xs : Bits (8 * n)} :
    @toBytes (n + 1) (b ++ xs) = b :: toBytes xs := by
  match b with
  | ⦃_, _, _, _, _, _, _, _⦄ => rfl

def Bits.factor {k m} : ∀ {n}, Bits (k * m + k * n) → Bits (k * (m + n))
  | 0, xs => xs
  | _ + 1, xs => xs.prefix.prefix ++ Bits.factor (xs.prefix.suffix ++ xs.suffix)

def Bits.fappend {k m n} (xs : Bits (k * m)) (ys : Bits (k * n)) : Bits (k * (n + m)) :=
  factor <| xs ++ ys

def Bits.fappend_eq_append {k m n}
    (xs : Bits (k * (m + 1))) (ys : Bits (k * n)) :
    fappend xs ys = xs.prefix ++ fappend xs.suffix ys := by
  simp [fappend, factor, prefix_append, suffix_append]

lemma Bits.toBytes_eq_append {m n} {xs : Bits (8 * m)} {ys : Bits (8 * n)} :
    toBytes (fappend xs ys) = toBytes xs ++ toBytes ys := by
  induction m with
  | zero => cases xs; rfl
  | succ m ih =>
    have h_rw := @Bits.prefix_append_suffix (8 * m) 8 xs
    conv => rhs; lhs; arg 1; apply h_rw.symm
    rw [fappend_eq_append, toBytes_eq_cons, ih, toBytes_eq_cons, List.cons_append]

-- lemma Bits.max_eq_append {n} : (max (n + 1) : Bits (n + 1)) = 1 +> (max _ : Bits n) := rfl

-- lemma Bits.max_eq_append {n} : (max _ : Bits (n + 1)) = (max _ : Bits n) +> 1 := rfl
--
-- lemma Bits.append_eq_max {m n} {xs : Bits m} {ys : Bits n} :
--     xs ++ ys = max (m + n) ↔ xs = max m ∧ ys = max n := by
--   induction ys with
--   | nil => constructor <;> intro h; refine ⟨h, rfl⟩; apply h.left
--   | cons ys y ih =>
--     rename Nat => k; rw [append_cons, max_eq_append]
--     conv => lhs; rhs; apply (@max_eq_append (m + k)).symm
--     simp [max_eq_append]; rw [ih, and_assoc]
--
-- def Bytes.append : Bytes → Bytes → Bytes
--   | xs, [] => xs
--   | xs, ys :> y => append xs ys :> y
--
-- instance : HAppend Bytes Bytes Bytes := ⟨Bytes.append⟩
--
-- def Bytes.mem : Bytes → Byte → Prop
--   | [], _ => False
--   | bs :> b, b' => mem bs b' ∨ b = b'
--
-- instance : Membership Byte Bytes := ⟨Bytes.mem⟩
--
abbrev Bytes.Zero : Bytes → Prop := List.Forall (· = 0)
-- | [] => True
-- | x :: xs => x = 0 ∧ zero xs

-- lemma Bytes.zero_of_sig_eq_nil {bs : Bytes} : bs.sig = [] → bs.zero := by
--   induction bs with
--   | nil => intro _; constructor
--   | cons bs b ih =>
--     simp [sig]
--     rcases eq_nil_or_eq_cons bs.sig with h_nil | h_cons
--     · simp [h_nil]; intro h; refine ⟨ih h_nil, h⟩
--     · rcases h_cons with ⟨bs', b, h⟩; simp [h]
--
-- lemma Bytes.append_cons {xs ys : Bytes} {y} : xs ++ (ys :> y) = ((xs ++ ys) :> y) := by
--   simp [HAppend.hAppend, append]
--
-- lemma Bytes.append_inj' {xs₁ xs₂ ys₁ ys₂ : Bytes} :
--     xs₁ ++ xs₂ = ys₁ ++ ys₂ →
--     xs₂.length = ys₂.length →
--     xs₁ = ys₁ ∧ xs₂ = ys₂ := by
--   revert ys₂
--   induction xs₂ with
--   | nil =>
--     intros ys₂ h_eq h_len
--     cases ys₂ with
--     | nil => refine' ⟨h_eq, rfl⟩
--     | cons _ _ => cases h_len
--   | cons xs₂ x ih =>
--     intros ys₂ h_eq h_len
--     cases ys₂ with
--     | nil => cases h_len
--     | cons ys₂ y =>
--       simp [append_cons] at h_eq
--       rcases h_eq with ⟨h_eq, ⟨_⟩⟩
--       simp [length] at h_len
--       simp; apply ih h_eq h_len
--
-- lemma Bytes.length_append (xs ys : Bytes) : (xs ++ ys).length = xs.length + ys.length := by
--   induction ys with
--   | nil => rfl
--   | cons ys y ih =>
--     simp [append_cons, length]
--     rw [← Nat.add_assoc, ← ih]; rfl
--
-- lemma Bytes.append_inj {xs₁ xs₂ ys₁ ys₂ : Bytes}
--     (h_eq : xs₁ ++ xs₂ = ys₁ ++ ys₂)
--     (h_len : xs₁.length = ys₁.length) : xs₁ = ys₁ ∧ xs₂ = ys₂ := by
--   apply append_inj' h_eq
--   apply @Nat.add_left_cancel ys₁.length
--   have h := congrArg length h_eq
--   simp [length_append, h_len] at h; rw [h]
--
-- lemma Bytes.prefix_unique {xs ys zs : Bytes}
--     (h_len : xs.length = ys.length)
--     (h_xs : xs <<+ zs)
--     (h_ys : ys <<+ zs) : xs = ys := by
--   rcases h_xs with ⟨sfx, h⟩
--   rcases h_ys with ⟨sfx', h'⟩
--   apply And.left <| append_inj (Eq.trans h.symm h') h_len
--
-- lemma Bytes.singleton_inj {x y} (h : [x] = [y]) : x = y := by cases h; rfl
--
-- lemma Bytes.append_assoc (as bs cs : Bytes) : as ++ bs ++ cs = as ++ (bs ++ cs) := by
--   induction cs with
--   | nil => rfl
--   | cons cs c ih => simp [append_cons, ih]
--
-- lemma Bytes.prefix_trans {xs ys zs : Bytes}
--     (h : xs <<+ ys) (h' : ys <<+ zs) : xs <<+ zs := by
--   rcases h with ⟨sfx, h_sfx⟩
--   rcases h' with ⟨sfx', h_sfx'⟩
--   refine' ⟨sfx ++ sfx', _⟩
--   rw [h_sfx', h_sfx]
--   apply append_assoc
--
-- lemma Bytes.length_eq_zero {xs : Bytes} : xs.length = 0 ↔ xs = [] := by
-- cases xs <;> simp [length]
--
-- lemma Bytes.split_nil {xs ys : Bytes} : (xs <++ [] ++> ys) ↔ (xs = [] ∧ ys = []) := by
--   match xs with
--   | [] =>
--     match ys with
--     | [] => simp; rfl
--     | ys :> y => simp; intro h; cases h
--   | xs :> x => cases ys <;> {simp; intro h; cases h}
--
-- lemma Bytes.prefix_nil {xs : Bytes} : xs <<+ [] ↔ xs = [] := by
--   constructor <;> intro h
--   · rcases h with ⟨ys, h⟩; rw [split_nil] at h; apply h.left
--   · rw [h]; refine ⟨[], rfl⟩
--
-- lemma Bytes.length_snoc {xs x} : length ([x] ++ xs) = xs.length + 1 := by
--   simp [length_append, Nat.add_comm, length]


instance {ξ : Type u} {ρ : ξ → Prop} {xs : List ξ} --[dC : Decidable c]
    [d : ∀ x : ξ, Decidable (ρ x)] : Decidable (xs.Forall ρ) := by
  induction xs with
  | nil => apply instDecidableTrue
  | cons x xs ih => simp; apply instDecidableAnd

def Bytes.Max (bs : Bytes) : Prop := bs.Forall (· = .max 8)

lemma Bytes.max_cons (b) (bs : Bytes) :
    Max (b :: bs) ↔ (b = Bits.max 8 ∧ Max bs) := by
  simp only [Max, List.forall_cons]


instance (bs : Bytes) : Decidable bs.Max := by
  unfold Bytes.Max; infer_instance

def Bytes.succ : Bytes → Bytes
  | [] => []
  | b :: bs => (if Max bs then b.succ else b) :: succ bs

-- def Bytes.succ : Bytes → Bytes
--   | [] => []
--   | xs :> x =>
--     if x = Ox xF xF
--     then succ xs :> 0
--     else xs :> x.succ
--
-- lemma Bytes.succ_cons_max_eq {xs} : (xs :> Ox xF xF).succ = succ xs :> 0 := by
--   simp only [Bytes.succ]; rw [if_pos cst]
--
-- lemma Bytes.succ_cons_eq_of_ne {xs x} (h : x ≠ Ox xF xF) : (xs :> x).succ = xs :> x.succ := by
--   unfold Bytes.succ; rw [if_neg h]
--

--   | [] => True
--   | xs :> x => max xs ∧ x = Ox xF xF

lemma Bytes.toBits'_eq_zero {n} {xs : Bytes} (h : xs.Zero) :
    toBits' n xs = 0 := by
  induction n generalizing xs h with
  | zero => rfl
  | succ n ih =>
    match xs with
    | [] => simp [toBits']; rw [ih cst]; rfl
    | x :: xs =>
      simp [toBits', Bytes.Zero] at *
      simp [h.left, ih h.right]; rfl

lemma Bytes.max_iff_toBits'_eq_max {bs : Bytes} :
     bs.Max ↔ toBits' bs.length bs = Bits.max (8 * bs.length) := by
  induction bs with
  | nil => apply iff_of_true cst rfl
  | cons xs bs ih =>
    simp [max_cons, toBits']; rw [ih]
    apply (Bits.append_eq_max_iff xs (toBits' bs.length bs)).symm

lemma Bytes.toBits'_eq_max {n} {xs : Bytes} (h : xs.Max) (h' : n ≤ xs.length):
    toBits' n xs = Bits.max (8 * n) := by
  induction n generalizing xs h with
  | zero => rfl
  | succ n ih =>
    match xs with
    | [] => simp [List.length] at h'
    | x :: xs =>
      simp [List.length] at h'; simp [max_cons] at h; simp [toBits']
      rw [h.left, ih h.right h', Bits.max_append_max]; rfl

lemma List.forall_append {ξ : Type u} (π : ξ → Prop) (xs ys : List ξ)
    (h : xs.Forall π) (h' : ys.Forall π) : (xs ++ ys).Forall π := by
  induction xs with
  | nil => apply h'
  | cons x xs ih => simp [Forall] at *; refine' ⟨h.left, ih h.right⟩

lemma List.forall_reverse {ξ : Type u} (π : ξ → Prop) (xs : List ξ)
    (h : xs.Forall π) : xs.reverse.Forall π := by
  induction xs with
  | nil =>  constructor
  | cons x xs ih =>
    simp [reverse_cons] at *
    apply forall_append _ _ _ (ih h.right)
    simp [h.left]

lemma List.forall_replicate {ξ : Type u} (π : ξ → Prop) (n) (x) (h : π x) :
    (replicate n x).Forall π := by
  induction n with
  | zero => simp
  | succ n ih => simp [replicate, h, ih]

lemma List.forall_takeD {ξ : Type u} (π : ξ → Prop) (n) (xs : List ξ) (x)
    (h : xs.Forall π) (h' : π x) : (xs.takeD n x).Forall π := by
  induction n generalizing xs with
  | zero => simp [takeD]
  | succ n ih =>
    match xs with
    | [] => simp [h', forall_replicate]
    | x :: xs => simp at *; refine ⟨h.left, ih _ h.right⟩

lemma Bytes.toBits_eq_zero {n} {xs : Bytes} (h : xs.Zero) : toBits n xs = 0 := by
  apply toBits'_eq_zero (List.forall_reverse _ _ _)
  apply List.forall_takeD
  · apply List.forall_reverse _ _ h
  · rfl

-- lemma Bytes.of_toBits_succ_eq_toBits_succ {n} {bs bs' : Bytes} :
--     toBits (n + 1) bs = toBits (n + 1) bs' → toBits n bs = toBits n bs' := by
--   induction n generalizing bs bs' with
--   | zero => intro _; rfl
--   | succ n ih =>
--     match bs, bs' with
--     | nil, nil => simp [toBits]
--     | nil, cons bs' b' =>
--       simp [toBits]; intro h
--       rw [Bits.append_eq_append_iff] at h
--       rw [@ih nil bs' h.left, h.right]
--     | cons bs b, nil =>
--       simp [toBits]; intro h
--       rw [Bits.append_eq_append_iff] at h
--       rw [@ih nil bs h.left.symm, h.right]
--     | cons bs b, cons bs' b' =>
--       simp [toBits]; intro h
--       rw [Bits.append_eq_append_iff] at h
--       rw [ih h.left, h.right]

lemma List.takeD_concat {ξ : Type u} (n) (xs : List ξ) (y) :
    takeD n (xs.concat y) y = takeD n xs y := by
  induction xs generalizing n with
  | nil =>
    match n with
    | 0 => rfl
    | n + 1 => rfl
  | cons x xs ih =>
    match n with
    | 0 => rfl
    | n + 1 =>
      simp only [List.concat, takeD, headD, tail]; rw [ih]

lemma Bytes.toBits_zero_cons {n} {bs} :
    toBits n (0 :: bs) = toBits n bs := by
  unfold toBits; rw [List.reverse_cons', List.takeD_concat]

lemma Bytes.sig_toBits {n} (bs : Bytes) : bs.sig.toBits n = bs.toBits n := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    unfold sig
    by_cases hb : b = 0
    · cases hb; rw [List.dropWhile_cons_of_pos _]
      · apply Eq.trans ih; rw [toBits_zero_cons]
      · rw [decide_eq_true rfl]
    · rw [List.dropWhile_cons_of_neg _]
      rw [decide_eq_false hb]; simp

-- lemma Bytes.sig_toBits {n} (bs : Bytes) : bs.sig.toBits n = bs.toBits n := by
--   induction bs with
--   | nil => rfl
--   | cons bs b ih =>
--     rcases eq_nil_or_eq_cons bs.sig with h_nil | h_cons
--     · simp [sig]; simp [h_nil]
--       by_cases hb : b = 0
--       · rw [if_pos hb]
--         rw [@toBits_eq_zero n (bs :> b) ⟨zero_of_sig_eq_nil h_nil, hb⟩]
--         apply toBits_eq_zero; constructor
--       · rw [if_neg hb]
--         cases n with
--         | zero => rfl
--         | succ n =>
--           simp [toBits]
--           rw [← of_toBits_succ_eq_toBits_succ ih, h_nil]
--     · rcases h_cons with ⟨bs', b', h_sig⟩
--       simp [sig]; simp [h_sig]
--       cases n with
--       | zero => rfl
--       | succ n =>
--         simp [toBits]
--         rw [← of_toBits_succ_eq_toBits_succ ih, h_sig]
--
-- lemma Bytes.nil_append {xs} : [] ++ xs = xs := by
--   induction xs with
--   | nil => rfl
--   | cons xs x ih => rw [append_cons, ih]
lemma Bits.succ_max {k} : succ (max k) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp [max, succ, max_isMax, ih]; rfl

lemma Bytes.zero_succ_of_max {bs : Bytes} (h : Max bs) : (succ bs).Zero := by
  induction bs with
  | nil => constructor
  | cons b bs ih =>
    rw [max_cons] at h
    simp [succ, Zero, h.left, h.right, ih h.right, Bits.succ_max]

lemma Bytes.toBits'_succ  {bs : Bytes} :
    bs.succ.toBits' bs.length = (bs.toBits' bs.length).succ := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [Bytes.succ, toBits', Bits.succ_append, List.length]
    rw [ih]; by_cases h' : Max bs
    · simp [h', max_iff_toBits'_eq_max.mp h']
    · simp [h', mt max_iff_toBits'_eq_max.mpr h']


-- lemma Bytes.toBits_succ {n} {bs : Bytes} (h : ¬ bs.Max) :
--     bs.succ.toBits n = (bs.toBits n).succ := by
--   unfold toBits
--   have h_rw := @toBits'_succ (List.takeD n bs.reverse 0).reverse
--   rw [List.length_reverse, List.takeD_length] at h_rw
--   rw [← h_rw]
--   apply congr_arg








--  induction n generalizing bs with
--  | zero => rfl
--  | succ n ih =>
--    match bs with
--    | [] => cases (h cst)
--    | b :: bs =>
--      simp only [Bytes.succ, toBits]
--



-- lemma Bytes.toBits_succ {n} {xs : Bytes} :
--     ¬ xs.max → Bytes.toBits n xs.succ = (Bytes.toBits n xs).succ := by
--   revert xs
--   induction n with
--   | zero => intros _ _; simp [Bytes.toBits]; rfl
--   | succ n ih =>
--     intro xs h
--     match xs with
--     | [] => cases h (by constructor)
--     | xs :> x =>
--       cases em (x = Ox xF xF) with
--       | inl hx =>
--         rw [hx]; simp [Bytes.succ, Bytes.toBits, Bits.succ]
--         rw [ih _]; rfl; intro hc; apply h; refine ⟨hc, hx⟩
--       | inr hx =>
--         rw [Bytes.succ_cons_eq_of_ne hx]; simp [Bytes.toBits]
--         rw [Bits.succ_append_eq_of_ne _]; apply hx
--

lemma Bits.eq_max_iff_max_toBytes {k : ℕ} (xs : Bits (8 * k)) :
    xs = max (8 * k) ↔ xs.toBytes.Max := by
  induction k with
  | zero => cases xs; apply iff_of_true rfl cst
  | succ k ih =>
    rw [← @prefix_append_suffix (8 * k) 8 xs, toBytes_eq_cons]
    conv => lhs; rhs; apply (@max_append_max 8 (8 * k)).symm
    rw [append_eq_append_iff, ih]; simp [Bytes.Max]

lemma Bits.toBytes_succ {n} :
    ∀ {xs : Bits (8 * n)}, xs.succ.toBytes = Bytes.succ xs.toBytes := by
  induction n with
  | zero => simp [Nat.mul_zero]; intro xs; cases xs; rfl
  | succ n ih =>
    simp [Nat.mul_succ]; intro xs
    rw [← @prefix_append_suffix (8 * n) 8 xs, toBytes_eq_cons]
    simp [Bytes.succ]
    rw [← @ih xs.suffix, succ_append, toBytes_eq_cons]
    split
    · simp [(eq_max_iff_max_toBytes _).mp asm]
    · simp [mt (eq_max_iff_max_toBytes _).mpr asm]

















-- lemma Bits.toBytes_succ {n} {xs : Bits (8 * n)} :
--     xs.succ.toBytes = Bytes.succ xs.toBytes := by
--   revert xs
--   induction n with
--   | zero => simp [Nat.mul_zero]; intro xs; cases xs; rfl
--   | succ n ih =>
--     simp [Nat.mul_succ]; intro xs
--     rw [← @Bits.prefix_append_suffix (8 * n) 8 xs]
--     cases em (xs.tail = Ox xF xF) with
--     | inl h =>
--       rw [h]; simp only [Bits.toBytes]
--       apply Eq.trans _ <| Eq.symm Bytes.succ_cons_max_eq
--       rw [ih]; rfl
--     | inr h =>
--       rw [Bits.succ_append_eq_of_ne _]
--       simp [Bits.toBytes_append]
--       rw [Bytes.succ_cons_eq_of_ne h]
--       apply h

def List.drop? {ξ : Type u} : Nat → List ξ → Option (List ξ)
  | 0, xs => some xs
  | _ + 1, [] => none
  | n + 1, _ :: xs => xs.drop? n

lemma List.drop?_add {ξ : Type u} (m n : Nat) (xs : List ξ) :
    drop? (m + n) xs = drop? n xs >>= drop? m := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih =>
    cases xs <;> simp only [drop?]
    · rfl
    · apply ih

lemma List.get?_eq_drop?_head? {ξ : Type u} {xs : List ξ} {n : Nat} :
    get? xs n = drop? n xs >>= head? := by
  induction n generalizing xs with
  | zero => cases xs <;> simp [drop?]
  | succ n ih =>
    cases xs
    · simp [drop?]
    · simp only [get?, drop?, ih]

def List.take? {ξ : Type u} : Nat → List ξ → Option (List ξ)
  | 0, _ => some []
  | _ + 1, [] => none
  | n + 1, x :: xs => (x :: ·) <$> xs.take? n

def List.slice? {ξ : Type u} (xs : List ξ) (m n : Nat) : Option (List ξ) :=
  drop? m xs >>= take? n

def List.Slice {ξ : Type u} (xs : List ξ) (m : Nat) (ys : List ξ) : Prop :=
  ∃ n, xs.slice? m n = some ys

lemma List.slice?_cons {ξ : Type u} (x) (xs : List ξ) (m n : Nat) :
    slice? (x :: xs) (m + 1) n = slice? xs m n := rfl

def List.sliceD {ξ : Type u} [Zero ξ] (xs : List ξ) (m n : Nat) (x : ξ) : List ξ :=
  takeD n (drop m xs) x

-- lemma List.take?_eq_some_cons {ξ : Type u}
--     (n : ℕ) (x : ξ) (xs : List ξ) (y : ξ) (ys : List ξ) :
--     take? (n + 1) (x :: xs) = some (y :: ys) ↔ x = y ∧ take? n xs = some ys := by
--   simp only [take?]
--   cases take? n xs with
--   | none => simp
--   | some zs => simp

lemma List.slice?_eq_cons_iff {ξ : Type u} {xs : List ξ} {m n : Nat} {y} {ys} :
    slice? xs m (n + 1) = some (y :: ys) ↔
      (get? xs m = some y ∧ slice? xs (m + 1) n = some ys) := by
  induction m generalizing xs with
  | zero =>
    match xs with
    | [] => simp [slice?, drop?, Bind.bind, Option.bind, take?, get?]
    | x :: xs =>
      simp only
        [slice?, drop?, Bind.bind, Option.bind, get?, Option.some_inj, take?]
      cases take? n xs <;> simp
  | succ m ih =>
    match xs with
    | [] => simp [slice?, drop?, Bind.bind, Option.bind, take?, get?]
    | x :: xs =>
      rw [List.slice?_cons, ih]; rfl

lemma List.slice_cons_iff {ξ : Type u} {xs : List ξ} {m : Nat} {y} {ys} :
    xs.Slice m (y :: ys) ↔ (get? xs m = some y ∧ xs.Slice (m + 1) ys) := by
  simp only [Slice]
  constructor <;> intro h
  · rcases h with ⟨_ | n, h⟩
    · revert h; unfold slice?
      cases xs.drop? m with
      | none => simp
      | some xs' => simp [take?]
    · rw [slice?_eq_cons_iff] at h
      refine' ⟨h.left, _, h.right⟩
  · rcases h with ⟨h, n, h'⟩
    refine ⟨_, slice?_eq_cons_iff.mpr ⟨h, h'⟩⟩

lemma List.length_take? {ξ : Type u} {n : Nat} {xs ys : List ξ} :
    take? n xs = some ys → n = ys.length := by
  induction n generalizing xs ys with
  | zero => simp [take?]; intro h; simp [h]
  | succ n ih =>
    cases xs <;> simp [take?]
    intro ys' h h'; rw [ih h, ← h']; rfl

lemma List.length_slice? {ξ : Type u} {xs} {m n : Nat} {ys : List ξ} :
    slice? xs m n = some ys → n = ys.length := by
  unfold slice?; cases xs.drop? m <;> simp; apply length_take?

lemma List.get?_eq_of_slice?_eq {ξ : Type u} {xs : List ξ} {m n : Nat} {y} {ys} :
    slice? xs m (n + 1) = some (y :: ys) → get? xs m = some y := by
  rw [slice?_eq_cons_iff]; apply And.left

lemma List.get?_eq_of_slice {ξ : Type u} {xs : List ξ} {m : Nat} {y} {ys} :
    Slice xs m (y :: ys) → get? xs m = some y := by
  rw [slice_cons_iff]; apply And.left

lemma List.slice_iff_get?_eq {ξ : Type u} {xs : List ξ} {m : Nat} {y} :
    Slice xs m [y] ↔ get? xs m = some y := by
  refine' ⟨get?_eq_of_slice, λ h => ⟨1, _⟩⟩;
  revert h; rw [get?_eq_drop?_head?]; unfold slice?
  cases xs.drop? m with
  | none => simp
  | some xs' => cases xs' <;> simp; intro h'; simp [h', take?]

lemma List.of_take?_eq_append {ξ : Type u} {xs : List ξ}
    {n : Nat} {ys zs : List ξ} (h : take? n xs = some (ys ++ zs)) :
    take? ys.length xs = some ys ∧ xs.slice? ys.length zs.length = some zs := by
  induction ys generalizing n xs with
  | nil => simp [slice?, drop?] at *; rw [← length_take? h]; refine' ⟨rfl, h⟩
  | cons y ys ih =>
    cases n <;> simp [take?] at h
    cases xs <;> simp [take?] at h
    rcases h with ⟨h, ⟨_⟩⟩; constructor
    · rw [length_cons]; unfold take?; rw [(ih h).left]; rfl
    · apply (ih h).right

lemma List.of_slice?_eq_append {ξ : Type u} {xs : List ξ}
    {m n : Nat} {ys zs} (h : slice? xs m n = some (ys ++ zs)) :
    slice? xs m ys.length = some ys ∧
    slice? xs (m + ys.length) zs.length = some zs := by
  revert h; unfold slice?; rw [Nat.add_comm, drop?_add]
  cases xs.drop? m <;> simp; rename List ξ => xs'; apply of_take?_eq_append

lemma List.slice?_eq_prefix {ξ : Type u} {xs : List ξ}
    {m n : Nat} {ys zs} (h : slice? xs m n = some (ys ++ zs)) :
    slice? xs m ys.length = some ys := (of_slice?_eq_append h).left

lemma List.slice_prefix {ξ : Type u} {xs : List ξ}
    {m : Nat} {ys zs} (h : Slice xs m (ys ++ zs)) : Slice xs m ys := by
  rcases h with ⟨n, h⟩; refine ⟨_, (of_slice?_eq_append h).left⟩

-- lemma List.slice?_eq_suffix {ξ : Type u} {xs : List ξ}
--     {m n : Nat} {ys zs} (h : slice? xs m n = some (ys ++ zs)) :
--     slice? xs (m + ys.length) zs.length = some zs := (of_slice?_eq_append h).right

lemma List.slice_suffix {ξ : Type u} {xs : List ξ} {m : Nat} {ys zs}
    (h : Slice xs m (ys ++ zs)) : Slice xs (m + ys.length) zs := by
  rcases h with ⟨n, h⟩; refine ⟨_, (of_slice?_eq_append h).right⟩

lemma List.get?_length_eq_none {ξ : Type y} {xs : List ξ} :
    xs.get? xs.length = none :=
  (@get?_eq_none _ xs _).mpr (Nat.le_refl _)

lemma List.get?_length_ne_some {ξ : Type y} {xs : List ξ} {y} :
    xs.get? xs.length ≠ some y := by simp [get?_length_eq_none]

lemma List.not_slice_length {xs} {y} {ys : List ξ} :
    ¬ Slice xs xs.length (y :: ys) := by simp [slice_cons_iff]

--   intro h; rcases h with ⟨pfx, sfx, h_split, h_pfx, h_len⟩
--   have h_sfx : sfx = [] := by
--     have h := congrArg Bytes.length h_split
--     rw [Bytes.length_append, h_len] at h
--     have h' := Nat.eq_sub_of_add_eq' h.symm; simp at h'
--     rw [← Bytes.length_eq_zero, h']
--   rw [h_sfx, Bytes.prefix_nil] at h_pfx; cases h_pfx

  --rcases h with ⟨n, h⟩; refine ⟨_, (of_slice?_eq_append h).left⟩

lemma List.take?_length {ξ : Type u} (xs : List ξ) :
    take? xs.length xs = some xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [take?, ih]

lemma List.slice_refl {ξ : Type u} (xs : List ξ) : List.Slice xs 0 xs := by
  refine' ⟨xs.length, _⟩; simp [slice?, drop?, take?_length]

-- def sliceFill (bs : Bytes) (loc sz : Nat) (sc : Bytes) : Prop :=
--   (slice bs loc sc ∧ sc.length = sz) ∨
--   ∃ pfx sfx zrs,
--     (pfx <++ bs ++> sfx) ∧
--     (sfx <++ sc ++> zrs) ∧
--     pfx.length = loc ∧
--     sc.length = sz ∧
--     Bytes.zero zrs
--
-- lemma slice_unique {xs ys zs : Bytes} {k}
--     (h_eq : ys.length = zs.length)
--     (h_ys : slice xs k ys)
--     (h_zs : slice xs k zs) : ys = zs := by
--   simp [slice] at h_ys
--   rcases h_ys with ⟨pfx, sfx, h_split, h_pfx, h_len⟩
--   rcases h_zs with ⟨pfx', sfx', h_split', h_pfx', h_len'⟩
--   cases
--     And.right <|
--       Bytes.append_inj
--         (Eq.trans h_split.symm h_split')
--           (Eq.trans h_len h_len'.symm)
--   apply Bytes.prefix_unique h_eq h_pfx h_pfx'
--
-- lemma slice_singleton_unique {xs : Bytes} {k} {x y}
--     (h : slice xs k [x]) (h' : slice xs k [y]) : x = y := by
--   apply Bytes.singleton_inj <| slice_unique _ h h'; rfl
--
-- lemma slice_prefix {xs ys zs : Bytes} {k} (h : slice xs k (ys ++ zs)) :
--     slice xs k ys := by
--   rcases h with ⟨pfx, sfx, h_xs, h_sfx, h_len⟩
--   refine' ⟨pfx, sfx, h_xs, _, h_len⟩
--   apply Bytes.prefix_trans (pref_append _ _) h_sfx
--
-- lemma slice_suffix {xs ys zs : Bytes} {k} (h : slice xs k (ys ++ zs)) :
--     slice xs (k + ys.length) zs := by
--   rcases h with ⟨pfx, sfx, h_xs, h_sfx, h_len⟩
--   rcases h_sfx with ⟨sfx', h_sfx⟩
--   refine' ⟨pfx ++ ys, zs ++ sfx', _, pref_append _ _, _⟩
--   · rw [h_xs, h_sfx]; unfold Split; simp [← Bytes.append_assoc]
--   · rw [← h_len]; apply Bytes.length_append
--
lemma List.append_slice_suffix {ξ : Type y} {xs ys : List ξ} :
    Slice (xs ++ ys) xs.length ys := by
  have h := slice_suffix <| slice_refl <| xs ++ ys
  rw [Nat.zero_add] at h; exact h

lemma zero_toBytes_zero {n} : (@Bits.toBytes n 0).Zero := by
  induction n with
  | zero => constructor
  | succ n ih => simp [Bits.toBytes, Bytes.Zero]; refine ⟨rfl, ih⟩


lemma toBytes_zero_eq_replicate_zero {n} :
    (@Bits.toBytes n 0) = List.replicate n (0 : Byte) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h : (0 : Bits (8 * (n + 1))) = (0 : Byte) ++ (0 : Bits (8 * n)) := rfl
    rw [h]; simp [Bits.toBytes_eq_cons, List.replicate, ih]

-- lemma Bits.zero_ne_one : ∀ {n}, (0 : Bits (n + 1)) ≠ (1 : Bits (n + 1))
--   | 0, h => by cases h
--   | n + 1, h => by cases h
--
-- lemma Bits.invert_zero_eq_max {n} : ~ (0 : Bits n) = max _ := by
--   induction n with
--   | zero => apply nil_eq_nil
--   | succ n ih => rw [zero_eq_cons]; simp only [max, not]; rw [ih]; rfl
--
-- lemma Bits.max_and {n} {xs : Bits n} : and (max n) xs = xs := by
--   induction n with
--   | zero => apply nil_eq_nil
--   | succ n ih =>
--     cases xs with
--     | cons xs x =>
--       simp [max]
--       rw [cons_and_cons]
--       simp [Nat.add] at ih
--       rw [@ih xs]
--       cases x <;> rfl


lemma Bits.zipWith_comm (f : Bool → Bool → Bool)
    (hf : ∀ x y, f x y = f y x) (n) :
    ∀ x y : Bits n, zipWith f x y = zipWith f y x := by
  induction n with
  | zero => intro xs ys; apply nil_eq_nil
  | succ n ih =>
    intros xs ys
    match xs, ys with
    | x +> xs, y +> ys =>
      simp [zipWith, ih xs ys, hf x y]

lemma Bits.and_comm {n} : ∀ (x y : Bits n), and x y = and y x := by
  apply zipWith_comm; apply Bool.and_comm


lemma Bits.zero_and {n} {xs : Bits n} : and (0 : Bits n) xs = 0 := by
  induction n with
  | zero => apply nil_eq_nil
  | succ n ih =>
    cases xs with
    | cons xs x =>
      rw [zero_eq_cons, cons_and_cons, ih]
      cases x <;> rfl

lemma Bits.and_zero {n} {xs : Bits n} : and xs (0 : Bits n) = 0 := by
  rw [and_comm, zero_and]

-- lemma Bool.toNat_inj (x y : Bool) : x.toNat = y.toNat → x = y := by
--   cases x <;> cases y <;> simp
--
-- lemma Bits.toNat_inj {k} (xs ys : Bits k) (h : xs.toNat = ys.toNat) : xs = ys := by
--   induction k with
--   | zero => apply Bits.nil_eq_nil
--   | succ k ih =>
--     match xs, ys with
--     | x +> xs, y +> ys =>
--       simp [Bits.toNat] at h
--       cases Nat.eq_floor (Bool.toNat_lt _) (Bool.toNat_lt _) h
--       rw [ih xs ys asm, Bool.toNat_inj x y asm]
--
-- lemma toNat_toBits {k : ℕ} {xs : Bits k} : (Nat.toBits k <| Bits.toNat xs) = xs := by
--   apply Bits.toNat_inj; rw [toBits_toNat _ (Bits.toNat_lt_pow _)]
--
-- lemma Bits.of_toNat_le_toNat {k : ℕ} {xs ys : Bits k}
--     (h : xs.toNat ≤ ys.toNat) : xs ≤ ys := by
--   have h' := toBits_le_toBits h (toNat_lt_pow _)
--   rw [toNat_toBits, toNat_toBits] at h'; exact h'
--
-- lemma Bits.le_add_right {n} {xs ys : Bits n} (h : Nof xs ys) : xs ≤ xs + ys := by
--   apply of_toNat_le_toNat; rw [add_toNat _ _ h]; apply Nat.le_add_right
