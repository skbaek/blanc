-- Basic.lean : generic definitions and lemmas (e.g. for Booleans, lists,
-- bit vectors and bytes) that are useful for but not specific to Blanc

import Mathlib.Data.Nat.Defs
import Mathlib.Data.List.Lemmas
import Mathlib.Util.Notation3
import Mathlib.Data.Vector.Basic



-- Boolean lemmas --

instance : @Zero Bool := ⟨false⟩
instance : @One Bool := ⟨true⟩

def Bool.toChar : Bool → Char
  | 0 => '0'
  | 1 => '1'

lemma Bool.zero_or_one (x : Bool) : x = 0 ∨ x = 1 := by
  cases x
  · left; rfl
  · right; rfl

lemma not_true_lt {b} : ¬ true < b := by simp [LT.lt]
lemma false_lt_true : false < true := by simp [LT.lt]
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
abbrev B8 : Type := UInt8
abbrev B16 : Type := UInt16
abbrev B32 : Type := UInt32
abbrev B64 : Type := UInt64
abbrev B8s : Type := List B8
abbrev Bytes : Type := List Byte

def Bits.toChars : ∀ {n}, Bits n → List Char
  | 0, ⦃⦄ => []
  | _ + 1, x +> xs => Bool.toChar x :: xs.toChars

def Bits.toString {n} (bs : Bits n) : String := ⟨Bits.toChars bs⟩

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

lemma Bits.cons_lt_cons {n} {x y} {xs ys : Bits n} :
    x +> xs < y +> ys ↔ (x < y ∨ (x = y ∧ xs < ys)) := Iff.refl _

lemma Bits.cons_eq_cons {n} {x y} {xs ys : Bits n} :
    x +> xs = y +> ys ↔ (x = y ∧ xs = ys) := by simp

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

def Bits.le : ∀ {n : ℕ}, Bits n → Bits n → Prop
  | 0, ⦃⦄, ⦃⦄ => True
  | _, x +> xs, y +> ys => x < y ∨ (x = y ∧ le xs ys)

instance {n} : @LE (Bits n) := ⟨Bits.le⟩

lemma Bits.cons_le_cons {n} {xs ys : Bits n} {x y} :
    x +> xs ≤ y +> ys ↔ (x < y ∨ (x = y ∧ xs ≤ ys)) := Iff.refl _

instance {n : ℕ} (xs ys : Bits n) : Decidable (xs = ys) := by
  induction n with
  | zero => cases xs; cases ys; apply Decidable.isTrue rfl
  | succ n ih =>
    match xs, ys with
    | x +> xs, y +> ys =>
      rw [Bits.cons_eq_cons]; apply instDecidableAnd


instance {n : ℕ} (xs ys : Bits n) : Decidable (xs ≤ ys) := by
  induction n with
  | zero =>
    cases xs; cases ys;
    apply Decidable.isTrue; constructor
  | succ n =>
    match xs, ys with
    | x +> xs, y +> ys =>
      rw [Bits.cons_le_cons]; apply instDecidableOr

def B8.highBit (x : B8) : Bool := (x &&& 0x80) != 0
def B8.lowBit (x : B8) : Bool := (x &&& 0x01) != 0

def B16.highBit (x : B16) : Bool := (x &&& 0x8000) != 0
def B16.lowBit  (x : B16) : Bool := (x &&& 0x0001) != 0

def B32.highBit (x : B32) : Bool := (x &&& 0x80000000) != 0
def B32.lowBit  (x : B32) : Bool := (x &&& 0x00000001) != 0

def B64.highBit (x : B64) : Bool := (x &&& 0x8000000000000000) != 0
def B64.lowBit  (x : B64) : Bool := (x &&& 0x0000000000000001) != 0

def B128 : Type := B64 × B64
def B256 : Type := B128 × B128

def B128.highBit (x : B128) : Bool := x.1.highBit
def B128.lowBit  (x : B128) : Bool := x.2.lowBit

def B256.highBit (x : B256) : Bool := x.1.highBit
def B256.lowBit  (x : B256) : Bool := x.2.lowBit

instance : HAppend B64 B64 B128 := ⟨λ xs ys => ⟨xs, ys⟩⟩
instance : HAppend B128 B128 B256 := ⟨λ xs ys => ⟨xs, ys⟩⟩

def B64.max : B64 := 0xFFFFFFFFFFFFFFFF
def B128.max : B128 := (.max : B64) ++ (.max : B64)
def B256.max : B256 := (.max : B128) ++ (.max : B128)



instance {x y : B128} : Decidable (x = y) := by
  rw [@Prod.eq_iff_fst_eq_snd_eq B64 B64 x y]; apply instDecidableAnd

instance {x y : B256} : Decidable (x = y) := by
  rw [@Prod.eq_iff_fst_eq_snd_eq B128 B128 x y]; apply instDecidableAnd

def B128.LT (x y : B128) : Prop :=
  x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 < y.2)
instance : @LT B128 := ⟨B128.LT⟩
instance {x y : B128} : Decidable (x < y) := instDecidableOr

def B256.LT (x y : B256) : Prop :=
  x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 < y.2)

instance : @LT B256 := ⟨B256.LT⟩
instance {x y : B256} : Decidable (x < y) := instDecidableOr

def Nat.toB128 (n : Nat) : B128 :=
  let q := n / (2 ^ 64)
  q.toUInt64 ++ n.toUInt64

def Nat.toB256 (n : Nat) : B256 :=
  let q := n / (2 ^ 128)
  q.toB128 ++ n.toB128

instance {n} : OfNat B128 n := ⟨n.toB128⟩
instance {n} : OfNat B256 n := ⟨n.toB256⟩


def B8.toHexit : B8 → Char
  | 0x0 => '0'
  | 0x1 => '1'
  | 0x2 => '2'
  | 0x3 => '3'
  | 0x4 => '4'
  | 0x5 => '5'
  | 0x6 => '6'
  | 0x7 => '7'
  | 0x8 => '8'
  | 0x9 => '9'
  | 0xA => 'A'
  | 0xB => 'B'
  | 0xC => 'C'
  | 0xD => 'D'
  | 0xE => 'E'
  | 0xF => 'F'
  | _   => 'X'

def B8.highs (x : B8) : B8 := (x >>> 4)
def B8.lows (x : B8) : B8 := (x &&& 0x0F)

def B8.toHex (x : B8) : String :=
  ⟨[x.highs.toHexit, x.lows.toHexit]⟩

def B8s.toHex (bs : B8s) : String :=
  List.foldr (λ b s => B8.toHex b ++ s) "" bs

def B16.highs (x : B16) : B8 := (x >>> 8).toUInt8
def B16.lows : B16 → B8 := UInt16.toUInt8
def B16.toHex (x : B16) : String := x.highs.toHex ++ x.lows.toHex

def B32.highs (x : B32) : B16 := (x >>> 16).toUInt16
def B32.lows : B32 → B16 := UInt32.toUInt16
def B32.toHex (x : B32) : String := x.highs.toHex ++ x.lows.toHex

def B64.highs (x : B64) : B32 := (x >>> 32).toUInt32
def B64.lows : B64 → B32 := UInt64.toUInt32
def B64.toHex (x : B64) : String := x.highs.toHex ++ x.lows.toHex

def B128.toHex (x : B128) : String := x.1.toHex ++ x.2.toHex
def B256.toHex (x : B256) : String := x.1.toHex ++ x.2.toHex

def foo256 : B256 := 0xFEDCBA9876543210FEDCBA9876543210FEDCBA9876543210FEDCBA9876543210


def B128.LE (x y : B128) : Prop :=
  x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 ≤ y.2)
instance : @LE B128 := ⟨B128.LE⟩
instance {x y : B128} : Decidable (x ≤ y) := instDecidableOr

def B256.LE (x y : B256) : Prop :=
  x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 ≤ y.2)
instance : @LE B256 := ⟨B256.LE⟩
instance {x y : B256} : Decidable (x ≤ y) := instDecidableOr


def B128.shiftLeft : B128 → Nat → B128
  | ⟨xs, ys⟩, os =>
    if os = 0
    then ⟨xs, ys⟩
    else if os < 64
         then ⟨ (xs <<< os.toUInt64) ||| (ys >>> (64 - os).toUInt64),
                ys <<< os.toUInt64 ⟩
         else if os < 128
              then ⟨ys <<< (os - 64).toUInt64, 0⟩
              else ⟨0, 0⟩
instance : HShiftLeft B128 Nat B128 := ⟨B128.shiftLeft⟩

def B128.shiftRight : B128 → Nat → B128
  | ⟨xs, ys⟩, os =>
    if os = 0
    then ⟨xs, ys⟩
    else if os < 64
         then ⟨ xs >>> os.toUInt64,
                (xs <<< (64 - os).toUInt64) ||| (ys >>> os.toUInt64) ⟩
         else if os < 128
              then ⟨0, xs >>> (os - 64).toUInt64⟩
              else ⟨0, 0⟩
instance : HShiftRight B128 Nat B128 := ⟨B128.shiftRight⟩

def B128.or : B128 → B128 → B128
  | ⟨xh, xl⟩, ⟨yh, yl⟩ => ⟨xh ||| yh, xl ||| yl⟩
instance : HOr B128 B128 B128 := ⟨B128.or⟩
def B128.and : B128 → B128 → B128
  | ⟨xh, xl⟩, ⟨yh, yl⟩ => ⟨xh &&& yh, xl &&& yl⟩
instance : HAnd B128 B128 B128 := ⟨B128.and⟩

def B256.or : B256 → B256 → B256
  | ⟨xh, xl⟩, ⟨yh, yl⟩ => ⟨xh ||| yh, xl ||| yl⟩
instance : HOr B256 B256 B256 := ⟨B256.or⟩
def B256.and : B256 → B256 → B256
  | ⟨xh, xl⟩, ⟨yh, yl⟩ => ⟨xh &&& yh, xl &&& yl⟩
instance : HAnd B256 B256 B256 := ⟨B256.and⟩

def B128.xor : B128 → B128 → B128
  | ⟨xh, xl⟩, ⟨yh, yl⟩ => ⟨xh ^^^ yh, xl ^^^ yl⟩
instance : HXor B128 B128 B128 := ⟨B128.xor⟩
def B256.xor : B256 → B256 → B256
  | ⟨xh, xl⟩, ⟨yh, yl⟩ => ⟨xh ^^^ yh, xl ^^^ yl⟩
instance : HXor B256 B256 B256 := ⟨B256.xor⟩

def B256.shiftRight : B256 → Nat → B256
  | ⟨xs, ys⟩, os =>
    if os = 0
    then ⟨xs, ys⟩
    else if os < 128
         then ⟨ xs >>> os,
                (xs <<< (128 - os)) ||| (ys >>> os) ⟩
         else if os < 256
              then ⟨0, xs >>> (os - 128)⟩
              else ⟨0, 0⟩
instance : HShiftRight B256 Nat B256 := ⟨B256.shiftRight⟩

def B256.shiftLeft : B256 → Nat → B256
  | ⟨xs, ys⟩, os =>
    if os = 0
    then ⟨xs, ys⟩
    else  if os < 128
         then ⟨(xs <<< os) ||| (ys >>> (128 - os)), ys <<< os⟩
         else if os < 256
              then ⟨ys <<< (os - 128), 0⟩
              else ⟨0, 0⟩
instance : HShiftLeft B256 Nat B256 := ⟨B256.shiftLeft⟩

def B256.Slt (xs ys : B256) : Prop :=
  let x := xs.highBit
  let y := ys.highBit
  let xs' : B256 := xs &&& (B256.max >>> 1)
  let ys' : B256 := ys &&& (B256.max >>> 1)
  y < x ∨ (x = y ∧ xs' < ys')
instance {xs ys : B256} : Decidable (B256.Slt xs ys) := instDecidableOr

def Bits.Slt : ∀ {n : ℕ}, Bits n → Bits n → Prop
  | 0, ⦃⦄, ⦃⦄ => False
  | _ + 1, x +> xs, y +> ys => y < x ∨ (x = y ∧ xs < ys)

infix:70 " ±< " => Bits.Slt

lemma Bits.singleton_slt_singleton {x y : Bool} :
    ⦃x⦄ ±< ⦃y⦄ ↔ (x = 1 ∧ y = 0) := by
  cases x <;> cases y <;>
  simp [Bool.zero, Bool.one, Bits.Slt] <;>
  try {intro hc; cases hc}

def Bits.Sgt {n : ℕ} (xs ys : Bits n) : Prop := Slt ys xs
def B256.Sgt (xs ys : B256) : Prop := B256.Slt ys xs
instance {xs ys : B256} : Decidable (B256.Sgt xs ys) := instDecidableOr

infix:70 " ±> " => Bits.Sgt

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
  | 1 => ⦃1⦄
  | n + 2 => 0 +> one (n + 1)

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

def Bits.isMax : ∀ {n}, Bits n → Bool
  | 0, ⦃⦄ => true
  | _ + 1, x +> xs => x && xs.isMax

def Bits.succ : ∀ {n}, Bits n →  Bits n
  | 0, ⦃⦄ => ⦃⦄
  | _ + 1, x +> xs => (x != xs.isMax) +> xs.succ

def Bits.incr {n} : Bool → Bits n → Bits n
  | false => id
  | true => Bits.succ

def Overflow {n : ℕ} (xs ys : Bits n) : Prop := 2 ^ n ≤ xs.toNat + ys.toNat

def overflow : ∀ {n : ℕ}, Bits n → Bits n → Bool
| 0, ⦃⦄, ⦃⦄ => false
| _ + 1, x +> xs, y +> ys => (x && y) || ((x != y) && overflow xs ys)

lemma overflow_comm :
    ∀ {n : ℕ} (xs ys : Bits n), overflow xs ys = overflow ys xs := by
  apply Bits.rec2
  · rfl
  · intro n x xs y ys ih; simp only [overflow, bne]
    rw [Bool.and_comm, Bool.beq_comm, ih];

def Bits.add : ∀ {n : ℕ}, Bits n → Bits n → Bits n
  | 0, ⦃⦄, ⦃⦄ => ⦃⦄
  | _ + 1, x +> xs, y +> ys =>
    ((x != y) != overflow xs ys) +> (add xs ys)

infix:55 " ↟ " => Overflow

def Nof {n : ℕ} (xs ys : Bits n) : Prop := xs.toNat + ys.toNat < 2 ^ n

def Bits.nof_iff_not_overflow {n : ℕ} (xs ys : Bits n) : Nof xs ys ↔ ¬ xs ↟ ys := by
  simp [Overflow, Nof]

def Bits.sub {n} : Bits n → Bits n → Bits n
  | ⦃⦄, ⦃⦄ => ⦃⦄
  | x +> xs, y +> ys => ((x != y) != lt' xs ys) +> sub xs ys

instance {n} : HAdd (Bits n) (Bits n) (Bits n) := ⟨Bits.add⟩
instance {n} : Add (Bits n) := ⟨Bits.add⟩

instance {n} : HSub (Bits n) (Bits n) (Bits n) := ⟨Bits.sub⟩
instance {n} : Sub (Bits n) := ⟨Bits.sub⟩

lemma Bits.faux : ∀ {n} {xs ys : Bits n}, lt' xs ys = overflow (xs - ys) ys := by
  apply rec2
  · simp [lt']; rfl
  · intro n x xs y ys ih
    simp only [lt', overflow]
    conv => rhs; rhs; rhs; apply ih.symm
    cases (lt' xs ys) <;> cases y <;> simp

lemma Bits.lt_irrefl {n} {xs : Bits n} : ¬ xs < xs := by
  intro h;
  induction n with
  | zero => cases xs; cases h
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

def Bits.snoc : ∀ {n}, Bits n → Bool → Bits (n + 1)
  | 0, ⦃⦄, y => ⦃y⦄
  | _ + 1, x +> xs, y => x +> (xs.snoc y)

def Bits.shlo : ∀ {n}, Bits n → Bool → Bits n
  | 0, ⦃⦄, _ => ⦃⦄
  | _ + 1, _ +> xs, y => Bits.snoc xs y

def Bits.shl : Nat → ∀ {n}, Bits n → Bits n
  | 0, _, xs => xs
  | m + 1, _, xs => shlo (xs.shl m) 0

-- def Bits.shl : Nat → ∀ {n}, Bits n → Bits n
--   | 0, _, xs => xs
--   | _, 0, ⦃⦄ => ⦃⦄
--   | m + 1, _ + 1, _ +> xs => (shl m xs).snoc 0

-- def Bits.shro : ∀ {n}, Bool → Bits n → Bits n
--   | 0, _, ⦃⦄ => ⦃⦄
--   | n + 1, x, y +> ys =>  x +> shro y ys

--def Bits.shr' : ∀ {k m n : Nat}, Bits m → Bits n
--| 0, m, n, xs => _
--
--#exit
def Bits.prefixLe : ∀ {m n}, m ≤ n → Bits n → Bits m
| 0, _, _, _ => ⦃⦄
| m + 1, 0, h, _ => (Nat.not_succ_le_zero m h).elim
| _ + 1, _ + 1, h, x +> xs =>
  x +> prefixLe (Nat.le_of_succ_le_succ h) xs

def Bits.shr' : Nat → ∀ {m n}, m ≤ n → Bits n → Bits m
  | _, 0, _, _, _ => ⦃⦄
  | 0, _, _, h, xs => prefixLe h xs
  | k + 1, m + 1, n, h, xs =>
    0 +> @shr' k m n (le_trans (Nat.le_succ _) h) xs

def Bits.shr (m : Nat) {n} (xs : Bits n) : Bits n :=
  Bits.shr' m (le_refl n) xs

def Bits.isNeg : ∀ {n : ℕ}, Bits n → Bool
  | 0, _ => false
  | _ + 1, x +> _ => x

def B256.isNeg : B256 → Bool := B256.highBit

def Bits.neg {n : ℕ} (xs : Bits n) : Bits n := (~ xs).succ

def B128.complement : B128 → B128
  | ⟨xs, ys⟩ => ⟨~~~ xs, ~~~ ys⟩
instance : Complement B128 := ⟨B128.complement⟩

def B256.complement : B256 → B256
  | ⟨xs, ys⟩ => ⟨~~~ xs, ~~~ ys⟩
instance : Complement B256 := ⟨B256.complement⟩

def B8.toB256  (x : B8)  : B256 := ⟨0, ⟨0, x.toUInt64⟩⟩
def B16.toB256 (x : B16) : B256 := ⟨0, ⟨0, x.toUInt64⟩⟩
def B32.toB256 (x : B32) : B256 := ⟨0, ⟨0, x.toUInt64⟩⟩
def B64.toB256 (x : B64) : B256 := ⟨0, ⟨0, x⟩⟩

def B128.zero : B128 := ⟨0, 0⟩
instance : Zero B128 := ⟨.zero⟩
def B128.one : B128 := ⟨0, 1⟩
instance : One B128 := ⟨.one⟩
def B256.zero : B256 := ⟨0, 0⟩
instance : Zero B256 := ⟨.zero⟩
def B256.one : B256 := ⟨0, 1⟩
instance : One B256 := ⟨.one⟩

def B128.sub (x y : B128) : B128 :=
  let l := x.2 - y.2
  let c : B64 := if x.2 < y.2 then 1 else 0
  ⟨(x.1 - y.1) - c, l⟩
instance : HSub B128 B128 B128 := ⟨B128.sub⟩

def B128.add (x y : B128) : B128 :=
  let l := x.2 + y.2
  let c : B64 := if l < x.2 then 1 else 0
  ⟨x.1 + y.1 + c, l⟩
instance : HAdd B128 B128 B128 := ⟨B128.add⟩

def B256.add (x y : B256) : B256 :=
  let l := x.2 + y.2
  let c : B128 := if l < x.2 then 1 else 0
  ⟨x.1 + y.1 + c, l⟩
instance : HAdd B256 B256 B256 := ⟨B256.add⟩

def B256.sub (x y : B256) : B256 :=
  let l := x.2 - y.2
  let c : B128 := if x.2 < y.2 then 1 else 0
  ⟨(x.1 - y.1) - c, l⟩
instance : HSub B256 B256 B256 := ⟨B256.sub⟩
instance : Sub B256 := ⟨B256.sub⟩

def B256.neg (xs : B256) : B256 := (~~~ xs) + B256.one

def Bits.sar (m : Nat) {n} (xs : Bits n) : Bits n :=
  if isNeg xs
  then neg (shr m (neg xs))
  else shr m xs

def B256.sar (m : Nat) (xs : B256) : B256 :=
  if isNeg xs
  then neg ((neg xs) >>> m)
  else (xs >>> m)

def Bits.append : ∀ {m n}, Bits m → Bits n → Bits (n + m)
  | 0, _, ⦃⦄, ys => ys
  | _ + 1, _, x +> xs, ys => x +> append xs ys

instance {m n} : HAppend (Bits m) (Bits n) (Bits (n + m)) := ⟨Bits.append⟩

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

-- divMod acc pfx xs ys
-- assumes: pfx < ys
def divMod : ∀ {m n : ℕ}, Bits n → Bits m → Bits n → (Bits m × Bits n)
  | 0, _, pfx, ⦃⦄, _ => (0, pfx)
  | _ + 1, _, pfx, x +> xs, ys =>
    let pfx' := Bits.shlo pfx x
    if ys ≤ pfx'
    then let (div, mod) := divMod (pfx' - ys) xs ys
         (1 +> div, mod)
    else let (div, mod) := divMod pfx' xs ys
         (0 +> div, mod)

def Bits.div {n} (xs ys : Bits n) : Bits n :=
  if ys = 0 then 0 else (divMod 0 xs ys).fst

def Bits.mod {n} (xs ys : Bits n) : Bits n :=
  if ys = 0 then 0 else (divMod 0 xs ys).snd

instance {n} : HDiv (Bits n) (Bits n) (Bits n) := ⟨Bits.div⟩

instance {n} : HMod (Bits n) (Bits n) (Bits n) := ⟨Bits.mod⟩
instance {n} : Mod (Bits n) := ⟨Bits.mod⟩

-- minimum possible value in 2's complement
def Bits.smin : ∀ {n : ℕ}, Bits n
  | 0 => ⦃⦄
  | _ + 1 => 1 +> 0

-- minimum possible value in 2's complement
def B64.smin : B64 := 0x8000000000000000
def B128.smin : B128 := ⟨.smin, 0⟩
def B256.smin : B256 := ⟨.smin, 0⟩

def Bits.negOne {n : ℕ} : Bits n := max _

def B64.negOne  : B64  := .max
def B128.negOne : B128 := .max
def B256.negOne : B256 := .max

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


def Nat.toBool : Nat → Bool
  | 0 => 0
  | _ => 1

def Nat.toBitsAux' (n : Nat) : List Bool :=
  if n < 2
  then [n.toBool]
  else (n % 2).toBool :: (n / 2).toBitsAux'

def Bool.toBits {k} : Bool → Bits k
  | .false => 0
  | .true => 1

def Bools.toBits : ∀ n, List Bool → Bits n
  | 0, _ => ⦃⦄
  | n + 1, [] => 0 +> toBits n []
  | n + 1, x :: xs => x +> toBits n xs

def Nat.toBits' (m n : Nat) : Bits m :=
  let bs := (List.takeD m (Nat.toBitsAux' n) 0).reverse
  Bools.toBits m bs

def Bits.addmod {n : ℕ} (x y z : Bits n) : Bits n :=
  if z = 0
  then 0
  else Nat.toBits' n ((x.toNat + y.toNat) % z.toNat) -- (x + y) % z

def Bits.mulmod {n : ℕ} (x y z : Bits n) : Bits n :=
  if z = 0
  then 0
  else Nat.toBits' n ((x.toNat * y.toNat) % z.toNat) -- (x + y) % z

def Bits.expNat {n : ℕ} (x : Bits n) : Nat → Bits n
  | 0 => 1
  | k + 1 => x * x.expNat k

def Bits.exp {n : ℕ} (x y : Bits n) : Bits n := expNat x y.toNat

instance {n} : HPow (Bits n) (Bits n) (Bits n) := ⟨Bits.exp⟩

inductive Bits.Signext : Nat → Bool → ∀ {n}, Bits n → Bits n → Prop
  | zero : ∀ n x (xs : Bits n), Signext 0 x (x +> xs) (x +> xs)
  | succ :
    ∀ m n x y (xs ys : Bits n),
      Signext m y xs ys →
      Signext (m + 1) y (x +> xs) (y +> ys)

def Bits.signext {m} : Nat → Bits m → (Bits m × Bool)
  | _, ⦃⦄ => ⟨⦃⦄, 0⟩
  | 0, x +> xs => ⟨x +> xs, x⟩
  | n + 1, _ +> xs =>
    let ⟨ys, y⟩ := Bits.signext n xs
    ⟨y +> ys, y⟩

def Word.signext (x y : Word) : Word :=
  (Bits.signext (256 - (8 * (x.toNat + 1))) y).fst

abbrev Vec := Mathlib.Vector

def B64.toB8v (x : B64) : Vec B8 8 :=
  ⟨ [ (x >>> 56).toUInt8, (x >>> 48).toUInt8,
      (x >>> 40).toUInt8, (x >>> 32).toUInt8,
      (x >>> 24).toUInt8, (x >>> 16).toUInt8,
      (x >>> 8).toUInt8, x.toUInt8 ], rfl ⟩

def B64.toB8t (x : B64) : B8 × B8 × B8 × B8 × B8 × B8 × B8 × B8 :=
  ⟨ (x >>> 56).toUInt8, (x >>> 48).toUInt8,
    (x >>> 40).toUInt8, (x >>> 32).toUInt8,
    (x >>> 24).toUInt8, (x >>> 16).toUInt8,
    (x >>> 8).toUInt8, x.toUInt8 ⟩

def B64.toB8s (x : B64) : B8s :=
  [ (x >>> 56).toUInt8, (x >>> 48).toUInt8,
    (x >>> 40).toUInt8, (x >>> 32).toUInt8,
    (x >>> 24).toUInt8, (x >>> 16).toUInt8,
    (x >>> 8).toUInt8, x.toUInt8 ]


def B64.reverse (w : B64) : B64 :=
  ((w <<< 56) &&& (0xFF00000000000000 : B64)) |||
  ((w <<< 40) &&& (0x00FF000000000000 : B64)) |||
  ((w <<< 24) &&& (0x0000FF0000000000 : B64)) |||
  ((w <<< 8)  &&& (0x000000FF00000000 : B64)) |||
  ((w >>> 8)  &&& (0x00000000FF000000 : B64)) |||
  ((w >>> 24) &&& (0x0000000000FF0000 : B64)) |||
  ((w >>> 40) &&& (0x000000000000FF00 : B64)) |||
  ((w >>> 56) &&& (0x00000000000000FF : B64))


def B128.toB8s (x : B128) : B8s := x.1.toB8s ++ x.2.toB8s
def B256.toB8s (x : B256) : B8s := x.1.toB8s ++ x.2.toB8s

def B128.toB8v (x : B128) : Vec B8 16 :=
  Mathlib.Vector.append x.1.toB8v x.2.toB8v

def B256.toB8v (x : B256) : Vec B8 32 :=
  Mathlib.Vector.append x.1.toB8v x.2.toB8v

def B128.toNat (x : B128) : Nat := (x.1.toNat * (2 ^ 64)) + x.2.toNat
def B256.toNat (x : B256) : Nat := (x.1.toNat * (2 ^ 128)) + x.2.toNat

def B256.addmod (x y z : B256) : B256 :=
  if z = 0
  then 0
  else ((x.toNat + y.toNat) % z.toNat).toB256 -- (x + y) % z

def B256.mulmod (x y z : B256) : B256 :=
  if z = 0
  then 0
  else ((x.toNat * y.toNat) % z.toNat).toB256 -- (x + y) % z

def B256.signext (x y : B256) : B256 :=
  if h : x < 31
  then have h' : (32 - (x.toNat + 1)) < 32 := by omega
       let z : B8 := y.toB8v.get (32 - (x.toNat + 1))
       cond z.highBit
         ((B256.max <<< (8 * (x.toNat + 1))) ||| y)
         ((B256.max >>> (256 - (8 * (x.toNat + 1)))) &&& y)
  else y


def Bits.toInt {m} (xs : Bits m) : Int :=
  if xs.isNeg
  then .negSucc (~ xs).toNat
  else .ofNat xs.toNat

def Word.Signext (x y y' : Word) : Prop :=
  ∃ b, Bits.Signext (256 - (8 * (x.toNat + 1))) b y y'

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

abbrev Nib : Type := Bits 4

abbrev Nibs := List Nib

def Bits.toNibs : ∀ {n}, Bits (4 * n) → Nibs
  | 0, ⦃⦄ => []
  | _ + 1, b0 +> b1 +> b2 +> b3 +> bs =>
    ⦃b0, b1, b2, b3⦄ :: bs.toNibs

def Bytes.toBits' : ∀ (n : Nat), Bytes → Bits (8 * n)
  | 0, _ => ⦃⦄
  | n + 1, [] => (0 : Byte) ++ toBits' n []
  | n + 1, b :: bs => b ++ toBits' n bs

def Bytes.toBits (n : Nat) (bs : Bytes) : Bits (8 * n) :=
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

lemma Bits.sub_add_cancel : ∀ {n} {x y : Bits n}, x - y + y = x := by
  apply rec2; rfl
  intro n x xs y ys ih
  rw [cons_sub_cons, cons_add_cons, ih]
  apply congr_arg₂ _ _ rfl
  rw [← Bits.faux]; cases (lt' xs ys) <;> cases y <;> simp

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

lemma Bits.eq_max_iff_succ_toNat_eq_pow {n : Nat} (xs : Bits n) :
     xs = max _ ↔ xs.toNat.succ = 2 ^ n := by
  constructor <;> intro h
  · rw [h]; apply succ_toNat_max_eq_pow
  · apply toNat_inj; rw [← Nat.succ_inj, succ_toNat_max_eq_pow, h]

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

lemma Bits.nil_le_nil {xs ys : Bits 0} : xs ≤ ys := by
  cases xs; cases ys; constructor

lemma Bits.lt_succ_self {n} {xs : Bits n} (h : xs ≠ max n) : xs < xs.succ := by
  induction xs with
  | nil => cases (h nil_eq_nil)
  | cons x xs ih =>
    simp only [Ne, max_eq_cons, cons_eq_cons] at h
    cases x <;> simp [succ]
    · by_cases h' : xs = max _
      · left; simp [h', max_isMax]
      · right;
        simp [mt (eq_max_iff_isMax xs).mpr h']
        apply ih h'
    · simp [Bool.one] at h;
      simp [mt (eq_max_iff_isMax xs).mpr h]
      right; simp; apply ih h

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

lemma Bits.zero_le {n} : ∀ xs : Bits n, 0 ≤ xs := by
  induction n with
  | zero => intro xs; cases xs; constructor
  | succ n ih =>
    intro xs; match xs with
    | x +> xs =>
      rw [zero_eq_cons, cons_le_cons]
      cases x
      · right; refine ⟨rfl, ih xs⟩
      · left; constructor

lemma Bits.lt_of_le_of_lt {n} {xs ys zs : Bits n}
    (h : xs ≤ ys) (h' : ys < zs) : xs < zs := by
  cases lt_or_eq_of_le h with
  | inl h'' => apply lt_trans h'' h'
  | inr h'' => rw [h'']; exact h'

lemma Bits.le_of_le_of_lt {n} {xs ys zs : Bits n}
    (h : xs ≤ ys) (h' : ys < zs) : xs ≤ zs :=
  le_of_lt <| lt_of_le_of_lt h h'

lemma Nat.toBits_le_toBits {k m n : Nat} (h_le : m ≤ n) (h_lt : n < 2 ^ k) :
    (@toBits k m) ≤ (@toBits k n) := by
  induction n generalizing m with
  | zero => rw [le_zero] at h_le; cases h_le; apply Bits.zero_le
  | succ n ih =>
    rw [le_add_one_iff] at h_le
    rcases h_le with h_le | h_eq
    · have h_lt' := lt_trans (lt_succ_self n) h_lt
      have hh := ih h_le h_lt'
      simp [toBits]
      apply Bits.le_of_le_of_lt hh _
      apply Bits.lt_succ_self
      intro hc;
      rw [Bits.eq_max_iff_succ_toNat_eq_pow, toNat_toBits h_lt'] at hc
      rw [← hc] at h_lt; cases Nat.lt_irrefl _ h_lt
    · rw [h_eq]; apply Bits.le_refl


def Nib.toHexit : Nib → Char
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

def Byte.nib0 : Byte → Nib
  | ⦃w, x, y, z, _, _, _, _⦄ => ⦃w, x, y, z⦄

def Byte.nib1 : Byte → Nib
  | ⦃_, _, _, _, w, x, y, z⦄ => ⦃w, x, y, z⦄

def Byte.toHex (b : Byte) : String :=
⟨[b.nib0.toHexit, b.nib1.toHexit]⟩

def Nibs.toHex : Nibs → String
  | [] => ""
  | [b] => ⟨[b.toHexit]⟩
  | b :: bs => ⟨[b.toHexit] ++ (toHex bs).data⟩

def Bytes.toString : Bytes → String
  | [] => ""
  | [b] => b.toString
  | b :: bs => b.toString ++ " " ++ toString bs

instance : Repr Bytes := ⟨λ b _ => b.toString⟩

def Ox (hx hx' : Nib) : Byte := hx ++ hx'

lemma nib0_eq : ∀ {x y : Nib}, (Ox x y).nib0 = x
| ⦃_, _, _, _⦄, ⦃_, _, _, _⦄ => rfl

def x0 : Nib := ⦃0, 0, 0, 0⦄
def x1 : Nib := ⦃0, 0, 0, 1⦄
def x2 : Nib := ⦃0, 0, 1, 0⦄
def x3 : Nib := ⦃0, 0, 1, 1⦄
def x4 : Nib := ⦃0, 1, 0, 0⦄
def x5 : Nib := ⦃0, 1, 0, 1⦄
def x6 : Nib := ⦃0, 1, 1, 0⦄
def x7 : Nib := ⦃0, 1, 1, 1⦄
def x8 : Nib := ⦃1, 0, 0, 0⦄
def x9 : Nib := ⦃1, 0, 0, 1⦄
def xA : Nib := ⦃1, 0, 1, 0⦄
def xB : Nib := ⦃1, 0, 1, 1⦄
def xC : Nib := ⦃1, 1, 0, 0⦄
def xD : Nib := ⦃1, 1, 0, 1⦄
def xE : Nib := ⦃1, 1, 1, 0⦄
def xF : Nib := ⦃1, 1, 1, 1⦄

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

lemma Bits.not_lt {n : ℕ} (xs ys : Bits n) : ¬ xs < ys ↔ ys ≤ xs := by
  constructor
  · rw [← or_iff_not_imp_left]; apply lt_or_ge
  · intros h h'; cases lt_irrefl <| lt_of_le_of_lt h h'

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

lemma Bits.succ_cons {n} (x) (xs : Bits n) :
     (x +> xs).succ = (x != xs.isMax) +> xs.succ := rfl

lemma Bits.append_eq_max_iff {m n} (xs : Bits m) (ys : Bits n) :
    (xs ++ ys) = max (n + m) ↔ (xs = max m ∧ ys = max n) := by
  induction xs with
  | nil => simp [@nil_eq_nil ⦃⦄ (max 0)]; rfl
  | cons x xs ih =>
    rw [cons_append]; conv => lhs; rhs; apply (@max_eq_cons (n + _))
    rw [cons_eq_cons, ih, max_eq_cons, cons_eq_cons, and_assoc]

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

abbrev Bytes.Zero : Bytes → Prop := List.Forall (· = 0)

instance {ξ : Type u} {ρ : ξ → Prop} {xs : List ξ}
    [d : ∀ x : ξ, Decidable (ρ x)] : Decidable (xs.Forall ρ) := by
  induction xs with
  | nil => apply instDecidableTrue
  | cons x xs ih => simp; apply instDecidableAnd

def Bytes.Max (bs : Bytes) : Prop := bs.Forall (· = .max 8)

instance (bs : Bytes) : Decidable bs.Max := by
  unfold Bytes.Max; infer_instance

def Bytes.succ : Bytes → Bytes
  | [] => []
  | b :: bs => (if Max bs then b.succ else b) :: succ bs

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

def List.sliceD {ξ : Type u} (xs : List ξ) (m n : Nat) (x : ξ) : List ξ :=
  takeD n (drop m xs) x

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

lemma List.slice_prefix {ξ : Type u} {xs : List ξ}
    {m : Nat} {ys zs} (h : Slice xs m (ys ++ zs)) : Slice xs m ys := by
  rcases h with ⟨n, h⟩; refine ⟨_, (of_slice?_eq_append h).left⟩

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

lemma List.take?_length {ξ : Type u} (xs : List ξ) :
    take? xs.length xs = some xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [take?, ih]

lemma List.slice_refl {ξ : Type u} (xs : List ξ) : List.Slice xs 0 xs := by
  refine' ⟨xs.length, _⟩; simp [slice?, drop?, take?_length]

lemma List.append_slice_suffix {ξ : Type y} {xs ys : List ξ} :
    Slice (xs ++ ys) xs.length ys := by
  have h := slice_suffix <| slice_refl <| xs ++ ys
  rw [Nat.zero_add] at h; exact h

lemma toBytes_zero_eq_replicate_zero {n} :
    (@Bits.toBytes n 0) = List.replicate n (0 : Byte) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have h : (0 : Bits (8 * (n + 1))) = (0 : Byte) ++ (0 : Bits (8 * n)) := rfl
    rw [h]; simp [Bits.toBytes_eq_cons, List.replicate, ih]

lemma Bits.zero_ne_succ' {n} :
    zero (n + 1) ≠ (zero (n + 1)).succ := by
  induction n with
  | zero => intro h; cases h
  | succ n ih =>
    have h_rw : zero (n + 2) = 0 +> (zero (n + 1)) := rfl
    rw [h_rw, succ_cons]
    intro hc; rw [cons_eq_cons] at hc
    apply ih hc.right

lemma Bits.zero_ne_succ {n} :
    (0 : Bits (n + 1)) ≠ (0 : Bits (n + 1)).succ := zero_ne_succ'

lemma Bits.add_comm {n} {xs ys : Bits n} : xs + ys = ys + xs := by
  apply toNat_inj; simp [toNat_add]; rw [Nat.add_comm, overflow_comm]

lemma Bits.invert_zero_eq_max {n} : ~ (0 : Bits n) = max _ := by
  induction n with
  | zero => apply nil_eq_nil
  | succ n ih => rw [zero_eq_cons]; simp only [max, not]; rw [ih]; rfl

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

lemma toBits_toNat {k : ℕ} {xs : Bits k} : Nat.toBits k (Bits.toNat xs) = xs := by
  apply Bits.toNat_inj; rw [toNat_toBits (Bits.toNat_lt_pow _)]

lemma Bits.of_toNat_le_toNat {k : ℕ} {xs ys : Bits k}
    (h : xs.toNat ≤ ys.toNat) : xs ≤ ys := by
  have h' := Nat.toBits_le_toBits h (toNat_lt_pow _)
  rw [toBits_toNat, toBits_toNat] at h'; exact h'

lemma Bits.le_add_right {n} {xs ys : Bits n} (h : Nof xs ys) : xs ≤ xs + ys := by
  apply of_toNat_le_toNat; rw [toNat_add_eq_of_nof _ _ h]; apply Nat.le_add_right

def Hexit.toNib : Char → Option Nib
  | '0' => some x0
  | '1' => some x1
  | '2' => some x2
  | '3' => some x3
  | '4' => some x4
  | '5' => some x5
  | '6' => some x6
  | '7' => some x7
  | '8' => some x8
  | '9' => some x9
  | 'a' => some xA
  | 'b' => some xB
  | 'c' => some xC
  | 'd' => some xD
  | 'e' => some xE
  | 'f' => some xF
  | 'A' => some xA
  | 'B' => some xB
  | 'C' => some xC
  | 'D' => some xD
  | 'E' => some xE
  | 'F' => some xF
  |  _  => none

-- def Hexit.toHex : Char → Hex
--   | '0' => x0
--   | '1' => x1
--   | '2' => x2
--   | '3' => x3
--   | '4' => x4
--   | '5' => x5
--   | '6' => x6
--   | '7' => x7
--   | '8' => x8
--   | '9' => x9
--   | 'a' => xA
--   | 'b' => xB
--   | 'c' => xC
--   | 'd' => xD
--   | 'e' => xE
--   | 'f' => xF
--   | 'A' => xA
--   | 'B' => xB
--   | 'C' => xC
--   | 'D' => xD
--   | 'E' => xE
--   |  _  => xF

-- def Hex.toBits : ∀ s : String, Bits (4 * s.length)
--   | ⟨[]⟩ => ⦃⦄
--   | ⟨c :: cs⟩ => Hexit.toHex c ++ toBits ⟨cs⟩

def Hex.toBits : ∀ (n : Nat), String → Option (Bits (4 * n))
  | 0, ⟨[]⟩ => some ⦃⦄
  | 0, ⟨_ :: _⟩ => none
  | _ + 1, ⟨[]⟩ => none
  | n + 1, ⟨c :: cs⟩ => do
    let h ← Hexit.toNib c
    let hs ← toBits n ⟨cs⟩
    some (h ++ hs)

def Hex.toBits! (n : Nat) (s : String) : Bits (4 * n) :=
  let cs := (s.data.reverse.takeD n '0').reverse
  (Hex.toBits n ⟨cs⟩).getD 0



abbrev Qords : Type := Vec (Bits 64) 25
abbrev QordsU : Type := Vec B64 25

def Char.toByte (c : Char) : Byte := Nat.toBits 8 c.toNat
def String.toBytes (s : String) : Bytes := s.data.map Char.toByte

def Bytes.toHex (bs : Bytes) : String :=
  List.foldr (λ b s => Byte.toHex b ++ s) "" bs

def Bits.toHex : ∀ k : Nat, Bits (4 * k) → String
 | 0, ⦃⦄ => ""
 | k + 1, .cons b0 (.cons b1 (.cons b2 (.cons b3 bs))) =>
   ⟨[Nib.toHexit ⦃b0, b1, b2, b3⦄]⟩ ++ bs.toHex k



def Byte.toB8 (b : Byte) : B8 := ⟨⟨b.toNat, b.toNat_lt_pow⟩⟩

-- def Byte.toUInt8 (b : Byte) : UInt8 := ⟨⟨b.toNat, b.toNat_lt_pow⟩⟩
--def UInt8.toByte (i : UInt8) : Byte := i.toBitVec.toFin.val.toByte
def B8.toByte (i : B8) : Byte := i.toBitVec.toFin.val.toByte

def Bits.toB64 (xs : Bits 64) : B64 := ⟨⟨xs.toNat, xs.toNat_lt_pow⟩⟩
-- def UInt64.toBits (i : UInt64) : Bits 64 := Nat.toBits 64 i.toBitVec.toFin.val
def B64.toBits (i : B64) : Bits 64 := Nat.toBits' 64 i.toBitVec.toFin.val

def B64.lows' (i : B64) : B64 := (i &&& 0x00000000FFFFFFFF)
def B64.highs' (i : B64) : B64 := (i >>> 32)

def B64.carry (x y : B64) : B64 :=
  if x + y < x then 1 else 0 -- alternatively : ~~~ x < y, or ~~~ y < x

def Bits.toB128 (xys : Bits 128) : B128 :=
  let xs := @Bits.prefix 64 64 xys
  let ys := @Bits.suffix 64 64 xys
  ⟨xs.toB64, ys.toB64⟩

def Bits.toB256 (xys : Bits 256) : B256 :=
  let xs := @Bits.prefix 128 128 xys
  let ys := @Bits.suffix 128 128 xys
  ⟨xs.toB128, ys.toB128⟩


def B128.toBits (i : B128) : Bits 128 := i.1.toBits ++ i.2.toBits
def B256.toBits (i : B256) : Bits 256 := i.1.toBits ++ i.2.toBits

def B64.mulx (x y : B64) : B128 :=
  let xh := x.highs'
  let xl := x.lows'
  let yh := y.highs'
  let yl := y.lows'
  let ll := xl * yl
  let lh := xl * yh
  let hl := xh * yl
  let hh := xh * yh
  let lhl := lh <<< 32
  let hll := hl <<< 32
  let lt := ll + lhl
  let l := lt + hll
  let c : B64 :=
    match (lt < ll : Bool), (l < lt : Bool) with
    | true, true => 2
    | false, false => 0
    | _, _  => 1
  let h := hh + lh.highs' + hl.highs' + c --0 + c1
  ⟨h, l⟩

def B128.mulx (x y : B128) : B256 :=
  let ll := B64.mulx x.2 y.2
  let lh := B64.mulx x.2 y.1
  let hl := B64.mulx x.1 y.2
  let hh := B64.mulx x.1 y.1
  let lhl : B128 := ⟨lh.2, 0⟩
  let hll : B128 := ⟨hl.2, 0⟩
  let lt := ll + lhl
  let l := lt + hll
  let c : B128 :=
    match (lt < ll : Bool), (l < lt : Bool) with
    | true, true => ⟨0, 2⟩
    | false, false => ⟨0, 0⟩
    | _, _  => ⟨0, 1⟩
  let h := hh + ⟨0, lh.1⟩ + ⟨0, hl.1⟩ + c --0 + c1
  ⟨h, l⟩

def B256.mul (x y : B256) : B256 :=
  let ll := B128.mulx x.2 y.2
  let lh := B128.mulx x.2 y.1
  let hl := B128.mulx x.1 y.2
  ll + ⟨lh.2, 0⟩ + ⟨hl.2, 0⟩
instance : HMul B256 B256 B256 := ⟨B256.mul⟩

def divOffset : Nat → B256 → B256 → Option Nat
  | 0, _, _ => some 0
  | m + 1, x, y =>
    if x < y
    then none
    else if B256.smin ≤ y
         then some 0
         else match divOffset m x (y <<< 1) with
                   | none => some 0
                   | some n => some (n + 1)


def B256.divModCore : Nat → B256 → B256 → B256 → (B256 × B256)
  | 0,     x, _, z => ⟨z, x⟩
  | n + 1, x, y, z =>
    if x < y
    then divModCore n x (y >>> 1) (z <<< 1)
    else divModCore n (x - y) (y >>> 1) ((z <<< 1) + 1)
def B256.divMod (x y : B256) : B256 × B256 :=
  if y = 0
  then ⟨0, 0⟩
  else let os := divOffset 255 x y
       match os with
       | none => ⟨0, x⟩
       | some n =>
         B256.divModCore (n + 1) x (y <<< n) 0

instance : HDiv B256 B256 B256 := ⟨λ x y => (B256.divMod x y).fst⟩
instance : HMod B256 B256 B256 := ⟨λ x y => (B256.divMod x y).snd⟩

#eval ((2 : B256) / foo256).toHex

def B256.sdiv (xs ys : B256) : B256 :=
  if ys = 0
  then 0
  else if xs = smin ∧ ys = negOne
       then smin
       else match (isNeg xs, isNeg ys) with
            | (0, 0) => xs / ys
            | (1, 0) => neg ((neg xs) / ys)
            | (0, 1) => neg (xs / (neg ys))
            | (1, 1) => (neg xs) / (neg ys)

def B256.abs (xs : B256) : B256 := if isNeg xs then neg xs else xs

def B256.smod (xs ys : B256) : B256 :=
  if ys = 0
  then 0
  else let mod := (abs xs) % (abs ys)
       if isNeg xs then neg mod else mod

-- @Bits.bexpCore m n x y := ⟨r, s⟩, where
--   r := x ^ y
--   s := if n = 0 then _ else x ^ (2 ^ (n - 1))
def Bits.bexpCore : ∀ {m n : Nat}, Bits m → Bits n → (Bits m × Bits m)
  | m, 0, x, ⦃⦄ => ⟨1, 1⟩
  | m, 1, x, ⦃b⦄ => ⟨cond b x 1, x⟩
  | m, n + 1, x, Bits.cons y ys =>
    let ⟨r, s⟩ := @Bits.bexpCore m n x ys
    let s₂ := s * s
    ⟨(cond y s₂ 1) * r, s₂⟩

def B64.teg (xs : B64) (n : Nat) : Bool :=
  ((xs >>> n.toUInt64) &&& 0x0000000000000001) != 0

def B128.teg (xs : B128) (n : Nat) : Bool :=
  if n < 64
  then xs.2.teg n
  else xs.1.teg (n - 64)

def B256.teg (xs : B256) (n : Nat) : Bool :=
  if n < 128
  then xs.2.teg n
  else xs.1.teg (n - 128)

-- def Bits.getD : ∀ {m}, Bits m → Nat → Bool → Bool
--   | 0, ⦃⦄, _, d => d
--   | _ + 1, x +> _, 0, _ => x
--   | _ + 1, _ +> xs, n + 1, d => Bits.getD xs n d
--
-- def B256.getD (xs : B256) (n : Nat) (b : Bool) : Bool :=
--   if n < 64
--   then xs.1.1.getD n b
--   else _


def B256.bexpCore : Nat → B256 → B256 → (B256 × B256)
 | 0, xs, _ => ⟨1, xs⟩
 | n + 1, xs, ys =>
   let ⟨r, s⟩ := B256.bexpCore n xs ys
   let y : Bool := ys.teg n
   ⟨(cond y s 1) * r, s * s⟩

def B256.bexp (xs ys : B256) : B256 :=
  (B256.bexpCore 256 xs ys).fst

def Bits.bexp {m : Nat} (xs ys : Bits m) : Bits m :=
  (@Bits.bexpCore m m xs ys).fst

instance : HPow B256 B256 B256 := ⟨B256.bexp⟩



------------------------------KECCAK------------------------------

-- 256-bit keccak hash function. Ported from Andrey Jivsov's
-- C implementation (https://github.com/brainhub/SHA3IUF)

def Qords'.init : Array B64 := Array.mkArray 25 0 --Mathlib.Vector.replicate 25 (.zero 64)
def Qords.init : Qords := Mathlib.Vector.replicate 25 (.zero 64)
def QordsU.init : QordsU := Mathlib.Vector.replicate 25 0

#check List.toString

def Qords.toString (ws : Qords) : String :=
  let f : Fin 25 → String :=
    λ k => Bits.toHex 16 (ws.get k)
  s!"{f 0} {f 1} {f 2} {f 3} {f 4}\n" ++
  s!"{f 5} {f 6} {f 7} {f 8} {f 9}\n" ++
  s!"{f 10} {f 11} {f 12} {f 13} {f 14}\n" ++
  s!"{f 15} {f 16} {f 17} {f 18} {f 19}\n" ++
  s!"{f 20} {f 21} {f 22} {f 23} {f 24}\n"


def QordsU.toString (ws : QordsU) : String :=
  let f : Fin 25 → String :=
    λ k => Bits.toHex 16 (B64.toBits (ws.get k))
  s!"{f 0} {f 1} {f 2} {f 3} {f 4}\n" ++
  s!"{f 5} {f 6} {f 7} {f 8} {f 9}\n" ++
  s!"{f 10} {f 11} {f 12} {f 13} {f 14}\n" ++
  s!"{f 15} {f 16} {f 17} {f 18} {f 19}\n" ++
  s!"{f 20} {f 21} {f 22} {f 23} {f 24}\n"

def Qords.app (k : Nat) (f : Bits 64 → Bits 64) (ws : Qords) : Qords :=
  ws.set k <| f <| ws.get k

def QordsU.app (k : Nat) (f : B64 → B64) (ws : QordsU) : QordsU :=
  ws.set k <| f <| ws.get k

def Qords'.app (k : Nat) (f : B64 → B64) (ws : Array B64) : Array B64 :=
  match ws.get? k with
  | none => ws
  | some x => ws.setD k (f x)

infixr:65 " ^^ " => Bits.xor

def sha3rotl64 (xs : Bits 64) (y : Nat) : Bits 64 :=
  Bits.or (xs.shl y) (xs.shr (64 - y))

def sha3rotl64' (xs : B64) (y : Nat) : B64 :=
  (xs <<< y.toUInt64) ||| (xs >>> (64 - y).toUInt64)

def sha3rotl64U (xs : B64) (y : Nat) : B64 := sha3rotl64' xs y

def Keccak.θ'' (t : Bits 64) (i : Nat) : Nat → Qords → Qords
  | 0, ws => ws
  | j + 1, ws => θ'' t i j <| ws.app ((j * 5) + i) (· ^^ t)

def KeccakU.θ'' (t : B64) (i : Nat) : Nat → QordsU → QordsU
  | 0, ws => ws
  | j + 1, ws => θ'' t i j <| ws.app ((j * 5) + i) (· ^^^ t)

def Keccak'.θ'' (t : B64) (i : Nat) : Nat → Array B64 → Array B64
  | 0, ws => ws
  | j + 1, ws => θ'' t i j <| Qords'.app ((j * 5) + i) (· ^^^ t) ws

def Keccak'.θ' (bc : Array B64) : Nat → Array B64 → Array B64
| 0, ws => ws
| i + 1, ws =>
  let t : B64 :=
    bc.get! ((i + 4) % 5) ^^^ sha3rotl64' (bc.get! ((i + 1) % 5)) 1
  θ' bc i <| θ'' t i 5 ws

def KeccakU.θ' (bc : Vec B64 5) : Nat → QordsU → QordsU
| 0, ws => ws
| i + 1, ws =>
  let t : B64 := bc.get (i + 4) ^^^ sha3rotl64U (bc.get (i + 1)) 1
  θ' bc i <| θ'' t i 5 ws

def Keccak.θ' (bc : Vec (Bits 64) 5) : Nat → Qords → Qords
| 0, ws => ws
| i + 1, ws =>
  let t : Bits 64 := bc.get (i + 4) ^^ sha3rotl64 (bc.get (i + 1)) 1
  θ' bc i <| θ'' t i 5 ws

def Keccak'.θ (ws : Array B64) : Array B64 :=
  let g : Fin 5 → B64 :=
    λ x =>
      ws.get! x ^^^ ws.get! (x + 5) ^^^ ws.get! (x + 10) ^^^
      ws.get! (x + 15) ^^^ ws.get! (x + 20)
  let bc : Array B64 := #[g 0, g 1, g 2, g 3, g 4]
  θ' bc 5 ws


def KeccakU.θ (ws : QordsU) : QordsU :=
  let g : Fin 5 → B64 :=
    λ x => ws.get x ^^^ ws.get (x + 5) ^^^ ws.get (x + 10) ^^^
          ws.get (x + 15) ^^^ ws.get (x + 20)
  let bc : Vec B64 5 := ⟨[g 0, g 1, g 2, g 3, g 4], rfl⟩
  θ' bc 5 ws

def Keccak.θ (ws : Qords) : Qords :=
  let g : Fin 5 → Bits 64 :=
    λ x => ws.get x ^^ ws.get (x + 5) ^^ ws.get (x + 10) ^^
          ws.get (x + 15) ^^ ws.get (x + 20)
  let bc : Vec (Bits 64) 5 := ⟨[g 0, g 1, g 2, g 3, g 4], rfl⟩
  θ' bc 5 ws

def keccak_rdnc_00 : Bits 64 := Hex.toBits! 16 "0000000000000001"
def keccak_rdnc_01 : Bits 64 := Hex.toBits! 16 "0000000000008082"
def keccak_rdnc_02 : Bits 64 := Hex.toBits! 16 "800000000000808a"
def keccak_rdnc_03 : Bits 64 := Hex.toBits! 16 "8000000080008000"
def keccak_rdnc_04 : Bits 64 := Hex.toBits! 16 "000000000000808b"
def keccak_rdnc_05 : Bits 64 := Hex.toBits! 16 "0000000080000001"
def keccak_rdnc_06 : Bits 64 := Hex.toBits! 16 "8000000080008081"
def keccak_rdnc_07 : Bits 64 := Hex.toBits! 16 "8000000000008009"
def keccak_rdnc_08 : Bits 64 := Hex.toBits! 16 "000000000000008a"
def keccak_rdnc_09 : Bits 64 := Hex.toBits! 16 "0000000000000088"
def keccak_rdnc_10 : Bits 64 := Hex.toBits! 16 "0000000080008009"
def keccak_rdnc_11 : Bits 64 := Hex.toBits! 16 "000000008000000a"
def keccak_rdnc_12 : Bits 64 := Hex.toBits! 16 "000000008000808b"
def keccak_rdnc_13 : Bits 64 := Hex.toBits! 16 "800000000000008b"
def keccak_rdnc_14 : Bits 64 := Hex.toBits! 16 "8000000000008089"
def keccak_rdnc_15 : Bits 64 := Hex.toBits! 16 "8000000000008003"
def keccak_rdnc_16 : Bits 64 := Hex.toBits! 16 "8000000000008002"
def keccak_rdnc_17 : Bits 64 := Hex.toBits! 16 "8000000000000080"
def keccak_rdnc_18 : Bits 64 := Hex.toBits! 16 "000000000000800a"
def keccak_rdnc_19 : Bits 64 := Hex.toBits! 16 "800000008000000a"
def keccak_rdnc_20 : Bits 64 := Hex.toBits! 16 "8000000080008081"
def keccak_rdnc_21 : Bits 64 := Hex.toBits! 16 "8000000000008080"
def keccak_rdnc_22 : Bits 64 := Hex.toBits! 16 "0000000080000001"
def keccak_rdnc_23 : Bits 64 := Hex.toBits! 16 "8000000080008008"

def keccakf_rndc' : Array B64 :=
  #[ 0x0000000000000001,
     0x0000000000008082,
     0x800000000000808a,
     0x8000000080008000,
     0x000000000000808b,
     0x0000000080000001,
     0x8000000080008081,
     0x8000000000008009,
     0x000000000000008a,
     0x0000000000000088,
     0x0000000080008009,
     0x000000008000000a,
     0x000000008000808b,
     0x800000000000008b,
     0x8000000000008089,
     0x8000000000008003,
     0x8000000000008002,
     0x8000000000000080,
     0x000000000000800a,
     0x800000008000000a,
     0x8000000080008081,
     0x8000000000008080,
     0x0000000080000001,
     0x8000000080008008 ]

def keccakf_rndcU : Vec B64 24 :=
  ⟨ [ 0x0000000000000001, 0x0000000000008082, 0x800000000000808a, 0x8000000080008000,
      0x000000000000808b, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
      0x000000000000008a, 0x0000000000000088, 0x0000000080008009, 0x000000008000000a,
      0x000000008000808b, 0x800000000000008b, 0x8000000000008089, 0x8000000000008003,
      0x8000000000008002, 0x8000000000000080, 0x000000000000800a, 0x800000008000000a,
      0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008 ], rfl ⟩

def keccakf_rndc : Vec (Bits 64) 24 :=
  ⟨ [ keccak_rdnc_00, keccak_rdnc_01, keccak_rdnc_02, keccak_rdnc_03,
      keccak_rdnc_04, keccak_rdnc_05, keccak_rdnc_06, keccak_rdnc_07,
      keccak_rdnc_08, keccak_rdnc_09, keccak_rdnc_10, keccak_rdnc_11,
      keccak_rdnc_12, keccak_rdnc_13, keccak_rdnc_14, keccak_rdnc_15,
      keccak_rdnc_16, keccak_rdnc_17, keccak_rdnc_18, keccak_rdnc_19,
      keccak_rdnc_20, keccak_rdnc_21, keccak_rdnc_22, keccak_rdnc_23 ], rfl ⟩

def keccakf_rotc : Vec Nat 24 :=
  ⟨ [ 1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 2, 14, 27,
      41, 56, 8, 25, 43, 62, 18, 39, 61, 20, 44 ], rfl ⟩

def keccakf_piln : Vec Nat 24 :=
  ⟨ [ 10, 7, 11, 17, 18, 3, 5, 16, 8, 21, 24, 4,
      15, 23, 19, 13, 12, 2, 20, 14, 22, 9, 6, 1 ], rfl ⟩

def Keccak'.ρπ' : Nat → B64 → Array B64 → Array B64
  | 0, _, ws => ws
  | k + 1, t, ws =>
    let i := 23 - k
    let j := keccakf_piln.get i
    let ws' := ws.setD j (sha3rotl64' t <| keccakf_rotc.get i)
    ρπ' k (ws.get! j) ws'

def KeccakU.ρπ' : Nat → B64 → QordsU → QordsU
  | 0, _, ws => ws
  | k + 1, t, ws =>
    let i := 23 - k
    let j := keccakf_piln.get i
    let ws' := ws.set j (sha3rotl64U t <| keccakf_rotc.get i)
    ρπ' k (ws.get j) ws'

def Keccak.ρπ' : Nat → Bits 64 → Qords → Qords
  | 0, _, ws => ws
  | k + 1, t, ws =>
    let i := 23 - k
    let j := keccakf_piln.get i
    let ws' := ws.set j (sha3rotl64 t <| keccakf_rotc.get i)
    ρπ' k (ws.get j) ws'

def Keccak.ρπ (ws : Qords) : Qords := ρπ' 24 (ws.get 1) ws

def KeccakU.ρπ (ws : QordsU) : QordsU := ρπ' 24 (ws.get 1) ws

def Keccak'.ρπ (ws : Array B64) : Array B64 := ρπ' 24 (ws.get! 1) ws

def Keccak.χ'' (ws : Qords) (bc : Vec (Bits 64) 5) (j : Nat) : Nat → Qords
  | 0 => ws
  | i + 1 =>
    let ws' := ws.app (j + i) (· ^^ (.and (bc.get (i + 1)).not (bc.get (i + 2))))
    χ'' ws' bc j i

def KeccakU.χ'' (ws : QordsU) (bc : Vec B64 5) (j : Nat) : Nat → QordsU
  | 0 => ws
  | i + 1 =>
    let ws' := ws.app (j + i) (· ^^^ ((~~~ bc.get (i + 1)) &&& (bc.get (i + 2))))
    χ'' ws' bc j i

def Keccak'.χ'' (ws : Array B64)
    (bc : Array B64) (j : Nat) : Nat → Array B64
  | 0 => ws
  | i + 1 =>
    let ws' :=
      Qords'.app (j + i) (· ^^^ ((~~~ bc.get! (i + 1)) &&& (bc.get! (i + 2)))) ws
    χ'' ws' bc j i

def Keccak'.χ' (ws : Array B64) : Nat → Array B64
  | 0 => ws
  | k + 1 =>
    let j := k * 5
    let f : Nat → B64 := λ x => ws.get! (j + x)
    let bc : Array B64 := #[f 0, f 1, f 2, f 3, f 4]
    let ws' : Array B64 := Keccak'.χ'' ws bc j 5
    χ' ws' k

def KeccakU.χ' (ws : QordsU) : Nat → QordsU
  | 0 => ws
  | k + 1 =>
    let j := k * 5
    let f : Nat → B64 := λ x => ws.get (j + x)
    let bc : Vec B64 5 := ⟨[f 0, f 1, f 2, f 3, f 4], rfl⟩
    let ws' : QordsU := KeccakU.χ'' ws bc j 5
    χ' ws' k

def Keccak.χ' (ws : Qords) : Nat → Qords
  | 0 => ws
  | k + 1 =>
    let j := k * 5
    let f : Nat → Bits 64 := λ x => ws.get (j + x)
    let bc : Vec (Bits 64) 5 := ⟨[f 0, f 1, f 2, f 3, f 4], rfl⟩
    let ws' : Qords := Keccak.χ'' ws bc j 5
    χ' ws' k

def Keccak.χ (ws : Qords) : Qords := χ' ws 5
def KeccakU.χ (ws : QordsU) : QordsU := χ' ws 5
def Keccak'.χ (ws : Array B64) : Array B64 := χ' ws 5

def Keccak.ι (round : Nat) (ws : Qords) : Qords :=
  ws.app 0 (· ^^ keccakf_rndc.get round)

def KeccakU.ι (round : Nat) (ws : QordsU) : QordsU :=
  ws.app 0 (· ^^^ keccakf_rndcU.get round)

def Keccak'.ι (round : Nat) (ws : Array B64) : Array B64 :=
  Qords'.app 0 (UInt64.xor · <| keccakf_rndc'.get! round) ws

def Keccak.aux : Nat → Qords → Qords
| 0, ws => ws
| 24, ws =>
  let temp := θ ws
  -- dbg_trace s!"input :\n{ws.toString}"
  -- dbg_trace s!"output :\n{temp.toString}"
  aux 23 <| ι 0 <| χ <| ρπ temp
| n + 1, ws =>
  aux n <| ι (23 - n) <| χ <| ρπ <| θ ws

def KeccakU.aux : Nat → QordsU → QordsU
| 0, ws => ws
| 24, ws =>
  let temp := θ ws
  -- dbg_trace s!"input :\n{ws.toString}"
  -- dbg_trace s!"output :\n{temp.toString}"
  aux 23 <| ι 0 <| χ <| ρπ temp
| n + 1, ws =>
  aux n <| ι (23 - n) <| χ <| ρπ <| θ ws

def Keccak'.aux : Nat → Array B64 → Array B64
| 0, ws => ws
| n + 1, ws => aux n <| ι (23 - n) <| χ <| ρπ <| θ ws

def Keccak.f (ws : Qords) : Qords := aux 24 ws
def KeccakU.f (ws : QordsU) : QordsU := aux 24 ws

def Qord.reverse (w : Bits 64) : Bits 64 :=
  Bytes.toBits 8 (@Bits.toBytes 8 w).reverse

abbrev Qords' := Array B64

def Array.htn {ξ : Type u} (xs : Array ξ) (n : Nat) : Option ξ :=
  xs.get? <| xs.size - n

def Array.htnD {ξ : Type u} (xs : Array ξ) (n : Nat) (x : ξ) : ξ :=
  xs.getD (xs.size - n) x

def Array.htn! {ξ : Type u} [Inhabited ξ] (xs : Array ξ) (n : Nat) : ξ :=
  xs.get! (xs.size - n)

def B8s.toB64 (a b c d e f g h : B8) : B64 :=
  let a64 : B64 := a.toUInt64
  let b64 : B64 := b.toUInt64
  let c64 : B64 := c.toUInt64
  let d64 : B64 := d.toUInt64
  let e64 : B64 := e.toUInt64
  let f64 : B64 := f.toUInt64
  let g64 : B64 := g.toUInt64
  let h64 : B64 := h.toUInt64
  (a64 <<< 56) |||
  (b64 <<< 48) |||
  (c64 <<< 40) |||
  (d64 <<< 32) |||
  (e64 <<< 24) |||
  (f64 <<< 16) |||
  (g64 <<< 8)  |||
  h64



instance {n : Nat} : ToString (Bits n) := ⟨@Bits.toString n⟩

def keccak : Fin 17 → Bytes → Qords → Word
| wc, b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: bs, ws =>
  let t : Bits 64 := Bytes.toBits 8 [b7, b6, b5, b4, b3, b2, b1, b0]
  let ws' := ws.app wc (· ^^ t)
  keccak (wc + 1) bs <| if wc = 16 then (Keccak.f ws') else ws'
| wc, bs, ws =>
  let t : Bits 64 := Bytes.toBits' 8 ((bs ++ [Bits.one 8]).takeD 8 (.zero 8)).reverse
  let s := (Hex.toBits 16 "8000000000000000").getD 0
  let temp0 := Qords.app wc (· ^^ t) ws
  let temp1 := Qords.app 16 (· ^^ s) temp0
  let ws' := Keccak.f temp1
  (Qord.reverse <| ws'.get 0) ++ (Qord.reverse <| ws'.get 1) ++
  (Qord.reverse <| ws'.get 2) ++ (Qord.reverse <| ws'.get 3)



def keccakU : Fin 17 → B8s → QordsU → B256
| wc, b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: bs, ws =>
  let t : B64 := B8s.toB64 b7 b6 b5 b4 b3 b2 b1 b0
  let ws' := ws.app wc (· ^^^ t)
  keccakU (wc + 1) bs <| if wc = 16 then (KeccakU.f ws') else ws'
| wc, bs, ws =>
  let us := (bs ++ [(1 : B8)]).takeD 8 (0 : B8)
  let t : B64 :=
    B8s.toB64
      (us.get! 7) (us.get! 6) (us.get! 5) (us.get! 4)
      (us.get! 3) (us.get! 2) (us.get! 1) (us.get! 0)
  let s : B64 := (8 : B64) <<< 60
  let temp0 := QordsU.app wc (· ^^^ t) ws
  let temp1 := QordsU.app 16 (· ^^^ s) temp0
  let ws' := KeccakU.f temp1
  --Qord.reverse (ws'.get 0).toBits ++
  --Qord.reverse (ws'.get 1).toBits ++
  --Qord.reverse (ws'.get 2).toBits ++
  --Qord.reverse (ws'.get 3).toBits
  (B64.reverse (ws'.get 0) ++ B64.reverse (ws'.get 1)) ++
  (B64.reverse (ws'.get 2) ++ B64.reverse (ws'.get 3))

  --⟨B64.reverse (ws'.get 0), B64.reverse (ws'.get 1)⟩ ++ ⟨B64.reverse (ws'.get 2), B64.reverse (ws'.get 3)⟩

def keccakA (n : Nat) (wc : Fin 17) (bs : Array B8) (ws : QordsU) : B256 :=
  if 7 < n
  then let b0 : B8 := bs.htn! n
       let b1 : B8 := bs.htn! (n - 1)
       let b2 : B8 := bs.htn! (n - 2)
       let b3 : B8 := bs.htn! (n - 3)
       let b4 : B8 := bs.htn! (n - 4)
       let b5 : B8 := bs.htn! (n - 5)
       let b6 : B8 := bs.htn! (n - 6)
       let b7 : B8 := bs.htn! (n - 7)
       let t : B64 := B8s.toB64 b7 b6 b5 b4 b3 b2 b1 b0
       let ws' := QordsU.app wc (UInt64.xor · t) ws
       keccakA (n - 8) (wc + 1) bs <| if wc = 16 then (KeccakU.f ws') else ws'
  else let us := (bs.toList ++ [(1 : B8)]).takeD 8 (0 : B8)
       let t : B64 :=
         B8s.toB64
           (us.get! 7) (us.get! 6) (us.get! 5) (us.get! 4)
           (us.get! 3) (us.get! 2) (us.get! 1) (us.get! 0)
       let s : B64 := (8 : B64) <<< 60
       let temp0 := QordsU.app wc (· ^^^ t) ws
       let temp1 := QordsU.app 16 (· ^^^ s) temp0
       let ws' := KeccakU.f temp1
       -- Qord.reverse (ws'.get 0).toBits ++
       -- Qord.reverse (ws'.get 1).toBits ++
       -- Qord.reverse (ws'.get 2).toBits ++
       -- Qord.reverse (ws'.get 3).toBits
      (B64.reverse (ws'.get 0) ++ B64.reverse (ws'.get 1)) ++
      (B64.reverse (ws'.get 2) ++ B64.reverse (ws'.get 3))

def Bytes.keccak (bs : Bytes) : Word :=
  _root_.keccak (0 : Fin 17) bs Qords.init

def B8s.keccak (bs : B8s) : B256 :=
  _root_.keccakU (0 : Fin 17) bs QordsU.init

def B8a.keccak (bs : Array B8) : B256 :=
  keccakA bs.size (0 : Fin 17) bs QordsU.init

def String.keccak (s : String) : Word :=
  Bytes.keccak s.toBytes

def List.splitAt? {ξ : Type u} : Nat → List ξ → Option (List ξ × List ξ)
  | 0, xs => some ([], xs)
  | _ + 1, [] => none
  | n + 1, x :: xs => .map (x :: ·) id <$> xs.splitAt? n

def B8s.toNat' : Nat → B8s → Nat
  | k, [] => k
  | k, b :: bs => B8s.toNat' ((k * 256) + b.toNat) bs
def B8s.toNat (bs : B8s) : Nat := bs.toNat' 0

def Bytes.toNat' : Nat → Bytes → Nat
  | k, [] => k
  | k, b :: bs => Bytes.toNat' ((k * 256) + b.toNat) bs
def Bytes.toNat (bs : Bytes) : Nat := bs.toNat' 0

def Nat.toBytesCore (n : Nat) : Bytes :=
  if n < 256
  then [n.toByte]
  else (n % 256).toByte :: (n / 256).toBytesCore
def Nat.toBytes (n : Nat) : Bytes := n.toBytesCore.reverse

def Nat.toB8sCore (n : Nat) : B8s :=
  if n < 256
  then [n.toUInt8]
  else (n % 256).toUInt8 :: (n / 256).toB8sCore
def Nat.toB8s (n : Nat) : B8s := n.toB8sCore.reverse



-------------------------------- RLP --------------------------------

inductive RLP : Type
  | bytes : Bytes → RLP
  | list : List RLP → RLP

mutual def RLP.decode' : Nat → Bytes → Option (RLP × Bytes)
    | _, [] => none
    | 0, _ :: _ => none
    | _ + 1, b@⦃0, _, _, _, _, _, _, _⦄ :: bs => some (.bytes [b], bs)
    | _ + 1, b@⦃1, 0, 1, 1, 1, _, _, _⦄ :: bs => do
      let (lbs, bs') ← List.splitAt? (b - Ox xB x7).toNat bs
      let (rbs, bs'') ← List.splitAt? (Bytes.toNat lbs) bs'
      return ⟨.bytes rbs, bs''⟩
    | _ + 1, b@⦃1, 0, _, _, _, _, _, _⦄ :: bs =>
      .map .bytes id <$> List.splitAt? (b - Ox x8 x0).toNat bs
    | k + 1, b@⦃1, 1, 1, 1, 1, _, _, _⦄ :: bs => do
      let (lbs, bs') ← List.splitAt? (b - Ox xF x7).toNat bs
      let (rbs, bs'') ← List.splitAt? (Bytes.toNat lbs) bs'
      let rs ← RLPs.decode k rbs
      return ⟨.list rs, bs''⟩
    | k + 1, b@⦃1, 1, _, _, _, _, _, _⦄ :: bs => do
      let (rbs, bs') ← List.splitAt? (b - Ox xC x0).toNat bs
      let rs ← RLPs.decode k rbs
      return ⟨.list rs, bs'⟩
  def RLPs.decode : Nat → Bytes → Option (List RLP)
    | _, [] => some []
    | 0, _ :: _ => none
    | k + 1, bs@(_ :: _) => do
      let (r, bs') ← RLP.decode' (k + 1) bs
      let rs ← RLPs.decode k bs'
      return (r :: rs)
end

def RLP.decode (bs : Bytes) : Option RLP :=
  match RLP.decode' bs.length bs with
  | some (r, []) => some r
  | _ => none

def RLP.encodeBytes : Bytes → Bytes
  | [b] =>
    if b < (Ox x8 x0)
    then [b]
    else [Ox x8 x1, b]
  | bs =>
    if bs.length < 56
    then (Ox x8 x0 + bs.length.toByte) :: bs
    else let lbs : Bytes := bs.length.toBytes
         (Ox xB x7 + lbs.length.toByte) :: (lbs ++ bs)

mutual
  def RLP.encode : RLP → Bytes
    | .bytes [b] =>
      if b < (Ox x8 x0)
      then [b]
      else [Ox x8 x1, b]
    | .bytes bs =>
      if bs.length < 56
      then (Ox x8 x0 + bs.length.toByte) :: bs
      else let lbs : Bytes := bs.length.toBytes
           (Ox xB x7 + lbs.length.toByte) :: (lbs ++ bs)
    | .list rs => RLPs.encode rs
  def RLPs.encodeMap : List RLP → Bytes
    | .nil => []
    | .cons r rs => r.encode ++ RLPs.encodeMap rs
  def RLPs.encode (rs : List RLP) : Bytes :=
    let bs := RLPs.encodeMap rs
    let len := bs.length
    if len < 56
    then (Ox xC x0 + len.toByte) :: bs
    else let lbs : Bytes := len.toBytes
         (Ox xF x7 + lbs.length.toByte) :: (lbs ++ bs)
end

partial def RLP.toStrings : RLP → List String
  | .bytes bs => [s!"0x{bs.toHex}"]
  | .list rs => "List:" :: (rs.map RLP.toStrings).flatten.map ("  " ++ ·)


-------------------------------- RLP' --------------------------------

inductive RLP' : Type
  | b8s : B8s → RLP'
  | list : List RLP' → RLP'


def B8.toBools (x0 : B8) :
    Bool × Bool × Bool × Bool × Bool × Bool × Bool × Bool :=
  let x1 := x0 <<< 1
  let x2 := x1 <<< 1
  let x3 := x2 <<< 1
  let x4 := x3 <<< 1
  let x5 := x4 <<< 1
  let x6 := x5 <<< 1
  let x7 := x6 <<< 1
  ⟨ x0.highBit, x1.highBit, x2.highBit, x3.highBit,
    x4.highBit, x5.highBit, x6.highBit, x7.highBit ⟩

mutual
  def RLP'.decode' : Nat → B8s → Option (RLP' × B8s)
    | _, [] => none
    | 0, _ :: _ => none
    | k + 1, b :: bs =>
      match b.toBools with
    | ⟨0, _, _, _, _, _, _, _⟩ => some (.b8s [b], bs)
    | ⟨1, 0, 1, 1, 1, _, _, _⟩ => do
      let (lbs, bs') ← List.splitAt? (b - 0xB7).toNat bs
      let (rbs, bs'') ← List.splitAt? (B8s.toNat lbs) bs'
      return ⟨.b8s rbs, bs''⟩
    | ⟨1, 0, _, _, _, _, _, _⟩ =>
      .map .b8s id <$> List.splitAt? (b - 0x80).toNat bs
    | ⟨1, 1, 1, 1, 1, _, _, _⟩ => do
      let (lbs, bs') ← List.splitAt? (b - 0xF7).toNat bs
      let (rbs, bs'') ← List.splitAt? (B8s.toNat lbs) bs'
      let rs ← RLPs'.decode k rbs
      return ⟨.list rs, bs''⟩
    | ⟨1, 1, _, _, _, _, _, _⟩ => do
      let (rbs, bs') ← List.splitAt? (b - 0xC0).toNat bs
      let rs ← RLPs'.decode k rbs
      return ⟨.list rs, bs'⟩

  def RLPs'.decode : Nat → B8s → Option (List RLP')
    | _, [] => some []
    | 0, _ :: _ => none
    | k + 1, bs@(_ :: _) => do
      let (r, bs') ← RLP'.decode' (k + 1) bs
      let rs ← RLPs'.decode k bs'
      return (r :: rs)
end

def RLP'.decode (bs : B8s) : Option RLP' :=
  match RLP'.decode' bs.length bs with
  | some (r, []) => some r
  | _ => none

def RLP'.encodeBytes : B8s → B8s
  | [b] => if b < (0x80) then [b] else [0x81, b]
  | bs =>
    if bs.length < 56
    then (0x80 + Nat.toUInt8 bs.length) :: bs
    else let lbs : B8s := bs.length.toB8s
         (0xB7 + lbs.length.toUInt8) :: (lbs ++ bs)

mutual
  def RLP'.encode : RLP' → B8s
    | .b8s [b] => if b < (0x80) then [b] else [0x81, b]
    | .b8s bs =>
      if bs.length < 56
      then (0x80 + bs.length.toUInt8) :: bs
      else let lbs : B8s := bs.length.toB8s
           (0xB7 + lbs.length.toUInt8) :: (lbs ++ bs)
    | .list rs => RLPs'.encode rs
  def RLPs'.encodeMap : List RLP' → B8s
    | .nil => []
    | .cons r rs => r.encode ++ RLPs'.encodeMap rs
  def RLPs'.encode (rs : List RLP') : B8s :=
    let bs := RLPs'.encodeMap rs
    let len := bs.length
    if len < 56
    then (0xC0 + len.toUInt8) :: bs
    else let lbs : B8s := len.toB8s
         (0xF7 + lbs.length.toUInt8) :: (lbs ++ bs)
end

partial def RLP'.toStrings : RLP' → List String
  | .b8s bs => [s!"0x{bs.toHex}"]
  | .list rs => "List:" :: (rs.map RLP'.toStrings).flatten.map ("  " ++ ·)
