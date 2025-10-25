-- Basic.lean : generic definitions and lemmas (e.g. for Booleans, lists,
-- bit vectors and bytes) useful for but not specific to Blanc

import Mathlib.Data.Nat.Basic
import Mathlib.Data.List.Lemmas
import Mathlib.Util.Notation3
import Mathlib.Data.Vector.Basic
import Elevm.Types



-- Boolean lemmas --

instance : @Zero Bool := ⟨false⟩
instance : @One Bool := ⟨true⟩

def Bool.toChar : Bool → Char
  | 0 => '0'
  | 1 => '1'

theorem Bool.zero_or_one (x : Bool) : x = 0 ∨ x = 1 := by
  cases x
  · left; rfl
  · right; rfl

theorem not_true_lt {b} : ¬ true < b := by simp [LT.lt]
theorem Bool.zero : 0 = false := rfl
theorem Bool.one : 1 = true := rfl

def Split {α} [HAppend α α α] : α → α → α → Prop
  | a, ab, b => ab = a ++ b

notation x " <++ " xy " ++> " y => Split x xy y

def Pref {ξ} [HAppend ξ ξ ξ] (x : ξ) (xy : ξ) : Prop :=
  ∃ y : ξ, x <++ xy ++> y

infix:45 " <<+ " => Pref

theorem pref_append {ξ} [HAppend ξ ξ ξ] (xs ys : ξ) : xs <<+ xs ++ ys := ⟨ys, rfl⟩

def Frel {A B} (a : A) (r : B → B → Prop) (f g : A → B) : Prop :=
  ∀ a', (a = a' → r (f a') (g a')) ∧ (a ≠ a' → f a' = g a')

def Overwrite {A B} (x : A) (y : B) : (A → B) → (A → B) → Prop := Frel x (λ _ y' => y = y')

theorem List.of_cons_pref_of_cons_pref {ξ} {x y : ξ} {xs ys zs} :
    (x :: xs <<+ zs) → (y :: ys <<+ zs) →
      x = y ∧ ∃ zs', (xs <<+ zs') ∧ (ys <<+ zs') := by
  intros h0 h1
  rcases h0 with ⟨sfx, h0⟩
  rcases h1 with ⟨sfx', h1⟩
  rcases List.cons_eq_cons.mp (Eq.trans h0.symm h1) with ⟨h_head, h_tail⟩
  refine ⟨h_head, xs ++ sfx, pref_append _ _, sfx', h_tail⟩

theorem pref_head_unique {ξ} {x y : ξ} {xs ys zs} :
    (x :: xs <<+ zs) → (y :: ys <<+ zs) → x = y := by
  intros hx hy; apply (List.of_cons_pref_of_cons_pref hx hy).left

theorem List.pref_unique {ξ} {xs ys zs : List ξ}
    (h_len : xs.length = ys.length) (h : xs <<+ zs) (h' : ys <<+ zs) : xs = ys := by
  rcases h with ⟨sfx, h⟩; rcases h' with ⟨sfx', h'⟩
  apply List.append_inj_left (Eq.trans h.symm h') h_len

theorem pref_of_split {X} {x xy y : List X} : (x <++ xy ++> y) → (x <<+ xy) := λ h => ⟨y, h⟩

theorem List.of_cons_split_cons {X} {x y : X} {xs ys zs} :
    ((x :: xs) <++ y :: ys ++> zs) → (x = y ∧ (xs <++ ys ++> zs)) := by
  simp [Split]; intros h h'; simp [h, h']

theorem List.of_cons_split {X} {x : X} {xs ys zs} (h : (x :: xs) <++ ys ++> zs) :
    ∃ ys', (ys = x :: ys' ∧ (xs <++ ys' ++> zs)) := by
  cases ys with
  | nil => cases h
  | cons y ys =>
    rcases of_cons_split_cons h with ⟨⟨_⟩, h'⟩
    refine' ⟨_, rfl, h'⟩

theorem List.of_nil_split {X} {p p' : List X} : ([] <++ p ++> p') → p = p' := by simp [Split]

universe u

theorem Nat.forall_lt_succ_iff_forall_le {n : ℕ} {p : ℕ → Prop} :
    (∀ m < (n + 1), p m) ↔ (∀ m ≤ n, p m) := by
  constructor <;> intros h m h' <;> apply h
  · rw [Nat.lt_succ_iff]; apply h'
  · rw [← Nat.lt_succ_iff]; apply h'

theorem Nat.forall_le_succ {n : ℕ} {p : ℕ → Prop} :
    (∀ m ≤ n + 1, p m) ↔ (∀ m ≤ n, p m) ∧ p (n + 1) := by
  rw [← Nat.forall_lt_succ_iff_forall_le, ← Nat.forall_lt_succ_iff_forall_le]
  apply Nat.forall_lt_succ_right

syntax "asm" : term
macro_rules
  | `(term| asm) => `(term| by assumption)

syntax "cst" : term
macro_rules
  | `(term| cst) => `(term| by constructor)

theorem split_of_prefix {X} {x xy: List X} : (x <<+ xy) → ∃ y, (x <++ xy ++> y) := id

theorem pref_iff_isPrefix {ξ} {xs ys : List ξ} : xs <<+ ys ↔ xs <+: ys := by
  constructor <;> intro h <;> rcases h with ⟨zs, h⟩ <;> refine' ⟨zs, h.symm⟩

theorem pref_trans {X} {x xy xyz : List X} : (x <<+ xy) → (xy <<+ xyz) → (x <<+ xyz) := by
  simp [pref_iff_isPrefix]; apply List.IsPrefix.trans

theorem append_split {X} {x y z yz xyz : List X} (h : x <++ xyz ++> yz)
    (h' : y <++ yz ++> z) : (x ++ y) <++ xyz ++> z := by
  simp [Split] at *; rw [h, h']

theorem of_append_split {X} {x y z yz xyz : List X}
    (h : x <++ xyz ++> yz) (h' : (x ++ y) <++ xyz ++> z) : (y <++ yz ++> z) := by
  simp [Split] at *; apply List.append_inj_right (Eq.trans h.symm h') rfl

theorem of_append_pref {X} {x y yz xyz : List X} :
    (x <++ xyz ++> yz) → (x ++ y <<+ xyz) → (y <<+ yz) := by
  intros h0 h1; rcases h1 with ⟨z, h1⟩
  refine ⟨z, of_append_split h0 h1⟩

theorem append_pref {X} {x y yz xyz : List X} :
    (x <++ xyz ++> yz) → (y <<+ yz) → (x ++ y <<+ xyz) := by
  intros h0 h1; rcases split_of_prefix h1 with ⟨z, h2⟩
  refine ⟨z, append_split h0 h2⟩

theorem nil_pref {X} {xs : List X} : ([] <<+ xs) := ⟨xs, rfl⟩

theorem cons_pref_cons {X} {x y : X} {p pq} :
    x = y → (p <<+ pq) → (x :: p <<+ y :: pq) := by
  intros h0 h1; rw [h0]; rcases h1 with ⟨q, h2⟩; rw [h2]; refine ⟨q, rfl⟩

syntax "show_pref" : tactic
macro_rules
  | `(tactic| show_pref) =>
    `(tactic| first | apply nil_pref
                    | apply cons_pref_cons; rfl; show_pref )

theorem of_cons_cons_pref_of_cons_cons_pref {X} {x y x' y' : X} {xs xs' ys} :
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


-- abbrev Word := B256

theorem Bool.lt_or_ge (x y : Bool) : x < y ∨ x ≥ y := by
  cases x <;> cases y <;> simp

theorem Bool.lt_or_eq_of_le {x y : Bool} : x ≤ y → (x < y ∨ x = y) := by
  cases x <;> cases y <;> simp

theorem Bool.beq_eq_true (a b : Bool) : ((a == b) = true) = (a = b) := by
  cases a <;> cases b <;> simp

theorem List.takeD_concat {ξ : Type u} (n) (xs : List ξ) (y) :
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

theorem List.drop?_add {ξ : Type u} (m n : Nat) (xs : List ξ) :
    drop? (m + n) xs = drop? n xs >>= drop? m := by
  induction n generalizing xs with
  | zero => rfl
  | succ n ih =>
    cases xs <;> simp only [drop?]
    · rfl
    · apply ih

theorem List.get?_eq_drop?_head? {ξ : Type u} {xs : List ξ} {n : Nat} :
    xs[n]? = drop? n xs >>= head? := by
  induction n generalizing xs with
  | zero => cases xs <;> simp [drop?]
  | succ n ih =>
    cases xs
    · simp [drop?]
    · simp [drop?]; apply ih

def List.Slice {ξ : Type u} (xs : List ξ) (m : Nat) (ys : List ξ) : Prop :=
  ∃ n, xs.slice? m n = some ys

theorem List.slice?_cons {ξ : Type u} (x) (xs : List ξ) (m n : Nat) :
    slice? (x :: xs) (m + 1) n = slice? xs m n := rfl

theorem List.slice?_eq_cons_iff {ξ : Type u} {xs : List ξ} {m n : Nat} {y} {ys} :
    slice? xs m (n + 1) = some (y :: ys) ↔
      (xs[m]? = some y ∧ slice? xs (m + 1) n = some ys) := by
  induction m generalizing xs with
  | zero =>
    match xs with
    | [] => simp [slice?, drop?, Bind.bind, Option.bind, take?]
    | x :: xs =>
      simp only
        [slice?, drop?, Bind.bind, Option.bind, take?]
      cases take? n xs <;> simp
  | succ m ih =>
    match xs with
    | [] => simp [slice?, drop?, Bind.bind, Option.bind]
    | x :: xs =>
      rw [List.slice?_cons, ih]; rfl

theorem List.slice_cons_iff {ξ : Type u} {xs : List ξ} {m : Nat} {y} {ys} :
    xs.Slice m (y :: ys) ↔ (xs[m]? = some y ∧ xs.Slice (m + 1) ys) := by
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

theorem List.length_take? {ξ : Type u} {n : Nat} {xs ys : List ξ} :
    take? n xs = some ys → n = ys.length := by
  induction n generalizing xs ys with
  | zero => simp [take?]; intro h; simp [h]
  | succ n ih =>
    cases xs <;> simp [take?]
    intro ys' h h'; rw [ih h, ← h']; rfl

theorem List.length_slice? {ξ : Type u} {xs} {m n : Nat} {ys : List ξ} :
    slice? xs m n = some ys → n = ys.length := by
  unfold slice?; cases xs.drop? m <;> simp; apply length_take?

theorem List.get?_eq_of_slice {ξ : Type u} {xs : List ξ} {m : Nat} {y} {ys} :
    Slice xs m (y :: ys) → xs[m]? = some y := by
  rw [slice_cons_iff]; apply And.left

theorem List.slice_iff_get?_eq {ξ : Type u} {xs : List ξ} {m : Nat} {y} :
    Slice xs m [y] ↔ xs[m]? = some y := by
  refine' ⟨get?_eq_of_slice, λ h => ⟨1, _⟩⟩;
  revert h; rw [get?_eq_drop?_head?]; unfold slice?
  cases xs.drop? m with
  | none => simp
  | some xs' => cases xs' <;> simp; intro h'; simp [h', take?]

theorem List.of_take?_eq_append {ξ : Type u} {xs : List ξ}
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

theorem List.of_slice?_eq_append {ξ : Type u} {xs : List ξ}
    {m n : Nat} {ys zs} (h : slice? xs m n = some (ys ++ zs)) :
    slice? xs m ys.length = some ys ∧
    slice? xs (m + ys.length) zs.length = some zs := by
  revert h; unfold slice?; rw [Nat.add_comm, drop?_add]
  cases xs.drop? m <;> simp; rename List ξ => xs'; apply of_take?_eq_append

theorem List.slice_prefix {ξ : Type u} {xs : List ξ}
    {m : Nat} {ys zs} (h : Slice xs m (ys ++ zs)) : Slice xs m ys := by
  rcases h with ⟨n, h⟩; refine ⟨_, (of_slice?_eq_append h).left⟩

theorem List.slice_suffix {ξ : Type u} {xs : List ξ} {m : Nat} {ys zs}
    (h : Slice xs m (ys ++ zs)) : Slice xs (m + ys.length) zs := by
  rcases h with ⟨n, h⟩; refine ⟨_, (of_slice?_eq_append h).right⟩

theorem List.get?_length_ne_some {ξ : Type y} {xs : List ξ} {y} :
    xs[xs.length]? ≠ some y := by simp

theorem List.not_slice_length {xs} {y} {ys : List ξ} :
    ¬ Slice xs xs.length (y :: ys) := by simp [slice_cons_iff]

theorem List.take?_length {ξ : Type u} (xs : List ξ) :
    take? xs.length xs = some xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [take?, ih]

theorem List.slice_refl {ξ : Type u} (xs : List ξ) : List.Slice xs 0 xs := by
  refine' ⟨xs.length, _⟩; simp [slice?, drop?, take?_length]

theorem List.append_slice_suffix {ξ : Type y} {xs ys : List ξ} :
    Slice (xs ++ ys) xs.length ys := by
  have h := slice_suffix <| slice_refl <| xs ++ ys
  rw [Nat.zero_add] at h; exact h


-- B(2^n) lemmas (transfer to ELEVM later) --

lemma B128.le_refl (x : B128) : x ≤ x := by
  right; refine ⟨rfl, UInt64.le_refl _⟩

lemma B256.le_refl (x : B256) : x ≤ x := by
  right; refine ⟨rfl, B128.le_refl _⟩

lemma B128.sub_eq (x y : B128) :
  x - y = ⟨(x.1 - y.1) - (if x.2 < y.2 then 1 else 0), x.2 - y.2⟩ := rfl

lemma B256.sub_eq (x y : B256) :
  x - y = ⟨(x.1 - y.1) - (if x.2 < y.2 then 1 else 0), x.2 - y.2⟩ := rfl

def B128.add_eq (x y : B128) :
  x + y = ⟨x.1 + y.1 + if x.2 + y.2 < x.2 then 1 else 0, x.2 + y.2⟩ := rfl

def B256.add_eq (x y : B256) :
  x + y = ⟨x.1 + y.1 + if x.2 + y.2 < x.2 then 1 else 0, x.2 + y.2⟩ := rfl

lemma B128.sub_self (a : B128) : a - a = 0 := by
  rw [B128.sub_eq]; simp [UInt64.sub_self]; rfl

lemma B128.lt_irrefl (x : B128) : ¬ x < x := by
  intro h; rcases h with h | h <;> simp [UInt64.lt_irrefl] at h

lemma B256.sub_self (a : B256) : a - a = 0 := by
  rw [B256.sub_eq]; simp [B128.sub_self, B128.lt_irrefl]; rfl

def Adr.max : Adr := ⟨-1, -1, -1⟩

lemma Nat.lt_of_lt_high {sz high low high' low' : Nat}
    (h_high : high < high') (h_low : low < sz) :
    high * sz + low < high' * sz + low' := by
  rcases high' with _ | high'
  · cases Nat.not_lt_zero _ h_high
  · have h_le := Nat.le_of_lt_succ h_high
    rw [Nat.succ_mul, Nat.add_assoc]
    apply @Nat.add_lt_add_of_le_of_lt
    · apply Nat.mul_le_mul_right _ h_le
    · apply Nat.lt_add_right _ h_low


lemma B128.lt_iff (x y : B128) :
  x < y ↔ (x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 < y.2)) := Iff.refl _

lemma B256.lt_iff (x y : B256) :
  x < y ↔ (x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 < y.2)) := Iff.refl _

lemma B128.le_iff (x y : B128) :
    x ≤ y ↔ (x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 ≤ y.2)) := Iff.refl _

lemma B256.le_iff (x y : B256) :
    x ≤ y ↔ (x.1 < y.1 ∨ (x.1 = y.1 ∧ x.2 ≤ y.2)) := Iff.refl _

lemma B256.le_or_gt (a b : B256) : a ≤ b ∨ a > b := by sorry

lemma B128.le_or_gt (a b : B128) : a ≤ b ∨ a > b := by
  simp [GT.gt]; rw [B128.le_iff, B128.lt_iff];
  rcases UInt64.le_or_lt a.1 b.1 with h | h
  · rcases UInt64.lt_or_eq_of_le h with h' | h'
    · left; left; apply h'
    · rcases UInt64.le_or_lt a.2 b.2 with h'' | h''
      · left; right; refine ⟨h', h''⟩
      · right; right; refine ⟨h'.symm, h''⟩
  · right; left; apply h

lemma B128.lt_or_ge (a b : B128) : a < b ∨ a ≥ b :=
  Or.symm <| B128.le_or_gt _ _

lemma UInt64.toNat_lt_pow (a : UInt64) : a.toNat < 2 ^ 64 :=
  UInt64.toNat_lt_size _

lemma B128.toNat_eq (x : B128) : x.toNat = (x.1.toNat * (2 ^ 64)) + x.2.toNat := rfl

lemma B128.toNat_lt_toNat {a b : B128} (h : a < b) : a.toNat < b.toNat := by
  rcases a with ⟨ah, al⟩; rcases b with ⟨bh, bl⟩
  rcases h with h | h <;> simp at h <;> simp only [B128.toNat]
  · rw [UInt64.lt_iff_toNat_lt] at h
    apply Nat.lt_of_lt_high h
    apply UInt64.toNat_lt_size
  · rw [h.1]; apply Nat.add_lt_add_left
    rw [← UInt64.lt_iff_toNat_lt]; apply h.2


lemma B128.toNat_lt_size (x : B128) : x.toNat < 2 ^ 128 := by
  rcases x with ⟨xh, xl⟩; simp only [B128.toNat]
  have h : 2 ^ 128 = 2 ^ 64 * 2 ^ 64 + 0 := rfl
  rw [h]; clear h
  apply Nat.lt_of_lt_high <;> apply UInt64.toNat_lt_size

lemma B256.toNat_lt_size (x : B256) : x.toNat < 2 ^ 256 := by
  rcases x with ⟨xh, xl⟩; simp only [B256.toNat]
  have h : 2 ^ 256 = 2 ^ 128 * 2 ^ 128 + 0 := rfl
  rw [h]; clear h
  apply Nat.lt_of_lt_high <;> apply B128.toNat_lt_size

lemma B128.lt_or_eq_of_le {n m : B128} (h : n ≤ m) : n < m ∨ n = m := by
  rcases h with h | h
  · left; left; apply h
  · rcases UInt64.lt_or_eq_of_le h.2 with h' | h'
    · left; right; refine ⟨h.1, h'⟩
    · right; apply Prod.ext h.1 h'

lemma B256.lt_or_eq_of_le {n m : B256} (h : n ≤ m) : n < m ∨ n = m := by
  rcases h with h | h
  · left; left; apply h
  · rcases B128.lt_or_eq_of_le h.2 with h' | h'
    · left; right; refine ⟨h.1, h'⟩
    · right; apply Prod.ext h.1 h'

lemma B256.toNat_lt_toNat {a b : B256} (h : a < b) : a.toNat < b.toNat := by
  rcases a with ⟨ah, al⟩; rcases b with ⟨bh, bl⟩
  rcases h with h | h <;> simp at h <;> simp only [B256.toNat]
  · apply Nat.lt_of_lt_high <| B128.toNat_lt_toNat h
    apply B128.toNat_lt_size
  · rw [h.1]; apply Nat.add_lt_add_left
    apply B128.toNat_lt_toNat h.2

lemma B128.le_of_lt {a b : B128} (h : a < b) : a ≤ b := by
  rcases h with h | h
  · left; apply h
  · right; refine' ⟨h.1, UInt64.le_of_lt h.2⟩

lemma B256.le_of_lt {a b : B256} (h : a < b) : a ≤ b := by
  rcases h with h | h
  · left; apply h
  · right; refine' ⟨h.1, B128.le_of_lt h.2⟩

lemma B128.toNat_le_toNat {a b : B128} (h : a ≤ b) : a.toNat ≤ b.toNat := by
  rcases B128.lt_or_eq_of_le h with h | h
  · apply Nat.le_of_lt <| B128.toNat_lt_toNat h
  · rw [h]

lemma B256.toNat_le_toNat {a b : B256} (h : a ≤ b) : a.toNat ≤ b.toNat := by
  rcases B256.lt_or_eq_of_le h with h | h
  · apply Nat.le_of_lt <| B256.toNat_lt_toNat h
  · rw [h]

lemma B128.lt_of_toNat_lt_toNat {a b : B128} (lt : a.toNat < b.toNat) : a < b := by
  rcases B128.le_or_gt b a with h | h
  · cases not_le_of_gt lt <| B128.toNat_le_toNat h
  · apply h

lemma B256.lt_of_toNat_lt_toNat {a b : B256} (lt : a.toNat < b.toNat) : a < b := by
  rcases B256.le_or_gt b a with h | h
  · cases not_le_of_gt lt <| B256.toNat_le_toNat h
  · apply h

lemma B128.lt_iff_toNat_lt_toNat {a b : B128} : a < b ↔ a.toNat < b.toNat := by
  constructor
  · apply B128.toNat_lt_toNat
  · apply B128.lt_of_toNat_lt_toNat

lemma B256.lt_iff_toNat_lt_toNat {a b : B256} : a < b ↔ a.toNat < b.toNat := by
  constructor
  · apply B256.toNat_lt_toNat
  · apply B256.lt_of_toNat_lt_toNat

lemma UInt64.toNat_sub_of_lt (a b : UInt64) (h : a < b) :
    (a - b).toNat = 2 ^ 64 + a.toNat - b.toNat := by
  rw [UInt64.toNat_sub]
  have h_le : b.toNat ≤ 2 ^ 64 :=
    le_of_lt <| UInt64.toNat_lt_size _
  have h_lt : a.toNat < b.toNat := by
    rw [← UInt64.lt_iff_toNat_lt]; apply h
  rw [← Nat.sub_add_comm h_le]
  rw [Nat.mod_eq_of_lt]
  rw [← Nat.sub_sub_right _ (le_of_lt h_lt) ]
  apply Nat.sub_lt_self
  · apply Nat.zero_lt_sub_of_lt h_lt
  · apply le_trans (Nat.sub_le _ _) h_le

lemma UInt64.succ_toNat_neg_one :
  (-1 : UInt64).toNat.succ = 2 ^ 64 := rfl

lemma UInt64.toNat_le_toNat_neg_one (x : UInt64) :
    x.toNat ≤ (-1 : UInt64).toNat := by
  rw [← Nat.lt_succ_iff]; apply UInt64.toNat_lt_size

lemma UInt64.le_neg_one (x : UInt64) : x ≤ -1 := by
  rw [UInt64.le_iff_toNat_le]; apply UInt64.toNat_le_toNat_neg_one

lemma B128.high_le_of_lt {a b : B128} (h : a < b) : a.1 ≤ b.1 := by
  rcases h with h | h
  · apply UInt64.le_of_lt h
  · simp [h.1]

lemma Nat.mod_two_pow_add {k m n : ℕ} :
    k % 2 ^ (m + n) = k / 2 ^ n % 2 ^ m * 2 ^ n + k % 2 ^ n := by
  induction n generalizing k m with
  | zero => simp [Nat.mod_one]
  | succ n ih =>
    rw [← Nat.add_assoc]
    rw [Nat.mod_two_pow_succ, ih]
    rw [Nat.div_div_eq_div_mul]
    rw [← Nat.pow_succ']
    rw [Nat.add_mul]
    rw [Nat.pow_succ]
    rw [Nat.mul_assoc]
    rw [Nat.add_assoc]
    apply congr_arg₂ _ rfl
    rw [← Nat.pow_succ]
    rw [Nat.mod_two_pow_succ]

lemma Nat.mod_two_pow_mul_two_pow {k m n : Nat} :
    (k % 2 ^ m) * 2 ^ n = (k * 2 ^ n) % 2 ^ (m + n) := by
  rw [Nat.mod_two_pow_add, Nat.mul_div_cancel]
  · simp [Nat.mul_mod_left]
  · apply Nat.pow_pos; omega



lemma Nat.mod_two_shiftLeft {k m n : Nat} :
    (k % 2 ^ m) <<< n = (k <<< n) % 2 ^ (m + n) := by
  simp [Nat.shiftLeft_eq]
  apply Nat.mod_two_pow_mul_two_pow

lemma Nat.exists_eq_shiftLeft_of_dvd {n x} (hx : 2 ^ n ∣ x) :
    ∃ y, x = y <<< n := by
  rcases exists_eq_mul_right_of_dvd hx with ⟨y, ⟨_⟩⟩
  rw [Nat.mul_comm, ← Nat.shiftLeft_eq]
  refine ⟨y, rfl⟩

lemma Nat.add_eq_or {n x y} (hx : 2 ^ n ∣ x) (hy : y < 2 ^ n) :
    x + y = x ||| y := by
  rcases exists_eq_shiftLeft_of_dvd hx with ⟨z, ⟨_⟩⟩
  rw [Nat.shiftLeft_add_eq_or_of_lt hy]

lemma Nat.add_mod_two_pow_distrib
    {m n x y : Nat} (hx : 2 ^ m ∣ x) (hy : y < 2 ^ m) :
    (x + y) % (2 ^ n) = x % (2 ^ n) + y % (2 ^ n) := by
  rw [add_eq_or hx hy, or_mod_two_pow]
  by_cases h : m ≤ n
  · rw [add_eq_or _ (@Nat.mod_lt_of_lt _ (2 ^ n) _ hy)]
    apply (@Nat.dvd_mod_iff (2 ^ m) x (2 ^ n) _).mpr hx
    apply Nat.pow_dvd_pow _ h
  · rw [not_le] at h
    have h' := Nat.pow_dvd_pow 2 (Nat.le_of_lt h)
    simp [@Nat.mod_eq_zero_of_dvd (2 ^ n) x (Nat.dvd_trans h' hx)]

lemma Nat.concat_modadd_concat {m n x x' y y' : Nat}
    (hx' : x' < 2 ^ n) (hy' : y' < 2 ^ n) :
    ((x * 2 ^ n + x') + (y * 2 ^ n + y')) % 2 ^ (m + n)
      = (((x + y + (if x' + y' < 2 ^ n then 0 else 1)) % 2 ^ m) * 2 ^ n)
      + ((x' + y') % 2 ^ n) := by
  have rw :
      (x * 2 ^ n + x' + (y * 2 ^ n + y')) = (x + y) * 2 ^ n + x' + y' := by
    rw [Nat.add_add_add_comm, ← Nat.add_mul, Nat.add_assoc]
  rw [rw]; clear rw
  have pow_le : 2 ^ n ≤ 2 ^ (m + n) := by
    apply Nat.pow_le_pow_right <;> omega
  by_cases h : x' + y' < 2 ^ n
  · rw [if_pos h, Nat.add_zero, Nat.add_assoc]
    rw [Nat.add_mod_two_pow_distrib (Nat.dvd_mul_left _ _) h]
    apply congr_arg₂
    · rw [← Nat.mod_two_pow_mul_two_pow]
    · rw [Nat.mod_eq_of_lt h]
      rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h pow_le)]
  · rw [if_neg h]
    have rw :
        (x + y) * 2 ^ n + x' + y' =
        (x + y + 1) * 2 ^ n + ((x' + y') % 2 ^ n) := by
      rw [Nat.add_mul _ 1, Nat.add_assoc, Nat.add_assoc]
      apply congr_arg₂ _ rfl
      apply Eq.trans (Nat.mod_add_div' (x' + y') (2 ^ n)).symm
      rw [Nat.add_comm]
      apply congr_arg₂ _ (congr_arg₂ _ _ rfl) rfl
      rw [Nat.div_eq_iff (Nat.pow_pos (by omega)), Nat.one_mul]
      refine' ⟨le_of_not_gt h, Nat.le_pred_of_lt _⟩
      apply Nat.add_lt_add_of_lt_of_le hx' (le_of_lt hy')
    rw [rw]; clear rw h
    rw [Nat.add_mod_two_pow_distrib (Nat.dvd_mul_left _ _)]
    · apply congr_arg₂
      · rw [← Nat.mod_two_pow_mul_two_pow]
      · rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.pow_pos (by omega))) pow_le)]
    · apply Nat.mod_lt _ <| Nat.pow_pos (by omega)

lemma Nat.concat_modsub_concat {m n x x' y y' : Nat}
    (hx' : x' < 2 ^ n) (hy : y < 2 ^ m) (hy' : y' < 2 ^ n) :
    (2 ^ (m + n) + (x * 2 ^ n + x') - (y * 2 ^ n + y')) % 2 ^ (m + n) =
    (((2 ^ m + x - y - (if x' < y' then 1 else 0)) % 2 ^ m) * 2 ^ n)
    + ((2 ^ n + x' - y') % 2 ^ n) := by
  have h :
      2 ^ (m + n) + (x * 2 ^ n + x') - (y * 2 ^ n + y') =
        (2 ^ m + x - y) * 2 ^ n + x' - y' := by
    have h : y * 2 ^ n ≤ 2 ^ (m + n) + x * 2 ^ n := by
      apply le_trans _ (Nat.le_add_right _ _); rw [Nat.pow_add]
      apply mul_le_mul_right; apply Nat.le_of_lt hy
    rw [← Nat.add_assoc, ← Nat.sub_sub, Nat.sub_add_comm h]
    rw [Nat.mul_sub_right_distrib, Nat.add_mul, Nat.pow_add]
  rw [h]; clear h
  have h_le : 2 ^ n ≤ 2 ^ (m + n) := by
    apply Nat.pow_le_pow_right <;> omega
  by_cases h : x' < y'
  · rw [if_pos h]
    have h' :
        (2 ^ m + x - y) * 2 ^ n + x' - y' =
        (2 ^ m + x - y - 1) * 2 ^ n + (2 ^ n + x' - y') := by
      rw [← Nat.add_sub_assoc (by omega)]
      rw [Nat.mul_sub_right_distrib _ 1, Nat.one_mul]
      rw [← Nat.add_assoc, Nat.sub_add_cancel]
      apply Nat.le_mul_of_pos_left; omega
    rw [h']; clear h'
    have h_lt : (2 ^ n + x' - y') < 2 ^ n := by omega
    rw [Nat.add_mod_two_pow_distrib (Nat.dvd_mul_left _ _) h_lt]
    apply congr_arg₂
    · rw [← Nat.mod_two_pow_mul_two_pow]
    · rw [Nat.mod_eq_of_lt h_lt]
      rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h_lt h_le)]
  · rw [if_neg h]; rw [not_lt] at h
    rw [Nat.add_sub_assoc h, Nat.add_sub_assoc h]
    rw [Nat.sub_zero, Nat.add_mod_left]
    have h_lt : x' - y' < 2 ^ n :=
      Nat.lt_of_le_of_lt (Nat.sub_le _ _) hx'
    rw [Nat.add_mod_two_pow_distrib (Nat.dvd_mul_left _ _) h_lt]
    apply congr_arg₂
    · rw [← Nat.mod_two_pow_mul_two_pow]
    · rw [Nat.mod_eq_of_lt h_lt]
      rw [Nat.mod_eq_of_lt (Nat.lt_of_lt_of_le h_lt h_le)]

lemma UInt64.toNat_sub' (a b : UInt64) :
    (a - b).toNat = (2 ^ 64 + a.toNat - b.toNat) % 2 ^ 64 := by
  rw [UInt64.toNat_sub, Nat.sub_add_comm]
  apply le_of_lt <| UInt64.toNat_lt_size _

lemma Nat.add_mod_eq_add_sub {k m n : Nat} (m_lt : m < k)
    (n_lt : n < k) (k_le : k ≤ m + n) : (m + n) % k = m + n - k := by
  rcases Nat.exists_eq_add_of_le k_le with ⟨d, eq⟩
  rw [eq, Nat.add_mod_left]
  have d_lt : d < k := by
    rw [← @Nat.add_lt_add_iff_left k, ← eq]
    apply Nat.add_lt_add m_lt n_lt
  simp [Nat.mod_eq_of_lt d_lt]

lemma Nat.add_sub_mod_eq_sub {k m n : Nat}
    (hm : m < k) (h : n ≤ m) : (k + m - n) % k = m - n := by
  rw [Nat.add_sub_assoc h, Nat.add_mod_left, Nat.mod_eq_of_lt]
  apply lt_of_le_of_lt (Nat.sub_le _ _) hm

lemma Nat.add_sub_mod_eq_add_sub {k m n : Nat}
    (hn : n ≤ k) (h : m < n) : (k + m - n) % k = k + m - n := by
  rw [Nat.mod_eq_of_lt]
  apply Nat.sub_lt_right_of_lt_add (by omega)
  apply Nat.add_lt_add_left h

lemma B128.toNat_one : B128.toNat 1 = 1 := rfl
lemma B128.zero_eq : (0 : B128) = ⟨0, 0⟩ := rfl
lemma B128.sub_zero (x : B128) : x - 0 = x := by
  simp [B128.sub_eq, B128.zero_eq]

lemma B64.toNat_overflow {x y : B64} :
    x + y < x ↔ 2 ^ 64 ≤ x.toNat + y.toNat := by
  rw [UInt64.lt_iff_toNat_lt, UInt64.toNat_add]
  by_cases h : x.toNat + y.toNat < 2 ^ 64
  · rw [Nat.mod_eq_of_lt h]
    apply iff_of_false <;> omega
  · rw [not_lt] at h
    rw [
      Nat.add_mod_eq_add_sub
        (UInt64.toNat_lt_pow _)
        (UInt64.toNat_lt_pow _)
        h
    ]
    apply iff_of_true _ h
    rw [Nat.sub_lt_iff_lt_add h]
    apply Nat.add_lt_add_left <| UInt64.toNat_lt_size _


lemma B128.toNat_add (x y : B128) :
    (x + y).toNat = (x.toNat + y.toNat) % 2 ^ 128 := by
  rw [B128.add_eq]; simp only [B128.toNat]
  rw [
    @Nat.concat_modadd_concat 64 64 x.1.toNat x.2.toNat y.1.toNat y.2.toNat
      (UInt64.toNat_lt_size _)
      (UInt64.toNat_lt_size _)
  ]
  apply congr_arg₂ _ (congr_arg₂ _ _ rfl) (by rw [UInt64.toNat_add])
  by_cases h : x.2 + y.2 < x.2
  · rw [if_pos h, if_neg (not_lt_of_ge (B64.toNat_overflow.mp h))]; clear h
    simp only [UInt64.toNat_add, UInt64.toNat_one]
    rcases _root_.le_or_gt (2 ^ 64) (x.1.toNat + y.1.toNat) with h | h
    · rw [
        Nat.add_mod_eq_add_sub
          (UInt64.toNat_lt_pow x.1)
          (UInt64.toNat_lt_pow y.1)
          h,
        ← Nat.add_mod_right
      ]
      apply congr_arg₂ _ (by omega) rfl
    · rw [Nat.mod_eq_of_lt h]
  · rw [if_neg h, if_pos (lt_of_not_ge <| mt B64.toNat_overflow.mpr h)]
    simp only [UInt64.toNat_add, UInt64.toNat_zero, Nat.add_zero, Nat.mod_mod]

lemma B128.toNat_zero : (0 : B128).toNat = 0 := rfl

lemma B128.toNat_overflow {x y : B128} :
    x + y < x ↔ 2 ^ 128 ≤ x.toNat + y.toNat := by
  rw [B128.lt_iff_toNat_lt_toNat, B128.toNat_add]
  by_cases h : x.toNat + y.toNat < 2 ^ 128
  · rw [Nat.mod_eq_of_lt h]
    apply iff_of_false <;> omega
  · rw [not_lt] at h
    rw [
      Nat.add_mod_eq_add_sub
        (B128.toNat_lt_size _)
        (B128.toNat_lt_size _)
        h
    ]
    apply iff_of_true _ h
    rw [Nat.sub_lt_iff_lt_add h]
    apply Nat.add_lt_add_left <| B128.toNat_lt_size _

lemma B256.toNat_add (x y : B256) :
    (x + y).toNat = (x.toNat + y.toNat) % 2 ^ 256 := by
  rw [B256.add_eq]; simp only [B256.toNat]
  rw [
    @Nat.concat_modadd_concat 128 128 x.1.toNat x.2.toNat y.1.toNat y.2.toNat
      (B128.toNat_lt_size _)
      (B128.toNat_lt_size _)
  ]
  apply congr_arg₂ _ (congr_arg₂ _ _ rfl) (by rw [B128.toNat_add])
  by_cases h : x.2 + y.2 < x.2
  · rw [if_pos h, if_neg (not_lt_of_ge (B128.toNat_overflow.mp h))]; clear h
    simp only [B128.toNat_add, B128.toNat_one]
    rcases _root_.le_or_gt (2 ^ 128) (x.1.toNat + y.1.toNat) with h | h
    · rw [
        Nat.add_mod_eq_add_sub
          (B128.toNat_lt_size x.1)
          (B128.toNat_lt_size y.1)
          h,
        ← Nat.add_mod_right
      ]
      apply congr_arg₂ _ (by omega) rfl
    · rw [Nat.mod_eq_of_lt h]
  · rw [if_neg h, if_pos (lt_of_not_ge <| mt B128.toNat_overflow.mpr h)]
    rw [B128.toNat_add, B128.toNat_zero, Nat.add_zero, Nat.add_zero]
    rw [B128.toNat_add , Nat.mod_mod]

def B256.Nof (xs ys : B256) : Prop := xs.toNat + ys.toNat < 2 ^ 256

lemma B256.toNat_add_eq_of_nof (x y : B256) (h : B256.Nof x y) :
    (x + y).toNat = (x.toNat + y.toNat) := by
  rw [B256.toNat_add, Nat.mod_eq_of_lt h]

lemma B128.toNat_sub (a b : B128) :
    (a - b).toNat = (2 ^ 128 + a.toNat - b.toNat) % 2 ^ 128 := by
  rw [B128.sub_eq]; simp only [B128.toNat]
  rw [
    @Nat.concat_modsub_concat 64 64 a.1.toNat a.2.toNat b.1.toNat b.2.toNat
      (UInt64.toNat_lt_size _)
      (UInt64.toNat_lt_size _)
      (UInt64.toNat_lt_size _)
  ]
  apply congr_arg₂ _ _ (by rw [UInt64.toNat_sub'])
  apply congr_arg₂ _ _ rfl
  by_cases h : a.2 < b.2
  · rw [if_pos h, if_pos (UInt64.lt_iff_toNat_lt.mp h)]; clear h
    rw [UInt64.toNat_sub', UInt64.toNat_one, UInt64.toNat_sub']
    rcases _root_.le_or_gt b.1.toNat a.1.toNat with h | h
    · rw [Nat.add_sub_mod_eq_sub (UInt64.toNat_lt_pow _) h]
      rw [← Nat.add_sub_assoc h]
    · rw [Nat.add_sub_mod_eq_add_sub (Nat.le_of_lt (UInt64.toNat_lt_pow b.1)) h]
      have h' : 2 ^ 64 + UInt64.toNat a.1 - UInt64.toNat b.1 < 2 ^ 64 := by
        apply Nat.sub_lt_right_of_lt_add
        · apply Nat.le_of_lt
          apply lt_of_lt_of_le (UInt64.toNat_lt_size _) (Nat.le_add_right _ _)
        · apply Nat.add_lt_add_left h
      have h'' : 1 ≤ 2 ^ 64 + UInt64.toNat a.1 - UInt64.toNat b.1 := by
        apply Nat.succ_le_of_lt
        apply
          lt_of_lt_of_le
            (Nat.zero_lt_sub_of_lt (UInt64.toNat_lt_pow b.1))
            (by omega)
      rw [Nat.add_sub_mod_eq_sub h' h'']
      rw [← Nat.sub_add_eq, Nat.add_sub_mod_eq_add_sub]
      · apply Nat.succ_le_of_lt <| UInt64.toNat_lt_pow _
      · apply lt_trans h <| Nat.lt_succ_self _
  · rw [if_neg h, if_neg (mt UInt64.lt_iff_toNat_lt.mpr h)]
    rw [Nat.sub_zero, UInt64.sub_zero, UInt64.toNat_sub']

lemma B128.lt_iff_toNat_lt_toNat' {x y : B128} : x < y ↔ x.toNat < y.toNat := by
  apply Iff.intro B128.toNat_lt_toNat;
  intro h
  rcases B128.le_or_gt y x with h' | h'
  · rw [← not_le] at h; cases h <| B128.toNat_le_toNat h'
  · apply h'

lemma B256.toNat_sub (a b : B256) :
    (a - b).toNat = (2 ^ 256 + a.toNat - b.toNat) % 2 ^ 256 := by
  rw [B256.sub_eq]; simp only [B256.toNat]
  rw [
    @Nat.concat_modsub_concat 128 128 a.1.toNat a.2.toNat b.1.toNat b.2.toNat
      (B128.toNat_lt_size _)
      (B128.toNat_lt_size _)
      (B128.toNat_lt_size _)
  ]
  apply congr_arg₂ _ _ (by rw [B128.toNat_sub])
  apply congr_arg₂ _ _ rfl
  by_cases h : a.2 < b.2
  · rw [if_pos h, if_pos (B128.toNat_lt_toNat h)]; clear h
    rw [B128.toNat_sub, B128.toNat_one, B128.toNat_sub]
    rcases _root_.le_or_gt b.1.toNat a.1.toNat with h | h
    · rw [Nat.add_sub_mod_eq_sub (B128.toNat_lt_size _) h]
      rw [← Nat.add_sub_assoc h]
    · rw [Nat.add_sub_mod_eq_add_sub (Nat.le_of_lt (B128.toNat_lt_size b.1)) h]
      have h' : 2 ^ 128 + B128.toNat a.1 - B128.toNat b.1 < 2 ^ 128 := by
        apply Nat.sub_lt_right_of_lt_add
        · apply Nat.le_of_lt
          apply lt_of_lt_of_le (B128.toNat_lt_size _) (Nat.le_add_right _ _)
        · apply Nat.add_lt_add_left h
      have h'' : 1 ≤ 2 ^ 128 + a.1.toNat - b.1.toNat := by
        apply Nat.succ_le_of_lt
        apply
          lt_of_lt_of_le
            (Nat.zero_lt_sub_of_lt (B128.toNat_lt_size b.1))
            (by omega)
      rw [Nat.add_sub_mod_eq_sub h' h'']
      rw [← Nat.sub_add_eq, Nat.add_sub_mod_eq_add_sub]
      · apply Nat.succ_le_of_lt <| B128.toNat_lt_size _
      · apply lt_trans h <| Nat.lt_succ_self _
  · rw [if_neg h, if_neg, Nat.sub_zero, B128.sub_zero, B128.toNat_sub]--, if_neg ()
    rw [← B128.lt_iff_toNat_lt_toNat]; apply h

theorem B256.toNat_sub_eq_of_le (xs ys : B256) (h : ys ≤ xs) :
    (xs - ys).toNat = xs.toNat - ys.toNat := by
  rw [toNat_sub, Nat.add_sub_mod_eq_sub]-- rw [← not_lt, lt_iff_lt'] at h; simp [h]
  · apply B256.toNat_lt_size
  · apply B256.toNat_le_toNat h









#exit

lemma B256.toNat_add (x y : B256) :
    (x + y).toNat = (x.toNat + y.toNat) % 2 ^ 256 := by
