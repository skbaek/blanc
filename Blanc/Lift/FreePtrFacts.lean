import Blanc.Lift.FreePtr
import Blanc.Lift.SymTransfer
import Jaune.MulDiv

/-!
# The meaning of the free-pointer checker's facts, and their rules' soundness (F3a)

The free-pointer checker (`Blanc/Lift/FreePtr.lean`) reasons about symbols through a list of
`Fact`s.  This module gives each fact its meaning under a symbol valuation `ν : Nat → B256`
(`Fact.Holds`, `AllHold`) and proves every rule that produces facts sound over a bare
`List Fact`, never over the checker's state `FSt` (co-design amendment A1), so that the
write-site checker reuses them on its own fact list:

* the interval reading `bndOf`/`bnd2`/`lo`/`hi`, `constOf`, `entails`, and the derived tests
  `good`, `apartW`, `not64`;
* `opFacts` (the facts about an instruction's fresh result) against `Ninst.Run`;
* `learn1`/`refineFacts` (what a `JUMPI` arm learns) and the `closeLive` filter;
* `compat` (an incoming state meets an annotation: the annotation's facts hold under the
  renamed valuation) and `resume` (the caller's facts and the callee's renamed summary hold
  together under one glued valuation).

The stack side (symbols carried by words through `ninstTransfer`) is in
`Blanc/Lift/SymTransfer.lean`.
-/

namespace Blanc.Lift.FreePtr

open Jaune AbstractStackSafety Blanc.Lift.SymTransfer

/-! ## A word shifted right is no larger -/

private theorem UInt64.shr_toNat_le (a : UInt64) (k : Nat) :
    (a >>> k.toUInt64).toNat ≤ a.toNat := by
  rw [UInt64.toNat_shiftRight]
  exact Nat.shiftRight_le _ _

private theorem UInt64.shr_toNat_lt {a : UInt64} {k : Nat} (hk0 : 0 < k) (hk : k < 64)
    (ha : 0 < a.toNat) : (a >>> k.toUInt64).toNat < a.toNat := by
  rw [UInt64.toNat_shiftRight, Nat.toUInt64_eq, UInt64.toNat_ofNat', Nat.mod_eq_of_lt
    (by omega : k < 2 ^ 64), Nat.mod_eq_of_lt hk, Nat.shiftRight_eq_div_pow]
  exact Nat.div_lt_self ha (Nat.one_lt_two_pow (by omega))

private theorem B128.toNat_eq_add (x : B128) : x.toNat = x.1.toNat * 2 ^ 64 + x.2.toNat := by
  rw [B128.toNat, ← Nat.shiftLeft_add_eq_or_of_lt (UInt64.toNat_lt _), Nat.shiftLeft_eq]

private theorem B256.toNat_eq_add (x : B256) : x.toNat = x.1.toNat * 2 ^ 128 + x.2.toNat := by
  rw [B256.toNat, ← Nat.shiftLeft_add_eq_or_of_lt B128.toNat_lt, Nat.shiftLeft_eq]

private theorem B128.zero_shiftLeft (k : Nat) : (0 : B128) <<< k = 0 := by
  show B128.shiftLeft (0, 0) k = (0, 0)
  by_cases h0 : k = 0
  · simp only [B128.shiftLeft, h0, ↓reduceIte]
    rfl
  by_cases h64 : k < 64
  · simp only [B128.shiftLeft, h0, h64, ↓reduceIte, UInt64.zero_shiftLeft,
      UInt64.zero_shiftRight, UInt64.zero_or]
    rfl
  by_cases h128 : k < 128
  · simp only [B128.shiftLeft, h0, h64, h128, ↓reduceIte, UInt64.zero_shiftLeft]
    rfl
  · simp only [B128.shiftLeft, h0, h64, h128, ↓reduceIte]
    rfl

private theorem B128.zero_or (z : B128) : (0 : B128) ||| z = z := by
  obtain ⟨p, q⟩ := z
  show B128.or (0, 0) (p, q) = (p, q)
  simp only [B128.or, UInt64.zero_or]
  rfl

private theorem B128.shr_toNat (x : B128) (k : Nat) :
    (x >>> k).toNat ≤ x.toNat ∧ (0 < k → 0 < x.toNat → (x >>> k).toNat < x.toNat) := by
  obtain ⟨a, b⟩ := x
  show (B128.shiftRight (a, b) k).toNat ≤ B128.toNat (a, b) ∧
    (0 < k → 0 < B128.toNat (a, b) → (B128.shiftRight (a, b) k).toNat < B128.toNat (a, b))
  have hx := B128.toNat_eq_add (a, b)
  have hb := UInt64.toNat_lt b
  simp only at hx
  by_cases h0 : k = 0
  · subst h0
    exact ⟨Nat.le_refl _, fun h => absurd h (Nat.lt_irrefl 0)⟩
  by_cases h64 : k < 64
  · have e : B128.shiftRight (a, b) k = (a >>> k.toUInt64, (a <<< (64 - k).toUInt64) ||| (b >>> k.toUInt64)) := by
      simp only [B128.shiftRight, h0, h64, ↓reduceIte]
      rfl
    have hr := B128.toNat_eq_add (a >>> k.toUInt64, (a <<< (64 - k).toUInt64) ||| (b >>> k.toUInt64))
    simp only at hr
    rw [e, hr, hx]
    have hlo := UInt64.toNat_lt ((a <<< (64 - k).toUInt64) ||| (b >>> k.toUInt64))
    have hhi := UInt64.shr_toNat_le a k
    by_cases ha : a.toNat = 0
    · have ha0 : a = 0 := UInt64.toNat_inj.mp (by rw [ha]; rfl)
      subst ha0
      simp only [UInt64.zero_shiftLeft, UInt64.zero_or, UInt64.zero_shiftRight,
        UInt64.toNat_zero, Nat.zero_mul, Nat.zero_add]
      exact ⟨UInt64.shr_toNat_le b k, fun hk hx' => UInt64.shr_toNat_lt hk h64 hx'⟩
    · have hlt := UInt64.shr_toNat_lt (Nat.pos_of_ne_zero h0) h64 (Nat.pos_of_ne_zero ha)
      constructor
      · omega
      · intro _ _; omega
  by_cases h128 : k < 128
  · have e : B128.shiftRight (a, b) k = (0, a >>> (k - 64).toUInt64) := by
      simp only [B128.shiftRight, h0, h64, h128, ↓reduceIte]
      rfl
    have hr := B128.toNat_eq_add ((0 : UInt64), a >>> (k - 64).toUInt64)
    simp only [UInt64.toNat_zero, Nat.zero_mul, Nat.zero_add] at hr
    rw [e, hr, hx]
    have hhi := UInt64.shr_toNat_le a (k - 64)
    constructor
    · omega
    · intro _ _; omega
  · have e : B128.shiftRight (a, b) k = (0, 0) := by
      simp only [B128.shiftRight, h0, h64, h128, ↓reduceIte]
      rfl
    rw [e, hx]
    exact ⟨Nat.zero_le _, fun _ h => h⟩

/-- `SHR` never grows its shifted operand. -/
theorem B256.shr_toNat_le (y : B256) (k : Nat) : (y >>> k).toNat ≤ y.toNat := by
  obtain ⟨xs, ys⟩ := y
  show (B256.shiftRight (xs, ys) k).toNat ≤ B256.toNat (xs, ys)
  have hx := B256.toNat_eq_add (xs, ys)
  have hys := B128.toNat_lt (x := ys)
  simp only at hx
  by_cases h0 : k = 0
  · subst h0
    exact Nat.le_refl _
  by_cases h128 : k < 128
  · have e : B256.shiftRight (xs, ys) k = (xs >>> k, (xs <<< (128 - k)) ||| (ys >>> k)) := by
      simp only [B256.shiftRight, h0, h128, ↓reduceIte]
      rfl
    have hr := B256.toNat_eq_add (xs >>> k, (xs <<< (128 - k)) ||| (ys >>> k))
    simp only at hr
    rw [e, hr, hx]
    have hlo := B128.toNat_lt (x := (xs <<< (128 - k)) ||| (ys >>> k))
    have hhi := B128.shr_toNat xs k
    by_cases hxs : xs.toNat = 0
    · have hx0 : xs = 0 := (B128.toNat_inj xs 0).mp (by rw [hxs]; rfl)
      subst hx0
      rw [B128.zero_shiftLeft, B128.zero_or]
      have hy := (B128.shr_toNat ys k).1
      omega
    · have hlt := hhi.2 (Nat.pos_of_ne_zero h0) (Nat.pos_of_ne_zero hxs)
      omega
  by_cases h256 : k < 256
  · have e : B256.shiftRight (xs, ys) k = (0, xs >>> (k - 128)) := by
      simp only [B256.shiftRight, h0, h128, h256, ↓reduceIte]
      rfl
    have hr := B256.toNat_eq_add ((0 : B128), xs >>> (k - 128))
    simp only [show (0 : B128).toNat = 0 from rfl, Nat.zero_mul, Nat.zero_add] at hr
    rw [e, hr, hx]
    have hhi := (B128.shr_toNat xs (k - 128)).1
    omega
  · have e : B256.shiftRight (xs, ys) k = (0, 0) := by
      simp only [B256.shiftRight, h0, h128, h256, ↓reduceIte]
      rfl
    rw [e, hx]
    exact Nat.zero_le _

/-! ## Meaning -/

/-- The meaning of one fact under the symbol valuation `ν`. -/
def Fact.Holds (ν : Nat → B256) : Fact → Prop
  | .bnd s l h => l ≤ (ν s).toNat ∧ (ν s).toNat ≤ h
  | .le s t => (ν s).toNat ≤ (ν t).toNat
  | .lt s t => (ν s).toNat < (ν t).toNat
  | .ltr r x y => ν r = B256.ltCheck (ν x) (ν y)
  | .isz r s => ν r = B256.eqCheck (ν s) 0
  | .orr r x y => ν r = ν x ||| ν y

/-- Every fact of the list holds under `ν`. -/
def AllHold (ν : Nat → B256) (fs : List Fact) : Prop := ∀ f ∈ fs, f.Holds ν

section Meaning

variable {ν ν' : Nat → B256} {fs gs : List Fact}

theorem AllHold.sub (hsub : ∀ g ∈ gs, g ∈ fs) (h : AllHold ν fs) : AllHold ν gs :=
  fun g hg => h g (hsub g hg)

theorem AllHold.append (h1 : AllHold ν fs) (h2 : AllHold ν gs) : AllHold ν (fs ++ gs) := by
  intro f hf
  rcases List.mem_append.mp hf with hf | hf
  · exact h1 f hf
  · exact h2 f hf

theorem AllHold.filter (p : Fact → Bool) (h : AllHold ν fs) : AllHold ν (fs.filter p) :=
  h.sub fun _ hg => List.mem_of_mem_filter hg

theorem closeLive_sub {kv : List Nat} {fp : Option Nat} {f : Fact}
    (h : f ∈ closeLive kv fp fs) : f ∈ fs := by
  unfold closeLive at h
  exact List.mem_of_mem_filter h

theorem AllHold.closeLive (kv : List Nat) (fp : Option Nat) (h : AllHold ν fs) :
    AllHold ν (closeLive kv fp fs) :=
  h.sub fun _ hg => closeLive_sub hg

theorem Fact.holds_congr {f : Fact} (h : ∀ s ∈ f.syms, ν s = ν' s) (hf : f.Holds ν) :
    f.Holds ν' := by
  cases f <;> simp only [Fact.syms, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq] at h <;> simp only [Fact.Holds] at hf ⊢
  all_goals first
    | (obtain ⟨h1, h2, h3⟩ := h; rw [← h1, ← h2, ← h3]; exact hf)
    | (obtain ⟨h1, h2⟩ := h; rw [← h1, ← h2]; exact hf)
    | (rw [← h]; exact hf)

theorem Fact.holds_rename {m : Nat → Nat} {f : Fact} :
    (f.rename m).Holds ν ↔ f.Holds (ν ∘ m) := by
  cases f <;> exact Iff.rfl

/-- Facts not naming `r` survive a one-point update at `r`. -/
theorem AllHold.update {r : Nat} {w : B256} (hr : ∀ f ∈ fs, r ∉ f.syms) (h : AllHold ν fs) :
    AllHold (Function.update ν r w) fs := fun f hm =>
  Fact.holds_congr (fun s hs => (Function.update_of_ne
    (by rintro rfl; exact hr f hm hs) _ _).symm) (h f hm)

end Meaning

/-! ## Fresh symbols -/

section Fresh

variable {kv : List Nat} {fs : List Fact} {fp : Option Nat} {s : Nat}

theorem lt_freshSym_kv (h : s ∈ kv) : s < freshSym kv fs fp :=
  lt_fresh_kv (List.mem_append_left _ h)

theorem lt_freshSym_fp (h : fp = some s) : s < freshSym kv fs fp :=
  lt_fresh_kv (List.mem_append_right _ (by rw [h]; exact List.mem_singleton_self s))

theorem lt_freshSym_fact {f : Fact} (hf : f ∈ fs) (hs : s ∈ f.syms) : s < freshSym kv fs fp :=
  Nat.lt_succ_of_le (le_foldr_max (List.mem_append_right _ (List.mem_flatMap.mpr ⟨f, hf, hs⟩)))

/-- The fresh symbol names no fact of the list. -/
theorem freshSym_not_mem_syms : ∀ f ∈ fs, freshSym kv fs fp ∉ f.syms :=
  fun _ hf hs => Nat.lt_irrefl _ (lt_freshSym_fact hf hs)

end Fresh

/-! ## The interval reading is sound -/

section Entails

variable {ν : Nat → B256} {fs : List Fact}

/-- A projected `bnd` bound holds under the valuation. -/
private theorem bndProj_sound (hf : AllHold ν fs) {f : Fact} (hmem : f ∈ fs)
    {s' lo hi : Nat} (h : bndProj f = some (s', lo, hi)) :
    lo ≤ (ν s').toNat ∧ (ν s').toNat ≤ hi := by
  have hH := hf f hmem
  cases f with
  | bnd s'' lo' hi' =>
    simp only [Fact.Holds] at hH
    simp only [bndProj] at h
    obtain ⟨rfl, rfl, rfl⟩ := Option.some.inj h
    exact hH
  | le _ _ =>
    simp only [bndProj] at h
    cases h
  | lt _ _ =>
    simp only [bndProj] at h
    cases h
  | ltr _ _ _ =>
    simp only [bndProj] at h
    cases h
  | isz _ _ =>
    simp only [bndProj] at h
    cases h
  | orr _ _ _ =>
    simp only [bndProj] at h
    cases h

/-- A projected order fact holds under the valuation. -/
private theorem ordProj_sound (hf : AllHold ν fs) {f : Fact} (hmem : f ∈ fs)
    {strict : Bool} {a b : Nat} (h : ordProj f = some (strict, a, b)) :
    (strict = true → (ν a).toNat < (ν b).toNat) ∧
      (strict = false → (ν a).toNat ≤ (ν b).toNat) := by
  have hH := hf f hmem
  cases f with
  | lt a' b' =>
    simp only [Fact.Holds] at hH
    simp only [ordProj] at h
    obtain ⟨rfl, rfl, rfl⟩ := Option.some.inj h
    exact ⟨fun _ => hH, fun hcon => absurd hcon (by decide)⟩
  | le a' b' =>
    simp only [Fact.Holds] at hH
    simp only [ordProj] at h
    obtain ⟨rfl, rfl, rfl⟩ := Option.some.inj h
    exact ⟨fun hcon => absurd hcon (by decide), fun _ => hH⟩
  | bnd _ _ _ =>
    simp only [ordProj] at h
    cases h
  | ltr _ _ _ =>
    simp only [ordProj] at h
    cases h
  | isz _ _ =>
    simp only [ordProj] at h
    cases h
  | orr _ _ _ =>
    simp only [ordProj] at h
    cases h

/-- Every symbol value fits in the checker's largest word. -/
private theorem val_le_maxW (ν : Nat → B256) (t : Nat) : (ν t).toNat ≤ maxW := by
  have := B256.toNat_lt (ν t); unfold maxW; omega

theorem bndOf_sound (hf : AllHold ν fs) (s : Nat) :
    (bndOf fs s).1 ≤ (ν s).toNat ∧ (ν s).toNat ≤ (bndOf fs s).2 :=
  BndInterval.bndOfG_sound (val_le_maxW ν)
    (fun _f hmem _ _ _ h => bndProj_sound hf hmem h) s

theorem bnd2_sound (hf : AllHold ν fs) (s : Nat) :
    (bnd2 fs s).1 ≤ (ν s).toNat ∧ (ν s).toNat ≤ (bnd2 fs s).2 :=
  BndInterval.bnd2G_sound (val_le_maxW ν)
    (fun _f hmem _ _ _ h => bndProj_sound hf hmem h)
    (fun _f hmem _ _ _ h => ordProj_sound hf hmem h) s

theorem lo_le (hf : AllHold ν fs) (s : Nat) : lo fs s ≤ (ν s).toNat := (bnd2_sound hf s).1

theorem le_hi (hf : AllHold ν fs) (s : Nat) : (ν s).toNat ≤ hi fs s := (bnd2_sound hf s).2

theorem entails_sound (hf : AllHold ν fs) {g : Fact} (he : entails fs g = true) : g.Holds ν := by
  cases g with
  | bnd s l h =>
    simp only [entails, Bool.and_eq_true, decide_eq_true_eq] at he
    have := bnd2_sound hf s
    exact ⟨by unfold lo at he; omega, by unfold hi at he; omega⟩
  | lt s t =>
    simp only [entails, Bool.or_eq_true, List.contains_iff_mem, decide_eq_true_eq] at he
    rcases he with he | he
    · exact hf _ he
    · have := le_hi hf s; have := lo_le hf t
      show (ν s).toNat < (ν t).toNat
      omega
  | le s t =>
    simp only [entails, Bool.or_eq_true, List.contains_iff_mem, decide_eq_true_eq] at he
    rcases he with (he | he) | he
    · exact hf _ he
    · have := hf _ he; simp only [Fact.Holds] at this ⊢; omega
    · have := le_hi hf s; have := lo_le hf t
      show (ν s).toNat ≤ (ν t).toNat
      omega
  | _ =>
    simp only [entails, List.contains_iff_mem] at he
    exact hf _ he

theorem constOf_sound (hf : AllHold ν fs) {s c : Nat} (h : constOf fs s = some c) :
    (ν s).toNat = c := by
  unfold constOf at h
  split at h
  · cases h
    have := lo_le hf s; have := le_hi hf s
    omega
  · cases h

theorem good_sound (hf : AllHold ν fs) {s : Nat} (h : good fs s = true) :
    fpLo ≤ (ν s).toNat ∧ (ν s).toNat ≤ fpCap := by
  simp only [good, Bool.and_eq_true, decide_eq_true_eq] at h
  have := lo_le hf s; have := le_hi hf s
  exact ⟨by omega, by omega⟩

theorem apartW_sound (hf : AllHold ν fs) {a lenHi len : Nat} (h : apartW fs a lenHi = true)
    (hl : len ≤ lenHi) : (ν a).toNat + len ≤ 0x40 ∨ 0x60 ≤ (ν a).toNat := by
  simp only [apartW, Bool.or_eq_true, decide_eq_true_eq] at h
  have := lo_le hf a; have := le_hi hf a
  omega

theorem not64_sound (hf : AllHold ν fs) {a : Nat} (h : not64 fs a = true) :
    (ν a).toNat ≠ 64 := by
  simp only [not64, Bool.or_eq_true, decide_eq_true_eq] at h
  have := lo_le hf a; have := le_hi hf a
  omega

end Entails

/-! ## The fact rules of `opFacts` are sound -/

section OpFacts

private theorem ite_one_zero_toNat_le (c : Prop) [Decidable c] :
    (if c then (1 : B256) else 0).toNat ≤ 1 := by
  split
  · exact Nat.le_of_eq rfl
  · exact Nat.zero_le _

private theorem B256.div_toNat_le (x y : B256) : (x / y).toNat ≤ x.toNat := by
  by_cases hy : y = 0
  · subst hy
    show (B256.divMod x 0).fst.toNat ≤ _
    simp only [B256.divMod, ↓reduceIte]
    exact Nat.zero_le _
  · rw [B256.toNat_div hy]
    exact Nat.div_le_self _ _

private theorem B256.toNat_eq_zero {x : B256} (h : x.toNat = 0) : x = 0 :=
  B256.toNat_inj _ _ (by rw [h]; rfl)

private theorem run_eq_top_any {sevm : Sevm} {d d' : Devm} (run : Ninst.Run sevm d (.reg .eq) d') :
    ∃ a b St, d'.stack = B256.eqCheck a b :: St := by
  rcases of_run_reg run with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  obtain ⟨x, y, hd⟩ := Devm.diffBurn_of_applyBinary run
  obtain ⟨s1, _, hpush⟩ := hd.stack
  simp only [Stack.Push, Split] at hpush
  exact ⟨x, y, s1, by simpa only [List.cons_append, List.nil_append] using hpush⟩

/-- **The facts `opFacts` attaches to the fresh result `r` hold once `r` names the concrete
result** `w` (the top word after the step): the input symbols `kv` name the words `S` on top
of the stack, and `r` is not among them.  An `MSIZE` needs the memory below `memCap`. -/
theorem opFacts_sound {ν : Nat → B256} {fs : List Fact} {kv : List Nat} {S rest : List B256}
    {n : Ninst} {r : Nat} {w : B256} {sevm : Sevm} {d d' : Devm}
    (hf : AllHold ν fs) (hr : r ∉ kv) (hS : List.Forall₂ (fun s w => ν s = w) kv S)
    (hstack : d.stack = S ++ rest) (run : Ninst.Run sevm d n d')
    (htop : d'.stack.head? = some w) (hms : n = .reg .msize → d.memory.size ≤ memCap) :
    AllHold (Function.update ν r w) (opFacts fs n kv r) := by
  have upd : ∀ s ∈ kv, Function.update ν r w s = ν s := fun s hs =>
    Function.update_of_ne (by rintro rfl; exact hr hs) _ _
  have hwr : Function.update ν r w r = w := Function.update_self _ _ _
  have two : ∀ {x y : Nat} {kt : List Nat}, kv = x :: y :: kt →
      ∃ St, d.stack = ν x :: ν y :: St := by
    intro x y kt hk
    subst hk
    cases hS with
    | cons h0 h1 =>
      cases h1 with
      | cons h1 _ => exact ⟨_, by rw [hstack, ← h0, ← h1]; rfl⟩
  have one : ∀ {x : Nat} {kt : List Nat}, kv = x :: kt → ∃ St, d.stack = ν x :: St := by
    intro x kt hk
    subst hk
    cases hS with
    | cons h0 _ => exact ⟨_, by rw [hstack, ← h0]; rfl⟩
  have headOf : ∀ {v : B256} {St : List B256}, d'.stack = v :: St → w = v := by
    intro v St h
    rw [h] at htop
    simp only [List.head?_cons, Option.some.injEq] at htop
    exact htop.symm
  have m0 : ∀ {x : Nat} {kt : List Nat}, x ∈ x :: kt := List.mem_cons_self
  have m1 : ∀ {x y : Nat} {kt : List Nat}, y ∈ x :: y :: kt :=
    List.mem_cons_of_mem _ List.mem_cons_self
  intro f hm
  cases n with
  | push _ _ => simp only [opFacts, List.not_mem_nil] at hm
  | exec _ => simp only [opFacts, List.not_mem_nil] at hm
  | dupn _ => simp only [opFacts, List.not_mem_nil] at hm
  | swapn _ => simp only [opFacts, List.not_mem_nil] at hm
  | exchange _ => simp only [opFacts, List.not_mem_nil] at hm
  | reg rr =>
  cases rr
  all_goals try (simp only [opFacts, List.not_mem_nil] at hm; done)
  case msize =>
    simp only [opFacts, List.mem_singleton] at hm
    subst hm
    have hv := headOf (run_msize_top run)
    have hsz := hms rfl
    show _ ≤ (Function.update ν r w r).toNat ∧ (Function.update ν r w r).toNat ≤ _
    rw [hwr, hv, B256.toNat_toB256_of_lt (by unfold memCap at hsz; omega)]
    exact ⟨Nat.zero_le _, hsz⟩
  case eq =>
    simp only [opFacts, List.mem_singleton] at hm
    subst hm
    obtain ⟨a, b, St, hst⟩ := run_eq_top_any run
    have hv := headOf hst
    show _ ≤ (Function.update ν r w r).toNat ∧ (Function.update ν r w r).toNat ≤ _
    rw [hwr, hv]
    exact ⟨Nat.zero_le _, ite_one_zero_toNat_le _⟩
  case add =>
    rcases kv with _ | ⟨x, _ | ⟨y, kt⟩⟩
    · simp only [opFacts, List.not_mem_nil] at hm
    · simp only [opFacts, List.not_mem_nil] at hm
    obtain ⟨St, hst⟩ := two rfl
    have hv := headOf (run_add_top run hst)
    have := lo_le hf x; have := le_hi hf x; have := lo_le hf y; have := le_hi hf y
    simp only [opFacts] at hm
    split at hm
    · rename_i hle
      have hsum := toNat_add_of_le (le_hi hf x) (le_hi hf y) hle
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl
      · show _ ≤ (Function.update ν r w r).toNat ∧ (Function.update ν r w r).toNat ≤ _
        rw [hwr, hv, hsum]; omega
      · show (Function.update ν r w x).toNat ≤ (Function.update ν r w r).toNat
        rw [upd x m0, hwr, hv, hsum]; omega
      · show (Function.update ν r w y).toNat ≤ (Function.update ν r w r).toNat
        rw [upd y m1, hwr, hv, hsum]; omega
    · simp only [List.not_mem_nil] at hm
  case sub =>
    rcases kv with _ | ⟨x, _ | ⟨y, kt⟩⟩
    · simp only [opFacts, List.not_mem_nil] at hm
    · simp only [opFacts, List.not_mem_nil] at hm
    obtain ⟨St, hst⟩ := two rfl
    have hv := headOf (run_sub_top run hst)
    have := lo_le hf x; have := le_hi hf x; have := lo_le hf y; have := le_hi hf y
    simp only [opFacts] at hm
    split at hm
    · rename_i hle
      have hd := B256.toNat_sub_eq_of_le (ν x) (ν y)
        (B256.le_iff_toNat_le_toNat.mpr (by omega))
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl
      · show _ ≤ (Function.update ν r w r).toNat ∧ (Function.update ν r w r).toNat ≤ _
        rw [hwr, hv, hd]; omega
      · show (Function.update ν r w r).toNat ≤ (Function.update ν r w x).toNat
        rw [upd x m0, hwr, hv, hd]; omega
    · simp only [List.not_mem_nil] at hm
  case mul =>
    rcases kv with _ | ⟨x, _ | ⟨y, kt⟩⟩
    · simp only [opFacts, List.not_mem_nil] at hm
    · simp only [opFacts, List.not_mem_nil] at hm
    obtain ⟨St, hst⟩ := two rfl
    have hv := headOf (run_mul_top run hst)
    have := lo_le hf x; have := le_hi hf x; have := lo_le hf y; have := le_hi hf y
    simp only [opFacts] at hm
    split at hm
    · rename_i hle
      have hp1 := Nat.mul_le_mul (le_hi hf x) (le_hi hf y)
      have hp0 := Nat.mul_le_mul (lo_le hf x) (lo_le hf y)
      have hd : (ν x * ν y).toNat = (ν x).toNat * (ν y).toNat := by
        rw [B256.toNat_mul, Nat.lo_eq_of_lt]
        unfold maxW at hle
        omega
      simp only [List.mem_singleton] at hm
      subst hm
      show _ ≤ (Function.update ν r w r).toNat ∧ (Function.update ν r w r).toNat ≤ _
      rw [hwr, hv, hd]
      exact ⟨hp0, hp1⟩
    · simp only [List.not_mem_nil] at hm
  case div =>
    rcases kv with _ | ⟨x, _ | ⟨y, kt⟩⟩
    · simp only [opFacts, List.not_mem_nil] at hm
    · simp only [opFacts, List.not_mem_nil] at hm
    obtain ⟨St, hst⟩ := two rfl
    have hv := headOf (run_div_top run hst)
    simp only [opFacts] at hm
    split at hm
    · rename_i hle
      have hy1 : 1 ≤ (ν y).toNat := Nat.le_trans hle (lo_le hf y)
      have hy0 : ν y ≠ 0 := fun h => by rw [h] at hy1; exact absurd hy1 (by decide)
      simp only [List.mem_singleton] at hm
      subst hm
      show _ ≤ (Function.update ν r w r).toNat ∧ (Function.update ν r w r).toNat ≤ _
      rw [hwr, hv, B256.toNat_div hy0]
      exact ⟨Nat.div_le_div (lo_le hf x) (le_hi hf y) (by omega),
        Nat.div_le_div (le_hi hf x) (lo_le hf y) (by omega)⟩
    · simp only [List.mem_singleton] at hm
      subst hm
      show _ ≤ (Function.update ν r w r).toNat ∧ (Function.update ν r w r).toNat ≤ _
      rw [hwr, hv]
      exact ⟨Nat.zero_le _, Nat.le_trans (B256.div_toNat_le _ _) (le_hi hf x)⟩
  case and =>
    rcases kv with _ | ⟨x, _ | ⟨y, kt⟩⟩
    · simp only [opFacts, List.not_mem_nil] at hm
    · simp only [opFacts, List.not_mem_nil] at hm
    obtain ⟨St, hst⟩ := two rfl
    have hv := headOf (run_and_top run hst)
    simp only [opFacts, List.mem_singleton] at hm
    subst hm
    show _ ≤ (Function.update ν r w r).toNat ∧ (Function.update ν r w r).toNat ≤ _
    rw [hwr, hv, B256.toNat_and]
    exact ⟨Nat.zero_le _, Nat.le_min.mpr ⟨Nat.le_trans Nat.and_le_left (le_hi hf x),
      Nat.le_trans Nat.and_le_right (le_hi hf y)⟩⟩
  case or =>
    rcases kv with _ | ⟨x, _ | ⟨y, kt⟩⟩
    · simp only [opFacts, List.not_mem_nil] at hm
    · simp only [opFacts, List.not_mem_nil] at hm
    obtain ⟨St, hst⟩ := two rfl
    have hv := headOf (run_or_top run hst)
    simp only [opFacts, List.mem_singleton] at hm
    subst hm
    show (Function.update ν r w r) = Function.update ν r w x ||| Function.update ν r w y
    rw [upd x m0, upd y m1, hwr, hv]
  case shr =>
    rcases kv with _ | ⟨x, _ | ⟨y, kt⟩⟩
    · simp only [opFacts, List.not_mem_nil] at hm
    · simp only [opFacts, List.not_mem_nil] at hm
    obtain ⟨St, hst⟩ := two rfl
    have hv := headOf (run_shr_top run hst)
    simp only [opFacts, List.mem_singleton] at hm
    subst hm
    show _ ≤ (Function.update ν r w r).toNat ∧ (Function.update ν r w r).toNat ≤ _
    rw [hwr, hv]
    exact ⟨Nat.zero_le _, Nat.le_trans (B256.shr_toNat_le _ _) (le_hi hf y)⟩
  case lt =>
    rcases kv with _ | ⟨x, _ | ⟨y, kt⟩⟩
    · simp only [opFacts, List.not_mem_nil] at hm
    · simp only [opFacts, List.not_mem_nil] at hm
    obtain ⟨St, hst⟩ := two rfl
    have hv := headOf (run_lt_top run hst)
    simp only [opFacts, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · show (Function.update ν r w r) = B256.ltCheck (Function.update ν r w x) (Function.update ν r w y)
      rw [upd x m0, upd y m1, hwr, hv]
    · show _ ≤ (Function.update ν r w r).toNat ∧ (Function.update ν r w r).toNat ≤ _
      rw [hwr, hv]
      exact ⟨Nat.zero_le _, ite_one_zero_toNat_le _⟩
  case gt =>
    rcases kv with _ | ⟨x, _ | ⟨y, kt⟩⟩
    · simp only [opFacts, List.not_mem_nil] at hm
    · simp only [opFacts, List.not_mem_nil] at hm
    obtain ⟨St, hst⟩ := two rfl
    have hv := headOf (run_gt_top run hst)
    simp only [opFacts, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · show (Function.update ν r w r) = B256.ltCheck (Function.update ν r w y) (Function.update ν r w x)
      rw [upd x m0, upd y m1, hwr, hv]
      rfl
    · show _ ≤ (Function.update ν r w r).toNat ∧ (Function.update ν r w r).toNat ≤ _
      rw [hwr, hv]
      exact ⟨Nat.zero_le _, ite_one_zero_toNat_le _⟩
  case iszero =>
    rcases kv with _ | ⟨x, kt⟩
    · simp only [opFacts, List.not_mem_nil] at hm
    obtain ⟨St, hst⟩ := one rfl
    have hv := headOf (run_iszero_top run hst)
    simp only [opFacts, List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl
    · show (Function.update ν r w r) = B256.eqCheck (Function.update ν r w x) 0
      rw [upd x m0, hwr, hv]
    · show _ ≤ (Function.update ν r w r).toNat ∧ (Function.update ν r w r).toNat ≤ _
      rw [hwr, hv]
      exact ⟨Nat.zero_le _, ite_one_zero_toNat_le _⟩

end OpFacts

/-! ## What a branch arm learns is sound -/

section Refine

variable {ν : Nat → B256} {fs : List Fact}

private theorem toNat_pos_of_ne {x : B256} (h : x ≠ 0) : 1 ≤ x.toNat :=
  Nat.pos_of_ne_zero fun h0 => h (B256.toNat_eq_zero h0)

private theorem toNat_le_maxW (x : B256) : x.toNat ≤ maxW := by
  have := B256.toNat_lt x; unfold maxW; omega

/-- **`learn1` is sound**: given the symbols `z` known zero and `nz` known nonzero, every learned
fact holds. -/
theorem learn1_sound (hf : AllHold ν fs) {z nz : List Nat} (hz : ∀ s ∈ z, ν s = 0)
    (hnz : ∀ s ∈ nz, ν s ≠ 0) : AllHold ν (learn1 fs z nz) := by
  intro g hg
  obtain ⟨f, hfm, hg⟩ := List.mem_flatMap.mp hg
  have hfh := hf f hfm
  cases f with
  | isz r s =>
    simp only [Fact.Holds] at hfh
    simp only at hg
    split at hg
    · rename_i hr
      simp only [List.mem_singleton] at hg
      subst hg
      have h0 := hz r (List.contains_iff_mem.mp hr)
      have hs : ν s ≠ 0 := by
        intro hs
        rw [hs] at hfh
        simp only [B256.eqCheck, ↓reduceIte] at hfh
        exact B256.one_ne_zero' (hfh.symm.trans h0)
      exact ⟨toNat_pos_of_ne hs, toNat_le_maxW _⟩
    · split at hg
      · rename_i _ hr
        simp only [List.mem_singleton] at hg
        subst hg
        have h1 := hnz r (List.contains_iff_mem.mp hr)
        have hs : ν s = 0 := by
          by_contra hs
          rw [hfh] at h1
          simp only [B256.eqCheck, hs, ↓reduceIte] at h1
          exact h1 rfl
        show 0 ≤ (ν s).toNat ∧ (ν s).toNat ≤ 0
        rw [hs]
        exact ⟨Nat.le_refl _, Nat.le_refl _⟩
      · simp only [List.not_mem_nil] at hg
  | ltr r x y =>
    simp only [Fact.Holds] at hfh
    simp only at hg
    split at hg
    · rename_i hr
      simp only [List.mem_singleton] at hg
      subst hg
      have h0 := hz r (List.contains_iff_mem.mp hr)
      show (ν y).toNat ≤ (ν x).toNat
      by_contra hlt
      have hxy : ν x < ν y := B256.lt_iff_toNat_lt_toNat.mpr (by omega)
      rw [hfh] at h0
      simp only [B256.ltCheck, hxy, ↓reduceIte] at h0
      exact B256.one_ne_zero' h0
    · split at hg
      · rename_i _ hr
        simp only [List.mem_singleton] at hg
        subst hg
        have h1 := hnz r (List.contains_iff_mem.mp hr)
        show (ν x).toNat < (ν y).toNat
        by_contra hge
        have hxy : ¬ ν x < ν y := fun h => hge (B256.lt_iff_toNat_lt_toNat.mp h)
        rw [hfh] at h1
        simp only [B256.ltCheck, hxy, ↓reduceIte] at h1
        exact h1 rfl
      · simp only [List.not_mem_nil] at hg
  | orr r x y =>
    simp only [Fact.Holds] at hfh
    simp only at hg
    split at hg
    · rename_i hr
      have h0 := hz r (List.contains_iff_mem.mp hr)
      rw [hfh] at h0
      obtain ⟨hx, hy⟩ := B256.of_or_eq_zero h0
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl
      · show 0 ≤ (ν x).toNat ∧ (ν x).toNat ≤ 0
        rw [hx]; exact ⟨Nat.le_refl _, Nat.le_refl _⟩
      · show 0 ≤ (ν y).toNat ∧ (ν y).toNat ≤ 0
        rw [hy]; exact ⟨Nat.le_refl _, Nat.le_refl _⟩
    · simp only [List.not_mem_nil] at hg
  | bnd _ _ _ => simp only [List.not_mem_nil] at hg
  | le _ _ => simp only [List.not_mem_nil] at hg
  | lt _ _ => simp only [List.not_mem_nil] at hg

theorem zeros_sound (hf : AllHold ν fs) : ∀ s ∈ zeros fs, ν s = 0 := by
  intro s hs
  obtain ⟨f, hfm, hs⟩ := List.mem_filterMap.mp hs
  have hfh := hf f hfm
  cases f with
  | bnd s' l h =>
    cases h with
    | zero =>
      simp only [Option.some.injEq] at hs
      subst hs
      exact B256.toNat_eq_zero (Nat.le_zero.mp hfh.2)
    | succ _ => simp only [reduceCtorEq] at hs
  | _ => simp only [reduceCtorEq] at hs

private theorem ones_sound (hf : AllHold ν fs) :
    ∀ s ∈ fs.filterMap (fun f => match f with
      | .bnd s 1 _ => some s
      | _ => none), ν s ≠ 0 := by
  intro s hs
  obtain ⟨f, hfm, hs⟩ := List.mem_filterMap.mp hs
  have hfh := hf f hfm
  cases f with
  | bnd s' l h =>
    by_cases hl : l = 1
    · subst hl
      simp only [Option.some.injEq] at hs
      subst hs
      intro h0
      have := hfh.1
      rw [h0] at this
      exact absurd this (by decide)
    · have : (match Fact.bnd s' l h with
          | .bnd s 1 _ => some s
          | _ => none) = none := by
        rcases l with _ | _ | l
        · rfl
        · exact absurd rfl hl
        · rfl
      rw [this] at hs
      cases hs
  | _ => simp only [reduceCtorEq] at hs

/-- **`refineFacts` is sound** on the arm where the condition word is zero (`zero = true`)
or nonzero (`zero = false`). -/
theorem refineFacts_sound (hf : AllHold ν fs) {c : Nat} {zero : Bool}
    (hz : zero = true → ν c = 0) (hnz : zero = false → ν c ≠ 0) :
    AllHold ν (refineFacts fs c zero) := by
  unfold refineFacts
  have h1 : AllHold ν ((if zero then [Fact.bnd c 0 0] else [Fact.bnd c 1 maxW]) ++ fs) := by
    refine AllHold.append ?_ hf
    cases zero
    · intro f hm
      simp only [Bool.false_eq_true, ↓reduceIte, List.mem_singleton] at hm
      subst hm
      exact ⟨toNat_pos_of_ne (hnz rfl), toNat_le_maxW _⟩
    · intro f hm
      simp only [↓reduceIte, List.mem_singleton] at hm
      subst hm
      show 0 ≤ (ν c).toNat ∧ (ν c).toNat ≤ 0
      rw [hz rfl]
      exact ⟨Nat.le_refl _, Nat.le_refl _⟩
  have r1 := learn1_sound h1 (z := if zero then [c] else []) (nz := if zero then [] else [c])
    (by
      cases zero
      · simp only [Bool.false_eq_true, ↓reduceIte, List.not_mem_nil, IsEmpty.forall_iff,
        forall_const]
      · simp only [↓reduceIte, List.mem_singleton, forall_eq]
        exact hz rfl)
    (by
      cases zero
      · simp only [Bool.false_eq_true, ↓reduceIte, List.mem_singleton, forall_eq]
        exact hnz rfl
      · simp only [↓reduceIte, List.not_mem_nil, IsEmpty.forall_iff, forall_const])
  have h2 := r1.append h1
  exact (learn1_sound h2 (zeros_sound r1) (ones_sound r1)).append h2

end Refine

/-! ## Joins and call continuations -/

section Joins

private theorem forall₂_of_zip {ν : Nat → B256} {m : Nat → Nat} :
    ∀ {as ss : List Nat} {S : List B256}, as.length = ss.length →
      (∀ p ∈ as.zip ss, m p.1 = p.2) → List.Forall₂ (fun s w => ν s = w) ss S →
      List.Forall₂ (fun a w => ν (m a) = w) as S
  | [], [], [], _, _, _ => .nil
  | a :: as, s :: ss, w :: S, hl, hz, .cons h0 hr => by
    refine .cons ?_ (forall₂_of_zip (Nat.succ.inj hl)
      (fun p hp => hz p (List.mem_cons_of_mem _ hp)) hr)
    rw [hz (a, s) List.mem_cons_self]
    exact h0
  | [], _ :: _, _, hl, _, _ => by cases hl
  | _ :: _, [], _, hl, _, _ => by cases hl

/-- **An accepted join is sound**: if the incoming state `σ` (words `S` named by `σ.kv` under
`ν`, facts holding) passes `compat σ A`, then the annotation `A` holds of the same words under
the renamed valuation `ν ∘ symMap A σ`, and the annotation's pointer symbol names the incoming
pointer symbol's value. -/
theorem compat_sound {σ A : FSt} {ν : Nat → B256} {S : List B256} (hc : compat σ A = true)
    (hS : List.Forall₂ (fun s w => ν s = w) σ.kv S) (hf : AllHold ν σ.facts) :
    List.Forall₂ (fun a w => (ν ∘ symMap A σ) a = w) A.kv S ∧
      AllHold (ν ∘ symMap A σ) A.facts ∧
      ∀ a, A.fp = some a → ∃ s, σ.fp = some s ∧ (ν ∘ symMap A σ) a = ν s := by
  unfold compat at hc
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hc
  obtain ⟨⟨⟨hlen, hzip⟩, hfp⟩, hfacts⟩ := hc
  refine ⟨forall₂_of_zip (ν := ν) (m := symMap A σ) hlen.symm (fun p hp => by simpa only [beq_iff_eq] using hzip p hp) hS,
    fun f hm => Fact.holds_rename.mp (entails_sound hf (hfacts f hm)), ?_⟩
  intro a ha
  rw [ha] at hfp
  simp only [Bool.and_eq_true, Option.isSome_iff_exists] at hfp
  obtain ⟨⟨s, hs⟩, _⟩ := hfp
  refine ⟨s, hs, ?_⟩
  simp only [Function.comp_apply, symMap, ha, ↓reduceIte, hs, Option.getD_some]

private theorem forall₂_agree {ν ν' : Nat → B256} {P : Nat → Prop}
    (h : ∀ s, P s → ν' s = ν s) :
    ∀ {l : List Nat} {S : List B256}, (∀ s ∈ l, P s) →
      List.Forall₂ (fun s w => ν s = w) l S → List.Forall₂ (fun s w => ν' s = w) l S
  | [], [], _, _ => .nil
  | s :: l, _ :: _, hl, .cons h0 hr =>
    .cons (by rw [h s (hl s List.mem_cons_self)]; exact h0)
      (forall₂_agree h (fun t ht => hl t (List.mem_cons_of_mem _ ht)) hr)

private theorem forall₂_map_shift {μ ν' : Nat → B256} {base : Nat}
    (h : ∀ s, ν' (base + s) = μ s) :
    ∀ {l : List Nat} {S : List B256}, List.Forall₂ (fun s w => μ s = w) l S →
      List.Forall₂ (fun s w => ν' s = w) (l.map (base + ·)) S
  | [], [], _ => .nil
  | s :: _, _ :: _, .cons h0 hr => .cons (by rw [h s]; exact h0) (forall₂_map_shift h hr)

private theorem forall₂_append' {ν : Nat → B256} :
    ∀ {l l' : List Nat} {S S' : List B256}, List.Forall₂ (fun s w => ν s = w) l S →
      List.Forall₂ (fun s w => ν s = w) l' S' →
      List.Forall₂ (fun s w => ν s = w) (l ++ l') (S ++ S')
  | [], _, [], _, .nil, h => h
  | _ :: _, _, _ :: _, _, .cons h0 hr, h => .cons h0 (forall₂_append' hr h)

/-- **A call continuation resumes soundly**: the caller's words `below` (named under `ν`,
facts holding) and the callee's returned words (named by its summary `R` under `μ`, `R`'s
facts holding) are together named by `resume σ below R` under one valuation that agrees with
`ν` below the fresh base and with `μ` shifted above it. -/
theorem resume_sound {σ R : FSt} {below : List Nat} {ν μ : Nat → B256} {Sb Sr : List B256}
    (hb : ∀ s ∈ below, s ∈ σ.kv) (hS : List.Forall₂ (fun s w => ν s = w) below Sb)
    (hf : AllHold ν σ.facts) (hR : List.Forall₂ (fun s w => μ s = w) R.kv Sr)
    (hRf : AllHold μ R.facts) :
    ∃ ν' : Nat → B256, (∀ s, s < freshSym σ.kv σ.facts σ.fp → ν' s = ν s) ∧
      (∀ s, ν' (freshSym σ.kv σ.facts σ.fp + s) = μ s) ∧
      List.Forall₂ (fun s w => ν' s = w) (resume σ below R).kv (Sr ++ Sb) ∧
      AllHold ν' (resume σ below R).facts ∧
      (resume σ below R).fp = R.fp.map (freshSym σ.kv σ.facts σ.fp + ·) := by
  let base := freshSym σ.kv σ.facts σ.fp
  let ν' : Nat → B256 := fun s => if base ≤ s then μ (s - base) else ν s
  have hlow : ∀ s, s < base → ν' s = ν s := fun s hs => by
    simp only [ν', show ¬ base ≤ s from Nat.not_le.mpr hs, ↓reduceIte]
  have hhigh : ∀ s, ν' (base + s) = μ s := fun s => by
    simp only [ν', Nat.le_add_right, ↓reduceIte, Nat.add_sub_cancel_left]
  refine ⟨ν', hlow, hhigh, ?_, ?_, rfl⟩
  · exact forall₂_append' (forall₂_map_shift hhigh hR)
      (forall₂_agree hlow (fun s hs => lt_freshSym_kv (hb s hs)) hS)
  · refine AllHold.closeLive _ _ (AllHold.append ?_ ?_)
    · intro g hg
      obtain ⟨f, hfm, rfl⟩ := List.mem_map.mp hg
      refine Fact.holds_rename.mpr ?_
      have : ν' ∘ (base + ·) = μ := funext hhigh
      rw [this]
      exact hRf f hfm
    · intro f hfm
      exact Fact.holds_congr (fun s hs => (hlow s (lt_freshSym_fact hfm hs)).symm) (hf f hfm)

end Joins

end Blanc.Lift.FreePtr
