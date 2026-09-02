import Blanc.CommonProofs
import Jaune.MulDiv
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.Ring

/-!
# Fixed-width word arithmetic

Small contract-neutral bridges between natural-number division/bit tests and
the fixed-width word operations used by compiled EVM loops.
-/

namespace Blanc

open Jaune
open Jaune.Ninst Ninst

/-! ## Ternary word-instruction transport -/

/-- Blanc-side monadic normal form for Jaune's generic three-operand word
instruction. This is the ternary companion of Jaune's `applyBinary_def`. -/
theorem applyTernary_def
    (f : B256 → B256 → B256 → B256) (cost : Nat) (devm : Devm) :
    applyTernary f cost devm = (do
      let ⟨x, devm'⟩ ← devm.pop
      let ⟨y, devm''⟩ ← devm'.pop
      let ⟨z, devm'''⟩ ← devm''.pop
      pushItem (f x y z) cost devm''') := by
  rcases devm with ⟨⟨stack, memory, gasLeft⟩, view, world⟩
  cases stack with
  | nil => rfl
  | cons x xs =>
    cases xs with
    | nil => rfl
    | cons y ys =>
      cases ys with
      | nil => rfl
      | cons z zs =>
        cases h : Mach.pushItem (f x y z) cost
            { stack := zs, memory := memory, gasLeft := gasLeft } with
        | error err =>
          rcases err with ⟨msg, mach'⟩
          cases mach'
          simp only [applyTernary, Mach.applyTernary, Mach.pop, pushItem,
            liftMachExecution, liftMach, Footprint.toExecution,
            Footprint.liftOutcome, Devm.pop_def, Devm.stack, Devm.setMach,
            bind, Except.bind, h]
        | ok out =>
          rcases out with ⟨_, mach'⟩
          cases mach'
          simp only [applyTernary, Mach.applyTernary, Mach.pop, pushItem,
            liftMachExecution, liftMach, Footprint.toExecution,
            Footprint.liftOutcome, Devm.pop_def, Devm.stack, Devm.setMach,
            bind, Except.bind, h]

/-- A successful generic ternary word instruction pops its three operands and
pushes their exact result while preserving every non-machine observation. -/
lemma Devm.diffBurn_of_applyTernary
    {f : B256 → B256 → B256 → B256} {cost : Nat} {s s' : Devm}
    (h : applyTernary f cost s = .ok s') :
    ∃ x y z, Devm.DiffBurn [x, y, z] [f x y z] s s' := by
  rw [applyTernary_def] at h
  rcases Except.bind_eq_ok h with ⟨⟨x, s₁⟩, h1, h'⟩
  rcases Except.bind_eq_ok h' with ⟨⟨y, s₂⟩, h2, h''⟩
  rcases Except.bind_eq_ok h'' with ⟨⟨z, s₃⟩, h3, h4⟩
  simp only at h4
  rw [pushItem_def] at h4
  refine ⟨x, y, z, Devm.diffBurn_of_pop_of_pushBurn
    (Devm.pop_append (Devm.pop_of_pop h1)
      (Devm.pop_append (Devm.pop_of_pop h2) (Devm.pop_of_pop h3)))
    (Devm.pushBurn_of_run h4)⟩

/-- Transport a known three-word stack prefix through any successful ternary
word operation represented as a `Devm.DiffBurn`. -/
lemma prefix_of_diffBurn_three
    (v : B256 → B256 → B256 → B256) {x y z xs} {s s' : Devm} :
    (∃ x' y' z', Devm.DiffBurn [x', y', z'] [v x' y' z'] s s') →
    (x :: y :: z :: xs <<+ s.stack) →
      (v x y z :: xs <<+ s'.stack) := by
  intros h0 h1
  rcases h0 with ⟨x', y', z', h0⟩
  rcases h0.stack with ⟨stk, h2, h3⟩
  rcases of_cons_cons_pref_of_cons_cons_pref h1 (pref_of_split h2)
    with ⟨hx, hy, ws, h, h'⟩
  rcases List.of_cons_pref_of_cons_pref h h' with ⟨hz, -⟩
  cases hx
  cases hy
  cases hz
  exact append_pref h3 (of_append_pref h2 h1)

/-- `ADDMOD` replaces three known stack heads by their full-width modular
sum. -/
lemma prefix_of_addmod {e} {x y z xs} {s s' : Devm} :
    Ninst.Run e s addmod s' → (x :: y :: z :: xs <<+ s.stack) →
      (B256.addmod x y z :: xs <<+ s'.stack) := by
  intro h0 h1
  refine prefix_of_diffBurn_three B256.addmod ?_ h1
  rcases of_run_reg h0 with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact Devm.diffBurn_of_applyTernary run

/-- `MULMOD` replaces three known stack heads by their full-width modular
product. -/
lemma prefix_of_mulmod {e} {x y z xs} {s s' : Devm} :
    Ninst.Run e s mulmod s' → (x :: y :: z :: xs <<+ s.stack) →
      (B256.mulmod x y z :: xs <<+ s'.stack) := by
  intro h0 h1
  refine prefix_of_diffBurn_three B256.mulmod ?_ h1
  rcases of_run_reg h0 with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact Devm.diffBurn_of_applyTernary run

/- These contract-neutral instances intentionally live in the lower-fanout
fixed-width module rather than extending the central `CommonProofs` rebuild
cone. Importing `WordArithmetic` makes the ternary and XOR cases available to
`line_inv`. -/
instance : Rinst.Hinv Devm.state Rinst.xor := by show_hinv_state
instance : Rinst.Hinv Devm.state Rinst.addmod := by show_hinv_state
instance : Rinst.Hinv Devm.state Rinst.mulmod := by show_hinv_state

instance : Rinst.Hinv Devm.memory Rinst.addmod := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  exact
    (Devm.diffBurn_of_applyTernary run).choose_spec.choose_spec.choose_spec.memory⟩

instance : Rinst.Hinv Devm.memory Rinst.mulmod := ⟨by
  intro pc sevm pre post run
  simp only [Rinst.run, Rinst.runCore] at run
  exact
    (Devm.diffBurn_of_applyTernary run).choose_spec.choose_spec.choose_spec.memory⟩

/-! ## EVM word bounds -/

/-- The cardinality of the EVM's 256-bit word ring. -/
def wordModulusN : Nat := 2 ^ 256

/-- The greatest natural number represented by an EVM word. -/
def maxWordN : Nat := wordModulusN - 1

theorem wordModulusN_pos : 0 < wordModulusN := by
  simp [wordModulusN]

theorem maxWordN_lt_wordModulusN : maxWordN < wordModulusN := by
  unfold maxWordN
  have := wordModulusN_pos
  omega

theorem maxWord_toNat : B256.max.toNat = maxWordN := by
  decide +kernel

/-! ## Exact two-word multiplication -/

/-- The low word of the exact 512-bit product of two EVM words. -/
def productLowWord (x y : B256) : B256 := x * y

/-- The high word of the exact 512-bit product, reconstructed from `MULMOD`
with its carry correction. -/
def productHighWord (x y : B256) : B256 :=
  let low := productLowWord x y
  let scratch := B256.mulmod x y B256.max
  (scratch - low) - (if scratch < low then 1 else 0)

theorem productLowWord_toNat (x y : B256) :
    (productLowWord x y).toNat = x.toNat * y.toNat % wordModulusN := by
  exact B256.toNat_mul_mod x y

private theorem product_quotient_lt_pred
    {m x y : Nat} (hm : 2 ≤ m) (hx : x < m) (hy : y < m) :
    x * y / m < m - 1 := by
  rw [Nat.div_lt_iff_lt_mul (by omega)]
  calc
    x * y ≤ (m - 1) * (m - 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    _ < (m - 1) * m :=
      Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
    _ = (m - 1) * m := rfl

private theorem product_mod_pred_eq_quotient_add_remainder_mod
    {m p : Nat} (hm : 2 ≤ m) :
    p % (m - 1) = (p / m + p % m) % (m - 1) := by
  have hsplit : p = p / m * m + p % m := (Nat.div_add_mod' p m).symm
  have hmSplit : m = (m - 1) + 1 := by omega
  calc
    p % (m - 1) = (p / m * m + p % m) % (m - 1) :=
      congrArg (fun n => n % (m - 1)) hsplit
    _ = (p / m * ((m - 1) + 1) + p % m) % (m - 1) := by
      rw [← hmSplit]
    _ = (p / m * (m - 1) + (p / m + p % m)) % (m - 1) := by
      simp only [Nat.mul_add, Nat.mul_one, Nat.add_assoc]
    _ = (p / m + p % m) % (m - 1) := by simp

/-- The staged high and low words recombine to the exact, untruncated product.
There is no single-word product or magnitude premise. -/
theorem productHighWord_mul_add_productLowWord_toNat (x y : B256) :
    (productHighWord x y).toNat * wordModulusN +
        (productLowWord x y).toNat =
      x.toNat * y.toNat := by
  let p := x.toNat * y.toNat
  let q := p / wordModulusN
  let r := p % wordModulusN
  let scratch := p % maxWordN
  have hmodulus : 2 ≤ wordModulusN := by
    unfold wordModulusN
    norm_num
  have hmaxWord : maxWordN = wordModulusN - 1 := rfl
  have hq : q < maxWordN := by
    exact product_quotient_lt_pred hmodulus (B256.toNat_lt x)
      (B256.toNat_lt y)
  have hr : r < wordModulusN := by
    exact Nat.mod_lt _ (by omega)
  have hsplit : q * wordModulusN + r = p := by
    exact Nat.div_add_mod' p wordModulusN
  have hscratch : scratch = (q + r) % maxWordN := by
    unfold scratch q r
    rw [hmaxWord]
    exact product_mod_pred_eq_quotient_add_remainder_mod hmodulus
  have hlow : (productLowWord x y).toNat = r := by
    unfold productLowWord r p wordModulusN
    exact B256.toNat_mul_mod x y
  have hscratchWord : (B256.mulmod x y B256.max).toNat = scratch := by
    rw [B256.toNat_mulmod (by decide), maxWord_toNat]
  by_cases hsum : q + r < maxWordN
  · have hscratchSmall : scratch = q + r := by
      rw [hscratch, Nat.mod_eq_of_lt hsum]
    have hgeNat :
        (productLowWord x y).toNat ≤
          (B256.mulmod x y B256.max).toNat := by
      calc
        (productLowWord x y).toNat = r := hlow
        _ ≤ q + r := Nat.le_add_left r q
        _ = (B256.mulmod x y B256.max).toNat :=
          (hscratchWord.trans hscratchSmall).symm
    have hnotBorrow :
        ¬B256.mulmod x y B256.max < productLowWord x y := by
      intro hlt
      exact (Nat.not_lt_of_ge hgeNat) (B256.toNat_lt_toNat hlt)
    have hleWord :
        productLowWord x y ≤ B256.mulmod x y B256.max :=
      B256.le_of_toNat_le_toNat hgeNat
    have hzeroLe :
        (0 : B256) ≤ B256.mulmod x y B256.max - productLowWord x y :=
      B256.le_of_toNat_le_toNat (Nat.zero_le _)
    have hhigh : (productHighWord x y).toNat = q := by
      rw [productHighWord, if_neg hnotBorrow]
      rw [B256.toNat_sub_eq_of_le _ _ hzeroLe, B256.toNat_zero,
        Nat.sub_zero]
      rw [B256.toNat_sub_eq_of_le _ _ hleWord, hscratchWord, hlow,
        hscratchSmall]
      omega
    rw [hhigh, hlow]
    change q * wordModulusN + r = p
    exact hsplit
  · have hsumLe : maxWordN ≤ q + r := by omega
    have hsumSub : q + r - maxWordN < maxWordN := by
      unfold maxWordN at hq hr hsumLe ⊢
      omega
    have hscratchLarge : scratch = q + r - maxWordN := by
      rw [hscratch, Nat.mod_eq_sub_mod hsumLe, Nat.mod_eq_of_lt hsumSub]
    have hborrow : B256.mulmod x y B256.max < productLowWord x y := by
      apply B256.lt_of_toNat_lt_toNat
      calc
        (B256.mulmod x y B256.max).toNat = q + r - maxWordN :=
          hscratchWord.trans hscratchLarge
        _ < r := by
          unfold maxWordN at hq hsumLe ⊢
          omega
        _ = (productLowWord x y).toNat := hlow.symm
    have hwrapped :
        ((B256.mulmod x y B256.max - productLowWord x y).toNat) = q + 1 := by
      rw [B256.toNat_sub, hscratchWord, hlow, hscratchLarge, Nat.lo_eq]
      have hinner :
          wordModulusN + (q + r - maxWordN) - r = q + 1 := by
        unfold maxWordN at hq hr hsumLe ⊢
        omega
      unfold wordModulusN at hinner
      rw [hinner, Nat.mod_eq_of_lt]
      unfold maxWordN at hq
      omega
    have honeLe :
        (1 : B256) ≤ B256.mulmod x y B256.max - productLowWord x y := by
      apply B256.le_of_toNat_le_toNat
      rw [B256.toNat_one, hwrapped]
      omega
    have hhigh : (productHighWord x y).toNat = q := by
      rw [productHighWord, if_pos hborrow]
      rw [B256.toNat_sub_eq_of_le _ _ honeLe, hwrapped, B256.toNat_one]
      omega
    rw [hhigh, hlow]
    change q * wordModulusN + r = p
    exact hsplit

theorem productHighWord_toNat (x y : B256) :
    (productHighWord x y).toNat =
      x.toNat * y.toNat / wordModulusN := by
  have hlow : (productLowWord x y).toNat < wordModulusN := by
    simpa [wordModulusN] using B256.toNat_lt (productLowWord x y)
  have hquotient :
      ((productHighWord x y).toNat * wordModulusN +
          (productLowWord x y).toNat) / wordModulusN =
        (productHighWord x y).toNat := by
    apply Nat.div_eq_of_lt_le
    · exact Nat.le_add_right _ _
    · rw [Nat.add_mul, Nat.one_mul]
      exact Nat.add_lt_add_left hlow _
  calc
    (productHighWord x y).toNat =
        ((productHighWord x y).toNat * wordModulusN +
          (productLowWord x y).toNat) / wordModulusN := hquotient.symm
    _ = x.toNat * y.toNat / wordModulusN := by
      rw [productHighWord_mul_add_productLowWord_toNat]

/-! ## Full-width division staging -/

/-- The natural number represented by a high/low pair of EVM words. -/
def wideNumeratorN (high low : B256) : Nat :=
  high.toNat * wordModulusN + low.toNat

/-- Removing a natural number's remainder leaves its exact quotient times the
divisor. This identity also covers the divisor-zero convention. -/
theorem Nat.sub_mod_eq_div_mul (n d : Nat) :
    n - n % d = n / d * d := by
  have division := Nat.mod_add_div n d
  rw [Nat.mul_comm d (n / d)] at division
  omega

/-- After remainder removal, dividing out any positive factor of the divisor
leaves the original quotient times the correspondingly reduced divisor. -/
theorem Nat.sub_mod_div_factor
    {n d twos : Nat}
    (twosPositive : 0 < twos)
    (twosDvdDenominator : twos ∣ d) :
    (n - n % d) / twos = n / d * (d / twos) := by
  rw [Nat.sub_mod_eq_div_mul]
  obtain ⟨factor, factorEq⟩ := twosDvdDenominator
  subst d
  let quotient := n / (twos * factor)
  change quotient * (twos * factor) / twos =
    quotient * ((twos * factor) / twos)
  calc
    quotient * (twos * factor) / twos =
        twos * (quotient * factor) / twos := by
      congr 1
      ring
    _ = quotient * factor :=
      Nat.mul_div_cancel_left _ twosPositive
    _ = quotient * ((twos * factor) / twos) := by
      rw [Nat.mul_div_cancel_left factor twosPositive]

/-- A two-word numerator divided by a single-word denominator fits in one
word whenever the high word is smaller than the denominator. -/
theorem Nat.two_word_div_lt_modulus
    {width high low denominator : Nat}
    (lowBound : low < 2 ^ width)
    (highLt : high < denominator) :
    (high * 2 ^ width + low) / denominator < 2 ^ width := by
  have denominatorPositive : 0 < denominator := by omega
  rw [Nat.div_lt_iff_lt_mul denominatorPositive]
  calc
    high * 2 ^ width + low <
        high * 2 ^ width + 2 ^ width :=
      Nat.add_lt_add_left lowBound _
    _ = (high + 1) * 2 ^ width := by ring
    _ ≤ denominator * 2 ^ width :=
      Nat.mul_le_mul_right (2 ^ width) (by omega)
    _ = 2 ^ width * denominator := Nat.mul_comm _ _

/-- The word-level representation of `2^256 mod denominator` used by standard
512-by-256 division. -/
def wordModulusFactorWord (denominator : B256) : B256 :=
  B256.addmod B256.max 1 denominator

/-- The remainder of the exact two-word numerator `high * 2^256 + low`,
computed without first constructing that unbounded natural number as a word. -/
def wideRemainderWord (high low denominator : B256) : B256 :=
  B256.addmod
    (B256.mulmod high (wordModulusFactorWord denominator) denominator)
    low denominator

theorem wordModulusFactorWord_toNat
    {denominator : B256} (nonzero : denominator ≠ 0) :
    (wordModulusFactorWord denominator).toNat =
      wordModulusN % denominator.toNat := by
  rw [wordModulusFactorWord, B256.toNat_addmod nonzero,
    maxWord_toNat, B256.toNat_one]
  congr 1

theorem wideRemainderWord_toNat
    {high low denominator : B256} (nonzero : denominator ≠ 0) :
    (wideRemainderWord high low denominator).toNat =
      wideNumeratorN high low % denominator.toNat := by
  rw [wideRemainderWord, B256.toNat_addmod nonzero,
    B256.toNat_mulmod nonzero,
    wordModulusFactorWord_toNat nonzero]
  unfold wideNumeratorN
  simp only [Nat.add_mod, Nat.mul_mod, Nat.mod_mod]

theorem wideRemainderWord_le_numerator
    {high low denominator : B256} (nonzero : denominator ≠ 0) :
    (wideRemainderWord high low denominator).toNat ≤
      wideNumeratorN high low := by
  rw [wideRemainderWord_toNat nonzero]
  exact Nat.mod_le _ _

/-- The borrow bit produced while subtracting a remainder from the low word. -/
def wideBorrowWord (low remainder : B256) : B256 :=
  B256.ltCheck low remainder

/-- Low word after subtracting a full-width remainder. -/
def wideSubLowWord (low remainder : B256) : B256 :=
  low - remainder

/-- High word after propagating the remainder-subtraction borrow. -/
def wideSubHighWord (high low remainder : B256) : B256 :=
  high - wideBorrowWord low remainder

/-- The two word-level subtraction results reconstruct exact natural-number
subtraction whenever the remainder does not exceed the represented numerator. -/
theorem wideSubWords_reconstruct
    {high low remainder : B256}
    (remainderLe : remainder.toNat ≤ wideNumeratorN high low) :
    (wideSubHighWord high low remainder).toNat * wordModulusN +
        (wideSubLowWord low remainder).toNat =
      wideNumeratorN high low - remainder.toNat := by
  unfold wideNumeratorN at remainderLe ⊢
  by_cases borrow : low < remainder
  · have lowLt : low.toNat < remainder.toNat :=
      B256.toNat_lt_toNat borrow
    have highPos : 0 < high.toNat := by
      by_contra highNotPos
      have highZero : high.toNat = 0 := by omega
      simp only [highZero, Nat.zero_mul, Nat.zero_add] at remainderLe
      omega
    have oneLeHigh : (1 : B256) ≤ high := by
      apply B256.le_of_toNat_le_toNat
      rw [B256.toNat_one]
      omega
    have highSub :
        (wideSubHighWord high low remainder).toNat = high.toNat - 1 := by
      rw [wideSubHighWord, wideBorrowWord, B256.ltCheck, if_pos borrow,
        B256.toNat_sub_eq_of_le _ _ oneLeHigh, B256.toNat_one]
    have lowSub :
        (wideSubLowWord low remainder).toNat =
          wordModulusN + low.toNat - remainder.toNat := by
      rw [wideSubLowWord, B256.toNat_sub]
      change
        (wordModulusN + low.toNat - remainder.toNat) ↾ 256 =
          wordModulusN + low.toNat - remainder.toNat
      rw [Nat.lo_eq_of_lt]
      unfold wordModulusN
      omega
    have highSplit :
        (high.toNat - 1) * wordModulusN + wordModulusN =
          high.toNat * wordModulusN := by
      calc
        (high.toNat - 1) * wordModulusN + wordModulusN =
            ((high.toNat - 1) + 1) * wordModulusN := by
              rw [Nat.add_mul, Nat.one_mul]
        _ = high.toNat * wordModulusN := by
          rw [Nat.sub_add_cancel (by omega)]
    have remainderLeModLow :
        remainder.toNat ≤ wordModulusN + low.toNat := by
      have remainderLt : remainder.toNat < wordModulusN := by
        simpa [wordModulusN] using B256.toNat_lt remainder
      exact (Nat.le_of_lt remainderLt).trans (Nat.le_add_right _ _)
    rw [highSub, lowSub]
    calc
      (high.toNat - 1) * wordModulusN +
          (wordModulusN + low.toNat - remainder.toNat) =
        (high.toNat - 1) * wordModulusN +
            (wordModulusN + low.toNat) - remainder.toNat :=
          (Nat.add_sub_assoc remainderLeModLow _).symm
      _ = ((high.toNat - 1) * wordModulusN + wordModulusN) +
            low.toNat - remainder.toNat := by
          rw [Nat.add_assoc]
      _ = high.toNat * wordModulusN + low.toNat - remainder.toNat := by
          rw [highSplit]
  · have remainderLeLow : remainder ≤ low := B256.not_lt.mp borrow
    have remainderLeLowNat : remainder.toNat ≤ low.toNat :=
      B256.toNat_le_toNat remainderLeLow
    have lowSub :
        (wideSubLowWord low remainder).toNat =
          low.toNat - remainder.toNat := by
      exact B256.toNat_sub_eq_of_le _ _ remainderLeLow
    have zeroLeHigh : (0 : B256) ≤ high :=
      B256.le_of_toNat_le_toNat (Nat.zero_le _)
    have highSub :
        (wideSubHighWord high low remainder).toNat = high.toNat := by
      rw [wideSubHighWord, wideBorrowWord, B256.ltCheck, if_neg borrow,
        B256.toNat_sub_eq_of_le _ _ zeroLeHigh,
        B256.toNat_zero, Nat.sub_zero]
    rw [highSub, lowSub]
    exact (Nat.add_sub_assoc remainderLeLowNat _).symm

/-- Subtracting the computed remainder makes the represented numerator exactly
divisible by the denominator. -/
theorem wideNumerator_sub_remainder_mod_eq_zero
    {high low denominator : B256} (nonzero : denominator ≠ 0) :
    (wideNumeratorN high low -
        (wideRemainderWord high low denominator).toNat) %
      denominator.toNat = 0 := by
  rw [wideRemainderWord_toNat nonzero]
  apply Nat.sub_mod_eq_zero_of_mod_eq
  exact (Nat.mod_mod _ _).symm

/-! ## Lowest-set-bit factorization -/

/-- Isolate the lowest set bit of a nonzero `width`-bit natural using its
bounded two's complement. This is the unbounded model of `x & (0 - x)` in a
fixed-width word. -/
def Nat.lowestSetBit (width n : Nat) : Nat :=
  n &&& (2 ^ width - n)

private theorem Nat.and_two_mul (a b : Nat) :
    (2 * a) &&& (2 * b) = 2 * (a &&& b) := by
  simpa [Nat.bit_false_apply] using Nat.land_bit false a false b

private theorem Nat.lowestSetBit_eq_one_of_odd
    {width n : Nat} (positive : 0 < n) (bound : n < 2 ^ width)
    (odd : n % 2 = 1) :
    Nat.lowestSetBit width n = 1 := by
  have widthPositive : 0 < width := by
    by_contra notPositive
    have widthZero : width = 0 := by omega
    subst width
    norm_num at bound
    omega
  unfold Nat.lowestSetBit
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_and]
  have predBound : n - 1 < 2 ^ width := by omega
  have subEq : 2 ^ width - n = 2 ^ width - ((n - 1) + 1) := by omega
  rw [subEq, Nat.testBit_two_pow_sub_succ predBound]
  cases i with
  | zero =>
      have nBit : n.testBit 0 = true :=
        Nat.mod_two_eq_one_iff_testBit_zero.mp odd
      have predEven : (n - 1) % 2 = 0 := by omega
      have predBit : (n - 1).testBit 0 = false :=
        Nat.mod_two_eq_zero_iff_testBit_zero.mp predEven
      simp [nBit, predBit, widthPositive]
  | succ i =>
      have halves : (n - 1) / 2 = n / 2 := by omega
      simp [Nat.testBit_succ, halves]
      tauto

private theorem Nat.lowestSetBit_succ_of_even
    {width n : Nat} (bound : n < 2 ^ (width + 1))
    (even : n % 2 = 0) :
    Nat.lowestSetBit (width + 1) n =
      2 * Nat.lowestSetBit width (n / 2) := by
  have nEq : n = 2 * (n / 2) := by omega
  have halfBound : n / 2 < 2 ^ width := by
    rw [Nat.pow_succ] at bound
    omega
  have subEq :
      2 ^ (width + 1) - n = 2 * (2 ^ width - n / 2) := by
    rw [Nat.pow_succ]
    omega
  unfold Nat.lowestSetBit
  calc
    n &&& (2 ^ (width + 1) - n) =
        (2 * (n / 2)) &&& (2 * (2 ^ width - n / 2)) :=
      congrArg₂ (fun a b : Nat => a &&& b) nEq subEq
    _ = 2 * ((n / 2) &&& (2 ^ width - n / 2)) :=
      Nat.and_two_mul _ _

/-- The isolated lowest set bit is a positive common power-of-two factor of
the input and the word modulus, and removing it leaves an odd quotient. -/
theorem Nat.lowestSetBit_spec
    {width n : Nat} (positive : 0 < n) (bound : n < 2 ^ width) :
    let twos := Nat.lowestSetBit width n
    0 < twos ∧ twos ∣ n ∧ twos ∣ 2 ^ width ∧
      (n / twos) % 2 = 1 := by
  induction width generalizing n with
  | zero =>
      norm_num at bound
      omega
  | succ width ih =>
      rcases Nat.mod_two_eq_zero_or_one n with even | odd
      · have halfPositive : 0 < n / 2 := by omega
        have halfBound : n / 2 < 2 ^ width := by
          rw [Nat.pow_succ] at bound
          omega
        have halfSpec := ih halfPositive halfBound
        let halfTwos := Nat.lowestSetBit width (n / 2)
        change
          0 < Nat.lowestSetBit (width + 1) n ∧
          Nat.lowestSetBit (width + 1) n ∣ n ∧
          Nat.lowestSetBit (width + 1) n ∣ 2 ^ (width + 1) ∧
          (n / Nat.lowestSetBit (width + 1) n) % 2 = 1
        change
          0 < halfTwos ∧ halfTwos ∣ n / 2 ∧
            halfTwos ∣ 2 ^ width ∧ ((n / 2) / halfTwos) % 2 = 1
          at halfSpec
        rcases halfSpec with ⟨halfTwosPositive, halfTwosDvdN,
          halfTwosDvdModulus, halfQuotientOdd⟩
        have lowBitEq :
            Nat.lowestSetBit (width + 1) n = 2 * halfTwos := by
          simpa [halfTwos] using Nat.lowestSetBit_succ_of_even bound even
        have nEq : n = 2 * (n / 2) := by omega
        refine ⟨?_, ?_, ?_, ?_⟩
        · rw [lowBitEq]
          omega
        · rw [lowBitEq, nEq]
          exact Nat.mul_dvd_mul_left 2 halfTwosDvdN
        · rw [lowBitEq, Nat.pow_succ]
          simpa [Nat.mul_comm] using
            Nat.mul_dvd_mul_left 2 halfTwosDvdModulus
        · rw [lowBitEq, nEq,
            Nat.mul_div_mul_left _ _ (by omega : 0 < 2)]
          exact halfQuotientOdd
      · have lowBitEq : Nat.lowestSetBit (width + 1) n = 1 :=
          Nat.lowestSetBit_eq_one_of_odd positive bound odd
        simp [lowBitEq, odd]

/-- The exact word operation used to isolate the largest power of two dividing
a nonzero word. -/
def lowestSetBitWord (x : B256) : B256 :=
  x &&& (B256.zero - x)

private theorem zero_sub_word_toNat
    {x : B256} (nonzero : x ≠ B256.zero) :
    (B256.zero - x).toNat = wordModulusN - x.toNat := by
  have xNatPositive : 0 < x.toNat := by
    by_contra notPositive
    have xNatZero : x.toNat = 0 := by omega
    apply nonzero
    exact B256.toNat_inj x B256.zero
      (xNatZero.trans (show 0 = B256.zero.toNat by rfl))
  rw [B256.toNat_sub]
  change (wordModulusN - x.toNat) ↾ 256 = wordModulusN - x.toNat
  rw [Nat.lo_eq_of_lt]
  unfold wordModulusN
  omega

theorem lowestSetBitWord_toNat
    {x : B256} (nonzero : x ≠ B256.zero) :
    (lowestSetBitWord x).toNat = Nat.lowestSetBit 256 x.toNat := by
  rw [lowestSetBitWord, B256.toNat_and, zero_sub_word_toNat nonzero]
  rfl

/-- Word-level lowest-set-bit factorization: the factor is positive, divides
both the input and `2^256`, and the reduced input is odd. -/
theorem lowestSetBitWord_spec
    {x : B256} (nonzero : x ≠ B256.zero) :
    let twos := (lowestSetBitWord x).toNat
    0 < twos ∧ twos ∣ x.toNat ∧ twos ∣ wordModulusN ∧
      (x.toNat / twos) % 2 = 1 := by
  have xNatPositive : 0 < x.toNat := by
    by_contra notPositive
    have xNatZero : x.toNat = 0 := by omega
    apply nonzero
    exact B256.toNat_inj x B256.zero
      (xNatZero.trans (show 0 = B256.zero.toNat by rfl))
  have spec := Nat.lowestSetBit_spec xNatPositive (B256.toNat_lt x)
  simpa [lowestSetBitWord_toNat nonzero, wordModulusN] using spec

theorem lowestSetBitWord_ne_zero
    {x : B256} (nonzero : x ≠ B256.zero) :
    lowestSetBitWord x ≠ B256.zero := by
  have positive := (lowestSetBitWord_spec nonzero).1
  intro zero
  rw [zero] at positive
  change 0 < 0 at positive
  omega

/-- Divide a nonzero word by its largest power-of-two factor. -/
def removeLowestSetBitWord (x : B256) : B256 :=
  x / lowestSetBitWord x

theorem removeLowestSetBitWord_toNat
    {x : B256} (nonzero : x ≠ B256.zero) :
    (removeLowestSetBitWord x).toNat =
      x.toNat / (lowestSetBitWord x).toNat := by
  exact B256.toNat_div (lowestSetBitWord_ne_zero nonzero)

/-- Removing the isolated power-of-two factor leaves an odd word. -/
theorem removeLowestSetBitWord_odd
    {x : B256} (nonzero : x ≠ B256.zero) :
    (removeLowestSetBitWord x).toNat % 2 = 1 := by
  rw [removeLowestSetBitWord_toNat nonzero]
  exact (lowestSetBitWord_spec nonzero).2.2.2

/-- Fixed-width representation of `2^256 / twos`. For `twos = 1` the
mathematical value is `2^256`, whose correct word representation is zero. -/
def wordModulusDivFactorWord (twos : B256) : B256 :=
  (B256.zero - twos) / twos + 1

theorem wordModulusDivFactorWord_toNat
    {twos : B256} (nonzero : twos ≠ B256.zero) :
    (wordModulusDivFactorWord twos).toNat =
      wordModulusN / twos.toNat % wordModulusN := by
  have twosPositive : 0 < twos.toNat := by
    by_contra notPositive
    have twosZero : twos.toNat = 0 := by omega
    apply nonzero
    exact B256.toNat_inj twos B256.zero
      (twosZero.trans (show 0 = B256.zero.toNat by rfl))
  have twosLe : twos.toNat ≤ wordModulusN := by
    have bound := B256.toNat_lt twos
    unfold wordModulusN
    omega
  rw [wordModulusDivFactorWord, B256.toNat_add,
    B256.toNat_div nonzero, zero_sub_word_toNat nonzero,
    B256.toNat_one]
  change
    ((wordModulusN - twos.toNat) / twos.toNat + 1) % wordModulusN =
      wordModulusN / twos.toNat % wordModulusN
  rw [← Nat.div_eq_sub_div twosPositive twosLe]

theorem div_two_div_pow (n k : Nat) :
    n / 2 / 2 ^ k = n / 2 ^ (k + 1) := by
  rw [Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm]

theorem div_pow_div_two (n k : Nat) :
    n / 2 ^ k / 2 = n / 2 ^ (k + 1) := by
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ]

theorem one_and_toB256_eq_mod_two (n : Nat) (hn : n < 2 ^ 256) :
    ((1 : B256) &&& Nat.toB256 n) = Nat.toB256 (n % 2) := by
  apply B256.toNat_inj
  rw [B256.toNat_and, B256.toNat_toB256_of_lt hn]
  rw [B256.toNat_toB256_of_lt (by omega : n % 2 < 2 ^ 256)]
  exact Nat.one_and_eq_mod_two n

theorem toB256_add_one_of_lt (n : Nat) (hn : n + 1 < 2 ^ 256) :
    Nat.toB256 n + 1 = Nat.toB256 (n + 1) := by
  apply B256.toNat_inj
  rw [B256.toNat_add_eq_of_nof]
  · rw [B256.toNat_toB256_of_lt (by omega : n < 2 ^ 256),
      B256.toNat_toB256_of_lt hn]
    rfl
  · unfold B256.Nof
    rw [B256.toNat_toB256_of_lt (by omega : n < 2 ^ 256)]
    exact hn

theorem toUInt64_shiftRight_one (n : Nat) (hn : n < 2 ^ 64) :
    n.toUInt64 >>> (1 : Nat).toUInt64 = (n / 2).toUInt64 := by
  rw [← UInt64.toNat_inj]
  rw [UInt64.toNat_shiftRight, toNat_toUInt64]
  rw [Nat.lo_eq_of_lt hn]
  have hright : (n / 2).toUInt64.toNat = n / 2 := by
    rw [toNat_toUInt64, Nat.lo_eq_of_lt (by omega : n / 2 < 2 ^ 64)]
  rw [hright, show ((1 : Nat).toUInt64).toNat = 1 by rfl]
  norm_num [Nat.shiftRight_eq_div_pow]

theorem toB128_shiftRight_one (n : Nat) (hn : n < 2 ^ 64) :
    Nat.toB128 n >>> 1 = Nat.toB128 (n / 2) := by
  have hn64 : n >>> 64 = 0 := Nat.shiftRight_eq_zero n 64 (by omega)
  have hhalf64 : (n / 2) >>> 64 = 0 :=
    Nat.shiftRight_eq_zero (n / 2) 64 (by omega)
  have hnword : Nat.toB128 n = ((0 : UInt64), n.toUInt64) := by
    unfold Nat.toB128
    rw [hn64]
    rfl
  have hhword : Nat.toB128 (n / 2) =
      ((0 : UInt64), (n / 2).toUInt64) := by
    unfold Nat.toB128
    rw [hhalf64]
    rfl
  rw [hnword, hhword]
  change B128.shiftRight ((0 : UInt64), n.toUInt64) 1 =
    ((0 : UInt64), (n / 2).toUInt64)
  simp only [B128.shiftRight, if_false, if_true, Nat.one_ne_zero,
    Nat.reduceLT]
  apply Prod.ext
  · rfl
  · simpa only [UInt64.zero_shiftLeft, UInt64.zero_or] using
      toUInt64_shiftRight_one n hn

theorem toB256_shiftRight_one (n : Nat) (hn : n < 2 ^ 64) :
    Nat.toB256 n >>> 1 = Nat.toB256 (n / 2) := by
  have hn128 : n >>> 128 = 0 := Nat.shiftRight_eq_zero n 128 (by omega)
  have hhalf128 : (n / 2) >>> 128 = 0 :=
    Nat.shiftRight_eq_zero (n / 2) 128 (by omega)
  have hnword : Nat.toB256 n = ((0 : B128), Nat.toB128 n) := by
    unfold Nat.toB256
    rw [hn128]
    rfl
  have hhword : Nat.toB256 (n / 2) =
      ((0 : B128), Nat.toB128 (n / 2)) := by
    unfold Nat.toB256
    rw [hhalf128]
    rfl
  rw [hnword, hhword]
  change B256.shiftRight ((0 : B128), Nat.toB128 n) 1 =
    ((0 : B128), Nat.toB128 (n / 2))
  simp only [B256.shiftRight, if_false, if_true, Nat.one_ne_zero,
    Nat.reduceLT]
  apply Prod.ext
  · rfl
  · have hzeroShift : (0 : B128) <<< 127 = 0 := by
      change B128.shiftLeft ((0 : UInt64), (0 : UInt64)) 127 =
        ((0 : UInt64), (0 : UInt64))
      norm_num [B128.shiftLeft]
    rw [show 128 - 1 = 127 by omega, hzeroShift, B128.zero_or]
    exact toB128_shiftRight_one n hn

/-! ## Bitwise word projections -/

/-- Bitwise `or` distributes over a shift-and-or split of both sides when the
low halves fit below the shift. -/
theorem Nat.or_or_shiftLeft {a b c d k : Nat}
    (hb : b < 2 ^ k) (hd : d < 2 ^ k) :
    ((a <<< k ||| b) ||| (c <<< k ||| d)) =
      ((a ||| c) <<< k) ||| (b ||| d) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_or, Nat.testBit_shiftLeft]
  by_cases hi : k ≤ i
  · have hpow : (2 : Nat) ^ k ≤ 2 ^ i :=
      Nat.pow_le_pow_right (by omega) hi
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb hpow),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hd hpow)]
    simp [hi]
  · simp [hi]

theorem B128.toNat_or (x y : B128) :
    (x ||| y).toNat = x.toNat ||| y.toNat := by
  show ((x.1 ||| y.1).toNat <<< 64) ||| (x.2 ||| y.2).toNat = _
  rw [UInt64.toNat_or, UInt64.toNat_or]
  exact (Nat.or_or_shiftLeft (UInt64.toNat_lt x.2)
    (UInt64.toNat_lt y.2)).symm

/-- `B256.toNat` preserves bitwise `or`. -/
theorem B256.toNat_or (x y : B256) :
    (x ||| y).toNat = x.toNat ||| y.toNat := by
  show ((x.1 ||| y.1).toNat <<< 128) ||| (x.2 ||| y.2).toNat = _
  rw [B128.toNat_or, B128.toNat_or]
  exact (Nat.or_or_shiftLeft (B128.toNat_lt (x := x.2))
    (B128.toNat_lt (x := y.2))).symm

/-- Bitwise `xor` distributes over a shift-and-or split of both sides when
the low halves fit below the shift. -/
theorem Nat.xor_or_shiftLeft {a b c d k : Nat}
    (hb : b < 2 ^ k) (hd : d < 2 ^ k) :
    ((a <<< k ||| b) ^^^ (c <<< k ||| d)) =
      ((a ^^^ c) <<< k) ||| (b ^^^ d) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [Nat.testBit_or, Nat.testBit_xor, Nat.testBit_shiftLeft]
  by_cases hi : k ≤ i
  · have hpow : (2 : Nat) ^ k ≤ 2 ^ i :=
      Nat.pow_le_pow_right (by omega) hi
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb hpow),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hd hpow)]
    simp [hi]
  · simp [hi]

theorem B128.toNat_xor (x y : B128) :
    (x ^^^ y).toNat = x.toNat ^^^ y.toNat := by
  show ((x.1 ^^^ y.1).toNat <<< 64) ||| (x.2 ^^^ y.2).toNat = _
  rw [UInt64.toNat_xor, UInt64.toNat_xor]
  exact (Nat.xor_or_shiftLeft (UInt64.toNat_lt x.2)
    (UInt64.toNat_lt y.2)).symm

theorem B256.toNat_xor (x y : B256) :
    (x ^^^ y).toNat = x.toNat ^^^ y.toNat := by
  show ((x.1 ^^^ y.1).toNat <<< 128) ||| (x.2 ^^^ y.2).toNat = _
  rw [B128.toNat_xor, B128.toNat_xor]
  exact (Nat.xor_or_shiftLeft (B128.toNat_lt (x := x.2))
    (B128.toNat_lt (x := y.2))).symm

/-! ## High-word folding after power-of-two division -/

/-- Dividing both words by a common power-of-two factor and shifting the high
word into the vacated low bits reconstructs division of the exact two-word
number, modulo the word width. -/
theorem Nat.fold_divided_words
    {width high low twos : Nat}
    (twosPositive : 0 < twos)
    (twosDvdModulus : twos ∣ 2 ^ width)
    (twosDvdLow : twos ∣ low)
    (lowBound : low < 2 ^ width) :
    low / twos ||| (high * (2 ^ width / twos) % 2 ^ width) =
      (high * 2 ^ width + low) / twos % 2 ^ width := by
  let modulus := 2 ^ width
  let factor := modulus / twos
  let lowQuotient := low / twos
  have modulusPositive : 0 < modulus := by
    simp [modulus]
  have factorPositive : 0 < factor := by
    unfold factor
    exact Nat.div_pos
      (Nat.le_of_dvd modulusPositive twosDvdModulus) twosPositive
  have factorMulTwos : factor * twos = modulus := by
    exact Nat.div_mul_cancel twosDvdModulus
  have factorDvdModulus : factor ∣ modulus := by
    exact ⟨twos, factorMulTwos.symm⟩
  obtain ⟨shift, -, factorEq⟩ :=
    (Nat.dvd_prime_pow Nat.prime_two).mp
      (show factor ∣ 2 ^ width by
        simpa [modulus] using factorDvdModulus)
  have lowQuotientLtFactor : lowQuotient < factor := by
    exact (Nat.div_lt_div_right (Nat.ne_of_gt twosPositive)
      twosDvdLow twosDvdModulus).2 lowBound
  let shifted := high * factor % modulus
  have factorDvdShifted : factor ∣ shifted := by
    apply (Nat.dvd_mod_iff factorDvdModulus).2
    exact Nat.dvd_mul_left factor high
  obtain ⟨shiftedHigh, shiftedEq⟩ := factorDvdShifted
  have shiftedBound : shifted < modulus := by
    exact Nat.mod_lt _ modulusPositive
  have shiftedHighLtTwos : shiftedHigh < twos := by
    rw [shiftedEq, ← factorMulTwos] at shiftedBound
    exact (Nat.mul_lt_mul_left factorPositive).mp shiftedBound
  have sumBound : shifted + lowQuotient < modulus := by
    rw [shiftedEq, ← factorMulTwos]
    calc
      factor * shiftedHigh + lowQuotient <
          factor * shiftedHigh + factor :=
        Nat.add_lt_add_left lowQuotientLtFactor _
      _ = factor * (shiftedHigh + 1) := by
        rw [Nat.mul_add, Nat.mul_one]
      _ ≤ factor * twos :=
        Nat.mul_le_mul_left factor (by omega)
  have orEq : lowQuotient ||| shifted = shifted + lowQuotient := by
    calc
      lowQuotient ||| shifted = shifted ||| lowQuotient :=
        Nat.or_comm _ _
      _ = factor * shiftedHigh ||| lowQuotient := by rw [shiftedEq]
      _ = 2 ^ shift * shiftedHigh ||| lowQuotient := by rw [factorEq]
      _ = 2 ^ shift * shiftedHigh + lowQuotient :=
        (Nat.two_pow_add_eq_or_of_lt
          (by simpa [factorEq] using lowQuotientLtFactor)
          shiftedHigh).symm
      _ = shifted + lowQuotient := by rw [shiftedEq, factorEq]
  have quotientEq :
      (high * modulus + low) / twos =
        high * factor + lowQuotient := by
    rw [Nat.add_div_of_dvd_left twosDvdLow,
      Nat.mul_div_assoc high twosDvdModulus]
  change lowQuotient ||| shifted =
    (high * modulus + low) / twos % modulus
  rw [orEq, quotientEq, Nat.add_mod]
  change shifted + lowQuotient =
    (shifted + lowQuotient % modulus) % modulus
  rw [Nat.mod_eq_of_lt (lowQuotientLtFactor.trans_le
      (Nat.le_of_dvd modulusPositive factorDvdModulus))]
  exact (Nat.mod_eq_of_lt sumBound).symm

/-- Fold a divided low word and the complementary shifted high word into one
word, matching the full-width division algorithm. -/
def foldDividedWords (high low twos : B256) : B256 :=
  (low / twos) ||| (high * wordModulusDivFactorWord twos)

theorem foldDividedWords_toNat
    {high low twos : B256}
    (twosNonzero : twos ≠ B256.zero)
    (twosDvdModulus : twos.toNat ∣ wordModulusN)
    (twosDvdLow : twos.toNat ∣ low.toNat) :
    (foldDividedWords high low twos).toNat =
      wideNumeratorN high low / twos.toNat % wordModulusN := by
  have twosPositive : 0 < twos.toNat := by
    by_contra notPositive
    have twosZero : twos.toNat = 0 := by omega
    apply twosNonzero
    exact B256.toNat_inj twos B256.zero
      (twosZero.trans (show 0 = B256.zero.toNat by rfl))
  rw [foldDividedWords, B256.toNat_or,
    B256.toNat_div twosNonzero, B256.toNat_mul_mod,
    wordModulusDivFactorWord_toNat twosNonzero]
  have folded := Nat.fold_divided_words
    (width := 256) (high := high.toNat) (low := low.toNat)
    (twos := twos.toNat) twosPositive
    (by simpa [wordModulusN] using twosDvdModulus)
    twosDvdLow (B256.toNat_lt low)
  simpa [wideNumeratorN, wordModulusN, Nat.mul_mod,
    Nat.mod_mod] using folded

/-- Low word of the exact numerator after subtracting its denominator
remainder. -/
def wideReducedLowWord (high low denominator : B256) : B256 :=
  wideSubLowWord low (wideRemainderWord high low denominator)

/-- High word of the exact numerator after subtracting its denominator
remainder and propagating the low-word borrow. -/
def wideReducedHighWord (high low denominator : B256) : B256 :=
  wideSubHighWord high low (wideRemainderWord high low denominator)

/-- Exact natural numerator after remainder subtraction. -/
def wideReducedNumeratorN (high low denominator : B256) : Nat :=
  wideNumeratorN high low - (wideRemainderWord high low denominator).toNat

theorem wideReducedWords_reconstruct
    {high low denominator : B256} (nonzero : denominator ≠ B256.zero) :
    (wideReducedHighWord high low denominator).toNat * wordModulusN +
        (wideReducedLowWord high low denominator).toNat =
      wideReducedNumeratorN high low denominator := by
  unfold wideReducedHighWord wideReducedLowWord wideReducedNumeratorN
  apply wideSubWords_reconstruct
  exact wideRemainderWord_le_numerator nonzero

theorem denominator_dvd_wideReducedNumerator
    {high low denominator : B256} (nonzero : denominator ≠ B256.zero) :
    denominator.toNat ∣ wideReducedNumeratorN high low denominator := by
  apply Nat.dvd_of_mod_eq_zero
  exact wideNumerator_sub_remainder_mod_eq_zero nonzero

/-- The denominator's isolated power-of-two factor also divides the reduced
low word; this is what makes the compiled word division exact. -/
theorem lowestSetBitWord_dvd_wideReducedLow
    {high low denominator : B256} (nonzero : denominator ≠ B256.zero) :
    (lowestSetBitWord denominator).toNat ∣
      (wideReducedLowWord high low denominator).toNat := by
  have spec := lowestSetBitWord_spec nonzero
  have twosDvdReduced : (lowestSetBitWord denominator).toNat ∣
      wideReducedNumeratorN high low denominator :=
    spec.2.1.trans (denominator_dvd_wideReducedNumerator nonzero)
  have twosDvdHigh : (lowestSetBitWord denominator).toNat ∣
      (wideReducedHighWord high low denominator).toNat * wordModulusN :=
    Nat.dvd_mul_left_of_dvd spec.2.2.1 _
  have reconstruct := wideReducedWords_reconstruct
    (high := high) (low := low) nonzero
  have highLe :
      (wideReducedHighWord high low denominator).toNat * wordModulusN ≤
        wideReducedNumeratorN high low denominator := by
    rw [← reconstruct]
    exact Nat.le_add_right _ _
  have lowEq :
      (wideReducedLowWord high low denominator).toNat =
        wideReducedNumeratorN high low denominator -
          (wideReducedHighWord high low denominator).toNat *
            wordModulusN := by
    omega
  rw [lowEq]
  exact Nat.dvd_sub twosDvdReduced twosDvdHigh

/-- Exact folded dividend produced after factoring powers of two out of the
denominator and reduced numerator. -/
def wideFoldedDividendWord (high low denominator : B256) : B256 :=
  foldDividedWords
    (wideReducedHighWord high low denominator)
    (wideReducedLowWord high low denominator)
    (lowestSetBitWord denominator)

theorem wideFoldedDividendWord_toNat
    {high low denominator : B256} (nonzero : denominator ≠ B256.zero) :
    (wideFoldedDividendWord high low denominator).toNat =
      wideReducedNumeratorN high low denominator /
          (lowestSetBitWord denominator).toNat % wordModulusN := by
  have spec := lowestSetBitWord_spec nonzero
  rw [wideFoldedDividendWord, foldDividedWords_toNat
    (lowestSetBitWord_ne_zero nonzero) spec.2.2.1
    (lowestSetBitWord_dvd_wideReducedLow nonzero)]
  rw [wideNumeratorN, wideReducedWords_reconstruct nonzero]

/-! ## Newton inverse refinement -/

/-- The four-bit inverse seed used by full-width unsigned division. -/
def inverseSeedWord (denominator : B256) : B256 :=
  3 * denominator ^^^ 2

/-- One Newton refinement in the EVM word ring. -/
def inverseNewtonStepWord (denominator inverse : B256) : B256 :=
  inverse * (2 - inverse * denominator)

/-- Repeated Newton refinement in the EVM word ring. -/
def inverseNewtonIter (denominator : B256) : Nat → B256 → B256
  | 0, inverse => inverse
  | count + 1, inverse =>
      inverseNewtonIter denominator count
        (inverseNewtonStepWord denominator inverse)

/-- A Newton inverse step squares the modulus on which the inverse is known. -/
theorem newtonStep_modEq_square
    (denominator inverse modulus : Int)
    (inverseCorrect :
      denominator * inverse ≡ 1 [ZMOD modulus]) :
    denominator * (inverse * (2 - denominator * inverse)) ≡ 1
      [ZMOD modulus * modulus] := by
  rw [Int.modEq_iff_dvd] at inverseCorrect ⊢
  rcases inverseCorrect with ⟨factor, factorEq⟩
  refine ⟨factor * factor, ?_⟩
  rw [show
      1 - denominator * (inverse * (2 - denominator * inverse)) =
        (1 - denominator * inverse) * (1 - denominator * inverse) by
      ring,
    factorEq]
  ring

/-- Word multiplication agrees with unbounded multiplication modulo the EVM
word modulus. -/
theorem b256_mul_modEq_wordModulus (x y : B256) :
    ((x * y).toNat : Int) ≡
      (x.toNat * y.toNat : Nat)
      [ZMOD (wordModulusN : Int)] := by
  rw [Int.natCast_modEq_iff]
  rw [B256.toNat_mul_mod]
  exact Nat.mod_modEq _ _

/-- Word subtraction agrees with integer subtraction modulo the EVM word
modulus, including the wrapped branch. -/
theorem b256_sub_modEq_wordModulus (x y : B256) :
    ((x - y).toNat : Int) ≡
      (x.toNat : Int) - (y.toNat : Int)
      [ZMOD (wordModulusN : Int)] := by
  rw [Int.modEq_iff_dvd]
  by_cases h : y ≤ x
  · have hnat : y.toNat ≤ x.toNat := B256.toNat_le_toNat h
    rw [B256.toNat_sub_eq_of_le x y h, Nat.cast_sub hnat]
    simp
  · have hltWord : x < y := B256.not_le.mp h
    have hlt : x.toNat < y.toNat := B256.toNat_lt_toNat hltWord
    have hsum : y.toNat ≤ wordModulusN + x.toNat := by
      have yBound := B256.toNat_lt y
      unfold wordModulusN
      omega
    have hbound :
        wordModulusN + x.toNat - y.toNat < wordModulusN := by
      omega
    rw [B256.toNat_sub]
    change (wordModulusN : Int) ∣
      (x.toNat : Int) - (y.toNat : Int) -
        ↑((wordModulusN + x.toNat - y.toNat) ↾ 256)
    rw [Nat.lo_eq_of_lt hbound, Nat.cast_sub hsum, Nat.cast_add]
    ring_nf
    exact Int.dvd_neg.mpr (dvd_refl (wordModulusN : Int))

/-- The exact word update represents the algebraic Newton update modulo
`2^256`. -/
theorem inverseNewtonStepWord_modEq_wordModulus
    (denominator inverse : B256) :
    ((inverseNewtonStepWord denominator inverse).toNat : Int) ≡
      (inverse.toNat : Int) *
        (2 - (inverse.toNat : Int) * (denominator.toNat : Int))
      [ZMOD (wordModulusN : Int)] := by
  have product := b256_mul_modEq_wordModulus inverse denominator
  have difference :=
    b256_sub_modEq_wordModulus (2 : B256) (inverse * denominator)
  have two : ((2 : B256).toNat : Int) = 2 := rfl
  have difference' :
      (((2 : B256) - inverse * denominator).toNat : Int) ≡
        2 - (inverse.toNat : Int) * (denominator.toNat : Int)
        [ZMOD (wordModulusN : Int)] := by
    apply difference.trans
    rw [two]
    exact (Int.ModEq.refl 2).sub product
  unfold inverseNewtonStepWord
  exact (b256_mul_modEq_wordModulus inverse
      ((2 : B256) - inverse * denominator)).trans
    ((Int.ModEq.refl (inverse.toNat : Int)).mul difference')

/-- A word-level Newton step squares any correctness modulus whose square
divides the EVM word modulus. -/
theorem inverseNewtonStepWord_modEq_square
    {denominator inverse : B256} {modulus : Int}
    (squareDvdWord : modulus * modulus ∣ (wordModulusN : Int))
    (inverseCorrect :
      (denominator.toNat : Int) * (inverse.toNat : Int) ≡ 1
        [ZMOD modulus]) :
    (denominator.toNat : Int) *
        ((inverseNewtonStepWord denominator inverse).toNat : Int) ≡ 1
      [ZMOD modulus * modulus] := by
  have stepCongruence :=
    (inverseNewtonStepWord_modEq_wordModulus denominator inverse).of_dvd
      squareDvdWord
  have lifted :=
    (Int.ModEq.refl (denominator.toNat : Int)).mul stepCongruence
  apply lifted.trans
  simpa [Int.mul_comm (inverse.toNat : Int) (denominator.toNat : Int)] using
    newtonStep_modEq_square (denominator.toNat : Int)
      (inverse.toNat : Int) modulus inverseCorrect

/-- Six word-level Newton refinements lift a four-bit inverse seed to a full
inverse modulo `2^256`. -/
theorem inverseNewtonIter_six_modEq
    {denominator seed : B256}
    (seedCorrect :
      (denominator.toNat : Int) * (seed.toNat : Int) ≡ 1 [ZMOD 16]) :
    (denominator.toNat : Int) *
        ((inverseNewtonIter denominator 6 seed).toNat : Int) ≡ 1
      [ZMOD (wordModulusN : Int)] := by
  have h1 := inverseNewtonStepWord_modEq_square
    (denominator := denominator) (inverse := seed) (modulus := 16)
    (by norm_num [wordModulusN]) seedCorrect
  have h2 := inverseNewtonStepWord_modEq_square
    (denominator := denominator)
    (inverse := inverseNewtonStepWord denominator seed)
    (modulus := 256) (by norm_num [wordModulusN]) h1
  have h3 := inverseNewtonStepWord_modEq_square
    (denominator := denominator)
    (inverse := inverseNewtonStepWord denominator
      (inverseNewtonStepWord denominator seed))
    (modulus := 65536) (by norm_num [wordModulusN]) h2
  have h4 := inverseNewtonStepWord_modEq_square
    (denominator := denominator)
    (inverse := inverseNewtonStepWord denominator
      (inverseNewtonStepWord denominator
        (inverseNewtonStepWord denominator seed)))
    (modulus := 4294967296) (by norm_num [wordModulusN]) h3
  have h5 := inverseNewtonStepWord_modEq_square
    (denominator := denominator)
    (inverse := inverseNewtonStepWord denominator
      (inverseNewtonStepWord denominator
        (inverseNewtonStepWord denominator
          (inverseNewtonStepWord denominator seed))))
    (modulus := 18446744073709551616)
    (by norm_num [wordModulusN]) h4
  have h6 := inverseNewtonStepWord_modEq_square
    (denominator := denominator)
    (inverse := inverseNewtonStepWord denominator
      (inverseNewtonStepWord denominator
        (inverseNewtonStepWord denominator
          (inverseNewtonStepWord denominator
            (inverseNewtonStepWord denominator seed)))))
    (modulus := 340282366920938463463374607431768211456)
    (by norm_num [wordModulusN]) h5
  simpa [inverseNewtonIter, wordModulusN] using h6

private theorem inverseSeedNat_mod_sixteen
    (n : Nat) (odd : n % 2 = 1) :
    (n * ((3 * n) ^^^ 2)) % 16 = 1 := by
  have h16 : n % 16 < 16 := Nat.mod_lt _ (by omega)
  have hodd16 : (n % 16) % 2 = 1 := by
    rw [Nat.mod_mod_of_dvd n (by omega : 2 ∣ 16)]
    exact odd
  rw [Nat.mul_mod n ((3 * n) ^^^ 2) 16]
  rw [show 16 = 2 ^ 4 by norm_num, Nat.xor_mod_two_pow]
  rw [← show 16 = 2 ^ 4 by norm_num]
  rw [Nat.mul_mod 3 n 16]
  change
    (n % 16 * (((3 * (n % 16)) % 16) ^^^ 2)) % 16 = 1
  generalize n % 16 = r at h16 hodd16 ⊢
  have hr :
      r = 1 ∨ r = 3 ∨ r = 5 ∨ r = 7 ∨
      r = 9 ∨ r = 11 ∨ r = 13 ∨ r = 15 := by
    omega
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    decide

private theorem inverseSeedWord_mod_sixteen (denominator : B256) :
    (inverseSeedWord denominator).toNat % 16 =
      ((3 * denominator.toNat) ^^^ 2) % 16 := by
  unfold inverseSeedWord
  rw [B256.toNat_xor, B256.toNat_mul_mod]
  change
    ((((3 * denominator.toNat) % (2 ^ 256)) ^^^ 2) % (2 ^ 4)) =
      (((3 * denominator.toNat) ^^^ 2) % (2 ^ 4))
  simp only [Nat.xor_mod_two_pow]
  rw [Nat.mod_mod_of_dvd]
  norm_num

/-- For every odd word, `(3 * denominator) xor 2` is an inverse modulo
`16`. -/
theorem inverseSeedWord_modEq_sixteen
    {denominator : B256} (odd : denominator.toNat % 2 = 1) :
    (denominator.toNat : Int) *
        ((inverseSeedWord denominator).toNat : Int) ≡ 1 [ZMOD 16] := by
  change
    ((denominator.toNat *
      (inverseSeedWord denominator).toNat : Nat) : Int) ≡
        ((1 : Nat) : Int) [ZMOD ((16 : Nat) : Int)]
  rw [Int.natCast_modEq_iff]
  change
    (denominator.toNat * (inverseSeedWord denominator).toNat) % 16 = 1
  rw [Nat.mul_mod]
  rw [inverseSeedWord_mod_sixteen]
  have h := inverseSeedNat_mod_sixteen denominator.toNat odd
  rw [Nat.mul_mod denominator.toNat
    ((3 * denominator.toNat) ^^^ 2) 16] at h
  exact h

/-- Six Newton refinements of the standard seed invert any odd EVM word
modulo the full word modulus. -/
theorem inverseNewtonIter_six_seed_modEq_wordModulus
    {denominator : B256} (odd : denominator.toNat % 2 = 1) :
    (denominator.toNat : Int) *
        ((inverseNewtonIter denominator 6
          (inverseSeedWord denominator)).toNat : Int) ≡ 1
      [ZMOD (wordModulusN : Int)] :=
  inverseNewtonIter_six_modEq (inverseSeedWord_modEq_sixteen odd)

/-! ## Exact full-width quotient -/

/-- The single-word quotient produced by remainder reduction, power-of-two
factor folding, and six Newton inverse refinements. -/
def wideQuotientWord (high low denominator : B256) : B256 :=
  wideFoldedDividendWord high low denominator *
    inverseNewtonIter
      (removeLowestSetBitWord denominator) 6
      (inverseSeedWord (removeLowestSetBitWord denominator))

/-- The standard full-width word algorithm returns the exact floor quotient
whenever its branch guard `high < denominator` establishes that the quotient
fits in one EVM word. -/
theorem wideQuotientWord_toNat
    {high low denominator : B256}
    (nonzero : denominator ≠ B256.zero)
    (noOverflow : high < denominator) :
    (wideQuotientWord high low denominator).toNat =
      wideNumeratorN high low / denominator.toNat := by
  let twos := (lowestSetBitWord denominator).toNat
  let reducedDenominator := removeLowestSetBitWord denominator
  let inverse := inverseNewtonIter reducedDenominator 6
    (inverseSeedWord reducedDenominator)
  let quotient := wideNumeratorN high low / denominator.toNat
  have twosSpec := lowestSetBitWord_spec nonzero
  have reducedDivision :
      wideReducedNumeratorN high low denominator / twos =
        quotient * reducedDenominator.toNat := by
    have factored := Nat.sub_mod_div_factor
      (n := wideNumeratorN high low) (d := denominator.toNat)
      (twos := twos) twosSpec.1 twosSpec.2.1
    simpa [twos, reducedDenominator, quotient,
      wideReducedNumeratorN, wideRemainderWord_toNat nonzero,
      removeLowestSetBitWord_toNat nonzero] using factored
  have foldedMod :
      (wideFoldedDividendWord high low denominator).toNat ≡
        quotient * reducedDenominator.toNat [MOD wordModulusN] := by
    rw [wideFoldedDividendWord_toNat nonzero, reducedDivision]
    exact Nat.mod_modEq _ _
  have inverseCorrect :
      reducedDenominator.toNat * inverse.toNat ≡
        1 [MOD wordModulusN] := by
    rw [← Int.natCast_modEq_iff]
    exact inverseNewtonIter_six_seed_modEq_wordModulus
      (removeLowestSetBitWord_odd nonzero)
  have productMod :
      (wideFoldedDividendWord high low denominator).toNat *
          inverse.toNat ≡ quotient [MOD wordModulusN] := by
    calc
      (wideFoldedDividendWord high low denominator).toNat *
          inverse.toNat ≡
        (quotient * reducedDenominator.toNat) * inverse.toNat
          [MOD wordModulusN] :=
          foldedMod.mul (Nat.ModEq.refl _)
      _ = quotient * (reducedDenominator.toNat * inverse.toNat) := by
        ring
      _ ≡ quotient * 1 [MOD wordModulusN] :=
        (Nat.ModEq.refl quotient).mul inverseCorrect
      _ = quotient := by simp
  have outputMod :
      (wideQuotientWord high low denominator).toNat ≡
        quotient [MOD wordModulusN] := by
    rw [wideQuotientWord, B256.toNat_mul_mod]
    exact (Nat.mod_modEq _ _).trans productMod
  have quotientBound : quotient < wordModulusN := by
    unfold quotient wideNumeratorN wordModulusN
    exact Nat.two_word_div_lt_modulus
      (B256.toNat_lt low) (B256.toNat_lt_toNat noOverflow)
  have outputBound :
      (wideQuotientWord high low denominator).toNat < wordModulusN := by
    simpa [wordModulusN] using
      B256.toNat_lt (wideQuotientWord high low denominator)
  exact Nat.ModEq.eq_of_lt_of_lt outputMod outputBound quotientBound

end Blanc
