import Blanc.BeaconDepositModel

/-!
# Beacon deposit model — combined invariant and algorithm correctness

The combined invariant `Inv` relates the accumulator state (branch slots and
count) to the leaf-list history, and the theorems here prove the pinned
algorithms correct against the naive reference `rootOf`/`mixedRootOf`:

* `empty_inv`, `empty_root` — the fresh contract satisfies the invariant and
  yields the reference empty root;
* `insert_spec` — under the exact source precondition
  `count < 2 ^ 32 - 1`, insertion succeeds, preserves the invariant, and
  appends exactly one leaf to the abstraction;
* `root_correct` — root computation from any invariant-satisfying state
  equals the reference mixed root of its leaf list;
* `walk_none_at_cap` / `insert_isSome_iff` — the `2 ^ 32 - 1` cap is exactly
  the boundary at which the insert walk's live-slot existence fails;
* `deposit_ne_assert_false` — the source's terminal `assert(false)` is
  unreachable;
* the B3 exactness lemmas (encoding lengths and the 64-byte width of every
  hash-call input).

Everything is stated over the abstract hash `H : Bytes → B256`; no property
of any concrete hash is used anywhere.
-/

namespace Blanc.BeaconDeposit

open Jaune

/-! ## Generic arithmetic helpers -/

/-- `n / m * m` recovers the aligned prefix `n - n % m`. -/
theorem div_mul_eq_sub_mod (n m : Nat) : n / m * m = n - n % m := by
  have h := Nat.div_add_mod n m
  have : m * (n / m) = n / m * m := Nat.mul_comm _ _
  omega

/-- Decrementing inside a nonzero residue class does not change the
quotient. -/
theorem pred_div_eq (m b : Nat) (h : 0 < m % b) : (m - 1) / b = m / b := by
  rcases Nat.eq_zero_or_pos b with hb | hb
  · subst hb; simp
  · have hd := Nat.div_add_mod m b
    have hlt : m % b < b := Nat.mod_lt _ hb
    have hcomm : b * (m / b) = m / b * b := Nat.mul_comm _ _
    apply Nat.div_eq_of_lt_le
    · omega
    · have hsucc : (m / b + 1) * b = m / b * b + b := Nat.succ_mul _ _
      omega

/-- Decrementing inside a nonzero residue class decrements the residue. -/
theorem pred_mod_of_pos (m b : Nat) (h : 0 < m % b) : (m - 1) % b = m % b - 1 := by
  rcases Nat.eq_zero_or_pos b with hb | hb
  · subst hb; simp
  · have hd := Nat.div_add_mod m b
    have hlt : m % b < b := Nat.mod_lt _ hb
    have hsplit : m - 1 = b * (m / b) + (m % b - 1) := by omega
    rw [hsplit, Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt (by omega)

/-- Decrementing a multiple of `b` lands on residue `b - 1`. -/
theorem pred_mod_eq (m b : Nat) (hm : 0 < m) (hb : 1 < b) (h : m % b = 0) :
    (m - 1) % b = b - 1 := by
  have hd := Nat.div_add_mod m b
  have hq : 0 < m / b := by
    rcases Nat.eq_zero_or_pos (m / b) with hq | hq
    · rw [hq] at hd; omega
    · exact hq
  have hble : b * 1 ≤ b * (m / b) := Nat.mul_le_mul_left b hq
  have hms : b * (m / b - 1) = b * (m / b) - b := by
    rw [Nat.mul_sub_one]
  have hsplit : m - 1 = b * (m / b - 1) + (b - 1) := by omega
  rw [hsplit, Nat.mul_add_mod]
  exact Nat.mod_eq_of_lt (by omega)

/-- The division-form bit of `m` at position `j` is untouched by the
decrement `m - 1` as long as the residue below `j` is nonzero. -/
theorem pred_div_pow_eq (m h j : Nat) (hj : h + 1 ≤ j) (hm : 0 < m % 2 ^ (h + 1)) :
    (m - 1) / 2 ^ j = m / 2 ^ j := by
  have hsplit : 2 ^ j = 2 ^ (h + 1) * 2 ^ (j - (h + 1)) := by
    rw [← Nat.pow_add]
    congr 1
    omega
  rw [hsplit, ← Nat.div_div_eq_div_mul, ← Nat.div_div_eq_div_mul,
    pred_div_eq _ _ hm]

/-- All division-form bits below `k` vanish exactly when `m % 2 ^ k = 0`. -/
theorem mod_two_pow_eq_zero_iff (m k : Nat) :
    m % 2 ^ k = 0 ↔ ∀ j, j < k → m / 2 ^ j % 2 = 0 := by
  induction k with
  | zero => simp [Nat.mod_one]
  | succ k ih =>
      rw [Nat.mod_pow_succ]
      constructor
      · intro h j hj
        have h1 : m % 2 ^ k = 0 := by omega
        have h2 : 2 ^ k * (m / 2 ^ k % 2) = 0 := by omega
        rcases Nat.mul_eq_zero.mp h2 with h2 | h2
        · exact absurd h2 (Nat.pos_iff_ne_zero.mp (Nat.two_pow_pos k))
        · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
          · exact ih.mp h1 j hj
          · rw [hj]; exact h2
      · intro h
        have h1 : m % 2 ^ k = 0 := ih.mpr fun j hj => h j (by omega)
        have h2 : m / 2 ^ k % 2 = 0 := h k (Nat.lt_succ_self k)
        rw [h1, h2, Nat.mul_zero]

/-! ## Reference-root basics -/

theorem rootAt_nil (H : Bytes → B256) (d : Nat) :
    rootAt H d [] = zeroHash H d := by
  induction d with
  | zero => rfl
  | succ d ih => simp only [rootAt, List.take_nil, List.drop_nil, ih, zeroHash]

/-- A list within the capacity of the left half roots against a zero right
half. -/
theorem rootAt_short (H : Bytes → B256) (d : Nat) (ls : List B256)
    (h : ls.length ≤ 2 ^ d) :
    rootAt H (d + 1) ls = hashPair H (rootAt H d ls) (zeroHash H d) := by
  simp only [rootAt]
  rw [List.take_of_length_le h, List.drop_eq_nil_of_le h, rootAt_nil]

/-- Evaluation-oriented derived form of `rootAt`: identical except that an
empty subtree short-circuits to its zero hash instead of recursing both
halves (the primary spec's double recursion is exponential to *evaluate*
on empty subtrees; it is the clean statement, this is the runnable one).
Proved equal below; the vector-check evaluator uses this form. -/
def rootAtE (H : Bytes → B256) : Nat → List B256 → B256
  | 0, ls => ls.headD 0
  | d + 1, ls =>
      if ls.isEmpty then zeroHash H (d + 1)
      else hashPair H (rootAtE H d (ls.take (2 ^ d))) (rootAtE H d (ls.drop (2 ^ d)))

/-- The derived evaluator computes exactly the reference root. -/
theorem rootAtE_eq (H : Bytes → B256) : ∀ (d : Nat) (ls : List B256),
    rootAtE H d ls = rootAt H d ls := by
  intro d
  induction d with
  | zero => intro ls; rfl
  | succ d ih =>
      intro ls
      rcases ls with - | ⟨x, xs⟩
      · show zeroHash H (d + 1) = rootAt H (d + 1) []
        rw [rootAt_nil]
      · show hashPair H (rootAtE H d ((x :: xs).take (2 ^ d)))
            (rootAtE H d ((x :: xs).drop (2 ^ d))) = rootAt H (d + 1) (x :: xs)
        rw [ih, ih]
        simp only [rootAt]

/-- An exact left half splits the reference root. -/
theorem rootAt_append (H : Bytes → B256) (d : Nat) (xs ys : List B256)
    (h : xs.length = 2 ^ d) :
    rootAt H (d + 1) (xs ++ ys) = hashPair H (rootAt H d xs) (rootAt H d ys) := by
  simp only [rootAt]
  rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega),
    List.drop_append_of_le_length (by omega), List.drop_eq_nil_of_le (by omega),
    List.nil_append]

/-! ## The combined invariant -/

/-- The completed (fully populated) aligned block of `2 ^ h` leaves that
`branch[h]` roots while bit `h` of the count is set: it starts at the largest
multiple of `2 ^ (h + 1)` not exceeding the count. -/
def completedBlock (h n : Nat) (ls : List B256) : List B256 :=
  (ls.drop (n / 2 ^ (h + 1) * 2 ^ (h + 1))).take (2 ^ h)

/-- The pending partial block at height `h`: the trailing `n % 2 ^ h`
leaves. -/
def pending (h n : Nat) (ls : List B256) : List B256 :=
  ls.drop (n - n % 2 ^ h)

/-- The combined invariant: the count is the leaf-list length, the history
fits the tree, and every live branch slot roots its completed block. -/
def Inv (H : Bytes → B256) (s : Acc) (ls : List B256) : Prop :=
  s.count = ls.length ∧ ls.length < 2 ^ 32 ∧
  ∀ h, h < 32 → s.count / 2 ^ h % 2 = 1 →
    s.branch h = rootAt H h (completedBlock h s.count ls)

/-- The empty seed satisfies the invariant. -/
theorem empty_inv (H : Bytes → B256) : Inv H Acc.empty [] := by
  refine ⟨rfl, by simp, fun h _ hbit => ?_⟩
  simp [Acc.empty, Nat.zero_div] at hbit

/-! ## Root-computation correctness -/

/-- A dead bit leaves the pending block unchanged one level up. -/
theorem pending_step_even (h n : Nat) (ls : List B256)
    (hb : n / 2 ^ h % 2 = 0) :
    pending (h + 1) n ls = pending h n ls := by
  unfold pending
  have : n % 2 ^ (h + 1) = n % 2 ^ h := by
    rw [Nat.mod_pow_succ, hb, Nat.mul_zero, Nat.add_zero]
  rw [this]

/-- A live bit splits the pending block one level up into the completed
block and the current pending block. -/
theorem pending_step_odd (h n : Nat) (ls : List B256) (hlen : ls.length = n)
    (hb : n / 2 ^ h % 2 = 1) :
    pending (h + 1) n ls = completedBlock h n ls ++ pending h n ls ∧
    (completedBlock h n ls).length = 2 ^ h := by
  have hmod : n % 2 ^ (h + 1) = n % 2 ^ h + 2 ^ h := by
    rw [Nat.mod_pow_succ, hb, Nat.mul_one]
  have hmodle : n % 2 ^ (h + 1) ≤ n := Nat.mod_le n _
  have hmodle' : n % 2 ^ h ≤ n := Nat.mod_le n _
  have hle : n % 2 ^ h + 2 ^ h ≤ n := hmod ▸ hmodle
  have hstart : n / 2 ^ (h + 1) * 2 ^ (h + 1) = n - (n % 2 ^ h + 2 ^ h) := by
    rw [div_mul_eq_sub_mod, hmod]
  constructor
  · unfold pending completedBlock
    rw [hstart, hmod]
    conv_lhs => rw [← List.take_append_drop (2 ^ h) (ls.drop (n - (n % 2 ^ h + 2 ^ h)))]
    congr 1
    rw [List.drop_drop]
    congr 1
    omega
  · unfold completedBlock
    rw [List.length_take, List.length_drop, hstart, hlen]
    omega

/-- Dead-bit step of the fold: the next node hashes against the zero
subtree. -/
theorem rootAt_pending_even (H : Bytes → B256) (h n : Nat) (ls : List B256)
    (hlen : ls.length = n) (hb : n / 2 ^ h % 2 = 0) :
    rootAt H (h + 1) (pending (h + 1) n ls)
      = hashPair H (rootAt H h (pending h n ls)) (zeroHash H h) := by
  rw [pending_step_even h n ls hb]
  apply rootAt_short
  unfold pending
  rw [List.length_drop, hlen]
  have := Nat.mod_lt n (Nat.two_pow_pos h)
  have := Nat.mod_le n (2 ^ h)
  omega

/-- Live-bit step of the fold: the next node hashes the completed block's
root against the pending root. -/
theorem rootAt_pending_odd (H : Bytes → B256) (h n : Nat) (ls : List B256)
    (hlen : ls.length = n) (hb : n / 2 ^ h % 2 = 1) :
    rootAt H (h + 1) (pending (h + 1) n ls)
      = hashPair H (rootAt H h (completedBlock h n ls))
          (rootAt H h (pending h n ls)) := by
  obtain ⟨hsplit, hlenb⟩ := pending_step_odd h n ls hlen hb
  rw [hsplit, rootAt_append H h _ _ hlenb]

/-- The fold's loop invariant: starting at height `h` with the pending root
and the shifted count, `k` more iterations reach the reference root of the
whole list, provided the list fits and every live slot in range roots its
completed block. -/
theorem climb_spec (H : Bytes → B256) (ls : List B256) :
    ∀ (k h : Nat) (br : Nat → B256),
      ls.length < 2 ^ (h + k) →
      (∀ h', h ≤ h' → h' < h + k → ls.length / 2 ^ h' % 2 = 1 →
        br h' = rootAt H h' (completedBlock h' ls.length ls)) →
      climb H br k h (ls.length / 2 ^ h) (rootAt H h (pending h ls.length ls))
        = rootAt H (h + k) ls := by
  intro k
  induction k with
  | zero =>
      intro h br hlt _
      have hmod : ls.length % 2 ^ h = ls.length :=
        Nat.mod_eq_of_lt (by simpa using hlt)
      simp only [climb, pending, hmod, Nat.sub_self, List.drop_zero,
        Nat.add_zero]
  | succ k ih =>
      intro h br hlt hbr
      simp only [climb]
      have hsize : ls.length / 2 ^ h / 2 = ls.length / 2 ^ (h + 1) := by
        rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ]
      have harith : h + (k + 1) = (h + 1) + k := by omega
      rcases Nat.mod_two_eq_zero_or_one (ls.length / 2 ^ h) with hb | hb
      · rw [if_neg (by omega), hsize,
          ← rootAt_pending_even H h ls.length ls rfl hb, harith]
        exact ih (h + 1) br (harith ▸ hlt)
          (fun h' h1 h2 => hbr h' (by omega) (by omega))
      · rw [if_pos hb, hbr h le_rfl (by omega) hb, hsize,
          ← rootAt_pending_odd H h ls.length ls rfl hb, harith]
        exact ih (h + 1) br (harith ▸ hlt)
          (fun h' h1 h2 => hbr h' (by omega) (by omega))

/-- Root computation from any invariant-satisfying state equals the
reference mixed root of its leaf list. -/
theorem root_correct (H : Bytes → B256) (s : Acc) (ls : List B256)
    (hInv : Inv H s ls) : Acc.root H s = mixedRootOf H ls := by
  obtain ⟨hc, hlt, hbr⟩ := hInv
  have h0 : ls.length / 2 ^ 0 = ls.length := by simp
  have hpend : rootAt H 0 (pending 0 ls.length ls) = 0 := by
    have hnil : pending 0 ls.length ls = ([] : List B256) := by
      unfold pending
      rw [Nat.pow_zero, Nat.mod_one, Nat.sub_zero, List.drop_length]
    rw [hnil, rootAt_nil]
    rfl
  have hclimb := climb_spec H ls 32 0 s.branch (by simpa using hc ▸ hlt)
    (fun h' _ h2 hbit => hc ▸ hbr h' (by omega) (hc ▸ hbit))
  rw [h0, hpend, Nat.zero_add] at hclimb
  unfold Acc.root mixedRootOf rootOf
  rw [hc, hclimb]

/-- The fresh contract's root is the reference empty mixed root. -/
theorem empty_root (H : Bytes → B256) :
    Acc.root H Acc.empty = mixedRootOf H [] :=
  root_correct H Acc.empty [] (empty_inv H)

/-! ## The insertion walk: liveness and the cap boundary -/

theorem div_two_div_pow (size j : Nat) : size / 2 / 2 ^ j = size / 2 ^ (j + 1) := by
  rw [Nat.div_div_eq_div_mul, Nat.mul_comm, ← Nat.pow_succ]

theorem div_pow_div_two (m h : Nat) : m / 2 ^ h / 2 = m / 2 ^ (h + 1) := by
  rw [Nat.div_div_eq_div_mul, ← Nat.pow_succ]

/-- The walk falls through exactly when every bit within its remaining
range is clear. -/
theorem walk_eq_none_iff (H : Bytes → B256) :
    ∀ (k h size : Nat) (node : B256) (br : Nat → B256),
      walk H br k h size node = none ↔ ∀ j, j < k → size / 2 ^ j % 2 = 0 := by
  intro k
  induction k with
  | zero => intro h size node br; simp [walk]
  | succ k ih =>
      intro h size node br
      simp only [walk]
      rcases Nat.mod_two_eq_zero_or_one size with hb | hb
      · rw [if_neg (by omega), ih (h + 1) (size / 2) _ br]
        constructor
        · intro hj j hjk
          rcases Nat.eq_zero_or_pos j with hj0 | hj0
          · subst hj0
            rw [Nat.pow_zero, Nat.div_one]
            exact hb
          · have hstep := hj (j - 1) (by omega)
            rw [div_two_div_pow] at hstep
            have hj1 : j - 1 + 1 = j := by omega
            rwa [hj1] at hstep
        · intro hj j hjk
          rw [div_two_div_pow]
          exact hj (j + 1) (by omega)
      · rw [if_pos hb]
        constructor
        · intro hnone
          exact absurd hnone (Option.some_ne_none _)
        · intro hj
          have h0 := hj 0 (Nat.succ_pos k)
          rw [Nat.pow_zero, Nat.div_one] at h0
          exact absurd h0 (by omega)

/-- The 32-step walk finds a live slot iff the walked count has a set bit
below 32. -/
theorem walk_isSome_iff (H : Bytes → B256) (br : Nat → B256) (node : B256)
    (m : Nat) :
    (walk H br 32 0 m node).isSome ↔ m % 2 ^ 32 ≠ 0 := by
  rw [Option.isSome_iff_ne_none, Ne, walk_eq_none_iff H 32 0 m node br,
    ← mod_two_pow_eq_zero_iff]

/-- **The cap boundary.** At `count = 2 ^ 32 - 1` the incremented count is
`2 ^ 32`, no bit below 32 is set, and the insert walk's live-slot existence
fails: the walk falls through to the source's `assert(false)`. The
`MAX_DEPOSIT_COUNT` guard is load-bearing, not decorative. -/
theorem walk_none_at_cap (H : Bytes → B256) (br : Nat → B256) (node : B256) :
    walk H br 32 0 ((2 ^ 32 - 1) + 1) node = none := by
  rw [walk_eq_none_iff, ← mod_two_pow_eq_zero_iff]
  have h1 : (2 ^ 32 - 1) + 1 = 2 ^ 32 := by omega
  rw [h1, Nat.mod_self]

/-- The guard in `Acc.insert` is exactly the walk's live-slot boundary:
insertion succeeds iff the count is below the cap. -/
theorem insert_isSome_iff (H : Bytes → B256) (s : Acc) (node : B256) :
    (Acc.insert H s node).isSome ↔ s.count < 2 ^ 32 - 1 := by
  unfold Acc.insert
  by_cases hc : s.count < 2 ^ 32 - 1
  · rw [if_pos hc, Option.isSome_map]
    rw [walk_isSome_iff]
    have h1 : (s.count + 1) % 2 ^ 32 = s.count + 1 := Nat.mod_eq_of_lt (by omega)
    rw [h1]
    constructor
    · intro _; exact hc
    · intro _; omega
  · rw [if_neg hc]
    simp
    omega

/-! ## Insertion preserves the invariant -/

theorem take_drop_append (i j : Nat) (l₁ l₂ : List B256)
    (h : i + j ≤ l₁.length) :
    ((l₁ ++ l₂).drop i).take j = (l₁.drop i).take j := by
  rw [List.drop_append_of_le_length (by omega),
    List.take_append_of_le_length (by rw [List.length_drop]; omega)]

/-- A set bit contributes its weight to any residue window containing it. -/
theorem mod_pow_ge_of_bit (m h k : Nat) (hk : h < k)
    (hb : m / 2 ^ h % 2 = 1) : 2 ^ h ≤ m % 2 ^ k := by
  have h1 : m % 2 ^ (h + 1) = m % 2 ^ h + 2 ^ h := by
    rw [Nat.mod_pow_succ, hb, Nat.mul_one]
  have h2 : m % 2 ^ k % 2 ^ (h + 1) = m % 2 ^ (h + 1) :=
    Nat.mod_mod_of_dvd m (Nat.pow_dvd_pow 2 (by omega))
  have h3 : m % 2 ^ k % 2 ^ (h + 1) ≤ m % 2 ^ k := Nat.mod_le _ _
  omega

/-- Two set bits contribute both weights to the wider residue window. -/
theorem mod_pow_ge_of_two_bits (m h h' : Nat) (hlt : h < h')
    (hb : m / 2 ^ h % 2 = 1) (hb' : m / 2 ^ h' % 2 = 1) :
    2 ^ h' + 2 ^ h ≤ m % 2 ^ (h' + 1) := by
  have h1 : m % 2 ^ (h' + 1) = m % 2 ^ h' + 2 ^ h' := by
    rw [Nat.mod_pow_succ, hb', Nat.mul_one]
  have h2 : 2 ^ h ≤ m % 2 ^ h' := mod_pow_ge_of_bit m h h' hlt hb
  omega

/-- Below a cleared residue window, every bit is clear. -/
theorem bit_zero_of_mod_zero (m h h' : Nat) (hlt : h' < h)
    (hm : m % 2 ^ h = 0) : m / 2 ^ h' % 2 = 0 := by
  have h1 : m % 2 ^ (h' + 1) = m % 2 ^ h % 2 ^ (h' + 1) :=
    (Nat.mod_mod_of_dvd m (Nat.pow_dvd_pow 2 (by omega))).symm
  rw [hm, Nat.zero_mod, Nat.mod_pow_succ] at h1
  have h2 : 2 ^ h' * (m / 2 ^ h' % 2) = 0 := by omega
  rcases Nat.mul_eq_zero.mp h2 with h3 | h3
  · exact absurd h3 (by have := Nat.two_pow_pos h'; omega)
  · exact h3

/-- A live slot's completed block is unchanged by appending the new leaf,
provided a strictly lower bit of the incremented count is also set. -/
theorem completedBlock_pred (h h' : Nat) (ls : List B256)
    (leaf : B256) (hlt : h < h')
    (hb : (ls.length + 1) / 2 ^ h % 2 = 1)
    (hb' : (ls.length + 1) / 2 ^ h' % 2 = 1) :
    completedBlock h' ls.length ls
      = completedBlock h' (ls.length + 1) (ls ++ [leaf]) := by
  have hwin : 0 < (ls.length + 1) % 2 ^ (h + 1) := by
    have := mod_pow_ge_of_bit (ls.length + 1) h (h + 1) (by omega) hb
    have := Nat.two_pow_pos h
    omega
  have hdiv : ls.length / 2 ^ (h' + 1) = (ls.length + 1) / 2 ^ (h' + 1) := by
    have hp := pred_div_pow_eq (ls.length + 1) h (h' + 1) (by omega) hwin
    rwa [Nat.add_sub_cancel] at hp
  unfold completedBlock
  rw [← hdiv]
  refine (take_drop_append _ _ _ _ ?_).symm
  have h2 : 2 ^ h' + 2 ^ h ≤ (ls.length + 1) % 2 ^ (h' + 1) :=
    mod_pow_ge_of_two_bits (ls.length + 1) h h' hlt hb hb'
  have h3 : ls.length / 2 ^ (h' + 1) * 2 ^ (h' + 1)
      = ls.length - ls.length % 2 ^ (h' + 1) := div_mul_eq_sub_mod _ _
  have h4 : ls.length % 2 ^ (h' + 1) ≤ ls.length := Nat.mod_le _ _
  have h5 : ls.length % 2 ^ (h' + 1) = (ls.length + 1) % 2 ^ (h' + 1) - 1 := by
    have hp := pred_mod_of_pos (ls.length + 1) (2 ^ (h' + 1)) (by omega)
    rwa [Nat.add_sub_cancel] at hp
  have := Nat.two_pow_pos h
  omega

/-- The insertion walk's loop invariant: with every bit of the incremented
count below `h` clear, a set bit within the remaining `k` heights, and the
accumulated node rooting the trailing `2 ^ h` block of the extended list,
the walk succeeds, and every live slot of the incremented count roots its
completed block in the extended list. -/
theorem walk_insert_spec (H : Bytes → B256) (ls : List B256) (leaf : B256) :
    ∀ (k h : Nat) (br : Nat → B256),
      h + k ≤ 32 →
      (ls.length + 1) % 2 ^ h = 0 →
      (ls.length + 1) / 2 ^ h ≠ 0 →
      (ls.length + 1) / 2 ^ h < 2 ^ k →
      (∀ h', h ≤ h' → h' < 32 → ls.length / 2 ^ h' % 2 = 1 →
        br h' = rootAt H h' (completedBlock h' ls.length ls)) →
      ∃ br',
        walk H br k h ((ls.length + 1) / 2 ^ h)
          (rootAt H h ((ls ++ [leaf]).drop (ls.length + 1 - 2 ^ h)))
          = some br' ∧
        ∀ h', h' < 32 → (ls.length + 1) / 2 ^ h' % 2 = 1 →
          br' h' = rootAt H h' (completedBlock h' (ls.length + 1) (ls ++ [leaf])) := by
  intro k
  induction k with
  | zero =>
      intro h br _ _ hne hlt _
      rw [Nat.pow_zero] at hlt
      exact absurd (Nat.lt_one_iff.mp hlt) hne
  | succ k ih =>
      intro h br hk32 hmod hne hlt hbr
      have hlen' : (ls ++ [leaf]).length = ls.length + 1 := by simp
      have hq1 : 1 ≤ (ls.length + 1) / 2 ^ h := Nat.pos_of_ne_zero hne
      have hpowh : 0 < 2 ^ h := Nat.two_pow_pos h
      have hge : 2 ^ h ≤ ls.length + 1 := by
        have hd := Nat.div_add_mod (ls.length + 1) (2 ^ h)
        have hmul : 2 ^ h * 1 ≤ 2 ^ h * ((ls.length + 1) / 2 ^ h) :=
          Nat.mul_le_mul_left _ hq1
        rw [Nat.mul_one] at hmul
        omega
      simp only [walk]
      rcases Nat.mod_two_eq_zero_or_one ((ls.length + 1) / 2 ^ h) with hb | hb
      · -- dead bit at `h`: combine with the old completed block and recurse
        rw [if_neg (by omega), div_pow_div_two]
        have hpow1 : (2 : Nat) ^ (h + 1) = 2 ^ h * 2 := Nat.pow_succ 2 h
        have hmod1 : (ls.length + 1) % 2 ^ (h + 1) = 0 := by
          rw [Nat.mod_pow_succ, hb, Nat.mul_zero, Nat.add_zero, hmod]
        have hne1 : (ls.length + 1) / 2 ^ (h + 1) ≠ 0 := by
          rw [← div_pow_div_two]
          omega
        have hlt1 : (ls.length + 1) / 2 ^ (h + 1) < 2 ^ k := by
          rw [← div_pow_div_two]
          rw [Nat.pow_succ] at hlt
          omega
        have hge1 : 2 ^ (h + 1) ≤ ls.length + 1 := by
          have hd := Nat.div_add_mod (ls.length + 1) (2 ^ (h + 1))
          have hq : 1 ≤ (ls.length + 1) / 2 ^ (h + 1) := Nat.pos_of_ne_zero hne1
          have hmul : 2 ^ (h + 1) * 1
              ≤ 2 ^ (h + 1) * ((ls.length + 1) / 2 ^ (h + 1)) :=
            Nat.mul_le_mul_left _ hq
          rw [Nat.mul_one] at hmul
          omega
        have hpm : ls.length % 2 ^ (h + 1) = 2 ^ (h + 1) - 1 := by
          have hp := pred_mod_eq (ls.length + 1) (2 ^ (h + 1)) (by omega)
            (by omega) hmod1
          rwa [Nat.add_sub_cancel] at hp
        have hbitpred : ls.length / 2 ^ h % 2 = 1 := by
          have hsplit : ls.length % 2 ^ (h + 1)
              = ls.length % 2 ^ h + 2 ^ h * (ls.length / 2 ^ h % 2) :=
            Nat.mod_pow_succ
          have hlt2 : ls.length % 2 ^ h < 2 ^ h := Nat.mod_lt _ hpowh
          rcases Nat.mod_two_eq_zero_or_one (ls.length / 2 ^ h) with hz | ho
          · rw [hz, Nat.mul_zero, Nat.add_zero] at hsplit
            omega
          · exact ho
        have hstartOld : ls.length / 2 ^ (h + 1) * 2 ^ (h + 1)
            = ls.length + 1 - 2 ^ (h + 1) := by
          rw [div_mul_eq_sub_mod]
          omega
        have hbrh := hbr h le_rfl (by omega) hbitpred
        have hcbeq : completedBlock h ls.length ls
            = ((ls ++ [leaf]).drop (ls.length + 1 - 2 ^ (h + 1))).take (2 ^ h) := by
          unfold completedBlock
          rw [hstartOld]
          refine (take_drop_append _ _ _ _ ?_).symm
          omega
        have hidx : ls.length + 1 - 2 ^ (h + 1) + 2 ^ h
            = ls.length + 1 - 2 ^ h := by omega
        have hlentake :
            (((ls ++ [leaf]).drop (ls.length + 1 - 2 ^ (h + 1))).take
              (2 ^ h)).length = 2 ^ h := by
          rw [List.length_take, List.length_drop, hlen']
          omega
        have hnode : hashPair H (br h)
            (rootAt H h ((ls ++ [leaf]).drop (ls.length + 1 - 2 ^ h)))
            = rootAt H (h + 1)
                ((ls ++ [leaf]).drop (ls.length + 1 - 2 ^ (h + 1))) := by
          conv_rhs => rw [← List.take_append_drop (2 ^ h)
            ((ls ++ [leaf]).drop (ls.length + 1 - 2 ^ (h + 1)))]
          rw [rootAt_append H h _ _ hlentake, List.drop_drop, hidx, hbrh, hcbeq]
        rw [hnode]
        exact ih (h + 1) br (by omega) hmod1 hne1 hlt1
          (fun h' h1 h2 hbit => hbr h' (by omega) h2 hbit)
      · -- live bit at `h`: write the node and stop
        rw [if_pos hb]
        refine ⟨setSlot br h
          (rootAt H h ((ls ++ [leaf]).drop (ls.length + 1 - 2 ^ h))), rfl, ?_⟩
        intro h' h32 hbit
        unfold setSlot
        by_cases heq : h' = h
        · subst heq
          rw [if_pos rfl]
          have hm1 : (ls.length + 1) % 2 ^ (h' + 1) = 2 ^ h' := by
            rw [Nat.mod_pow_succ, hb, Nat.mul_one, hmod, Nat.zero_add]
          have hstart : (ls.length + 1) / 2 ^ (h' + 1) * 2 ^ (h' + 1)
              = ls.length + 1 - 2 ^ h' := by
            rw [div_mul_eq_sub_mod, hm1]
          unfold completedBlock
          rw [hstart, List.take_of_length_le
            (by rw [List.length_drop, hlen']; omega)]
        · rw [if_neg heq]
          rcases Nat.lt_or_ge h' h with hlth | hgeh
          · have := bit_zero_of_mod_zero (ls.length + 1) h h' hlth hmod
            omega
          · have hgt : h < h' := by omega
            have hwin : 0 < (ls.length + 1) % 2 ^ (h + 1) := by
              have := mod_pow_ge_of_bit (ls.length + 1) h (h + 1) (by omega) hb
              omega
            have hbitOld : ls.length / 2 ^ h' % 2 = 1 := by
              have hp := pred_div_pow_eq (ls.length + 1) h h' (by omega) hwin
              rw [Nat.add_sub_cancel] at hp
              rw [hp]
              exact hbit
            rw [hbr h' (by omega) h32 hbitOld,
              completedBlock_pred h h' ls leaf hgt hb hbit]

/-- **Insertion under the exact source precondition** `count < 2 ^ 32 - 1`
succeeds, preserves the invariant, and appends exactly one leaf to the
abstraction. -/
theorem insert_spec (H : Bytes → B256) (s : Acc) (ls : List B256)
    (leaf : B256) (hInv : Inv H s ls) (hcap : s.count < 2 ^ 32 - 1) :
    ∃ s', Acc.insert H s leaf = some s' ∧ s'.count = s.count + 1 ∧
      Inv H s' (ls ++ [leaf]) := by
  obtain ⟨hc, hlt, hbr⟩ := hInv
  have hbr' : ∀ h', 0 ≤ h' → h' < 32 → ls.length / 2 ^ h' % 2 = 1 →
      s.branch h' = rootAt H h' (completedBlock h' ls.length ls) := by
    intro h' _ h2 hbit
    rw [← hc] at hbit ⊢
    exact hbr h' h2 hbit
  have hspec := walk_insert_spec H ls leaf 32 0 s.branch (by omega)
    (by rw [Nat.pow_zero, Nat.mod_one])
    (by rw [Nat.pow_zero, Nat.div_one]; omega)
    (by rw [Nat.pow_zero, Nat.div_one]; omega)
    hbr'
  obtain ⟨br', hwalk, hbrNew⟩ := hspec
  have hsize : (ls.length + 1) / 2 ^ 0 = s.count + 1 := by
    rw [Nat.pow_zero, Nat.div_one, hc]
  have hnode0 : rootAt H 0 ((ls ++ [leaf]).drop (ls.length + 1 - 2 ^ 0)) = leaf := by
    rw [Nat.pow_zero]
    have h1 : ls.length + 1 - 1 = ls.length := by omega
    rw [h1, List.drop_left]
    rfl
  rw [hsize, hnode0] at hwalk
  refine ⟨⟨br', s.count + 1⟩, ?_, rfl, ?_, ?_, ?_⟩
  · unfold Acc.insert
    rw [if_pos hcap, hwalk]
    rfl
  · simp [hc]
  · have hl : (ls ++ [leaf]).length = ls.length + 1 := by simp
    omega
  · intro h h32 hbit
    rw [hc] at hbit
    rw [hc]
    exact hbrNew h h32 hbit

/-! ## `deposit`: guard partition facts -/

/-- The source's terminal `assert(false)` is unreachable: under the cap
guard the walk always finds a live slot, so `deposit` never returns
`Reason.assert_false`. -/
theorem deposit_ne_assert_false (H : Bytes → B256) (s : Acc)
    (pubkey withdrawal_credentials signature : Bytes)
    (deposit_data_root : B256) (value : Nat) :
    deposit H s pubkey withdrawal_credentials signature deposit_data_root value
      ≠ .error .assert_false := by
  intro hEq
  simp only [deposit] at hEq
  split at hEq <;> try split at hEq <;> try split at hEq <;>
    try split at hEq <;> try split at hEq <;> try split at hEq <;>
    try split at hEq <;> try split at hEq <;> try split at hEq
  all_goals simp at hEq
  rename_i _discr hwalk
  have hcap' : s.count < 2 ^ 32 - 1 := by omega
  have hall := (walk_eq_none_iff H 32 0 (s.count + 1) _ s.branch).mp hwalk
  have hzero := (mod_two_pow_eq_zero_iff (s.count + 1) 32).mpr hall
  rw [Nat.mod_eq_of_lt (by omega)] at hzero
  omega

/-- Success characterization of `deposit`: every guard passed (in source
order), the event payload is exact — with the **pre-increment** count as its
`index` — and the state transition is exactly the guarded insertion of the
reconstructed deposit-data node. -/
theorem deposit_ok_spec (H : Bytes → B256) (s : Acc)
    (pubkey withdrawal_credentials signature : Bytes)
    (deposit_data_root : B256) (value : Nat) (s' : Acc) (ev : DepositEvent)
    (hEq : deposit H s pubkey withdrawal_credentials signature
      deposit_data_root value = .ok (s', ev)) :
    pubkey.length = 48 ∧ withdrawal_credentials.length = 32 ∧
    signature.length = 96 ∧ oneEther ≤ value ∧ value % oneGwei = 0 ∧
    value / oneGwei ≤ 2 ^ 64 - 1 ∧
    depositDataNode H pubkey withdrawal_credentials signature
      (le64 (value / oneGwei)) = deposit_data_root ∧
    s.count < 2 ^ 32 - 1 ∧
    s'.count = s.count + 1 ∧
    ev = ⟨pubkey, withdrawal_credentials, le64 (value / oneGwei), signature,
      le64 s.count⟩ ∧
    Acc.insert H s (depositDataNode H pubkey withdrawal_credentials signature
      (le64 (value / oneGwei))) = some s' := by
  simp only [deposit] at hEq
  split at hEq <;> try split at hEq <;> try split at hEq <;>
    try split at hEq <;> try split at hEq <;> try split at hEq <;>
    try split at hEq <;> try split at hEq <;> try split at hEq
  all_goals simp at hEq
  rename_i hcapNN _discr br hwalk
  obtain ⟨h1, h2⟩ := hEq
  have hrootEq : depositDataNode H pubkey withdrawal_credentials signature
      (le64 (value / oneGwei)) = deposit_data_root :=
    Decidable.of_not_not (by assumption)
  have hcap' : s.count < 2 ^ 32 - 1 := by omega
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, hrootEq,
    hcap', ?_, h2.symm, ?_⟩
  · rw [← h1]
  · unfold Acc.insert
    rw [if_pos hcap', hwalk]
    exact congrArg some h1

/-- `deposit` success preserves the invariant: the appended leaf is exactly
the reconstructed deposit-data node. -/
theorem deposit_inv (H : Bytes → B256) (s : Acc) (ls : List B256)
    (pubkey withdrawal_credentials signature : Bytes)
    (deposit_data_root : B256) (value : Nat) (s' : Acc) (ev : DepositEvent)
    (hInv : Inv H s ls)
    (hEq : deposit H s pubkey withdrawal_credentials signature
      deposit_data_root value = .ok (s', ev)) :
    Inv H s' (ls ++ [depositDataNode H pubkey withdrawal_credentials signature
      (le64 (value / oneGwei))]) := by
  obtain ⟨-, -, -, -, -, -, -, hcap, -, -, hins⟩ :=
    deposit_ok_spec H s pubkey withdrawal_credentials signature
      deposit_data_root value s' ev hEq
  obtain ⟨s'', hs'', -, hInv'⟩ := insert_spec H s ls _ hInv hcap
  rw [hins] at hs''
  obtain rfl := Option.some.inj hs''
  exact hInv'

/-! ## B3 exactness: encoding lengths and hash-input widths

Every `sha256` call in the pinned source takes exactly 64 bytes; these
lemmas state the same widths for the model's `H` call sites, plus the
encoding-length facts B4's vectors rely on. `B256.toBytes` always has
length 32, so no hypothesis about `H` is needed anywhere. -/

theorem le64_length (n : Nat) : (le64 n).length = 8 := rfl

theorem zeros_length (n : Nat) : (zeros n).length = n :=
  List.length_replicate

theorem le64_zero : le64 0 = zeros 8 := rfl

/-- Tree combine (source lines 77, 85, 87, 130, 134): 32 + 32 bytes. -/
theorem hashPair_input_length (a b : B256) :
    (a.toBytes ++ b.toBytes).length = 64 := by
  rw [List.length_append, B256.length_toBytes, B256.length_toBytes]

/-- Count mix-in (source lines 90–94): 32 + 8 + 24 bytes. -/
theorem mixIn_input_length (root : B256) (n : Nat) :
    (root.toBytes ++ le64 n ++ zeros 24).length = 64 := by
  simp [B256.length_toBytes, le64_length, zeros_length]

/-- Pubkey root (source line 129): 48 + 16 bytes under the length guard. -/
theorem pubkeyRoot_input_length (pubkey : Bytes) (h : pubkey.length = 48) :
    (pubkey ++ zeros 16).length = 64 := by
  simp [zeros_length, h]

/-- Signature root (source lines 130–133): 64 and 32 + 32 bytes under the
length guard. -/
theorem signatureRoot_input_lengths (signature : Bytes)
    (h : signature.length = 96) :
    (signature.take 64).length = 64 ∧
    (signature.drop 64 ++ zeros 32).length = 64 := by
  constructor
  · rw [List.length_take]
    omega
  · simp [zeros_length]
    omega

/-- Deposit-data node (source lines 134–137): 32 + 32 and 8 + 24 + 32 bytes
under the guards. -/
theorem depositDataNode_input_lengths (H : Bytes → B256)
    (pubkey withdrawal_credentials signature amountLE : Bytes)
    (hwc : withdrawal_credentials.length = 32) (ha : amountLE.length = 8) :
    ((pubkeyRoot H pubkey).toBytes ++ withdrawal_credentials).length = 64 ∧
    (amountLE ++ zeros 24 ++ (signatureRoot H signature).toBytes).length
      = 64 := by
  constructor <;> simp [B256.length_toBytes, zeros_length, hwc, ha]

end Blanc.BeaconDeposit
