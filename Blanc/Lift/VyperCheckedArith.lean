import Blanc.Lift.Vyper
import Blanc.Lift.InvWalkWorld
import Blanc.Lift.ExactWalkCut
import Blanc.Lift.VyperFrameLoop
import Blanc.Lift.MemGlue
import Blanc.Lift.StableSwapNewton.Defs

/-!
# Vyper 0.2.x checked `uint256` arithmetic and word-slot frames

Vyper 0.2.x compiles each checked `uint256` operation on the two stack words `[y, x]` (`y` on
top) to a fixed idiom: a guard over the operands, `PUSH2 ok JUMPI` past a reverting
fall-through, and a clean-up that leaves the result alone.  The trees here are those idioms
with the guard's tag, the reverting arm and the continuation as parameters:

* `vyMulT` computes `x * y`, guarded by `x = 0 ∨ (x * y) / x = y` (no wrap);
* `vyAddT` computes `x + y`, guarded by `¬ (x + y < x)` (no wrap);
* `vySubT` computes `x - y`, guarded by `¬ (x < y)` (no underflow);
* `vyDivT` computes `x / y`, guarded by `y ≠ 0`.

`ric_vyChk*` invert them (the guard holds, as a `Nat` fact, and the continuation runs from the
result); `rxc_vyChk*` run them forward at constant cost.

**Word-slot frames.**  A Vyper internal function keeps its variables in a fixed memory window
of words.  `WordFrame M0 M lo ws` says that `M` holds the words `ws` at `lo, lo + 32, …`,
inside the logical size, has `M0`'s size and agrees with `M0` outside the window.  The steps
`ric_mloadF`/`ric_mstoreF` (and their `PUSH2` forms) read and write a slot by index.

Nothing here mentions a contract.
-/

namespace Blanc.Lift

open Jaune

/-! ## The idiom trees -/

/-- Vyper's reverting arm `PUSH1 0 DUP1 REVERT`. -/
def vyRevertT : SFunc := .next (.push [0x00] (by decide)) (.next (.reg (.dup 0)) (.last .revert))

theorem vyRevertT_noOk : vyRevertT.noOk = true := rfl

/-- `x * y` checked (stack `[y, x]`): `DUP1 DUP3 MUL DUP3 ISZERO DUP3 DUP5 DUP4 DIV EQ OR
PUSH2 ok JUMPI`, then `JUMPDEST DUP1 SWAP1 POP SWAP1 POP SWAP1 POP`. -/
def vyMulT (h l : UInt8) (fail k : SFunc) : SFunc :=
  .next (.reg (.dup 0)) <| .next (.reg (.dup 2)) <| .next (.reg .mul) <| .next (.reg (.dup 2)) <|
    .next (.reg .iszero) <| .next (.reg (.dup 2)) <| .next (.reg (.dup 4)) <|
    .next (.reg (.dup 3)) <| .next (.reg .div) <| .next (.reg .eq) <| .next (.reg .or) <|
    .next (.push [h, l] (frameLoop_len2 h l)) <| .branch fail <| .dest <|
    .next (.reg (.dup 0)) <| .next (.reg (.swap 0)) <| .next (.reg .pop) <|
    .next (.reg (.swap 0)) <| .next (.reg .pop) <| .next (.reg (.swap 0)) <| .next (.reg .pop) k

/-- `x + y` checked (stack `[y, x]`): `DUP2 DUP2 DUP4 ADD LT ISZERO PUSH2 ok JUMPI`, then
`JUMPDEST DUP1 DUP3 ADD SWAP1 POP SWAP1 POP`. -/
def vyAddT (h l : UInt8) (fail k : SFunc) : SFunc :=
  .next (.reg (.dup 1)) (.next (.reg (.dup 1)) (.next (.reg (.dup 3)) (.next (.reg .add)
    (.next (.reg .lt) (.next (.reg .iszero) (.next (.push [h, l] (frameLoop_len2 h l))
    (.branch fail (.dest (.next (.reg (.dup 0)) (.next (.reg (.dup 2)) (.next (.reg .add)
    (.next (.reg (.swap 0)) (.next (.reg .pop) (.next (.reg (.swap 0)) (.next (.reg .pop)
      k)))))))))))))))

/-- `x - y` checked (stack `[y, x]`): `DUP1 DUP3 LT ISZERO PUSH2 ok JUMPI`, then
`JUMPDEST DUP1 DUP3 SUB SWAP1 POP SWAP1 POP`. -/
def vySubT (h l : UInt8) (fail k : SFunc) : SFunc :=
  .next (.reg (.dup 0)) (.next (.reg (.dup 2)) (.next (.reg .lt) (.next (.reg .iszero)
    (.next (.push [h, l] (frameLoop_len2 h l)) (.branch fail (.dest (.next (.reg (.dup 0))
    (.next (.reg (.dup 2)) (.next (.reg .sub) (.next (.reg (.swap 0)) (.next (.reg .pop)
    (.next (.reg (.swap 0)) (.next (.reg .pop) k)))))))))))))

/-- `x / y` checked (stack `[y, x]`): `DUP1 DUP1 PUSH2 ok JUMPI`, then
`JUMPDEST DUP3 DIV SWAP1 POP SWAP1 POP`. -/
def vyDivT (h l : UInt8) (fail k : SFunc) : SFunc :=
  .next (.reg (.dup 0)) (.next (.reg (.dup 0)) (.next (.push [h, l] (frameLoop_len2 h l))
    (.branch fail (.dest (.next (.reg (.dup 2)) (.next (.reg .div) (.next (.reg (.swap 0))
    (.next (.reg .pop) (.next (.reg (.swap 0)) (.next (.reg .pop) k))))))))))

/-! ## Guard facts -/

theorem B256.or_eqCheck_ne_zero {a b c d : B256} (h : (B256.eqCheck a b ||| B256.eqCheck c d) ≠ 0) :
    a = b ∨ c = d := by
  by_contra hn
  rw [not_or] at hn
  apply h
  simp only [B256.eqCheck, hn.1, hn.2, ↓reduceIte]
  decide

/-- Vyper's multiplication guard is the no-wrap predicate. -/
theorem B256.nofm_of_mulGuard {x y : B256} (h : (x * y) / x = y ∨ x = 0) :
    B256.Nofm x y := by
  rcases h with h | h
  · by_cases hx : x = 0
    · subst hx
      show (0 : B256).toNat * y.toNat < 2 ^ 256
      rw [B256.toNat_zero, Nat.zero_mul]; exact Nat.two_pow_pos _
    · have hnat := congrArg B256.toNat h
      rw [B256.toNat_div hx] at hnat
      have hfloor := Nat.mul_div_le (x * y).toNat x.toNat
      rw [hnat] at hfloor
      show x.toNat * y.toNat < 2 ^ 256
      exact Nat.lt_of_le_of_lt hfloor (B256.toNat_lt (x * y))
  · subst h
    show (0 : B256).toNat * y.toNat < 2 ^ 256
    rw [B256.toNat_zero, Nat.zero_mul]; exact Nat.two_pow_pos _

/-! ## Guards read as the checked operations on naturals -/

section Checked

open Blanc.StableSwapNewton

theorem chkMul_toNat_of_nofm {x y : B256} (h : B256.Nofm x y) :
    chkMul x.toNat y.toNat = some (x * y).toNat := by
  unfold chkMul wordSize
  rw [ite_eq_left (show x.toNat * y.toNat < 2 ^ 256 from h), B256.toNat_mul_eq_of_nofm h]

theorem chkAdd_toNat_of_lt {x y : B256} (h : x.toNat + y.toNat < 2 ^ 256) :
    chkAdd x.toNat y.toNat = some (x + y).toNat := by
  unfold chkAdd wordSize
  rw [ite_eq_left h, B256.toNat_add, Nat.lo, Nat.mod_eq_of_lt h]

theorem chkSub_toNat_of_le {x y : B256} (h : y.toNat ≤ x.toNat) :
    chkSub x.toNat y.toNat = some (x - y).toNat := by
  unfold chkSub
  rw [ite_eq_left h, B256.toNat_sub_eq_of_le _ _ (B256.le_iff_toNat_le_toNat.mpr h)]

theorem chkDiv_toNat_of_ne {x y : B256} (h : y ≠ 0) :
    chkDiv x.toNat y.toNat = some (x / y).toNat := by
  unfold chkDiv
  rw [ite_eq_right (B256.toNat_ne_zero h), B256.toNat_div h]

end Checked

/-! ## Comparison flags as branch conditions -/

/-- `ISZERO (GT x y)` is zero: `x > y`. -/
theorem toNat_lt_of_iszero_gt_eq_zero {x y : B256} (h : B256.eqCheck (B256.gtCheck x y) 0 = 0) :
    y.toNat < x.toNat := by
  unfold B256.gtCheck at h
  split at h
  · rename_i hl; rwa [gt_iff_lt, B256.lt_iff_toNat_lt_toNat] at hl
  · exact absurd h (by decide)

/-- `ISZERO (GT x y)` is nonzero: `x ≤ y`. -/
theorem toNat_le_of_iszero_gt_ne_zero {x y : B256} (h : B256.eqCheck (B256.gtCheck x y) 0 ≠ 0) :
    x.toNat ≤ y.toNat :=
  toNat_le_of_gtCheck_eq_zero (eq_zero_of_iszero_ne_zero h)

/-- `ISZERO (ISZERO g)` is zero: `g = 0`. -/
theorem eq_zero_of_iszero2_eq_zero {g : B256} (h : B256.eqCheck (B256.eqCheck g 0) 0 = 0) :
    g = 0 := by
  by_contra hg
  have : B256.eqCheck g 0 = 0 := by unfold B256.eqCheck; rw [ite_eq_right hg]
  rw [this] at h
  exact absurd h (by decide)

/-- `ISZERO (ISZERO g)` is nonzero: `g ≠ 0`. -/
theorem ne_zero_of_iszero2_ne_zero {g : B256} (h : B256.eqCheck (B256.eqCheck g 0) 0 ≠ 0) :
    g ≠ 0 := by
  intro hg
  apply h
  rw [hg]
  decide

/-! ## Signed range checks

Vyper 0.2 checks an `int128` index `0 ≤ i < n` with two `SLT`s. -/

theorem UInt64.and_low63 (h : UInt64) (hb : h.highBit = false) :
    h &&& 0x7fffffffffffffff = h := by
  unfold UInt64.highBit at hb
  simp only [bne_eq_false_iff_eq] at hb
  apply UInt64.toNat_inj.mp
  have hb' := congrArg UInt64.toNat hb
  rw [UInt64.toNat_and] at hb' ⊢
  have h64 := h.toNat_lt
  rw [show (0x7fffffffffffffff : UInt64).toNat = 2 ^ 63 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]
  rw [show (0x8000000000000000 : UInt64).toNat = 2 ^ 63 from rfl,
    show (0 : UInt64).toNat = 0 from rfl] at hb'
  have : h.toNat < 2 ^ 63 := by
    by_contra hc
    have ht : h.toNat.testBit 63 = true := by
      rw [Nat.testBit_eq_decide_div_mod_eq]
      simp only [decide_eq_true_eq]
      have : h.toNat / 2 ^ 63 = 1 := by omega
      omega
    have := Nat.testBit_and h.toNat (2 ^ 63) 63
    rw [hb', ht, Nat.testBit_two_pow_self, Nat.zero_testBit] at this
    exact absurd this (by decide)
  exact Nat.mod_eq_of_lt this

theorem UInt64.and_max_self (h : UInt64) : h &&& UInt64.max = h := by
  apply UInt64.toNat_inj.mp
  rw [UInt64.toNat_and, show UInt64.max.toNat = 2 ^ 64 - 1 from rfl,
    Nat.and_two_pow_sub_one_eq_mod]
  exact Nat.mod_eq_of_lt h.toNat_lt

/-- The low 255 bits, `B256.max >>> 1`. -/
def B256.low255 : B256 := ((0x7fffffffffffffff, UInt64.max), (UInt64.max, UInt64.max))

/-- `¬ (i <ₛ 0)` and `i <ₛ 3`: `i` is `0`, `1` or `2`. -/
theorem B256.toNat_lt_three_of_slt {i : B256} (h0 : ¬ B256.Slt i 0)
    (h3 : B256.Slt i (Bytes.toB256 [0x03])) : i.toNat < 3 := by
  have em : (B256.max >>> 1 : B256) = B256.low255 := rfl
  unfold B256.Slt at h0 h3
  rw [em] at h0 h3
  cases ha : i.highBit
  · have hand : i &&& B256.low255 = i := by
      obtain ⟨⟨a, b⟩, ⟨c, d⟩⟩ := i
      show ((a &&& 0x7fffffffffffffff, b &&& UInt64.max), (c &&& UInt64.max, d &&& UInt64.max)) = _
      rw [UInt64.and_low63 a ha, UInt64.and_max_self, UInt64.and_max_self, UInt64.and_max_self]
      rfl
    have h3m : Bytes.toB256 [0x03] &&& B256.low255 = Bytes.toB256 [0x03] := rfl
    have h3h : (Bytes.toB256 [0x03]).highBit = false := rfl
    rw [hand, h3m, ha, h3h] at h3
    have : i < Bytes.toB256 [0x03] := by
      rcases h3 with h | ⟨-, h⟩
      · exact absurd h (by decide)
      · exact h
    rw [B256.lt_iff_toNat_lt_toNat, show (Bytes.toB256 [0x03]).toNat = 3 by decide] at this
    exact this
  · exfalso
    apply h0
    left
    rw [ha]; decide

/-! ## Inverted -/

section Inv

variable {fs : List SFunc} {sevm : Sevm} {C : List Nat} {b : Devm} {S : List B256} {M : Mem}
  {G : Nat} {r : Seg} {h l : UInt8} {fail k : SFunc}

/-- `SLT`, inverted, with its value. -/
theorem ri_sltV {x y : B256} {d : Devm}
    (hr : Ninst.Run sevm (St b (x :: y :: S) M G) (.reg .slt) d) :
    ∃ G', d = St b (B256.sltCheck x y :: S) M G' := by
  rcases of_run_reg hr with ⟨pc, run⟩
  simp only [Rinst.run, Rinst.runCore] at run
  exact St.of_diff (v := B256.sltCheck) (Devm.diffBurn_of_applyBinary run)

/-- **Checked multiplication, inverted.** -/
theorem ric_vyMulT {x y : B256} (hf : fail.noOk = true)
    (run : SFunc.RunCut fs sevm C (St b (y :: x :: S) M G) (vyMulT h l fail k) r) :
    B256.Nofm x y ∧ ∃ G', SFunc.RunCut fs sevm C (St b ((x * y) :: S) M G') k r := by
  unfold vyMulT at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G1, rfl⟩ := ri_dup (w := y) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G2, rfl⟩ := ri_dup (w := x) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G3, rfl⟩ := ri_mul s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_dup (w := x) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_iszero s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G6, rfl⟩ := ri_dup (w := y) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G7, rfl⟩ := ri_dup (w := x) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G8, rfl⟩ := ri_dup (w := x * y) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G9, rfl⟩ := ri_div s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G10, rfl⟩ := ri_eq s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G11, rfl⟩ := ri_or s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G12, rfl⟩ := ri_push s1
  rcases ric_branch run with ⟨-, G13, run⟩ | ⟨hw, G13, run⟩
  · exact (run.false_of_noOk hf).elim
  obtain ⟨G14, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G15, rfl⟩ := ri_dup (w := x * y) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G16, rfl⟩ := ri_swap (S' := (x * y) :: (x * y) :: y :: x :: S) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G17, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G18, rfl⟩ := ri_swap (S' := y :: (x * y) :: x :: S) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G19, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G20, rfl⟩ := ri_swap (S' := x :: (x * y) :: S) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G21, rfl⟩ := ri_pop s1
  exact ⟨B256.nofm_of_mulGuard (B256.or_eqCheck_ne_zero hw), G21, run⟩

/-- **Checked addition, inverted.** -/
theorem ric_vyAddT {x y : B256} (hf : fail.noOk = true)
    (run : SFunc.RunCut fs sevm C (St b (y :: x :: S) M G) (vyAddT h l fail k) r) :
    x.toNat + y.toNat < 2 ^ 256 ∧ ∃ G', SFunc.RunCut fs sevm C (St b ((x + y) :: S) M G') k r := by
  unfold vyAddT at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G1, rfl⟩ := ri_dup (w := x) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G2, rfl⟩ := ri_dup (w := y) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G3, rfl⟩ := ri_dup (w := x) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_add s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_lt s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G6, rfl⟩ := ri_iszero s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G7, rfl⟩ := ri_push s1
  rcases ric_branch run with ⟨-, G8, run⟩ | ⟨hw, G8, run⟩
  · exact (run.false_of_noOk hf).elim
  obtain ⟨G9, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G10, rfl⟩ := ri_dup (w := y) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G11, rfl⟩ := ri_dup (w := x) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G12, rfl⟩ := ri_add s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G13, rfl⟩ := ri_swap (S' := y :: (x + y) :: x :: S) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G14, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G15, rfl⟩ := ri_swap (S' := x :: (x + y) :: S) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G16, rfl⟩ := ri_pop s1
  refine ⟨?_, G16, run⟩
  have h0 := eq_zero_of_iszero_ne_zero hw
  rw [B256.nof_iff_not_add_lt]
  intro hlt
  simp only [B256.ltCheck, hlt, ↓reduceIte] at h0
  exact absurd h0 (by decide)

/-- **Checked subtraction, inverted.** -/
theorem ric_vySubT {x y : B256} (hf : fail.noOk = true)
    (run : SFunc.RunCut fs sevm C (St b (y :: x :: S) M G) (vySubT h l fail k) r) :
    y.toNat ≤ x.toNat ∧ ∃ G', SFunc.RunCut fs sevm C (St b ((x - y) :: S) M G') k r := by
  unfold vySubT at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G1, rfl⟩ := ri_dup (w := y) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G2, rfl⟩ := ri_dup (w := x) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G3, rfl⟩ := ri_lt s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_iszero s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_push s1
  rcases ric_branch run with ⟨-, G6, run⟩ | ⟨hw, G6, run⟩
  · exact (run.false_of_noOk hf).elim
  obtain ⟨G7, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G8, rfl⟩ := ri_dup (w := y) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G9, rfl⟩ := ri_dup (w := x) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G10, rfl⟩ := ri_sub s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G11, rfl⟩ := ri_swap (S' := y :: (x - y) :: x :: S) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G12, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G13, rfl⟩ := ri_swap (S' := x :: (x - y) :: S) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G14, rfl⟩ := ri_pop s1
  exact ⟨toNat_ge_of_ltCheck_eq_zero (eq_zero_of_iszero_ne_zero hw), G14, run⟩

/-- **Checked division, inverted.** -/
theorem ric_vyDivT {x y : B256} (hf : fail.noOk = true)
    (run : SFunc.RunCut fs sevm C (St b (y :: x :: S) M G) (vyDivT h l fail k) r) :
    y ≠ 0 ∧ ∃ G', SFunc.RunCut fs sevm C (St b ((x / y) :: S) M G') k r := by
  unfold vyDivT at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G1, rfl⟩ := ri_dup (w := y) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G2, rfl⟩ := ri_dup (w := y) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G3, rfl⟩ := ri_push s1
  rcases ric_branch run with ⟨-, G4, run⟩ | ⟨hw, G4, run⟩
  · exact (run.false_of_noOk hf).elim
  obtain ⟨G5, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G6, rfl⟩ := ri_dup (w := x) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G7, rfl⟩ := ri_div s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G8, rfl⟩ := ri_swap (S' := y :: (x / y) :: x :: S) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G9, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G10, rfl⟩ := ri_swap (S' := x :: (x / y) :: S) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G11, rfl⟩ := ri_pop s1
  exact ⟨hw, G11, run⟩

end Inv

/-! ## Word-slot frames -/

/-- `M` holds the words `ws` at `lo, lo + 32, …` inside `M0`'s (word-aligned) size, has
`M0`'s size and agrees with `M0` outside `[lo, lo + 32 * ws.length)`. -/
structure WordFrame (M0 M : Mem) (lo : Nat) (ws : List B256) : Prop where
  size : M.size = M0.size
  aligned : M0.size % 32 = 0
  cover : lo + 32 * ws.length ≤ M0.size
  word : ∀ j (hj : j < ws.length), memWord M (lo + 32 * j) = ws[j]
  agree : Mem.AgreeOutside M0 M lo (lo + 32 * ws.length)
  wf : Mem.Wf M0 → Mem.Wf M

theorem WordFrame.init {M0 : Mem} {lo n : Nat} (hsz : M0.size % 32 = 0)
    (hc : lo + 32 * n ≤ M0.size) : WordFrame M0 M0 lo (frameWords M0 lo n) where
  size := rfl
  aligned := hsz
  cover := by rw [length_frameWords]; exact hc
  word j hj := by simp only [frameWords, List.getElem_map, List.getElem_range]
  agree := Mem.AgreeOutside.refl _ _ _
  wf h := h

theorem WordFrame.read {M0 M : Mem} {lo : Nat} {ws : List B256} (hF : WordFrame M0 M lo ws)
    {j : Nat} {v : B256} (hv : ws[j]? = some v) :
    Bytes.toB256 (M.read (lo + 32 * j) 32).1 = v ∧ (M.read (lo + 32 * j) 32).2 = M := by
  obtain ⟨hj, hvj⟩ := List.getElem?_eq_some_iff.mp hv
  refine ⟨(hF.word j hj).trans hvj, read_covered rfl (by rw [hF.size]; exact hF.aligned) ?_⟩
  rw [hF.size]
  have := hF.cover
  have : j + 1 ≤ ws.length := hj
  omega

theorem WordFrame.write {M0 M : Mem} {lo : Nat} {ws : List B256} (hF : WordFrame M0 M lo ws)
    {j : Nat} (hj : j < ws.length) (v : B256) :
    WordFrame M0 (M.write (lo + 32 * j) v.toBytes) lo (ws.set j v) where
  size := by
    have := hF.cover
    have : j + 1 ≤ ws.length := hj
    rw [Mem.size_write_word_of_add_le (by rw [hF.size]; omega), hF.size]
  aligned := hF.aligned
  cover := by rw [List.length_set]; exact hF.cover
  word j' hj' := by
    rw [List.length_set] at hj'
    rw [List.getElem_set]
    by_cases e : j = j'
    · subst e
      simp only [↓reduceIte]
      exact (Mem.memWord_write_word M _ v).1
    · simp only [e, ↓reduceIte]; rw [← hF.word j' hj']
      have := hF.cover
      have : j + 1 ≤ ws.length := hj
      have : j' + 1 ≤ ws.length := hj'
      refine memWord_write_of_disjoint (by rw [hF.size]; omega) ?_
      rw [B256.length_toBytes]
      rcases Nat.lt_or_gt_of_ne e with h | h <;> [right; left] <;> omega
  agree := by
    rw [List.length_set]
    refine hF.agree.trans ?_
    have hw := Mem.write_agree M (lo + 32 * j) v.toBytes
    rw [B256.length_toBytes] at hw
    have := hF.cover
    have : j + 1 ≤ ws.length := hj
    exact ⟨hw.1, fun i hi hout => hw.2 i hi (by omega)⟩
  wf h := (hF.wf h).write _ _

/-- What a callee leaves when it writes its result to the scratch word `0` on its way out:
the memory has `M0`'s size, keeps every byte of `M0` off the scratch word and the frame window
(the unfolded form of keeping `M0` off those windows), and reads `v` at `0`. -/
structure ScratchOut (M0 M : Mem) (lo hi : Nat) (v : B256) : Prop where
  size : M.size = M0.size
  keeps : M0.size ≤ M.size ∧
    ∀ i, i < M0.size → ¬ (i < 32 ∨ (lo ≤ i ∧ i < hi)) → M.data.getD i 0 = M0.data.getD i 0
  word0 : memWord M 0 = v
  wf : Mem.Wf M0 → Mem.Wf M

theorem WordFrame.scratch {M0 M : Mem} {lo : Nat} {ws : List B256} (hF : WordFrame M0 M lo ws)
    (hlo : 32 ≤ lo) (v : B256) :
    ScratchOut M0 (M.write 0 v.toBytes) lo (lo + 32 * ws.length) v ∧
      ∀ j w, ws[j]? = some w → memWord (M.write 0 v.toBytes) (lo + 32 * j) = w := by
  have hw := Mem.write_agree M 0 v.toBytes
  rw [B256.length_toBytes] at hw
  have hsz : (M.write 0 v.toBytes).size = M0.size := by
    rw [Mem.size_write_word_of_add_le (by rw [hF.size]; have := hF.cover; omega), hF.size]
  refine ⟨⟨hsz, ⟨by rw [hsz], fun i hi hn => ?_⟩, (Mem.memWord_write_word M 0 v).1,
    fun h => (hF.wf h).write _ _⟩, fun j w hv => ?_⟩
  · rw [hw.2 i (by rw [hF.size]; exact hi) (by omega)]
    exact hF.agree.2 i hi (by omega)
  · obtain ⟨hj, hvj⟩ := List.getElem?_eq_some_iff.mp hv
    have := hF.cover
    have : j + 1 ≤ ws.length := hj
    rw [memWord_write_of_disjoint (by rw [hF.size]; omega) (by rw [B256.length_toBytes]; omega),
      hF.word j hj, hvj]

/-- On a well-formed memory, a `ScratchOut` memory keeps `M0` off the scratch word and the frame
window. -/
theorem ScratchOut.keepsOff {M0 M : Mem} {lo hi : Nat} {v : B256} (h : ScratchOut M0 M lo hi v)
    (hwf : Mem.Wf M0) : Mem.KeepsOff M0 M [(0, 32), (lo, hi)] := by
  refine ⟨h.keeps.1, fun i hi' => ?_⟩
  have h0 := hi' (0, 32) List.mem_cons_self
  have h1 := hi' (lo, hi) (List.mem_cons_of_mem _ List.mem_cons_self)
  by_cases hlt : i < M0.size
  · exact h.keeps.2 i hlt (by simp only at h0 h1; omega)
  · have hw : Mem.Wf M := h.wf hwf
    unfold Mem.Wf at hwf hw
    have e1 : M.data.getD i 0 = 0 := by
      simp only [Array.getD, show ¬ i < M.data.size by rw [h.size] at hw; omega, ↓reduceDIte]
    have e2 : M0.data.getD i 0 = 0 := by
      simp only [Array.getD, show ¬ i < M0.data.size by omega, ↓reduceDIte]
    rw [e1, e2]

/-- A `ScratchOut` memory carries its result word. -/
theorem ScratchOut.words {M0 M : Mem} {lo hi : Nat} {v : B256} (h : ScratchOut M0 M lo hi v)
    (hs : 32 ≤ M0.size) : Words M [(0, v)] :=
  Words.cons.mpr ⟨⟨by rw [h.size]; exact hs, h.word0⟩, Words.nil M⟩

section FrameSteps

variable {fs : List SFunc} {sevm : Sevm} {C : List Nat} {b : Devm} {S : List B256} {M0 M : Mem}
  {G : Nat} {r : Seg} {f : SFunc} {lo : Nat} {ws : List B256}

/-- `MLOAD` of frame slot `j`, inverted. -/
theorem ric_mloadF (hF : WordFrame M0 M lo ws) (j : Nat) {i v : B256}
    (hi : i.toNat = lo + 32 * j) (hv : ws[j]? = some v)
    (run : SFunc.RunCut fs sevm C (St b (i :: S) M G) (.next (.reg .mload) f) r) :
    ∃ G', SFunc.RunCut fs sevm C (St b (v :: S) M G') f r := by
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G1, rfl⟩ := ri_mload s1
  obtain ⟨h1, h2⟩ := hF.read hv
  rw [hi, h1, h2] at run
  exact ⟨G1, run⟩

/-- `PUSH2 o; MLOAD` of frame slot `j`, inverted. -/
theorem ric_pushMloadF (hF : WordFrame M0 M lo ws) (j : Nat) {h l : UInt8}
    {le : [h, l].length ≤ 32} {v : B256}
    (hi : (Bytes.toB256 [h, l]).toNat = lo + 32 * j) (hv : ws[j]? = some v)
    (run : SFunc.RunCut fs sevm C (St b S M G) (.next (.push [h, l] le) (.next (.reg .mload) f))
      r) :
    ∃ G', SFunc.RunCut fs sevm C (St b (v :: S) M G') f r := by
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G1, rfl⟩ := ri_push s1
  exact ric_mloadF hF j hi hv run

/-- `MSTORE` into frame slot `j`, inverted. -/
theorem ric_mstoreF (hF : WordFrame M0 M lo ws) (j : Nat) {i v : B256}
    (hi : i.toNat = lo + 32 * j) (hj : j < ws.length)
    (run : SFunc.RunCut fs sevm C (St b (i :: v :: S) M G) (.next (.reg .mstore) f) r) :
    ∃ G' M', WordFrame M0 M' lo (ws.set j v) ∧ SFunc.RunCut fs sevm C (St b S M' G') f r := by
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G1, rfl⟩ := ri_mstore s1
  rw [hi] at run
  exact ⟨G1, _, hF.write hj v, run⟩

/-- `PUSH2 o; MSTORE` into frame slot `j`, inverted. -/
theorem ric_pushMstoreF (hF : WordFrame M0 M lo ws) (j : Nat) {h l : UInt8}
    {le : [h, l].length ≤ 32} {v : B256}
    (hi : (Bytes.toB256 [h, l]).toNat = lo + 32 * j) (hj : j < ws.length)
    (run : SFunc.RunCut fs sevm C (St b (v :: S) M G)
      (.next (.push [h, l] le) (.next (.reg .mstore) f)) r) :
    ∃ G' M', WordFrame M0 M' lo (ws.set j v) ∧ SFunc.RunCut fs sevm C (St b S M' G') f r := by
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G1, rfl⟩ := ri_push s1
  exact ric_mstoreF hF j hi hj run

end FrameSteps

/-! ## Forward -/

theorem B256.or_ne_zero_of_left {a c : B256} (ha : a = 1) (hc : c = 0 ∨ c = 1) : (a ||| c) ≠ 0 := by
  subst ha; rcases hc with rfl | rfl <;> decide

theorem B256.or_ne_zero_of_right {a c : B256} (ha : a = 0 ∨ a = 1) (hc : c = 1) :
    (a ||| c) ≠ 0 := by
  subst hc; rcases ha with rfl | rfl <;> decide

theorem B256.eqCheck_cases (a c : B256) : B256.eqCheck a c = 0 ∨ B256.eqCheck a c = 1 := by
  unfold B256.eqCheck; split <;> simp only [true_or, or_true]

/-- The multiplication guard holds for a product that does not wrap. -/
theorem B256.mulGuard_of_nofm {x y : B256} (h : B256.Nofm x y) :
    (B256.eqCheck ((x * y) / x) y ||| B256.eqCheck x 0) ≠ 0 := by
  by_cases hx : x = 0
  · refine B256.or_ne_zero_of_right (B256.eqCheck_cases _ _) ?_
    unfold B256.eqCheck; rw [ite_eq_left hx]
  · refine B256.or_ne_zero_of_left ?_ (B256.eqCheck_cases _ _)
    unfold B256.eqCheck
    rw [ite_eq_left]
    apply B256.toNat_inj
    rw [B256.toNat_div hx, B256.toNat_mul_eq_of_nofm h]
    exact Nat.mul_div_cancel_left _ (B256.toNat_pos hx)

section Fwd

variable {fs : List SFunc} {sevm : Sevm} {C : List Nat} {b : Devm} {S : List B256} {M : Mem}
  {G : Nat} {r : Seg} {h l : UInt8} {fail k : SFunc}

/-- **Checked multiplication, forward** (69 gas). -/
theorem rxc_vyMulT {x y : B256} (hn : B256.Nofm x y) (hroom : S.length + 8 < 1024)
    (kk : SFunc.RunExactCut fs sevm C (St b ((x * y) :: S) M G) k r) :
    SFunc.RunExactCut fs sevm C (St b (y :: x :: S) M (G + 69)) (vyMulT h l fail k) r := by
  unfold vyMulT
  refine rxc_dup (w := y) rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_dup (w := x) rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_binary (fn := (· * ·)) (c := gLow) (v := x * y) (by rintro ⟨⟩) (fun _ => rfl) rfl
    (by simp only [List.length_cons]; omega) ?_
  refine rxc_dup (w := x) rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_iszero rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_dup (w := y) rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_dup (w := x) rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_dup (w := x * y) rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_div rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_eq rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_or rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_push rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_branch_succ (B256.mulGuard_of_nofm hn) (rxc_dest ?_)
  refine rxc_dup (w := x * y) rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_swap (S' := (x * y) :: (x * y) :: y :: x :: S) rfl ?_
  refine rxc_pop ?_
  refine rxc_swap (S' := y :: (x * y) :: x :: S) rfl ?_
  refine rxc_pop ?_
  refine rxc_swap (S' := x :: (x * y) :: S) rfl ?_
  exact rxc_pop kk

/-- **Checked addition, forward** (51 gas). -/
theorem rxc_vyAddT {x y : B256} (hn : x.toNat + y.toNat < 2 ^ 256) (hroom : S.length + 8 < 1024)
    (kk : SFunc.RunExactCut fs sevm C (St b ((x + y) :: S) M G) k r) :
    SFunc.RunExactCut fs sevm C (St b (y :: x :: S) M (G + 51)) (vyAddT h l fail k) r := by
  unfold vyAddT
  refine rxc_dup (w := x) rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_dup (w := y) rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_dup (w := x) rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_add (by simp only [List.length_cons]; omega) ?_
  refine rxc_lt rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_iszero rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_push rfl (by simp only [List.length_cons]; omega) ?_
  have hnl : ¬ (x + y < x) := (B256.nof_iff_not_add_lt x y).mp hn
  refine rxc_branch_succ ?_ (rxc_dest ?_)
  · simp only [B256.ltCheck, hnl, ↓reduceIte]; decide
  refine rxc_dup (w := y) rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_dup (w := x) rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_add (by simp only [List.length_cons]; omega) ?_
  refine rxc_swap (S' := y :: (x + y) :: x :: S) rfl ?_
  refine rxc_pop ?_
  refine rxc_swap (S' := x :: (x + y) :: S) rfl ?_
  exact rxc_pop kk

/-- **Checked subtraction, forward** (45 gas). -/
theorem rxc_vySubT {x y : B256} (hn : y.toNat ≤ x.toNat) (hroom : S.length + 8 < 1024)
    (kk : SFunc.RunExactCut fs sevm C (St b ((x - y) :: S) M G) k r) :
    SFunc.RunExactCut fs sevm C (St b (y :: x :: S) M (G + 45)) (vySubT h l fail k) r := by
  unfold vySubT
  refine rxc_dup (w := y) rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_dup (w := x) rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_lt rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_iszero rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_push rfl (by simp only [List.length_cons]; omega) ?_
  have hnl : ¬ (x < y) := by rw [B256.lt_iff_toNat_lt_toNat]; omega
  refine rxc_branch_succ ?_ (rxc_dest ?_)
  · simp only [B256.ltCheck, hnl, ↓reduceIte]; decide
  refine rxc_dup (w := y) rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_dup (w := x) rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_sub' rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_swap (S' := y :: (x - y) :: x :: S) rfl ?_
  refine rxc_pop ?_
  refine rxc_swap (S' := x :: (x - y) :: S) rfl ?_
  exact rxc_pop kk

/-- **Checked division, forward** (38 gas). -/
theorem rxc_vyDivT {x y : B256} (hn : y ≠ 0) (hroom : S.length + 8 < 1024)
    (kk : SFunc.RunExactCut fs sevm C (St b ((x / y) :: S) M G) k r) :
    SFunc.RunExactCut fs sevm C (St b (y :: x :: S) M (G + 38)) (vyDivT h l fail k) r := by
  unfold vyDivT
  refine rxc_dup (w := y) rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_dup (w := y) rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_push rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_branch_succ hn (rxc_dest ?_)
  refine rxc_dup (w := x) rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_div rfl (by simp only [List.length_cons]; omega) ?_
  refine rxc_swap (S' := y :: (x / y) :: x :: S) rfl ?_
  refine rxc_pop ?_
  refine rxc_swap (S' := x :: (x / y) :: S) rfl ?_
  exact rxc_pop kk

/-- `MLOAD` of frame slot `j`, forward (3 gas). -/
theorem rxc_mloadF {M0 : Mem} {lo : Nat} {ws : List B256} (hF : WordFrame M0 M lo ws) (j : Nat)
    {i v : B256} {f : SFunc} (hi : i.toNat = lo + 32 * j) (hv : ws[j]? = some v)
    (hroom : S.length < 1024)
    (kk : SFunc.RunExactCut fs sevm C (St b (v :: S) M G) f r) :
    SFunc.RunExactCut fs sevm C (St b (i :: S) M (G + 3)) (.next (.reg .mload) f) r := by
  obtain ⟨hj, -⟩ := List.getElem?_eq_some_iff.mp hv
  have hsz : M.size % 32 = 0 := by rw [hF.size]; exact hF.aligned
  have hcov : i.toNat + 32 ≤ M.size := by
    rw [hF.size, hi]; have := hF.cover; have : j + 1 ≤ ws.length := hj; omega
  obtain ⟨h1, h2⟩ := hF.read hv
  exact rxc_mload (mload_covered_cost' hsz hcov) (by rw [hi]; exact h1) (by rw [hi]; exact h2)
    hroom kk

/-- `PUSH2 o; MLOAD` of frame slot `j`, forward (6 gas). -/
theorem rxc_pushMloadF {M0 : Mem} {lo : Nat} {ws : List B256} (hF : WordFrame M0 M lo ws)
    (j : Nat) {hh ll : UInt8} {le : [hh, ll].length ≤ 32} {v : B256} {f : SFunc}
    (hi : (Bytes.toB256 [hh, ll]).toNat = lo + 32 * j) (hv : ws[j]? = some v)
    (hroom : S.length + 1 < 1024)
    (kk : SFunc.RunExactCut fs sevm C (St b (v :: S) M G) f r) :
    SFunc.RunExactCut fs sevm C (St b S M (G + 6))
      (.next (.push [hh, ll] le) (.next (.reg .mload) f)) r :=
  rxc_push rfl (by omega) (rxc_mloadF hF j hi hv (by omega) kk)

/-- `MSTORE` into frame slot `j`, forward (3 gas). -/
theorem rxc_mstoreF {M0 : Mem} {lo : Nat} {ws : List B256} (hF : WordFrame M0 M lo ws) (j : Nat)
    {i v : B256} {f : SFunc} (hi : i.toNat = lo + 32 * j) (hj : j < ws.length)
    (kk : SFunc.RunExactCut fs sevm C (St b S (M.write (lo + 32 * j) v.toBytes) G) f r) :
    SFunc.RunExactCut fs sevm C (St b (i :: v :: S) M (G + 3)) (.next (.reg .mstore) f) r := by
  have hsz : M.size % 32 = 0 := by rw [hF.size]; exact hF.aligned
  have hcov : i.toNat + 32 ≤ M.size := by
    rw [hF.size, hi]; have := hF.cover; have : j + 1 ≤ ws.length := hj; omega
  exact rxc_mstore (mstore_covered_cost' hsz hcov) (by rw [hi]) kk

/-- `PUSH2 o; MSTORE` into frame slot `j`, forward (6 gas). -/
theorem rxc_pushMstoreF {M0 : Mem} {lo : Nat} {ws : List B256} (hF : WordFrame M0 M lo ws)
    (j : Nat) {hh ll : UInt8} {le : [hh, ll].length ≤ 32} {v : B256} {f : SFunc}
    (hi : (Bytes.toB256 [hh, ll]).toNat = lo + 32 * j) (hj : j < ws.length)
    (hroom : S.length + 1 < 1024)
    (kk : SFunc.RunExactCut fs sevm C (St b S (M.write (lo + 32 * j) v.toBytes) G) f r) :
    SFunc.RunExactCut fs sevm C (St b (v :: S) M (G + 6))
      (.next (.push [hh, ll] le) (.next (.reg .mstore) f)) r :=
  rxc_push rfl (by simp only [List.length_cons]; omega) (rxc_mstoreF hF j hi hj kk)

end Fwd

/-! ## Checked operations read back as guards (for the forward walks) -/

section CheckedInv

open Blanc.StableSwapNewton

theorem chkMul_inv {x y : B256} {v : Nat} (h : chkMul x.toNat y.toNat = some v) :
    B256.Nofm x y ∧ v = (x * y).toNat := by
  unfold chkMul wordSize at h
  split at h
  · rename_i hlt
    have hn : B256.Nofm x y := hlt
    exact ⟨hn, by rw [B256.toNat_mul_eq_of_nofm hn]; exact (Option.some.inj h).symm⟩
  · cases h

theorem chkAdd_inv {x y : B256} {v : Nat} (h : chkAdd x.toNat y.toNat = some v) :
    x.toNat + y.toNat < 2 ^ 256 ∧ v = (x + y).toNat := by
  unfold chkAdd wordSize at h
  split at h
  · rename_i hlt
    refine ⟨hlt, ?_⟩
    rw [B256.toNat_add, Nat.lo, Nat.mod_eq_of_lt hlt]; exact (Option.some.inj h).symm
  · cases h

theorem chkSub_inv {x y : B256} {v : Nat} (h : chkSub x.toNat y.toNat = some v) :
    y.toNat ≤ x.toNat ∧ v = (x - y).toNat := by
  unfold chkSub at h
  split at h
  · rename_i hle
    refine ⟨hle, ?_⟩
    rw [B256.toNat_sub_eq_of_le _ _ (B256.le_iff_toNat_le_toNat.mpr hle)]
    exact (Option.some.inj h).symm
  · cases h

theorem chkDiv_inv {x y : B256} {v : Nat} (h : chkDiv x.toNat y.toNat = some v) :
    y ≠ 0 ∧ v = (x / y).toNat := by
  unfold chkDiv at h
  split at h
  · cases h
  · rename_i hne
    have hy : y ≠ 0 := fun h0 => hne (by rw [h0]; rfl)
    exact ⟨hy, by rw [B256.toNat_div hy]; exact (Option.some.inj h).symm⟩

end CheckedInv

/-! ## `JUMPI` into a goto entry, forward -/

section FwdBranchTo

variable {fs : List SFunc} {sevm : Sevm} {C : List Nat} {b : Devm} {S : List B256} {M : Mem}
  {G : Nat} {r : Seg} {f g : SFunc} {j : Nat}

theorem rxc_branchTo_zero {d : B256} (k : SFunc.RunExactCut fs sevm C (St b S M G) f r) :
    SFunc.RunExactCut fs sevm C (St b (d :: 0 :: S) M (G + 10)) (.branchTo f j) r :=
  .toZero d popBurnBy_St2 k

theorem rxc_branchTo_cut {d w : B256} (hw : w ≠ 0) (hj : j ∈ C) :
    SFunc.RunExactCut fs sevm C (St b (d :: w :: S) M (G + 10)) (.branchTo f j)
      (.at j (St b S M G)) :=
  .toSuccCut d w hw hj popBurnBy_St2

theorem rxc_branchTo_succ {d w : B256} (hw : w ≠ 0) (hjC : j ∉ C) (hj : fs[j]? = some g)
    (k : SFunc.RunExactCut fs sevm C (St b S M G) g r) :
    SFunc.RunExactCut fs sevm C (St b (d :: w :: S) M (G + 10)) (.branchTo f j) r :=
  .toSucc d w hw hjC hj popBurnBy_St2 k

end FwdBranchTo

/-! ## Small word facts for the walks -/

/-- Stack room, whatever the shape of the stack's known prefix. -/
macro "vy_room" : tactic => `(tactic| first | omega | (simp only [List.length_cons]; omega))

theorem toB256_eq_toB256_iff {a c : Nat} (ha : a < 2 ^ 256) (hc : c < 2 ^ 256) :
    Nat.toB256 a = Nat.toB256 c ↔ a = c := by
  constructor
  · intro h
    have := congrArg B256.toNat h
    rwa [B256.toNat_toB256_of_lt ha, B256.toNat_toB256_of_lt hc] at this
  · intro h; rw [h]

theorem gtCheck_toNat (x y : B256) : B256.gtCheck x y = if y.toNat < x.toNat then 1 else 0 := by
  unfold B256.gtCheck
  by_cases h : y.toNat < x.toNat
  · rw [ite_eq_left h, ite_eq_left (by rw [gt_iff_lt, B256.lt_iff_toNat_lt_toNat]; exact h)]
  · rw [ite_eq_right h, ite_eq_right (by rw [gt_iff_lt, B256.lt_iff_toNat_lt_toNat]; exact h)]

end Blanc.Lift
