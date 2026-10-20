import Blanc.Lift.Curve3Pool.Callee.GetDTrees
import Blanc.Lift.Curve3Pool.Callee.GetYDLoop
import Blanc.Lift.Curve3Pool.Model

/-!
# `get_D`'s Newton loop with its nested `D_P` loop, inverted

The frame of `get_D` is the sixteen words at `0x140 … 0x320` (`gdFrame`): `xp[0..2]`, `amp`,
the return slot, `S`, the `S`-loop `_x` and counter, an unused word, `Dprev`, `D`, `Ann`, the
outer counter, `D_P`, the inner `_x` and the inner counter.  At the outer head (`0x58c`) the
stack holds `255` over the counter address `0x2c0` (`gdStk`); inside the inner loop `3` over
`0x320` sits above it (`gdIStk`).

* `ric_gdExit`, `ric_gdTail`: the exit at `0x79b` and the outer counter tail at `0x78a`;
* `ric_gdInner`: one inner iteration, `D_P = D_P * D / (xp[j] * N_COINS)`;
* `gdRest_step`: the rest of a pass, given `dPChk` for the inner loop's result: the checked
  body `bodyDChk` and the stopping test `closeEnough 1`, as `FuelStep`;
* `gdLoop_sound`: every run from the first (inline) pass ends as `gdOut` of the fuel loop.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune
open Blanc.StableSwapNewton

/-- `get_D`'s frame, `0x140 … 0x320`. -/
def gdFrame (x0 x1 x2 amp ρ s xs sc w8 dp d ann n p xv ic : B256) : List B256 :=
  [x0, x1, x2, amp, ρ, s, xs, sc, w8, dp, d, ann, n, p, xv, ic]

/-- The outer loop's stack: `255` over the counter address `0x2c0`. -/
abbrev gdStk (S : List B256) : List B256 := Nat.toB256 255 :: Nat.toB256 0x2c0 :: S

/-- The inner loop's stack: `3` over the counter address `0x320`, over the outer loop's. -/
abbrev gdIStk (S : List B256) : List B256 := Nat.toB256 3 :: Nat.toB256 0x320 :: gdStk S

/-- The balances as the model's vector. -/
abbrev gdX (x0 x1 x2 : B256) : Fin 3 → Nat := (V3.mk x0.toNat x1.toNat x2.toNat).get

/-- The outer head state: counter `n`, iterate `D`; fixed `xp`, the return slot, `S`, `Ann`. -/
def gdAt (b : Devm) (S : List B256) (M0 : Mem) (x0 x1 x2 ρ s ann : B256) (n D : Nat)
    (d : Devm) : Prop :=
  D < 2 ^ 256 ∧ ∃ M G amp xs sc w8 dp p xv ic, d = St b (gdStk S) M G ∧
    WordFrame M0 M 0x140 (gdFrame x0 x1 x2 amp ρ s xs sc w8 dp (Nat.toB256 D) ann (Nat.toB256 n)
      p xv ic)

/-- How a callee with the frame `[0x140, 0x340)` leaves: returning `v` over the caller's
stack, its memory as `ScratchOut`. -/
def calleeOut (b : Devm) (S : List B256) (M0 : Mem) (v : Option Nat) (r : Seg) : Prop :=
  ∃ y, v = some y ∧ y < 2 ^ 256 ∧ ∃ M G, r = .done (.returned (St b (Nat.toB256 y :: S) M G)) ∧
    ScratchOut M0 M 0x140 0x340 (Nat.toB256 y)

section Walk

variable {sevm : Sevm} {C : List Nat} {b : Devm} {S : List B256} {M0 M : Mem} {G : Nat}
  {r : Seg} {ws : List B256}

-- SEGMENT: gdExit
/-- **The exit**, inverted: `return D` leaves the `D` slot over the caller's stack. -/
theorem ric_gdExit (hF : WordFrame M0 M 0x140 ws) (hlen : ws.length = 16) {dw ρ : B256}
    (hd : ws[10]? = some dw) (hρ : ws[4]? = some ρ)
    (run : SFunc.RunCut progYD sevm C (St b (gdStk S) M G) gdExit r) :
    ∃ M' G', r = .done (.returned (St b (dw :: S) M' G')) ∧ ScratchOut M0 M' 0x140 0x340 dw := by
  unfold gdExit at run
  obtain ⟨G1, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G2, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G3, rfl⟩ := ri_pop s1
  obtain ⟨G4, run⟩ := ric_pushMloadF hF 10 (by decide) hd run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G6, rfl⟩ := ri_mstore s1
  rw [show (Bytes.toB256 [0x00]).toNat = 0 by decide] at run
  obtain ⟨hout, hw⟩ := hF.scratch (by decide) dw
  rw [hlen] at hout
  have hsz : (M.write 0 dw.toBytes).size % 32 = 0 := by rw [hout.size]; exact hF.aligned
  have hcov : ∀ o, o + 32 ≤ 0x340 → ((M.write 0 dw.toBytes).read o 32).2 = M.write 0 dw.toBytes :=
    fun o ho => read_covered rfl hsz (by rw [hout.size]; have := hF.cover; rw [hlen] at this; omega)
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G7, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G8, rfl⟩ := ri_mload s1
  rw [show (Bytes.toB256 [0x00]).toNat = 0 by decide, hcov 0 (by decide)] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G9, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G10, rfl⟩ := ri_mload s1
  rw [show (Bytes.toB256 [0x01, 0xc0]).toNat = 0x140 + 32 * 4 by decide,
    hcov _ (by decide)] at run
  have hρ' : Bytes.toB256 ((M.write 0 dw.toBytes).read (0x140 + 32 * 4) 32).1 = ρ := hw 4 ρ hρ
  rw [hρ'] at run
  obtain ⟨G11, hr⟩ := ric_ret run
  refine ⟨_, G11, ?_, hout⟩
  have h0 : Bytes.toB256 ((M.write 0 dw.toBytes).read 0 32).1 = dw := hout.word0
  rw [hr, h0]

-- SEGMENT: gdTail
/-- **The outer counter tail**, inverted. -/
theorem ric_gdTail (hF : WordFrame M0 M 0x140 ws) (hlen : ws.length = 16) {n k : Nat}
    {fall : SFunc} (hn : ws[12]? = some (Nat.toB256 n)) (hn255 : n < 255) (hk : k ∈ C)
    (run : SFunc.RunCut progYD sevm C (St b (gdStk S) M G) (gdTail k fall) r) :
    ∃ G' M', WordFrame M0 M' 0x140 (ws.set 12 (Nat.toB256 (n + 1))) ∧
      ((n + 1 ≠ 255 ∧ r = .at k (St b (gdStk S) M' G')) ∨
        (n + 1 = 255 ∧ SFunc.RunCut progYD sevm C (St b (gdStk S) M' G') fall r)) := by
  unfold gdTail at run
  obtain ⟨G1, run⟩ := ric_dest run
  obtain ⟨G2, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G3, rfl⟩ := ri_dup (w := Nat.toB256 0x2c0) rfl s1
  obtain ⟨G4, run⟩ := ric_mloadF hF 12 (by decide) hn run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G6, rfl⟩ := ri_add s1
  rw [one_add_toB256 (by omega)] at run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G7, rfl⟩ := ri_dup (w := Nat.toB256 (n + 1)) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G8, rfl⟩ := ri_dup (w := Nat.toB256 0x2c0) rfl s1
  obtain ⟨G9, M1, hF1, run⟩ := ric_mstoreF hF 12 (by decide) (by rw [hlen]; decide) run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G10, rfl⟩ := ri_dup (w := Nat.toB256 255) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G11, rfl⟩ := ri_eq s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G12, rfl⟩ := ri_iszero s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G13, rfl⟩ := ri_push s1
  have hiff := toB256_eq_toB256_iff (a := 255) (c := n + 1) (by decide) (by omega)
  rcases ric_branchToCut hk run with ⟨hw, G14, run⟩ | ⟨hw, G14, hr⟩
  · refine ⟨G14, M1, hF1, .inr ⟨?_, run⟩⟩
    by_contra hne
    have : B256.eqCheck (Nat.toB256 255) (Nat.toB256 (n + 1)) = 0 := by
      unfold B256.eqCheck; rw [ite_eq_right (fun h => hne (hiff.mp h).symm)]
    rw [this] at hw
    exact absurd hw (by decide)
  · refine ⟨G14, M1, hF1, .inl ⟨fun he => hw ?_, hr⟩⟩
    unfold B256.eqCheck; rw [ite_eq_left (hiff.mpr he.symm)]; decide

/-- The address of `xp[j]`, `0x140 + 32 j`. -/
theorem gdXpAddr {j : Nat} (hj : j < 3) :
    (Bytes.toB256 [0x01, 0x40] + Nat.toB256 j * Bytes.toB256 [0x20]).toNat = 0x140 + 32 * j := by
  rcases j with _ | _ | _ | j
  · decide
  · decide
  · decide
  · omega

/-- The inner `D_P` step on naturals. -/
def gdPStep (p D x : Nat) : Option Nat := do chkDiv (← chkMul p D) (← chkMul x 3)

-- SEGMENT: gdInner
/-- **One inner iteration**, inverted up to its `JUMPI`: `D_P` becomes `gdPStep D_P D xp[j]`,
the counter `j + 1`. -/
theorem ric_gdInner (hF : WordFrame M0 M 0x140 ws) (hlen : ws.length = 16) {j : Nat}
    {x p d : B256} (hj : ws[15]? = some (Nat.toB256 j)) (hj3 : j < 3) (hx : ws[j]? = some x)
    (hp : ws[13]? = some p) (hd : ws[10]? = some d) {jmp : SFunc}
    (run : SFunc.RunCut progYD sevm C (St b (gdIStk S) M G) (gdInner jmp) r) :
    ∃ G' M' p', gdPStep p.toNat d.toNat x.toNat = some p'.toNat ∧
      WordFrame M0 M' 0x140 (((ws.set 14 x).set 13 p').set 15 (Nat.toB256 (j + 1))) ∧
      SFunc.RunCut progYD sevm C (St b (Bytes.toB256 [0x05, 0xa0] ::
        B256.eqCheck (B256.eqCheck (Nat.toB256 3) (Nat.toB256 (j + 1))) 0 :: gdIStk S) M' G')
        jmp r := by
  unfold gdInner at run
  obtain ⟨G1, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G2, rfl⟩ := ri_push s1
  obtain ⟨G3, run⟩ := ric_pushMloadF hF 15 (by decide) hj run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_mul s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G6, rfl⟩ := ri_add s1
  obtain ⟨G7, run⟩ := ric_mloadF hF j (gdXpAddr hj3) hx run
  obtain ⟨G8, M1, hF1, run⟩ := ric_pushMstoreF hF 14 (by decide) (by rw [hlen]; decide) run
  have hp1 : (ws.set 14 x)[13]? = some p := by rw [List.getElem?_set_ne (by decide)]; exact hp
  have hd1 : (ws.set 14 x)[10]? = some d := by rw [List.getElem?_set_ne (by decide)]; exact hd
  have hx1 : (ws.set 14 x)[14]? = some x := by
    rw [List.getElem?_set_self (by rw [hlen]; decide)]
  obtain ⟨G9, run⟩ := ric_pushMloadF hF1 13 (by decide) hp1 run
  obtain ⟨G10, run⟩ := ric_pushMloadF hF1 10 (by decide) hd1 run
  obtain ⟨hm1, G11, run⟩ := ric_vyMulT vyRevertT_noOk run
  obtain ⟨G12, run⟩ := ric_pushMloadF hF1 14 (by decide) hx1 run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G13, rfl⟩ := ri_push s1
  obtain ⟨hm2, G14, run⟩ := ric_vyMulT vyRevertT_noOk run
  obtain ⟨hdv, G15, run⟩ := ric_vyDivT vyRevertT_noOk run
  obtain ⟨G16, M2, hF2, run⟩ := ric_pushMstoreF hF1 13 (by decide)
    (by rw [List.length_set, hlen]; decide) run
  have hj2 : ((ws.set 14 x).set 13 ((p * d) / (x * Bytes.toB256 [0x03])))[15]? =
      some (Nat.toB256 j) := by
    rw [List.getElem?_set_ne (by decide), List.getElem?_set_ne (by decide)]; exact hj
  obtain ⟨G17, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G18, rfl⟩ := ri_dup (w := Nat.toB256 0x320) rfl s1
  obtain ⟨G19, run⟩ := ric_mloadF hF2 15 (by decide) hj2 run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G20, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G21, rfl⟩ := ri_add s1
  rw [one_add_toB256 (by omega)] at run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G22, rfl⟩ := ri_dup (w := Nat.toB256 (j + 1)) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G23, rfl⟩ := ri_dup (w := Nat.toB256 0x320) rfl s1
  obtain ⟨G24, M3, hF3, run⟩ := ric_mstoreF hF2 15 (by decide)
    (by rw [List.length_set, List.length_set, hlen]; decide) run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G25, rfl⟩ := ri_dup (w := Nat.toB256 3) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G26, rfl⟩ := ri_eq s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G27, rfl⟩ := ri_iszero s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G28, rfl⟩ := ri_push s1
  refine ⟨G28, M3, _, ?_, hF3, run⟩
  have e3 : (3 : Nat) = (Bytes.toB256 [0x03]).toNat := by decide
  unfold gdPStep
  rw [e3, chkMul_toNat_of_nofm hm1, chkMul_toNat_of_nofm hm2]
  simp only [Option.bind_eq_bind, Option.bind_some]
  exact chkDiv_toNat_of_ne hdv

/-- The Newton body on words: the checked body at the words' values is the word the bytes
compute, given the inner loop's `D_P`. -/
theorem bodyDChk_words {x : Fin 3 → Nat} {ann s p dw : B256} (hdp : dPChk x dw.toNat = some p.toNat)
    (hm1 : B256.Nofm ann s) (hm2 : B256.Nofm p (Bytes.toB256 [0x03]))
    (ha1 : (ann * s).toNat + (p * Bytes.toB256 [0x03]).toNat < 2 ^ 256)
    (hm3 : B256.Nofm (ann * s + p * Bytes.toB256 [0x03]) dw)
    (hs : (Bytes.toB256 [0x01]).toNat ≤ ann.toNat)
    (hm4 : B256.Nofm (ann - Bytes.toB256 [0x01]) dw)
    (hm5 : B256.Nofm (Bytes.toB256 [0x04]) p)
    (ha2 : ((ann - Bytes.toB256 [0x01]) * dw).toNat + (Bytes.toB256 [0x04] * p).toNat < 2 ^ 256)
    (hdv : (ann - Bytes.toB256 [0x01]) * dw + Bytes.toB256 [0x04] * p ≠ 0) :
    bodyDChk x ann.toNat s.toNat dw.toNat =
      some (((ann * s + p * Bytes.toB256 [0x03]) * dw) /
        ((ann - Bytes.toB256 [0x01]) * dw + Bytes.toB256 [0x04] * p)).toNat := by
  have e3 : (3 : Nat) = (Bytes.toB256 [0x03]).toNat := by decide
  have e1 : (1 : Nat) = (Bytes.toB256 [0x01]).toNat := by decide
  have e4 : (4 : Nat) = (Bytes.toB256 [0x04]).toNat := by decide
  unfold bodyDChk
  rw [hdp, e3, e1, e4]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [chkMul_toNat_of_nofm hm1, chkMul_toNat_of_nofm hm2]
  simp only [Option.bind_some]
  rw [chkAdd_toNat_of_lt ha1]
  simp only [Option.bind_some]
  rw [chkMul_toNat_of_nofm hm3, chkSub_toNat_of_le hs]
  simp only [Option.bind_some]
  rw [chkMul_toNat_of_nofm hm4, chkMul_toNat_of_nofm hm5]
  simp only [Option.bind_some]
  rw [chkAdd_toNat_of_lt ha2]
  simp only [Option.bind_some]
  exact chkDiv_toNat_of_ne hdv

-- SEGMENT: gdRest
/-- **The rest of a Newton pass**, inverted, at any copy (exit `e`, tail `t`, continuation head
`k`, fall-through `fall` after the last pass): given the inner loop's `D_P = dPChk x D`, the
checked body `bodyDChk x Ann S` and the stopping test `closeEnough 1`, as `FuelStep`. -/
theorem gdRest_step {x0 x1 x2 ρ s ann amp xs sc w8 dp p xv ic : B256} {e t k : Nat}
    {fall fall' : SFunc}
    (he : progYD[e]? = some gdExit) (ht : progYD[t]? = some (gdTail k fall'))
    (heC : e ∉ C) (htC : t ∉ C) (hkC : k ∈ C) (hfall : fall = gdExit ∨ fall = .undefined)
    (hfall' : fall' = gdExit ∨ fall' = .undefined)
    {n D : Nat} (hn : n < 255) (hD : D < 2 ^ 256)
    (hdp : dPChk (gdX x0 x1 x2) D = some p.toNat)
    (hF : WordFrame M0 M 0x140 (gdFrame x0 x1 x2 amp ρ s xs sc w8 dp (Nat.toB256 D) ann
      (Nat.toB256 n) p xv ic))
    (run : SFunc.RunCut progYD sevm C (St b (gdIStk S) M G) (gdRest e t k fall) r) :
    FuelStep k 255 (bodyDChk (gdX x0 x1 x2) ann.toNat s.toNat)
      (fun new prev => decide (closeEnough 1 new prev)) (gdAt b S M0 x0 x1 x2 ρ s ann)
      (calleeOut b S M0) n D r := by
  have hyN : (Nat.toB256 D).toNat = D := B256.toNat_toB256_of_lt hD
  unfold gdRest at run
  obtain ⟨G1, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G2, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G3, rfl⟩ := ri_pop s1
  obtain ⟨G4, run⟩ := ric_pushMloadF hF 10 (by decide) rfl run
  obtain ⟨G5, M1, hF1, run⟩ := ric_pushMstoreF hF 9 (by decide) (lt16 (by decide)) run
  obtain ⟨G6, run⟩ := ric_pushMloadF hF1 11 (by decide) rfl run
  obtain ⟨G7, run⟩ := ric_pushMloadF hF1 5 (by decide) rfl run
  obtain ⟨hm1, G8, run⟩ := ric_vyMulT vyRevertT_noOk run
  obtain ⟨G9, run⟩ := ric_pushMloadF hF1 13 (by decide) rfl run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G10, rfl⟩ := ri_push s1
  obtain ⟨hm2, G11, run⟩ := ric_vyMulT vyRevertT_noOk run
  obtain ⟨ha1, G12, run⟩ := ric_vyAddT vyRevertT_noOk run
  obtain ⟨G13, run⟩ := ric_pushMloadF hF1 10 (by decide) rfl run
  obtain ⟨hm3, G14, run⟩ := ric_vyMulT vyRevertT_noOk run
  obtain ⟨G15, run⟩ := ric_pushMloadF hF1 11 (by decide) rfl run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G16, rfl⟩ := ri_push s1
  obtain ⟨hs, G17, run⟩ := ric_vySubT vyRevertT_noOk run
  obtain ⟨G18, run⟩ := ric_pushMloadF hF1 10 (by decide) rfl run
  obtain ⟨hm4, G19, run⟩ := ric_vyMulT vyRevertT_noOk run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G20, rfl⟩ := ri_push s1
  obtain ⟨G21, run⟩ := ric_pushMloadF hF1 13 (by decide) rfl run
  obtain ⟨hm5, G22, run⟩ := ric_vyMulT vyRevertT_noOk run
  obtain ⟨ha2, G23, run⟩ := ric_vyAddT vyRevertT_noOk run
  obtain ⟨hdv, G24, run⟩ := ric_vyDivT vyRevertT_noOk run
  rw [← hyN] at hdp
  have hbody := bodyDChk_words hdp hm1 hm2 ha1 hm3 hs hm4 hm5 ha2 hdv
  rw [hyN] at hbody
  generalize (((ann * s + p * Bytes.toB256 [0x03]) * Nat.toB256 D) /
    ((ann - Bytes.toB256 [0x01]) * Nat.toB256 D + Bytes.toB256 [0x04] * p)) = q at hbody run
  obtain ⟨G25, M2, hF2, run⟩ := ric_pushMstoreF hF1 10 (by decide) (lt16 (by decide)) run
  obtain ⟨G26, run⟩ := ric_pushMloadF hF2 9 (by decide) rfl run
  obtain ⟨G27, run⟩ := ric_pushMloadF hF2 10 (by decide) rfl run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G28, rfl⟩ := ri_gt s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G29, rfl⟩ := ri_iszero s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G30, rfl⟩ := ri_push s1
  have hqw : Nat.toB256 q.toNat = q := toB256_toNat q
  have hqlt : q.toNat < 2 ^ 256 := B256.toNat_lt q
  have hexit : ∀ G', SFunc.RunCut progYD sevm C
      (St b (Bytes.toB256 [0x07, 0x9b] :: gdStk S) M2 G') (.jump e) r →
      calleeOut b S M0 (some q.toNat) r := by
    intro G' run
    obtain ⟨G'', run⟩ := ric_jump heC he run
    obtain ⟨M', G3', hr, hout⟩ := ric_gdExit hF2 rfl rfl rfl run
    exact ⟨q.toNat, rfl, hqlt, M', G3', by rw [hqw]; exact hr, by rw [hqw]; exact hout⟩
  have hstop : ∀ G', closeEnough 1 q.toNat D →
      SFunc.RunCut progYD sevm C (St b (Bytes.toB256 [0x07, 0x9b] :: gdStk S) M2 G')
        (.jump e) r → FuelStep k 255 (bodyDChk (gdX x0 x1 x2) ann.toNat s.toNat)
        (fun new prev => decide (closeEnough 1 new prev)) (gdAt b S M0 x0 x1 x2 ρ s ann)
        (calleeOut b S M0) n D r := by
    intro G' hc run
    have ho := hexit G' run
    obtain ⟨_, _, _, M', G'', hr, _⟩ := id ho
    unfold FuelStep
    rw [hbody]
    simp only [decide_eq_true_eq, hc, true_or, ↓reduceIte]
    rw [hr] at ho ⊢
    exact ho
  have htail : ∀ G' f, (f = gdExit ∨ f = .undefined) →
      SFunc.RunCut progYD sevm C (St b (gdStk S) M2 G') (gdTail k f) r →
      ¬ closeEnough 1 q.toNat D → FuelStep k 255 (bodyDChk (gdX x0 x1 x2) ann.toNat s.toNat)
        (fun new prev => decide (closeEnough 1 new prev)) (gdAt b S M0 x0 x1 x2 ρ s ann)
        (calleeOut b S M0) n D r := by
    intro G' f hf run hnc
    obtain ⟨G'', M', hF', hcase⟩ := ric_gdTail hF2 rfl rfl hn hkC run
    unfold FuelStep
    rw [hbody]
    simp only [decide_eq_true_eq, hnc, false_or]
    rcases hcase with ⟨hne, hr⟩ | ⟨heq, run⟩
    · rw [ite_eq_right hne]
      refine ⟨_, hr, hqlt, M', G'', amp, xs, sc, w8, Nat.toB256 D, p, xv, ic, rfl, ?_⟩
      rw [hqw]; exact hF'
    · rw [ite_eq_left heq]
      rcases hf with rfl | rfl
      · obtain ⟨M'', G3', hr, hout⟩ := ric_gdExit hF' rfl rfl rfl run
        rw [hr]
        exact ⟨q.toNat, rfl, hqlt, M'', G3', by rw [hqw], by rw [hqw]; exact hout⟩
      · exact (ric_undefined run).elim
  rcases ric_branch run with ⟨hw, G31, run⟩ | ⟨hw, G31, run⟩
  · -- `D > Dprev`
    have hgt := toNat_lt_of_iszero_gt_eq_zero hw
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G32, rfl⟩ := ri_push s1
    obtain ⟨G33, run⟩ := ric_pushMloadF hF2 10 (by decide) rfl run
    obtain ⟨G34, run⟩ := ric_pushMloadF hF2 9 (by decide) rfl run
    obtain ⟨hle, G35, run⟩ := ric_vySubT vyRevertT_noOk run
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G36, rfl⟩ := ri_gt s1
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G37, rfl⟩ := ri_iszero s1
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G38, rfl⟩ := ri_iszero s1
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G39, rfl⟩ := ri_push s1
    have hsub : (q - Nat.toB256 D).toNat = q.toNat - D := by
      rw [B256.toNat_sub_eq_of_le _ _ (B256.le_iff_toNat_le_toNat.mpr hle), hyN]
    rw [hyN] at hgt
    rcases ric_branch run with ⟨hw2, G40, run⟩ | ⟨hw2, G40, run⟩
    · have h0 := eq_zero_of_iszero2_eq_zero hw2
      have hle1 := toNat_le_of_gtCheck_eq_zero h0
      rw [hsub, show (Bytes.toB256 [0x01]).toNat = 1 by decide] at hle1
      obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G41, rfl⟩ := ri_push s1
      refine hstop G41 ?_ run
      unfold closeEnough; rw [ite_eq_left hgt]; exact hle1
    · have h0 := ne_zero_of_iszero2_ne_zero hw2
      obtain ⟨G41, run⟩ := ric_dest run
      obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G42, rfl⟩ := ri_push s1
      obtain ⟨G43, run⟩ := ric_jump htC ht run
      refine htail G43 _ hfall' run ?_
      unfold closeEnough; rw [ite_eq_left hgt]
      intro hle1
      apply h0
      unfold B256.gtCheck
      rw [ite_eq_right]
      rw [gt_iff_lt, B256.lt_iff_toNat_lt_toNat, hsub,
        show (Bytes.toB256 [0x01]).toNat = 1 by decide]
      omega
  · -- `D ≤ Dprev`
    have hngt := toNat_le_of_iszero_gt_ne_zero hw
    rw [hyN] at hngt
    obtain ⟨G32, run⟩ := ric_dest run
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G33, rfl⟩ := ri_push s1
    obtain ⟨G34, run⟩ := ric_pushMloadF hF2 9 (by decide) rfl run
    obtain ⟨G35, run⟩ := ric_pushMloadF hF2 10 (by decide) rfl run
    obtain ⟨hle, G36, run⟩ := ric_vySubT vyRevertT_noOk run
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G37, rfl⟩ := ri_gt s1
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G38, rfl⟩ := ri_iszero s1
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G39, rfl⟩ := ri_iszero s1
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G40, rfl⟩ := ri_push s1
    have hsub : (Nat.toB256 D - q).toNat = D - q.toNat := by
      rw [B256.toNat_sub_eq_of_le _ _ (B256.le_iff_toNat_le_toNat.mpr hle), hyN]
    have hng : ¬ q.toNat > D := by omega
    rcases ric_branch run with ⟨hw2, G41, run⟩ | ⟨hw2, G41, run⟩
    · have h0 := eq_zero_of_iszero2_eq_zero hw2
      have hle1 := toNat_le_of_gtCheck_eq_zero h0
      rw [hsub, show (Bytes.toB256 [0x01]).toNat = 1 by decide] at hle1
      obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G42, rfl⟩ := ri_push s1
      refine hstop G42 ?_ run
      unfold closeEnough; rw [ite_eq_right hng]; exact hle1
    · have h0 := ne_zero_of_iszero2_ne_zero hw2
      obtain ⟨G42, run⟩ := ric_dest run
      refine htail G42 _ hfall run ?_
      unfold closeEnough; rw [ite_eq_right hng]
      intro hle1
      apply h0
      unfold B256.gtCheck
      rw [ite_eq_right]
      rw [gt_iff_lt, B256.lt_iff_toNat_lt_toNat, hsub,
        show (Bytes.toB256 [0x01]).toNat = 1 by decide]
      omega

/-- The inner loop's state: inner counter `j`, `D_P = p`, at the outer counter `n`, iterate `D`. -/
def gdIAt (b : Devm) (S : List B256) (M0 : Mem) (x0 x1 x2 ρ s ann : B256) (n D j : Nat) (p : B256)
    (d : Devm) : Prop :=
  ∃ M G amp xs sc w8 dp xv, d = St b (gdIStk S) M G ∧
    WordFrame M0 M 0x140 (gdFrame x0 x1 x2 amp ρ s xs sc w8 dp (Nat.toB256 D) ann (Nat.toB256 n)
      p xv (Nat.toB256 j))

-- SEGMENT: gdHeadPre
/-- The outer head up to the inner loop: `D_P = D`, inner counter `0`. -/
theorem ric_gdHeadPre {x0 x1 x2 ρ s ann : B256} {n D : Nat} {d : Devm} {jmp : SFunc}
    (hAt : gdAt b S M0 x0 x1 x2 ρ s ann n D d)
    (run : SFunc.RunCut progYD sevm C d (gdHead jmp) r) :
    ∃ d', gdIAt b S M0 x0 x1 x2 ρ s ann n D 0 (Nat.toB256 D) d' ∧
      SFunc.RunCut progYD sevm C d' (gdInner jmp) r := by
  obtain ⟨hD, M, G, amp, xs, sc, w8, dp, p, xv, ic, rfl, hF⟩ := hAt
  unfold gdHead at run
  obtain ⟨G1, run⟩ := ric_dest run
  obtain ⟨G2, run⟩ := ric_pushMloadF hF 10 (by decide) rfl run
  obtain ⟨G3, M1, hF1, run⟩ := ric_pushMstoreF hF 13 (by decide) (lt16 (by decide)) run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G6, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G7, rfl⟩ := ri_dup (w := Bytes.toB256 [0x00]) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G8, rfl⟩ := ri_dup (w := Bytes.toB256 [0x03, 0x20]) rfl s1
  obtain ⟨G9, M2, hF2, run⟩ := ric_mstoreF hF1 15 (by decide) (lt16 (by decide)) run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G10, rfl⟩ := ri_add s1
  rw [show Bytes.toB256 [0x03] + Bytes.toB256 [0x00] = Nat.toB256 3 by decide,
    show Bytes.toB256 [0x03, 0x20] = Nat.toB256 0x320 by decide] at run
  rw [show Bytes.toB256 [0x00] = Nat.toB256 0 by decide] at hF2
  exact ⟨_, ⟨M2, G10, amp, xs, sc, w8, dp, xv, rfl, hF2⟩, run⟩

theorem gdFrame_x {x0 x1 x2 amp ρ s xs sc w8 dp d ann n p xv ic : B256} {j : Nat} (hj : j < 3) :
    (gdFrame x0 x1 x2 amp ρ s xs sc w8 dp d ann n p xv ic)[j]? = some ([x0, x1, x2][j]'hj) := by
  rcases j with _ | _ | _ | j
  · rfl
  · rfl
  · rfl
  · omega

-- SEGMENT: gdInnerAt
/-- One inner iteration from the inner state, up to its `JUMPI`. -/
theorem ric_gdInnerAt {x0 x1 x2 ρ s ann p : B256} {n D j : Nat} {d : Devm} {jmp : SFunc}
    (hj3 : j < 3) (hAt : gdIAt b S M0 x0 x1 x2 ρ s ann n D j p d)
    (run : SFunc.RunCut progYD sevm C d (gdInner jmp) r) :
    ∃ p', gdPStep p.toNat (Nat.toB256 D).toNat ([x0, x1, x2][j]'hj3).toNat = some p'.toNat ∧
      ∃ M' G', (∃ amp xs sc w8 dp xv, WordFrame M0 M' 0x140 (gdFrame x0 x1 x2 amp ρ s xs sc w8 dp
        (Nat.toB256 D) ann (Nat.toB256 n) p' xv (Nat.toB256 (j + 1)))) ∧
      SFunc.RunCut progYD sevm C (St b (Bytes.toB256 [0x05, 0xa0] ::
        B256.eqCheck (B256.eqCheck (Nat.toB256 3) (Nat.toB256 (j + 1))) 0 :: gdIStk S) M' G')
        jmp r := by
  obtain ⟨M, G, amp, xs, sc, w8, dp, xv, rfl, hF⟩ := hAt
  obtain ⟨G', M', p', hp, hF', run⟩ :=
    ric_gdInner hF rfl rfl hj3 (gdFrame_x hj3) rfl rfl run
  exact ⟨p', hp, M', G', ⟨amp, xs, sc, w8, dp, _, hF'⟩, run⟩

/-- An inner `JUMPI` that goes on to entry `k'` (the counter below `3`). -/
theorem ric_gdJmpOn {w : B256} (hw : w ≠ 0) {f g : SFunc} {k' : Nat} (hkC : k' ∉ C)
    (hk : progYD[k']? = some g) {M : Mem} {G : Nat}
    (run : SFunc.RunCut progYD sevm C (St b (Bytes.toB256 [0x05, 0xa0] :: w :: gdIStk S) M G)
      (.branchTo f k') r) :
    ∃ G', SFunc.RunCut progYD sevm C (St b (gdIStk S) M G') g r := by
  rcases ric_branchTo hkC hk run with ⟨h0, -⟩ | ⟨-, G', run⟩
  · exact absurd h0 hw
  · exact ⟨G', run⟩

/-- An inner `JUMPI` that falls through to the rest of the pass (the counter at `3`). -/
theorem ric_gdJmpOut {f : SFunc} {k' : Nat} (hkC : k' ∉ C) {g : SFunc}
    (hk : progYD[k']? = some g) {M : Mem} {G : Nat}
    (run : SFunc.RunCut progYD sevm C (St b (Bytes.toB256 [0x05, 0xa0] ::
      B256.eqCheck (B256.eqCheck (Nat.toB256 3) (Nat.toB256 3)) 0 :: gdIStk S) M G)
      (.branchTo f k') r) :
    ∃ G', SFunc.RunCut progYD sevm C (St b (gdIStk S) M G') f r := by
  rcases ric_branchTo hkC hk run with ⟨-, G', run⟩ | ⟨h0, -⟩
  · exact ⟨G', run⟩
  · exact absurd iszero_eq3_eq h0

/-- The last inner `JUMPI` of the first pass (`.branch rest .undefined`). -/
theorem ric_gdJmpOut' {f : SFunc} {M : Mem} {G : Nat}
    (run : SFunc.RunCut progYD sevm C (St b (Bytes.toB256 [0x05, 0xa0] ::
      B256.eqCheck (B256.eqCheck (Nat.toB256 3) (Nat.toB256 3)) 0 :: gdIStk S) M G)
      (.branch f .undefined) r) :
    ∃ G', SFunc.RunCut progYD sevm C (St b (gdIStk S) M G') f r := by
  rcases ric_branch run with ⟨-, G', run⟩ | ⟨h0, -⟩
  · exact ⟨G', run⟩
  · exact absurd iszero_eq3_eq h0

theorem dPChk_of_steps {x0 x1 x2 D p0 p1 p2 : Nat} (h0 : gdPStep D D x0 = some p0)
    (h1 : gdPStep p0 D x1 = some p1) (h2 : gdPStep p1 D x2 = some p2) :
    dPChk (V3.mk x0 x1 x2).get D = some p2 := by
  unfold gdPStep at h0 h1 h2
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h0 h1 h2
  obtain ⟨a0, ha0, b0, hb0, hc0⟩ := h0
  obtain ⟨a1, ha1, b1, hb1, hc1⟩ := h1
  obtain ⟨a2, ha2, b2, hb2, hc2⟩ := h2
  unfold dPChk
  rw [show (V3.mk x0 x1 x2).get 0 = x0 from rfl, show (V3.mk x0 x1 x2).get 1 = x1 from rfl,
    show (V3.mk x0 x1 x2).get 2 = x2 from rfl]
  simp only [Option.bind_eq_bind, ha0, hb0, hc0, ha1, hb1, hc1, ha2, hb2, hc2, Option.bind_some]

theorem gdStep0 {x0 x1 x2 p : B256} {D : Nat} (hD : D < 2 ^ 256)
    (h : gdPStep (Nat.toB256 D).toNat (Nat.toB256 D).toNat (([x0, x1, x2] : List B256)[0]'(Nat.zero_lt_succ _)).toNat =
      some p.toNat) : gdPStep D D x0.toNat = some p.toNat := by
  rw [B256.toNat_toB256_of_lt hD] at h; exact h

theorem gdStepJ {x0 x1 x2 p p' : B256} {D j : Nat} (hD : D < 2 ^ 256) (hj : j < 3)
    (h : gdPStep p.toNat (Nat.toB256 D).toNat ([x0, x1, x2][j]'hj).toNat = some p'.toNat) :
    gdPStep p.toNat D ([x0, x1, x2][j]'hj).toNat = some p'.toNat := by
  rw [B256.toNat_toB256_of_lt hD] at h; exact h

variable {x0 x1 x2 ρ s ann : B256}

-- SEGMENT: gdPass533
/-- The steady pass (head 533, the inner loop through 517 twice). -/
theorem gdPass533 (n D : Nat) (d : Devm) (hn : n < 255)
    (hAt : gdAt b S M0 x0 x1 x2 ρ s ann n D d) (r : Seg)
    (run : SFunc.RunCut progYD sevm [533] d (gdHead (.branchTo .undefined 517)) r) :
    FuelStep 533 255 (bodyDChk (gdX x0 x1 x2) ann.toNat s.toNat)
      (fun new prev => decide (closeEnough 1 new prev)) (gdAt b S M0 x0 x1 x2 ρ s ann)
      (calleeOut b S M0) n D r := by
  have hD := hAt.1
  obtain ⟨d1, hI, run⟩ := ric_gdHeadPre hAt run
  obtain ⟨p0, hp0, M1, G1, ⟨amp, xs, sc, w8, dp, xv, hF1⟩, run⟩ :=
    ric_gdInnerAt (j := 0) (by decide) hI run
  obtain ⟨G2, run⟩ := ric_gdJmpOn (iszero_eq3_ne (by decide)) (by decide) progGD_517 run
  obtain ⟨p1, hp1, M2, G3, ⟨amp, xs, sc, w8, dp, xv, hF2⟩, run⟩ :=
    ric_gdInnerAt (j := 1) (by decide) ⟨M1, G2, amp, xs, sc, w8, dp, xv, rfl, hF1⟩ run
  obtain ⟨G4, run⟩ := ric_gdJmpOn (iszero_eq3_ne (by decide)) (by decide) progGD_517 run
  obtain ⟨p2, hp2, M3, G5, ⟨amp, xs, sc, w8, dp, xv, hF3⟩, run⟩ :=
    ric_gdInnerAt (j := 2) (by decide) ⟨M2, G4, amp, xs, sc, w8, dp, xv, rfl, hF2⟩ run
  obtain ⟨G6, run⟩ := ric_gdJmpOut (by decide) progGD_517 run
  have hdp := dPChk_of_steps (gdStep0 hD hp0) (gdStepJ hD (by decide) hp1)
    (gdStepJ hD (by decide) hp2)
  exact gdRest_step progGD_531 progGD_532 (by decide) (by decide) List.mem_cons_self (.inl rfl)
    (.inl rfl) hn hD hdp hF3 run

-- SEGMENT: gdPass489
/-- The peeled second pass (head 489, inner 503 then 517). -/
theorem gdPass489 (n D : Nat) (d : Devm) (hn : n < 255)
    (hAt : gdAt b S M0 x0 x1 x2 ρ s ann n D d) (r : Seg)
    (run : SFunc.RunCut progYD sevm [533] d (gdHead (.branchTo .undefined 503)) r) :
    FuelStep 533 255 (bodyDChk (gdX x0 x1 x2) ann.toNat s.toNat)
      (fun new prev => decide (closeEnough 1 new prev)) (gdAt b S M0 x0 x1 x2 ρ s ann)
      (calleeOut b S M0) n D r := by
  have hD := hAt.1
  obtain ⟨d1, hI, run⟩ := ric_gdHeadPre hAt run
  obtain ⟨p0, hp0, M1, G1, ⟨amp, xs, sc, w8, dp, xv, hF1⟩, run⟩ :=
    ric_gdInnerAt (j := 0) (by decide) hI run
  obtain ⟨G2, run⟩ := ric_gdJmpOn (iszero_eq3_ne (by decide)) (by decide) progGD_503 run
  obtain ⟨p1, hp1, M2, G3, ⟨amp, xs, sc, w8, dp, xv, hF2⟩, run⟩ :=
    ric_gdInnerAt (j := 1) (by decide) ⟨M1, G2, amp, xs, sc, w8, dp, xv, rfl, hF1⟩ run
  obtain ⟨G4, run⟩ := ric_gdJmpOn (iszero_eq3_ne (by decide)) (by decide) progGD_517 run
  obtain ⟨p2, hp2, M3, G5, ⟨amp, xs, sc, w8, dp, xv, hF3⟩, run⟩ :=
    ric_gdInnerAt (j := 2) (by decide) ⟨M2, G4, amp, xs, sc, w8, dp, xv, rfl, hF2⟩ run
  obtain ⟨G6, run⟩ := ric_gdJmpOut (by decide) progGD_517 run
  have hdp := dPChk_of_steps (gdStep0 hD hp0) (gdStepJ hD (by decide) hp1)
    (gdStepJ hD (by decide) hp2)
  exact gdRest_step progGD_531 progGD_532 (by decide) (by decide) List.mem_cons_self (.inl rfl)
    (.inl rfl) hn hD hdp hF3 run

-- SEGMENT: gdPass0
/-- The first pass (head inline after the set-up, inner 459 then 473). -/
theorem gdPass0 (n D : Nat) (d : Devm) (hn : n < 255)
    (hAt : gdAt b S M0 x0 x1 x2 ρ s ann n D d) (r : Seg)
    (run : SFunc.RunCut progYD sevm [489] d (gdHead (.branchTo .undefined 459)) r) :
    FuelStep 489 255 (bodyDChk (gdX x0 x1 x2) ann.toNat s.toNat)
      (fun new prev => decide (closeEnough 1 new prev)) (gdAt b S M0 x0 x1 x2 ρ s ann)
      (calleeOut b S M0) n D r := by
  have hD := hAt.1
  obtain ⟨d1, hI, run⟩ := ric_gdHeadPre hAt run
  obtain ⟨p0, hp0, M1, G1, ⟨amp, xs, sc, w8, dp, xv, hF1⟩, run⟩ :=
    ric_gdInnerAt (j := 0) (by decide) hI run
  obtain ⟨G2, run⟩ := ric_gdJmpOn (iszero_eq3_ne (by decide)) (by decide) progGD_459 run
  obtain ⟨p1, hp1, M2, G3, ⟨amp, xs, sc, w8, dp, xv, hF2⟩, run⟩ :=
    ric_gdInnerAt (j := 1) (by decide) ⟨M1, G2, amp, xs, sc, w8, dp, xv, rfl, hF1⟩ run
  obtain ⟨G4, run⟩ := ric_gdJmpOn (iszero_eq3_ne (by decide)) (by decide) progGD_473 run
  obtain ⟨p2, hp2, M3, G5, ⟨amp, xs, sc, w8, dp, xv, hF3⟩, run⟩ :=
    ric_gdInnerAt (j := 2) (by decide) ⟨M2, G4, amp, xs, sc, w8, dp, xv, rfl, hF2⟩ run
  obtain ⟨G6, run⟩ := ric_gdJmpOut' run
  have hdp := dPChk_of_steps (gdStep0 hD hp0) (gdStepJ hD (by decide) hp1)
    (gdStepJ hD (by decide) hp2)
  exact gdRest_step progGD_487 progGD_488 (by decide) (by decide) List.mem_cons_self (.inr rfl)
    (.inr rfl) hn hD hdp hF3 run

/-- The `D` loop's fuel-loop form at the frame's `xp`, `Ann`, `S`. -/
abbrev gdLoop (x0 x1 x2 ann s : B256) (fuel D : Nat) : Option Nat :=
  fuelLoop (bodyDChk (gdX x0 x1 x2) ann.toNat s.toNat)
    (fun new prev => decide (closeEnough 1 new prev)) fuel D

-- SEGMENT: gdLoop
/-- **The Newton loop**, inverted from its first (inline) pass. -/
theorem gdLoop_sound : ∀ n D d r, n < 255 → gdAt b S M0 x0 x1 x2 ρ s ann n D d →
    SFunc.RunCut progYD sevm [] d (gdHead (.branchTo .undefined 459)) r →
    calleeOut b S M0 (gdLoop x0 x1 x2 ann s (255 - n) D) r := by
  have h533 := RunCut_fuelLoop_sound (P := Ninst.Run) (sevm := sevm) (C := []) progGD_533
    List.not_mem_nil (gdAt b S M0 x0 x1 x2 ρ s ann) (calleeOut b S M0)
    (fun n D d hn hAt r run => gdPass533 n D d hn hAt r run)
  have h489 := RunCut_fuelLoop_peel (P := Ninst.Run) (sevm := sevm) (C := []) progGD_533
    List.not_mem_nil (gdAt b S M0 x0 x1 x2 ρ s ann) (calleeOut b S M0) h533
    (fun n D d hn hAt r run => gdPass489 n D d hn hAt r run)
  exact RunCut_fuelLoop_peel (P := Ninst.Run) (sevm := sevm) (C := []) progGD_489
    List.not_mem_nil (gdAt b S M0 x0 x1 x2 ρ s ann) (calleeOut b S M0) h489
    (fun n D d hn hAt r run => gdPass0 n D d hn hAt r run)

end Walk

end Blanc.Lift.Curve3Pool
