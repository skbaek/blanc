import Blanc.Lift.Curve3Pool.Callee.GetYLoop
import Blanc.Lift.Curve3Pool.Callee.GetYD

/-!
# `get_y` before its Newton loop, inverted

The coin loop of `get_y` runs over a frame of twenty-four words `0x140 … 0x440` (`gyCFrame`):
the memory covers the coin-loop counter `0x420` but not yet the `y`-loop words above it.

* `ric_gyPost`: the set-up after the coin loop writes `b`, `y_prev`, `y` and the `y`-loop
  counter `0x440 … 0x4a0` (possibly growing memory, over a tracked memory), then the whole `y`
  loop runs over the twenty-eight-word frame (`gyLoop_sound`): `gyOut` of `ydPostRes`;
* `ric_gyCoinTail*`, `ric_gyAcc`, `ric_gyTest`: one iteration of the coin loop
  (`for _i in range(N_COINS)`: `_x = x` at `i`, skip `j`, else `_x = xp[_i]`): `gyCoinStep`.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune
open Blanc.StableSwapNewton

/-- `get_y`'s windows: scratch word `0` and its frame `[0x140, 0x4c0)`. -/
abbrev gyWin : List (Nat × Nat) := [(0, 0x20), (0x140, 0x4c0)]

/-- `get_y`'s frame at the coin loop, `0x140 … 0x440`. -/
def gyCFrame (i j x x0 x1 x2 ρ amp w8 w9 D w11 w12 w13 w14 w15 w16 w17 w18 c s ann xv cc : B256) :
    List B256 :=
  [i, j, x, x0, x1, x2, ρ, amp, w8, w9, D, w11, w12, w13, w14, w15, w16, w17, w18, c, s, ann, xv,
    cc]

/-- The coin loop's stack: the bound `3` over the counter address `0x420`. -/
abbrev gyCStk (S : List B256) : List B256 := Nat.toB256 3 :: Nat.toB256 0x420 :: S

/-- How `get_y` leaves, from a base memory `M0`: returning `y` over the caller's stack, memory
kept off `gyWin`, well formed, word-aligned, `y` at scratch word `0`. -/
def gyOut (b : Devm) (S : List B256) (M0 : Mem) (v : Option Nat) (r : Seg) : Prop :=
  ∃ y, v = some y ∧ y < 2 ^ 256 ∧ ∃ M G, r = .done (.returned (St b (Nat.toB256 y :: S) M G)) ∧
    Mem.KeepsOff M0 M gyWin ∧ Mem.Wf M ∧ Words M [(0, Nat.toB256 y)] ∧ M.size % 32 = 0

/-- One coin-loop iteration of `get_y` on naturals, `(c, S_)` in and out: coin `k` adds `x`
when it is `i`, is skipped when it is `j`, else adds `xk`. -/
def gyCoinStep (i j k x xk D : Nat) (cs : Nat × Nat) : Option (Nat × Nat) :=
  if i = k then ydAccN cs.1 cs.2 x D else if j = k then some cs else ydAccN cs.1 cs.2 xk D

theorem gyCoinStep_i {j k x xk D : Nat} {cs : Nat × Nat} :
    gyCoinStep k j k x xk D cs = ydAccN cs.1 cs.2 x D := by
  unfold gyCoinStep; rw [if_pos rfl]

theorem gyCoinStep_j {i k x xk D : Nat} {cs : Nat × Nat} (hi : i ≠ k) :
    gyCoinStep i k k x xk D cs = some cs := by
  unfold gyCoinStep; rw [if_neg hi, if_pos rfl]

theorem gyCoinStep_other {i j k x xk D : Nat} {cs : Nat × Nat} (hi : i ≠ k) (hj : j ≠ k) :
    gyCoinStep i j k x xk D cs = ydAccN cs.1 cs.2 xk D := by
  unfold gyCoinStep; rw [if_neg hi, if_neg hj]

theorem eq_of_iszero_eqCheck_eq_zero {a b : B256} (h : B256.eqCheck (B256.eqCheck a b) 0 = 0) :
    a = b := by
  by_contra hne
  unfold B256.eqCheck at h
  rw [if_neg hne, if_pos rfl] at h
  exact absurd h (by decide)

theorem ne_of_iszero_eqCheck_ne_zero {a b : B256} (h : B256.eqCheck (B256.eqCheck a b) 0 ≠ 0) :
    a ≠ b := by
  intro he
  apply h
  rw [he, eqCheck_self]
  decide

theorem toB256_0x4a0 : Bytes.toB256 [0x04, 0xa0] = Nat.toB256 0x4a0 := by decide

theorem toB256_0x420 : Bytes.toB256 [0x04, 0x20] = Nat.toB256 0x420 := by decide

section Walk

variable {sevm : Sevm} {C : List Nat} {b : Devm} {S : List B256} {M0 M : Mem} {G : Nat}
  {r : Seg}

-- SEGMENT: gyPost
/-- **After the coin loop**, inverted through the whole `y` loop. -/
theorem ric_gyPost {i j x x0 x1 x2 ρ amp w8 w9 D w11 w12 w13 w14 w15 w16 w17 w18 c s ann xv
    cc : B256} (hwf : Mem.Wf M0)
    (hF : WordFrame M0 M 0x140 (gyCFrame i j x x0 x1 x2 ρ amp w8 w9 D w11 w12 w13 w14 w15 w16 w17
      w18 c s ann xv cc))
    (run : SFunc.RunCut progYD sevm [] (St b (gyCStk S) M G) gyPost0 r) :
    gyOut b S M0 (ydPostRes c.toNat s.toNat D.toNat ann.toNat) r := by
  have hal0 := hF.aligned
  have hT0 := hF.memTrack hwf (W := gyWin) (n := 24) rfl (by decide)
  have hρ : Words M [(0x200, ρ)] := hF.words1 (j := 6) rfl
  have hD : Words M [(0x280, D)] := hF.words1 (j := 10) rfl
  have hc : Words M [(0x3a0, c)] := hF.words1 (j := 19) rfl
  have hs : Words M [(0x3c0, s)] := hF.words1 (j := 20) rfl
  have hann : Words M [(0x3e0, ann)] := hF.words1 (j := 21) rfl
  have hT := hT0.withWords (L' := [(0x200, ρ), (0x280, D), (0x3a0, c), (0x3c0, s), (0x3e0, ann)])
    (Words.append.mpr ⟨hρ, Words.append.mpr ⟨hD, Words.append.mpr ⟨hc,
      Words.append.mpr ⟨hs, hann⟩⟩⟩⟩)
  clear hT0 hρ hD hc hs hann
  unfold gyPost0 gyPost at run
  have hd := ric_dest run
  clear run
  obtain ⟨_, run⟩ := hd
  istep; istep
  imload 0x3a0; imload 0x280
  obtain ⟨hm1, _, run⟩ := ric_vyMulT vyRevertT_noOk run
  imload 0x3e0; istep
  obtain ⟨hm2, _, run⟩ := ric_vyMulT vyRevertT_noOk run
  obtain ⟨hd1, _, run⟩ := ric_vyDivT vyRevertT_noOk run
  imstoreO 0x3a0
  imload 0x3c0; imload 0x280; imload 0x3e0
  obtain ⟨hd2, _, run⟩ := ric_vyDivT vyRevertT_noOk run
  obtain ⟨ha1, _, run⟩ := ric_vyAddT vyRevertT_noOk run
  imstoreO 0x440
  istep; imstoreO 0x460
  imload 0x280; imstoreO 0x480
  istep; istep; istep; istep; istep; imstoreO' 0x4a0
  rename_i M5 G4
  istep
  rename_i G5
  rw [toB256_255, toB256_0x4a0] at run
  have hρ5 := hT.words.memWord (o := 0x200) (v := ρ) (by wmem)
  have hD5 := hT.words.memWord (o := 0x280) (v := D) (by wmem)
  have hc5 := hT.words.memWord (o := 0x3a0) (v := (c * D) / (ann * Bytes.toB256 [0x03]))
    (by wmem)
  have hb5 := hT.words.memWord (o := 0x440) (v := s + D / ann) (by wmem)
  have hyp5 := hT.words.memWord (o := 0x460) (v := Bytes.toB256 [0x00]) (by wmem)
  have hy5 := hT.words.memWord (o := 0x480) (v := D) (by wmem)
  have hn5 := hT.words.memWord (o := 0x4a0) (v := Bytes.toB256 [0x00]) (by wmem)
  have hcs5 := hT.mem_size (o := 0x4a0) (v := Bytes.toB256 [0x00]) (by wmem)
  have hF5 := WordFrame.init (M0 := M5) (lo := 0x140) (n := 28) (hT.aligned hal0) (by omega)
  rw [show frameWords M5 0x140 28 = [memWord M5 0x140, memWord M5 0x160, memWord M5 0x180,
    memWord M5 0x1a0, memWord M5 0x1c0, memWord M5 0x1e0, memWord M5 0x200, memWord M5 0x220,
    memWord M5 0x240, memWord M5 0x260, memWord M5 0x280, memWord M5 0x2a0, memWord M5 0x2c0,
    memWord M5 0x2e0, memWord M5 0x300, memWord M5 0x320, memWord M5 0x340, memWord M5 0x360,
    memWord M5 0x380, memWord M5 0x3a0, memWord M5 0x3c0, memWord M5 0x3e0, memWord M5 0x400,
    memWord M5 0x420, memWord M5 0x440, memWord M5 0x460, memWord M5 0x480, memWord M5 0x4a0]
    from rfl, hρ5, hD5, hc5, hb5, hyp5, hy5, hn5, toB256_zero] at hF5
  have hDlt := B256.toNat_lt D
  have hAt : gyAt b S M5 D ρ ((c * D) / (ann * Bytes.toB256 [0x03])) (s + D / ann) 0 D.toNat
      (St b (gyStk S) M5 G5) := by
    refine ⟨hDlt, M5, G5, memWord M5 0x140, memWord M5 0x160, memWord M5 0x180, memWord M5 0x1a0,
      memWord M5 0x1c0, memWord M5 0x1e0, memWord M5 0x220, memWord M5 0x240, memWord M5 0x260,
      memWord M5 0x2a0, memWord M5 0x2c0, memWord M5 0x2e0, memWord M5 0x300, memWord M5 0x320,
      memWord M5 0x340, memWord M5 0x360, memWord M5 0x380, memWord M5 0x3c0, memWord M5 0x3e0,
      memWord M5 0x400, memWord M5 0x420, Nat.toB256 0, rfl, ?_⟩
    rw [toB256_toNat]
    exact hF5
  have hloop := gyLoop_sound 0 D.toNat _ r (by decide) hAt run
  have hres : ydPostRes c.toNat s.toNat D.toNat ann.toNat =
      ydLoop ((c * D) / (ann * Bytes.toB256 [0x03])) (s + D / ann) D (255 - 0) D.toNat := by
    have e3 : (3 : Nat) = (Bytes.toB256 [0x03]).toNat := by decide
    unfold ydPostRes ydLoop
    rw [e3, chkMul_toNat_of_nofm hm1, chkMul_toNat_of_nofm hm2]
    simp only [Option.bind_eq_bind, Option.bind_some]
    rw [chkDiv_toNat_of_ne hd1, chkDiv_toNat_of_ne hd2]
    simp only [Option.bind_some]
    rw [chkAdd_toNat_of_lt ha1]
    simp only [Option.bind_some]
    rw [loopYChk_eq_fuelLoop]
  rw [hres]
  obtain ⟨y, hv, hy, Mf, Gf, hr, hout⟩ := hloop
  have hwf5 := hT.wf
  exact ⟨y, hv, hy, Mf, Gf, hr, hT.keeps.trans ((hout.keepsOff hwf5).widen (by decide)),
    hout.wf hwf5, hout.words (by omega), by rw [hout.size]; exact hT.aligned hal0⟩

-- SEGMENT: gyCoinTail
/-- **The coin-loop counter tail**, inverted up to its `JUMPI`. -/
theorem ric_gyCoinTail (hF : WordFrame M0 M 0x140 ws) (hlen : ws.length = 24) {j : Nat}
    (hj : ws[23]? = some (Nat.toB256 j)) (hj3 : j < 3) {jmp : SFunc}
    (run : SFunc.RunCut progYD sevm C (St b (gyCStk S) M G) (gyCoinTail jmp) r) :
    ∃ G' M', WordFrame M0 M' 0x140 (ws.set 23 (Nat.toB256 (j + 1))) ∧
      SFunc.RunCut progYD sevm C (St b (Bytes.toB256 [0x1a, 0x50] ::
        B256.eqCheck (B256.eqCheck (Nat.toB256 3) (Nat.toB256 (j + 1))) 0 :: gyCStk S) M' G')
        jmp r := by
  unfold gyCoinTail at run
  obtain ⟨G1, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G2, rfl⟩ := ri_dup (w := Nat.toB256 0x420) rfl s1
  obtain ⟨G3, run⟩ := ric_mloadF hF 23 (by decide) hj run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_add s1
  rw [one_add_toB256 (by omega)] at run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G6, rfl⟩ := ri_dup (w := Nat.toB256 (j + 1)) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G7, rfl⟩ := ri_dup (w := Nat.toB256 0x420) rfl s1
  obtain ⟨G8, M1, hF1, run⟩ := ric_mstoreF hF 23 (by decide) (by rw [hlen]; decide) run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G9, rfl⟩ := ri_dup (w := Nat.toB256 3) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G10, rfl⟩ := ri_eq s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G11, rfl⟩ := ri_iszero s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G12, rfl⟩ := ri_push s1
  exact ⟨G12, M1, hF1, run⟩

/-- The tail of a non-final iteration: on to the next test at entry `k`. -/
theorem ric_gyCoinTail_next (hF : WordFrame M0 M 0x140 ws) (hlen : ws.length = 24) {j k : Nat}
    {g : SFunc} (hj : ws[23]? = some (Nat.toB256 j)) (hj3 : j < 3) (hkC : k ∉ C)
    (hk : progYD[k]? = some g)
    (run : SFunc.RunCut progYD sevm C (St b (gyCStk S) M G)
      (gyCoinTail (.branchTo .undefined k)) r) :
    ∃ G' M', WordFrame M0 M' 0x140 (ws.set 23 (Nat.toB256 (j + 1))) ∧
      SFunc.RunCut progYD sevm C (St b (gyCStk S) M' G') g r := by
  obtain ⟨G1, M1, hF1, run⟩ := ric_gyCoinTail hF hlen hj hj3 run
  rcases ric_branchTo hkC hk run with ⟨-, G2, run⟩ | ⟨-, G2, run⟩
  · exact (ric_undefined run).elim
  · exact ⟨G2, M1, hF1, run⟩

/-- The tail of the final iteration: on to the post-loop `g`. -/
theorem ric_gyCoinTail_last (hF : WordFrame M0 M 0x140 ws) (hlen : ws.length = 24) {j : Nat}
    {g : SFunc} (hj : ws[23]? = some (Nat.toB256 j)) (hj3 : j < 3)
    (run : SFunc.RunCut progYD sevm C (St b (gyCStk S) M G) (gyCoinTail (.branch g .undefined))
      r) :
    ∃ G' M', WordFrame M0 M' 0x140 (ws.set 23 (Nat.toB256 (j + 1))) ∧
      SFunc.RunCut progYD sevm C (St b (gyCStk S) M' G') g r := by
  obtain ⟨G1, M1, hF1, run⟩ := ric_gyCoinTail hF hlen hj hj3 run
  rcases ric_branch run with ⟨-, G2, run⟩ | ⟨-, G2, run⟩
  · exact ⟨G2, M1, hF1, run⟩
  · exact (ric_undefined run).elim

-- SEGMENT: gyAcc
/-- **The coin-loop accumulation**, inverted: `ydAccN` on the frame's `c`, `S_`, `_x`, `D`. -/
theorem ric_gyAcc (hF : WordFrame M0 M 0x140 ws) (hlen : ws.length = 24) {c s x D : B256}
    (hc : ws[19]? = some c) (hs : ws[20]? = some s) (hx : ws[22]? = some x)
    (hD : ws[10]? = some D) {tail : SFunc}
    (run : SFunc.RunCut progYD sevm C (St b (gyCStk S) M G) (gyAcc tail) r) :
    ∃ G' M' c' s', ydAccN c.toNat s.toNat x.toNat D.toNat = some (c'.toNat, s'.toNat) ∧
      WordFrame M0 M' 0x140 ((ws.set 20 s').set 19 c') ∧
      SFunc.RunCut progYD sevm C (St b (gyCStk S) M' G') tail r := by
  unfold gyAcc at run
  obtain ⟨G1, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G2, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G3, rfl⟩ := ri_dup (w := Bytes.toB256 [0x03, 0xc0]) rfl s1
  obtain ⟨G4, run⟩ := ric_mloadF hF 20 (by decide) hs run
  obtain ⟨G5, run⟩ := ric_pushMloadF hF 22 (by decide) hx run
  obtain ⟨ha1, G6, run⟩ := ric_vyAddT vyRevertT_noOk run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G7, rfl⟩ := ri_dup (w := Bytes.toB256 [0x03, 0xc0]) rfl s1
  obtain ⟨G8, M1, hF1, run⟩ := ric_mstoreF hF 20 (by decide) (by rw [hlen]; decide) run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G9, rfl⟩ := ri_pop s1
  have hc1 : (ws.set 20 (s + x))[19]? = some c := by rw [List.getElem?_set_ne (by decide)]; exact hc
  have hD1 : (ws.set 20 (s + x))[10]? = some D := by rw [List.getElem?_set_ne (by decide)]; exact hD
  have hx1 : (ws.set 20 (s + x))[22]? = some x := by
    rw [List.getElem?_set_ne (by decide)]; exact hx
  obtain ⟨G10, run⟩ := ric_pushMloadF hF1 19 (by decide) hc1 run
  obtain ⟨G11, run⟩ := ric_pushMloadF hF1 10 (by decide) hD1 run
  obtain ⟨hm1, G12, run⟩ := ric_vyMulT vyRevertT_noOk run
  obtain ⟨G13, run⟩ := ric_pushMloadF hF1 22 (by decide) hx1 run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G14, rfl⟩ := ri_push s1
  obtain ⟨hm2, G15, run⟩ := ric_vyMulT vyRevertT_noOk run
  obtain ⟨hd, G16, run⟩ := ric_vyDivT vyRevertT_noOk run
  obtain ⟨G17, M2, hF2, run⟩ := ric_pushMstoreF hF1 19 (by decide)
    (by rw [List.length_set, hlen]; decide) run
  refine ⟨G17, M2, _, _, ?_, hF2, run⟩
  have e3 : (3 : Nat) = (Bytes.toB256 [0x03]).toNat := by decide
  unfold ydAccN
  rw [e3, chkAdd_toNat_of_lt ha1]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [chkMul_toNat_of_nofm hm1, chkMul_toNat_of_nofm hm2]
  simp only [Option.bind_some]
  rw [chkDiv_toNat_of_ne hd]
  simp only [Option.bind_some]

/-- The address of `xp[k]`, `0x1a0 + 32 k`, as the frame's slot `3 + k`. -/
theorem gyXpAddr {k : Nat} (hk : k < 3) :
    (Bytes.toB256 [0x20] * Nat.toB256 k + Bytes.toB256 [0x01, 0xa0]).toNat =
      0x140 + 32 * (3 + k) := by
  rcases k with _ | _ | _ | k
  · decide
  · decide
  · decide
  · omega

-- SEGMENT: gyTest
/-- **The coin-loop test**, inverted: coin `k` is `i` (`_x = x`, on to the accumulation `k1`),
or is neither `i` nor `j` (`_x = xp[k]`, on to the accumulation behind a `JUMPDEST`, `k2`), or
is `j` (on to the tail `k3`). -/
theorem ric_gyTest {ws : List B256} (hF : WordFrame M0 M 0x140 ws) (hlen : ws.length = 24)
    {i j x xk : B256} {k k1 k2 k3 : Nat} {g1 g2 g3 : SFunc} (hi : ws[0]? = some i)
    (hj : ws[1]? = some j) (hx : ws[2]? = some x) (hk : ws[23]? = some (Nat.toB256 k))
    (hk3 : k < 3) (hxk : ws[3 + k]? = some xk) (hk1C : k1 ∉ C) (hk2C : k2 ∉ C) (hk3C : k3 ∉ C)
    (hk1 : progYD[k1]? = some g1) (hk2 : progYD[k2]? = some g2) (hk3' : progYD[k3]? = some g3)
    (run : SFunc.RunCut progYD sevm C (St b (gyCStk S) M G) (gyTest k1 k2 k3) r) :
    (i = Nat.toB256 k ∧ ∃ G' M', WordFrame M0 M' 0x140 (ws.set 22 x) ∧
        SFunc.RunCut progYD sevm C (St b (gyCStk S) M' G') g1 r) ∨
      (i ≠ Nat.toB256 k ∧ j ≠ Nat.toB256 k ∧ ∃ G' M', WordFrame M0 M' 0x140 (ws.set 22 xk) ∧
        SFunc.RunCut progYD sevm C (St b (gyCStk S) M' G') g2 r) ∨
      (i ≠ Nat.toB256 k ∧ j = Nat.toB256 k ∧ ∃ G',
        SFunc.RunCut progYD sevm C (St b (gyCStk S) M G') g3 r) := by
  unfold gyTest at run
  obtain ⟨G1, run⟩ := ric_dest run
  obtain ⟨G2, run⟩ := ric_pushMloadF hF 0 (by decide) hi run
  obtain ⟨G3, run⟩ := ric_pushMloadF hF 23 (by decide) hk run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G4, rfl⟩ := ri_eq s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_iszero s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G6, rfl⟩ := ri_push s1
  rcases ric_branch run with ⟨hw, G7, run⟩ | ⟨hw, G7, run⟩
  · -- coin `i`: `_x = x`
    have heq := (eq_of_iszero_eqCheck_eq_zero hw).symm
    obtain ⟨G8, run⟩ := ric_pushMloadF hF 2 (by decide) hx run
    obtain ⟨G9, M1, hF1, run⟩ := ric_pushMstoreF hF 22 (by decide) (by rw [hlen]; decide) run
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G10, rfl⟩ := ri_push s1
    obtain ⟨G11, run⟩ := ric_jump hk1C hk1 run
    exact .inl ⟨heq, G11, M1, hF1, run⟩
  · have hne : i ≠ Nat.toB256 k := fun h => ne_of_iszero_eqCheck_ne_zero hw h.symm
    obtain ⟨G8, run⟩ := ric_dest run
    obtain ⟨G9, run⟩ := ric_pushMloadF hF 1 (by decide) hj run
    obtain ⟨G10, run⟩ := ric_pushMloadF hF 23 (by decide) hk run
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G11, rfl⟩ := ri_xor s1
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G12, rfl⟩ := ri_iszero s1
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G13, rfl⟩ := ri_push s1
    rcases ric_branch run with ⟨hw2, G14, run⟩ | ⟨hw2, G14, run⟩
    · -- neither: `_x = xp[k]`
      have hnj : j ≠ Nat.toB256 k := by
        intro he
        rw [he, (B256.xor_eq_zero_iff _ _).mpr rfl] at hw2
        exact absurd hw2 (by decide)
      obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G15, rfl⟩ := ri_push s1
      obtain ⟨G16, run⟩ := ric_pushMloadF hF 23 (by decide) hk run
      obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G17, rfl⟩ := ri_push s1
      obtain ⟨d1, s1, run⟩ := ric_next run
      obtain ⟨G18, rfl⟩ := ri_dup (w := Nat.toB256 k) rfl s1
      obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G19, rfl⟩ := ri_lt s1
      obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G20, rfl⟩ := ri_push s1
      rcases ric_branch run with ⟨-, G21, run⟩ | ⟨-, G21, run⟩
      · exact (ric_undefined run).elim
      obtain ⟨G22, run⟩ := ric_dest run
      obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G23, rfl⟩ := ri_push s1
      obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G24, rfl⟩ := ri_mul s1
      obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G25, rfl⟩ := ri_add s1
      obtain ⟨G26, run⟩ := ric_mloadF hF (3 + k) (gyXpAddr hk3) hxk run
      obtain ⟨G27, M1, hF1, run⟩ := ric_pushMstoreF hF 22 (by decide) (by rw [hlen]; decide) run
      obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G28, rfl⟩ := ri_push s1
      obtain ⟨G29, run⟩ := ric_jump hk2C hk2 run
      exact .inr (.inl ⟨hne, hnj, G29, M1, hF1, run⟩)
    · -- coin `j`: `continue`
      have hje : j = Nat.toB256 k := by
        have := eq_zero_of_iszero_ne_zero hw2
        exact ((B256.xor_eq_zero_iff _ _).mp this).symm
      obtain ⟨G15, run⟩ := ric_dest run
      obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G16, rfl⟩ := ri_push s1
      obtain ⟨G17, run⟩ := ric_jump hk3C hk3' run
      exact .inr (.inr ⟨hne, hje, G17, run⟩)

/-- The model's step at coin `k`, from the test's outcome. -/
theorem gyStep_of_test {i j x xk : B256} {k : Nat} (hk : k < 3) {D : Nat} {cs : Nat × Nat}
    {P : Option (Nat × Nat) → Prop}
    (h1 : i = Nat.toB256 k → P (ydAccN cs.1 cs.2 x.toNat D))
    (h2 : i ≠ Nat.toB256 k → j ≠ Nat.toB256 k → P (ydAccN cs.1 cs.2 xk.toNat D))
    (h3 : i ≠ Nat.toB256 k → j = Nat.toB256 k → P (some cs))
    (ht : i = Nat.toB256 k ∨ (i ≠ Nat.toB256 k ∧ j ≠ Nat.toB256 k) ∨
      (i ≠ Nat.toB256 k ∧ j = Nat.toB256 k)) :
    P (gyCoinStep i.toNat j.toNat k x.toNat xk.toNat D cs) := by
  have hk' : k < 2 ^ 256 := by omega
  rcases ht with he | ⟨hne, hnj⟩ | ⟨hne, hje⟩
  · rw [toNat_of_eq hk' he, gyCoinStep_i]; exact h1 he
  · rw [gyCoinStep_other (ne_toNat_of_ne hne) (ne_toNat_of_ne hnj)]; exact h2 hne hnj
  · rw [toNat_of_eq hk' hje, gyCoinStep_j (ne_toNat_of_ne hne)]; exact h3 hne hje

-- SEGMENT: gyStage2
theorem gyStage2 {i j x x0 x1 x2 ρ amp w8 w9 D w11 w12 w13 w14 w15 w16 w17 w18 c s ann xv : B256} {M : Mem} {G : Nat} {r : Seg}
    (hwf : Mem.Wf M0)
    (hF : WordFrame M0 M 0x140 (gyCFrame i j x x0 x1 x2 ρ amp w8 w9 D w11 w12 w13 w14 w15 w16 w17
      w18 c s ann xv (Nat.toB256 2)))
    (run : SFunc.RunCut progYD sevm [] (St b (gyCStk S) M G) (gyTest 115 116 117) r) :
    gyOut b S M0 ((gyCoinStep i.toNat j.toNat 2 x.toNat x2.toNat D.toNat (c.toNat, s.toNat)).bind
      fun cs => ydPostRes cs.1 cs.2 D.toNat ann.toNat) r := by
  rcases ric_gyTest hF rfl rfl rfl rfl rfl (by decide) rfl List.not_mem_nil List.not_mem_nil
    List.not_mem_nil progGY_115 progGY_116 progGY_117 run with
    ⟨heq, G1, M1, hF1, run⟩ | ⟨hne, hnj, G1, M1, hF1, run⟩ | ⟨hne, hje, G1, run⟩
  · obtain ⟨G2, M2, c', s', hacc, hF2, run⟩ := ric_gyAcc hF1 rfl rfl rfl rfl rfl run
    obtain ⟨G3, M3, hF3, run⟩ := ric_gyCoinTail_last hF2 rfl rfl (by decide) run
    rw [toNat_of_eq (by decide) heq, gyCoinStep_i, hacc, Option.bind_some]
    exact ric_gyPost hwf hF3 run
  · obtain ⟨G2, run⟩ := ric_dest run
    obtain ⟨G3, M2, c', s', hacc, hF2, run⟩ := ric_gyAcc hF1 rfl rfl rfl rfl rfl run
    obtain ⟨G4, M3, hF3, run⟩ := ric_gyCoinTail_last hF2 rfl rfl (by decide) run
    rw [gyCoinStep_other (ne_toNat_of_ne hne) (ne_toNat_of_ne hnj), hacc, Option.bind_some]
    exact ric_gyPost hwf hF3 run
  · obtain ⟨G2, M2, hF2, run⟩ := ric_gyCoinTail_last hF rfl rfl (by decide) run
    rw [toNat_of_eq (by decide) hje, gyCoinStep_j (ne_toNat_of_ne hne), Option.bind_some]
    exact ric_gyPost hwf hF2 run

-- SEGMENT: gyStage1
theorem gyStage1 {i j x x0 x1 x2 ρ amp w8 w9 D w11 w12 w13 w14 w15 w16 w17 w18 c s ann xv : B256} {M : Mem} {G : Nat} {r : Seg}
    (hwf : Mem.Wf M0)
    (hF : WordFrame M0 M 0x140 (gyCFrame i j x x0 x1 x2 ρ amp w8 w9 D w11 w12 w13 w14 w15 w16 w17
      w18 c s ann xv (Nat.toB256 1)))
    (run : SFunc.RunCut progYD sevm [] (St b (gyCStk S) M G) (gyTest 70 71 72) r) :
    gyOut b S M0 ((gyCoinStep i.toNat j.toNat 1 x.toNat x1.toNat D.toNat (c.toNat, s.toNat)).bind
      fun cs =>
      (gyCoinStep i.toNat j.toNat 2 x.toNat x2.toNat D.toNat cs).bind fun cs =>
        ydPostRes cs.1 cs.2 D.toNat ann.toNat) r := by
  rcases ric_gyTest hF rfl rfl rfl rfl rfl (by decide) rfl List.not_mem_nil List.not_mem_nil
    List.not_mem_nil progGY_70 progGY_71 progGY_72 run with
    ⟨heq, G1, M1, hF1, run⟩ | ⟨hne, hnj, G1, M1, hF1, run⟩ | ⟨hne, hje, G1, run⟩
  · obtain ⟨G2, M2, c', s', hacc, hF2, run⟩ := ric_gyAcc hF1 rfl rfl rfl rfl rfl run
    obtain ⟨G3, M3, hF3, run⟩ :=
      ric_gyCoinTail_next hF2 rfl rfl (by decide) List.not_mem_nil progGY_95 run
    have h := gyStage2 hwf hF3 run
    rw [toNat_of_eq (by decide) heq] at h ⊢
    rw [gyCoinStep_i, hacc, Option.bind_some]
    exact h
  · obtain ⟨G2, run⟩ := ric_dest run
    obtain ⟨G3, M2, c', s', hacc, hF2, run⟩ := ric_gyAcc hF1 rfl rfl rfl rfl rfl run
    obtain ⟨G4, M3, hF3, run⟩ :=
      ric_gyCoinTail_next hF2 rfl rfl (by decide) List.not_mem_nil progGY_95 run
    rw [gyCoinStep_other (ne_toNat_of_ne hne) (ne_toNat_of_ne hnj), hacc, Option.bind_some]
    exact gyStage2 hwf hF3 run
  · obtain ⟨G2, M2, hF2, run⟩ :=
      ric_gyCoinTail_next hF rfl rfl (by decide) List.not_mem_nil progGY_95 run
    have h := gyStage2 hwf hF2 run
    rw [toNat_of_eq (by decide) hje] at h ⊢
    rw [gyCoinStep_j (ne_toNat_of_ne hne), Option.bind_some]
    exact h

-- SEGMENT: gyStage0
theorem gyStage0 {i j x x0 x1 x2 ρ amp w8 w9 D w11 w12 w13 w14 w15 w16 w17 w18 c s ann xv : B256} {M : Mem} {G : Nat} {r : Seg}
    (hwf : Mem.Wf M0)
    (hF : WordFrame M0 M 0x140 (gyCFrame i j x x0 x1 x2 ρ amp w8 w9 D w11 w12 w13 w14 w15 w16 w17
      w18 c s ann xv (Nat.toB256 0)))
    (run : SFunc.RunCut progYD sevm [] (St b (gyCStk S) M G) (gyTest 559 560 9) r) :
    gyOut b S M0 ((gyCoinStep i.toNat j.toNat 0 x.toNat x0.toNat D.toNat (c.toNat, s.toNat)).bind
      fun cs =>
      (gyCoinStep i.toNat j.toNat 1 x.toNat x1.toNat D.toNat cs).bind fun cs =>
        (gyCoinStep i.toNat j.toNat 2 x.toNat x2.toNat D.toNat cs).bind fun cs =>
          ydPostRes cs.1 cs.2 D.toNat ann.toNat) r := by
  rcases ric_gyTest hF rfl rfl rfl rfl rfl (by decide) rfl List.not_mem_nil List.not_mem_nil
    List.not_mem_nil progGY_559 progGY_560 progGY_9 run with
    ⟨heq, G1, M1, hF1, run⟩ | ⟨hne, hnj, G1, M1, hF1, run⟩ | ⟨hne, hje, G1, run⟩
  · obtain ⟨G2, M2, c', s', hacc, hF2, run⟩ := ric_gyAcc hF1 rfl rfl rfl rfl rfl run
    obtain ⟨G3, M3, hF3, run⟩ :=
      ric_gyCoinTail_next hF2 rfl rfl (by decide) List.not_mem_nil progGY_44 run
    have h := gyStage1 hwf hF3 run
    rw [toNat_of_eq (by decide) heq] at h ⊢
    rw [gyCoinStep_i, hacc, Option.bind_some]
    exact h
  · obtain ⟨G2, run⟩ := ric_dest run
    obtain ⟨G3, M2, c', s', hacc, hF2, run⟩ := ric_gyAcc hF1 rfl rfl rfl rfl rfl run
    obtain ⟨G4, M3, hF3, run⟩ :=
      ric_gyCoinTail_next hF2 rfl rfl (by decide) List.not_mem_nil progGY_44 run
    rw [gyCoinStep_other (ne_toNat_of_ne hne) (ne_toNat_of_ne hnj), hacc, Option.bind_some]
    exact gyStage1 hwf hF3 run
  · obtain ⟨G2, M2, hF2, run⟩ :=
      ric_gyCoinTail_next hF rfl rfl (by decide) List.not_mem_nil progGY_44 run
    have h := gyStage1 hwf hF2 run
    rw [toNat_of_eq (by decide) hje] at h ⊢
    rw [gyCoinStep_j (ne_toNat_of_ne hne), Option.bind_some]
    exact h

end Walk

end Blanc.Lift.Curve3Pool
