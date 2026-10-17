import Blanc.Lift.Curve3Pool.Callee.GetYDTrees
import Blanc.Lift.FuelLoopWalk
import Blanc.Lift.StableSwapNewton.Fuel

/-!
# `get_y_D`'s Newton `y` loop, inverted

The frame of `get_y_D` is the sixteen words at `0x140 … 0x320` (`ydFrame`): `A_`, `i`, `xp[0..2]`,
`D`, the return slot, `c`, `S_`, `Ann`, `_x`, the coin-loop counter, `b`, `y_prev`, `y` and the
`y`-loop counter.  At the loop head (`0x3b88`) the stack holds the loop's bound `255` over its
counter address `0x320` (`ydStk`).

* `ric_ydExit`: the exit at `0x3cae` returns the `y` slot, through scratch word `0`;
* `ric_ydTail`: the counter tail at `0x3c9d` re-enters the head with the counter advanced, or
  falls through once it reached `255`;
* `ydHead_step`: one pass of any copy of the head is the checked body `bodyYChk c b D` followed by
  the stopping test `closeEnough 1`: `FuelStep` for `Blanc.Lift.fuelLoop`.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune
open Blanc.StableSwapNewton

/-- `get_y_D`'s frame, `0x140 … 0x320`. -/
def ydFrame (A i x0 x1 x2 D ρ c s ann xv cc bw yp y n : B256) : List B256 :=
  [A, i, x0, x1, x2, D, ρ, c, s, ann, xv, cc, bw, yp, y, n]

/-- The `y` loop's stack: the bound `255` over the counter address `0x320`. -/
abbrev ydStk (S : List B256) : List B256 := Nat.toB256 255 :: Nat.toB256 0x320 :: S

/-- The memory `get_y_D` leaves: its frame `[0x140, 0x340)` and scratch word `0` written. -/
abbrev YDOut (M0 M : Mem) (v : B256) : Prop := ScratchOut M0 M 0x140 0x340 v


/-- The `y` loop's head state: counter `n`, iterate `y`, and the loop's fixed words `D`, the
return slot `ρ`, `c` and `b` in the frame. -/
def ydAt (b : Devm) (S : List B256) (M0 : Mem) (D ρ c bw : B256) (n y : Nat) (d : Devm) : Prop :=
  y < 2 ^ 256 ∧ ∃ M G A i x0 x1 x2 s ann xv cc yp, d = St b (ydStk S) M G ∧
    WordFrame M0 M 0x140 (ydFrame A i x0 x1 x2 D ρ c s ann xv cc bw yp (Nat.toB256 y)
      (Nat.toB256 n))

/-- How `get_y_D` leaves: returning `y` over the caller's stack, its memory as `YDOut`. -/
def ydOut (b : Devm) (S : List B256) (M0 : Mem) (v : Option Nat) (r : Seg) : Prop :=
  ∃ y, v = some y ∧ ∃ M G, r = .done (.returned (St b (Nat.toB256 y :: S) M G)) ∧
    YDOut M0 M (Nat.toB256 y)

/-- The `y` body on words: the checked body at the words' values is the word the bytes compute. -/
theorem bodyYChk_words {yw c bw D : B256} (hm1 : B256.Nofm yw yw)
    (ha1 : (yw * yw).toNat + c.toNat < 2 ^ 256) (hm2 : B256.Nofm (Bytes.toB256 [0x02]) yw)
    (ha2 : (Bytes.toB256 [0x02] * yw).toNat + bw.toNat < 2 ^ 256)
    (hs : D.toNat ≤ (Bytes.toB256 [0x02] * yw + bw).toNat)
    (hd : Bytes.toB256 [0x02] * yw + bw - D ≠ 0) :
    bodyYChk c.toNat bw.toNat D.toNat yw.toNat =
      some ((yw * yw + c) / (Bytes.toB256 [0x02] * yw + bw - D)).toNat := by
  have e2 : (2 : Nat) = (Bytes.toB256 [0x02]).toNat := by decide
  unfold bodyYChk
  rw [e2, chkMul_toNat_of_nofm hm1, chkMul_toNat_of_nofm hm2]
  simp only [Option.bind_eq_bind, Option.bind_some]
  rw [chkAdd_toNat_of_lt ha1, chkAdd_toNat_of_lt ha2]
  simp only [Option.bind_some]
  rw [chkSub_toNat_of_le hs]
  simp only [Option.bind_some]
  exact chkDiv_toNat_of_ne hd

/-- A slot index below the frame's sixteen words. -/
theorem lt16 {j : Nat} {ws : List B256} (hj : j < 16) (hl : ws.length = 16 := by rfl) :
    j < ws.length := hl ▸ hj

section Walk

variable {sevm : Sevm} {C : List Nat} {b : Devm} {S : List B256} {M0 M : Mem} {G : Nat}
  {r : Seg} {ws : List B256}

-- SEGMENT: ydExit
/-- **The exit**, inverted: `return y` leaves the `y` slot over the caller's stack. -/
theorem ric_ydExit (hF : WordFrame M0 M 0x140 ws) (hlen : ws.length = 16) {yw ρ : B256}
    (hy : ws[14]? = some yw) (hρ : ws[6]? = some ρ)
    (run : SFunc.RunCut progYD sevm C (St b (ydStk S) M G) ydExit r) :
    ∃ M' G', r = .done (.returned (St b (yw :: S) M' G')) ∧ YDOut M0 M' yw := by
  unfold ydExit at run
  obtain ⟨G1, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G2, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G3, rfl⟩ := ri_pop s1
  obtain ⟨G4, run⟩ := ric_pushMloadF hF 14 (by decide) hy run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G6, rfl⟩ := ri_mstore s1
  rw [show (Bytes.toB256 [0x00]).toNat = 0 by decide] at run
  obtain ⟨hout, hw⟩ := hF.scratch (by decide) yw
  rw [hlen] at hout
  have hsz : (M.write 0 yw.toBytes).size % 32 = 0 := by rw [hout.size]; exact hF.aligned
  have hcov : ∀ o, o + 32 ≤ 0x340 → ((M.write 0 yw.toBytes).read o 32).2 = M.write 0 yw.toBytes :=
    fun o ho => read_covered rfl hsz (by rw [hout.size]; have := hF.cover; rw [hlen] at this; omega)
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G7, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G8, rfl⟩ := ri_mload s1
  rw [show (Bytes.toB256 [0x00]).toNat = 0 by decide, hcov 0 (by decide)] at run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G9, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G10, rfl⟩ := ri_mload s1
  rw [show (Bytes.toB256 [0x02, 0x00]).toNat = 0x140 + 32 * 6 by decide,
    hcov _ (by decide)] at run
  have hρ' : Bytes.toB256 ((M.write 0 yw.toBytes).read (0x140 + 32 * 6) 32).1 = ρ := hw 6 ρ hρ
  rw [hρ'] at run
  obtain ⟨G11, hr⟩ := ric_ret run
  refine ⟨_, G11, ?_, hout⟩
  have h0 : Bytes.toB256 ((M.write 0 yw.toBytes).read 0 32).1 = yw := hout.word0
  rw [hr, h0]

theorem toB256_eq_toB256_iff {a c : Nat} (ha : a < 2 ^ 256) (hc : c < 2 ^ 256) :
    Nat.toB256 a = Nat.toB256 c ↔ a = c := by
  constructor
  · intro h
    have := congrArg B256.toNat h
    rwa [B256.toNat_toB256_of_lt ha, B256.toNat_toB256_of_lt hc] at this
  · intro h; rw [h]

/-- `PUSH1 1 ADD` on a counter word. -/
theorem one_add_toB256 {n : Nat} (hn : n + 1 < 2 ^ 256) :
    Bytes.toB256 [0x01] + Nat.toB256 n = Nat.toB256 (n + 1) := by
  rw [show Bytes.toB256 [0x01] = Nat.toB256 1 by decide, toB256_add_toB256 (by omega),
    Nat.add_comm]

-- SEGMENT: ydTail
/-- **The counter tail**, inverted: the counter advances; below `255` the run re-enters the cut
head `k`, at `255` it falls through. -/
theorem ric_ydTail (hF : WordFrame M0 M 0x140 ws) (hlen : ws.length = 16) {n k : Nat}
    {fall : SFunc} (hn : ws[15]? = some (Nat.toB256 n)) (hn255 : n < 255) (hk : k ∈ C)
    (run : SFunc.RunCut progYD sevm C (St b (ydStk S) M G) (ydTail k fall) r) :
    ∃ G' M', WordFrame M0 M' 0x140 (ws.set 15 (Nat.toB256 (n + 1))) ∧
      ((n + 1 ≠ 255 ∧ r = .at k (St b (ydStk S) M' G')) ∨
        (n + 1 = 255 ∧ SFunc.RunCut progYD sevm C (St b (ydStk S) M' G') fall r)) := by
  unfold ydTail at run
  obtain ⟨G1, run⟩ := ric_dest run
  obtain ⟨G2, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G3, rfl⟩ := ri_dup (w := Nat.toB256 0x320) rfl s1
  obtain ⟨G4, run⟩ := ric_mloadF hF 15 (by decide) hn run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G5, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G6, rfl⟩ := ri_add s1
  rw [one_add_toB256 (by omega)] at run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G7, rfl⟩ := ri_dup (w := Nat.toB256 (n + 1)) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G8, rfl⟩ := ri_dup (w := Nat.toB256 0x320) rfl s1
  obtain ⟨G9, M1, hF1, run⟩ := ric_mstoreF hF 15 (by decide) (by rw [hlen]; decide) run
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

-- SEGMENT: ydHead
/-- **One pass of the `y` loop**, inverted, at any copy of the head (exit `e`, tail `t`,
continuation head `k`, fall-through `fall` after the last pass): the checked body
`bodyYChk c b D` and the stopping test `closeEnough 1`, as `FuelStep`. -/
theorem ydHead_step {D ρ c bw : B256} {e t k : Nat} {fall fall' : SFunc}
    (he : progYD[e]? = some ydExit) (ht : progYD[t]? = some (ydTail k fall'))
    (heC : e ∉ C) (htC : t ∉ C) (hkC : k ∈ C) (hfall : fall = ydExit ∨ fall = .undefined)
    (hfall' : fall' = ydExit ∨ fall' = .undefined)
    {n y : Nat} (hn : n < 255) {d : Devm} (hAt : ydAt b S M0 D ρ c bw n y d)
    (run : SFunc.RunCut progYD sevm C d (ydHead e t k fall) r) :
    FuelStep k 255 (bodyYChk c.toNat bw.toNat D.toNat)
      (fun new prev => decide (closeEnough 1 new prev)) (ydAt b S M0 D ρ c bw)
      (ydOut b S M0) n y r := by
  obtain ⟨hy, M, G, A, i, x0, x1, x2, s, ann, xv, cc, yp, rfl, hF⟩ := hAt
  have hyN : (Nat.toB256 y).toNat = y := B256.toNat_toB256_of_lt hy
  unfold ydHead at run
  obtain ⟨G1, run⟩ := ric_dest run
  obtain ⟨G2, run⟩ := ric_pushMloadF hF 14 (by decide) rfl run
  obtain ⟨G3, M1, hF1, run⟩ := ric_pushMstoreF hF 13 (by decide) (lt16 (by decide)) run
  obtain ⟨G4, run⟩ := ric_pushMloadF hF1 14 (by decide) rfl run
  obtain ⟨G5, run⟩ := ric_pushMloadF hF1 14 (by decide) rfl run
  obtain ⟨hm1, G6, run⟩ := ric_vyMulT vyRevertT_noOk run
  obtain ⟨G7, run⟩ := ric_pushMloadF hF1 7 (by decide) rfl run
  obtain ⟨ha1, G8, run⟩ := ric_vyAddT vyRevertT_noOk run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G9, rfl⟩ := ri_push s1
  obtain ⟨G10, run⟩ := ric_pushMloadF hF1 14 (by decide) rfl run
  obtain ⟨hm2, G11, run⟩ := ric_vyMulT vyRevertT_noOk run
  obtain ⟨G12, run⟩ := ric_pushMloadF hF1 12 (by decide) rfl run
  obtain ⟨ha2, G13, run⟩ := ric_vyAddT vyRevertT_noOk run
  obtain ⟨G14, run⟩ := ric_pushMloadF hF1 5 (by decide) rfl run
  obtain ⟨hs, G15, run⟩ := ric_vySubT vyRevertT_noOk run
  obtain ⟨hd, G16, run⟩ := ric_vyDivT vyRevertT_noOk run
  have hbody := bodyYChk_words hm1 ha1 hm2 ha2 hs hd
  rw [hyN] at hbody
  generalize ((Nat.toB256 y * Nat.toB256 y + c) /
    (Bytes.toB256 [0x02] * Nat.toB256 y + bw - D)) = q at hbody run
  obtain ⟨G17, M2, hF2, run⟩ := ric_pushMstoreF hF1 14 (by decide) (lt16 (by decide)) run
  obtain ⟨G18, run⟩ := ric_pushMloadF hF2 13 (by decide) rfl run
  obtain ⟨G19, run⟩ := ric_pushMloadF hF2 14 (by decide) rfl run
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G20, rfl⟩ := ri_gt s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G21, rfl⟩ := ri_iszero s1
  obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G22, rfl⟩ := ri_push s1
  have hqw : Nat.toB256 q.toNat = q := toB256_toNat q
  have hqlt : q.toNat < 2 ^ 256 := B256.toNat_lt q
  -- leaving through the exit `e`
  have hexit : ∀ G', SFunc.RunCut progYD sevm C
      (St b (Bytes.toB256 [0x3c, 0xae] :: ydStk S) M2 G') (.jump e) r →
      ydOut b S M0 (some q.toNat) r := by
    intro G' run
    obtain ⟨G'', run⟩ := ric_jump heC he run
    obtain ⟨M', G3', hr, hout⟩ := ric_ydExit hF2 rfl rfl rfl run
    exact ⟨q.toNat, rfl, M', G3', by rw [hqw]; exact hr, by rw [hqw]; exact hout⟩
  -- the stopping pass
  have hstop : ∀ G', closeEnough 1 q.toNat y →
      SFunc.RunCut progYD sevm C (St b (Bytes.toB256 [0x3c, 0xae] :: ydStk S) M2 G')
        (.jump e) r → FuelStep k 255 (bodyYChk c.toNat bw.toNat D.toNat)
        (fun new prev => decide (closeEnough 1 new prev)) (ydAt b S M0 D ρ c bw)
        (ydOut b S M0) n y r := by
    intro G' hc run
    have ho := hexit G' run
    obtain ⟨_, _, M', G'', hr, _⟩ := id ho
    unfold FuelStep
    rw [hbody]
    simp only [decide_eq_true_eq, hc, true_or, ↓reduceIte]
    rw [hr] at ho ⊢
    exact ho
  -- the tail: re-enter `k`, or fall through after the last pass
  have htail : ∀ G' f, (f = ydExit ∨ f = .undefined) →
      SFunc.RunCut progYD sevm C (St b (ydStk S) M2 G') (ydTail k f) r →
      ¬ closeEnough 1 q.toNat y → FuelStep k 255 (bodyYChk c.toNat bw.toNat D.toNat)
        (fun new prev => decide (closeEnough 1 new prev)) (ydAt b S M0 D ρ c bw)
        (ydOut b S M0) n y r := by
    intro G' f hf run hnc
    obtain ⟨G'', M', hF', hcase⟩ := ric_ydTail hF2 rfl rfl hn hkC run
    unfold FuelStep
    rw [hbody]
    simp only [decide_eq_true_eq, hnc, false_or]
    rcases hcase with ⟨hne, hr⟩ | ⟨heq, run⟩
    · rw [ite_eq_right hne]
      refine ⟨_, hr, hqlt, M', G'', A, i, x0, x1, x2, s, ann, xv, cc, Nat.toB256 y, rfl, ?_⟩
      rw [hqw]; exact hF'
    · rw [ite_eq_left heq]
      rcases hf with rfl | rfl
      · obtain ⟨M'', G3', hr, hout⟩ := ric_ydExit hF' rfl rfl rfl run
        rw [hr]
        exact ⟨q.toNat, rfl, M'', G3', by rw [hqw], by rw [hqw]; exact hout⟩
      · exact (ric_undefined run).elim
  rcases ric_branch run with ⟨hw, G23, run⟩ | ⟨hw, G23, run⟩
  · -- `y > y_prev`
    have hgt := toNat_lt_of_iszero_gt_eq_zero hw
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G24, rfl⟩ := ri_push s1
    obtain ⟨G25, run⟩ := ric_pushMloadF hF2 14 (by decide) rfl run
    obtain ⟨G26, run⟩ := ric_pushMloadF hF2 13 (by decide) rfl run
    obtain ⟨hle, G27, run⟩ := ric_vySubT vyRevertT_noOk run
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G28, rfl⟩ := ri_gt s1
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G29, rfl⟩ := ri_iszero s1
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G30, rfl⟩ := ri_iszero s1
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G31, rfl⟩ := ri_push s1
    have hsub : (q - Nat.toB256 y).toNat = q.toNat - y := by
      rw [B256.toNat_sub_eq_of_le _ _ (B256.le_iff_toNat_le_toNat.mpr hle), hyN]
    rw [hyN] at hgt
    rcases ric_branch run with ⟨hw2, G32, run⟩ | ⟨hw2, G32, run⟩
    · have h0 := eq_zero_of_iszero2_eq_zero hw2
      have hle1 := toNat_le_of_gtCheck_eq_zero h0
      rw [hsub, show (Bytes.toB256 [0x01]).toNat = 1 by decide] at hle1
      obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G33, rfl⟩ := ri_push s1
      refine hstop G33 ?_ run
      unfold closeEnough; rw [ite_eq_left hgt]; exact hle1
    · have h0 := ne_zero_of_iszero2_ne_zero hw2
      obtain ⟨G33, run⟩ := ric_dest run
      obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G34, rfl⟩ := ri_push s1
      obtain ⟨G35, run⟩ := ric_jump htC ht run
      refine htail G35 _ hfall' run ?_
      unfold closeEnough; rw [ite_eq_left hgt]
      intro hle1
      apply h0
      unfold B256.gtCheck
      rw [ite_eq_right]
      rw [gt_iff_lt, B256.lt_iff_toNat_lt_toNat, hsub,
        show (Bytes.toB256 [0x01]).toNat = 1 by decide]
      omega
  · -- `y ≤ y_prev`
    have hngt := toNat_le_of_iszero_gt_ne_zero hw
    rw [hyN] at hngt
    obtain ⟨G24, run⟩ := ric_dest run
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G25, rfl⟩ := ri_push s1
    obtain ⟨G26, run⟩ := ric_pushMloadF hF2 13 (by decide) rfl run
    obtain ⟨G27, run⟩ := ric_pushMloadF hF2 14 (by decide) rfl run
    obtain ⟨hle, G28, run⟩ := ric_vySubT vyRevertT_noOk run
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G29, rfl⟩ := ri_gt s1
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G30, rfl⟩ := ri_iszero s1
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G31, rfl⟩ := ri_iszero s1
    obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G32, rfl⟩ := ri_push s1
    have hsub : (Nat.toB256 y - q).toNat = y - q.toNat := by
      rw [B256.toNat_sub_eq_of_le _ _ (B256.le_iff_toNat_le_toNat.mpr hle), hyN]
    have hng : ¬ q.toNat > y := by omega
    rcases ric_branch run with ⟨hw2, G33, run⟩ | ⟨hw2, G33, run⟩
    · have h0 := eq_zero_of_iszero2_eq_zero hw2
      have hle1 := toNat_le_of_gtCheck_eq_zero h0
      rw [hsub, show (Bytes.toB256 [0x01]).toNat = 1 by decide] at hle1
      obtain ⟨d1, s1, run⟩ := ric_next run; obtain ⟨G34, rfl⟩ := ri_push s1
      refine hstop G34 ?_ run
      unfold closeEnough; rw [ite_eq_right hng]; exact hle1
    · have h0 := ne_zero_of_iszero2_ne_zero hw2
      obtain ⟨G34, run⟩ := ric_dest run
      refine htail G34 _ hfall run ?_
      unfold closeEnough; rw [ite_eq_right hng]
      intro hle1
      apply h0
      unfold B256.gtCheck
      rw [ite_eq_right]
      rw [gt_iff_lt, B256.lt_iff_toNat_lt_toNat, hsub,
        show (Bytes.toB256 [0x01]).toNat = 1 by decide]
      omega

end Walk

end Blanc.Lift.Curve3Pool

namespace Blanc.Lift.Curve3Pool

open Jaune
open Blanc.StableSwapNewton

section Loop

variable {sevm : Sevm} {b : Devm} {S : List B256} {M0 : Mem} {D ρ c bw : B256}

/-- The `y` loop's fuel-loop body and stopping test at the frame's `c`, `b`, `D`. -/
abbrev ydLoop (c bw D : B256) (fuel y : Nat) : Option Nat :=
  fuelLoop (bodyYChk c.toNat bw.toNat D.toNat) (fun new prev => decide (closeEnough 1 new prev))
    fuel y

-- SEGMENT: ydLoop
/-- **The `y` loop**, inverted from its first (inline) pass: every run from the head state at
counter `n` ends as `ydOut` of the fuel loop over the remaining `255 - n` passes. -/
theorem ydLoop_sound : ∀ n y d r, n < 255 → ydAt b S M0 D ρ c bw n y d →
    SFunc.RunCut progYD sevm [] d (ydHead 141 142 143 .undefined) r →
    ydOut b S M0 (ydLoop c bw D (255 - n) y) r := by
  have h205 := RunCut_fuelLoop_sound (P := Ninst.Run) (sevm := sevm) (C := []) progYD_205
    (List.not_mem_nil) (ydAt b S M0 D ρ c bw) (ydOut b S M0)
    (fun n y d hn hAt r run => ydHead_step progYD_185 progYD_204 (by decide) (by decide)
      List.mem_cons_self (.inl rfl) (.inl rfl) hn hAt run)
  have h187 := RunCut_fuelLoop_peel (P := Ninst.Run) (sevm := sevm) (C := []) progYD_205
    (List.not_mem_nil) (ydAt b S M0 D ρ c bw) (ydOut b S M0) h205
    (fun n y d hn hAt r run => ydHead_step (fall := .undefined) progYD_185 progYD_204
      (by decide) (by decide) List.mem_cons_self (.inr rfl) (.inl rfl) hn hAt run)
  have h165 := RunCut_fuelLoop_peel (P := Ninst.Run) (sevm := sevm) (C := []) progYD_187
    (List.not_mem_nil) (ydAt b S M0 D ρ c bw) (ydOut b S M0) h187
    (fun n y d hn hAt r run => ydHead_step (fall := .undefined) progYD_185 progYD_186
      (by decide) (by decide) List.mem_cons_self (.inr rfl) (.inr rfl) hn hAt run)
  have h143 := RunCut_fuelLoop_peel (P := Ninst.Run) (sevm := sevm) (C := []) progYD_165
    (List.not_mem_nil) (ydAt b S M0 D ρ c bw) (ydOut b S M0) h165
    (fun n y d hn hAt r run => ydHead_step (fall := .undefined) progYD_163 progYD_164
      (by decide) (by decide) List.mem_cons_self (.inr rfl) (.inr rfl) hn hAt run)
  exact RunCut_fuelLoop_peel (P := Ninst.Run) (sevm := sevm) (C := []) progYD_143
    (List.not_mem_nil) (ydAt b S M0 D ρ c bw) (ydOut b S M0) h143
    (fun n y d hn hAt r run => ydHead_step (fall := .undefined) progYD_141 progYD_142
      (by decide) (by decide) List.mem_cons_self (.inr rfl) (.inr rfl) hn hAt run)

end Loop

end Blanc.Lift.Curve3Pool
