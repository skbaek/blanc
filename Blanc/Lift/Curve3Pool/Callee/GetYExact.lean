import Blanc.Lift.Curve3Pool.Callee.GetY
import Blanc.Lift.Curve3Pool.Callee.GetYDExact
import Blanc.Lift.Curve3Pool.Callee.GetDExact

/-!
# `get_y`, forward: exact gas

The forward twin of `getY_spec`.  The `y` loop and the coin loop are the forward walks of
`GetYDExact.lean` at `get_y`'s offsets over its twenty-eight-word frame (the same pass costs
`ydStepC`/`ydStopC`/`ydCapC` and the exit `37`, the tail `45`, the post-loop `363`); the coin
test has three arms (coin `i`: `55`, `j`: `76`, else: `127`).  Over a memory already covering
`[0, 0x4c0)`, the whole callee costs `costGetY`: the glue `2100`, `_A`'s `aGas`, `get_D`'s
`costGetD`, and the coin and `y` loops.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune
open Blanc.StableSwapNewton

section Fwd

variable {sevm : Sevm} {C : List Nat} {b : Devm} {S : List B256} {M0 M : Mem} {G : Nat}
  {r : Seg} {ws : List B256}

theorem gyFrame_size_pos (hF : WordFrame M0 M 0x140 ws) (hlen : ws.length = 28) :
    M.size % 32 = 0 ∧ 0x4c0 ≤ M.size := by
  have := hF.cover; rw [hlen] at this
  exact ⟨by rw [hF.size]; exact hF.aligned, by rw [hF.size]; omega⟩

-- SEGMENT: rxc_gyExit
/-- **The exit**, forward (37 gas). -/
theorem rxc_gyExit (hF : WordFrame M0 M 0x140 ws) (hlen : ws.length = 28) {yw ρ : B256}
    (hy : ws[26]? = some yw) (hρ : ws[6]? = some ρ) (hroom : S.length + 4 < 1024) :
    ∃ M', ScratchOut M0 M' 0x140 0x4c0 yw ∧
      SFunc.RunExactCut progYD sevm C (St b (gyStk S) M (G + 37)) gyExit
        (.done (.returned (St b (yw :: S) M' G))) := by
  obtain ⟨hout, hw⟩ := hF.scratch (by decide) yw
  rw [hlen] at hout
  obtain ⟨hsz, hcov⟩ := gyFrame_size_pos hF hlen
  have hsz1 : (M.write 0 yw.toBytes).size % 32 = 0 := by rw [hout.size]; exact hF.aligned
  have hcov1 : 0x4c0 ≤ (M.write 0 yw.toBytes).size := by
    rw [hout.size, ← hF.size]; exact hcov
  refine ⟨_, hout, ?_⟩
  unfold gyExit
  refine rxc_dest (rxc_pop (rxc_pop ?_))
  refine rxc_pushMloadF hF 26 (by decide) hy (by omega) ?_
  refine rxc_push rfl (by vy_room) ?_
  refine rxc_mstore (c := 3) (i := Bytes.toB256 [0x00]) (mstore_covered_cost' hsz
    (by rw [show (Bytes.toB256 [0x00]).toNat = 0 by decide]; omega))
    (by rw [show (Bytes.toB256 [0x00]).toNat = 0 by decide]) ?_
  refine rxc_push rfl (by vy_room) ?_
  refine rxc_mload (c := 3) (i := Bytes.toB256 [0x00]) (v := yw) (mload_covered_cost' hsz1
    (by rw [show (Bytes.toB256 [0x00]).toNat = 0 by decide]; omega)) hout.word0
    (read_covered rfl hsz1 (by rw [show (Bytes.toB256 [0x00]).toNat = 0 by decide]; omega))
    (by omega) ?_
  refine rxc_push rfl (by vy_room) ?_
  have e200 : (Bytes.toB256 [0x02, 0x00]).toNat = 0x140 + 32 * 6 := by decide
  refine rxc_mload (c := 3) (i := Bytes.toB256 [0x02, 0x00]) (v := ρ) (mload_covered_cost' hsz1
    (by rw [e200]; omega)) (by rw [e200]; exact hw 6 ρ hρ)
    (read_covered rfl hsz1 (by rw [e200]; omega)) (by vy_room) ?_
  exact rxc_ret

-- SEGMENT: rxc_gyTail
/-- **The counter tail**, forward, re-entering the cut head (45 gas). -/
theorem rxc_gyTail_next (hF : WordFrame M0 M 0x140 ws) (hlen : ws.length = 28) {n k : Nat}
    {fall : SFunc} (hn : ws[27]? = some (Nat.toB256 n)) (hn1 : n + 1 < 255) (hk : k ∈ C)
    (hroom : S.length + 8 < 1024) :
    SFunc.RunExactCut progYD sevm C (St b (gyStk S) M (G + 45)) (gyTail k fall)
      (.at k (St b (gyStk S) (M.write (0x140 + 32 * 27) (Nat.toB256 (n + 1)).toBytes) G)) := by
  unfold gyTail
  refine rxc_dest (rxc_dest ?_)
  refine rxc_dup (w := Nat.toB256 0x4a0) rfl (by vy_room) ?_
  refine rxc_mloadF hF 27 (by decide) hn (by vy_room) ?_
  refine rxc_push rfl (by vy_room) ?_
  refine rxc_add' (one_add_toB256 (by omega)) (by vy_room) ?_
  refine rxc_dup (w := Nat.toB256 (n + 1)) rfl (by vy_room) ?_
  refine rxc_dup (w := Nat.toB256 0x4a0) rfl (by vy_room) ?_
  refine rxc_mstoreF hF 27 (by decide) (by rw [hlen]; decide) ?_
  refine rxc_dup (w := Nat.toB256 255) rfl (by vy_room) ?_
  refine rxc_eq rfl (by vy_room) ?_
  refine rxc_iszero rfl (by vy_room) ?_
  refine rxc_push rfl (by vy_room) ?_
  exact rxc_branchTo_cut (iszero_eq255_ne (by omega) (by omega)) hk

/-- **The counter tail**, forward, falling through after the last pass (45 gas). -/
theorem rxc_gyTail_last (hF : WordFrame M0 M 0x140 ws) (hlen : ws.length = 28) {n k : Nat}
    {fall : SFunc} (hn : ws[27]? = some (Nat.toB256 n)) (hn1 : n + 1 = 255)
    (hroom : S.length + 8 < 1024)
    (kk : SFunc.RunExactCut progYD sevm C
      (St b (gyStk S) (M.write (0x140 + 32 * 27) (Nat.toB256 (n + 1)).toBytes) G) fall r) :
    SFunc.RunExactCut progYD sevm C (St b (gyStk S) M (G + 45)) (gyTail k fall) r := by
  unfold gyTail
  refine rxc_dest (rxc_dest ?_)
  refine rxc_dup (w := Nat.toB256 0x4a0) rfl (by vy_room) ?_
  refine rxc_mloadF hF 27 (by decide) hn (by vy_room) ?_
  refine rxc_push rfl (by vy_room) ?_
  refine rxc_add' (one_add_toB256 (by omega)) (by vy_room) ?_
  refine rxc_dup (w := Nat.toB256 (n + 1)) rfl (by vy_room) ?_
  refine rxc_dup (w := Nat.toB256 0x4a0) rfl (by vy_room) ?_
  refine rxc_mstoreF hF 27 (by decide) (by rw [hlen]; decide) ?_
  refine rxc_dup (w := Nat.toB256 255) rfl (by vy_room) ?_
  refine rxc_eq rfl (by vy_room) ?_
  refine rxc_iszero rfl (by vy_room) ?_
  refine rxc_push rfl (by vy_room) ?_
  have hw : B256.eqCheck (B256.eqCheck (Nat.toB256 255) (Nat.toB256 (n + 1))) 0 = 0 := by
    rw [hn1]; decide
  rw [hw]
  exact rxc_branchTo_zero kk

-- SEGMENT: rxc_gyHeadPre
/-- **A Newton pass up to its stopping test**, forward (402 gas). -/
theorem rxc_gyHeadPre (hF : WordFrame M0 M 0x140 ws) (hlen : ws.length = 28) {yw c bw D : B256}
    (hy : ws[26]? = some yw) (hc : ws[19]? = some c) (hb : ws[24]? = some bw)
    (hD : ws[10]? = some D) (hm1 : B256.Nofm yw yw) (ha1 : (yw * yw).toNat + c.toNat < 2 ^ 256)
    (hm2 : B256.Nofm (Bytes.toB256 [0x02]) yw)
    (ha2 : (Bytes.toB256 [0x02] * yw).toNat + bw.toNat < 2 ^ 256)
    (hs : D.toNat ≤ (Bytes.toB256 [0x02] * yw + bw).toNat)
    (hd : Bytes.toB256 [0x02] * yw + bw - D ≠ 0) (hroom : S.length + 12 < 1024)
    {e t k : Nat} {fall : SFunc}
    (kk : SFunc.RunExactCut progYD sevm C (St b (Bytes.toB256 [0x1c, 0xc3] ::
      B256.eqCheck (B256.gtCheck ((yw * yw + c) / (Bytes.toB256 [0x02] * yw + bw - D)) yw) 0 ::
      gyStk S) ((M.write (0x140 + 32 * 25) yw.toBytes).write (0x140 + 32 * 26)
        ((yw * yw + c) / (Bytes.toB256 [0x02] * yw + bw - D)).toBytes) G) (gyHeadBr e t k fall) r) :
    SFunc.RunExactCut progYD sevm C (St b (gyStk S) M (G + 402)) (gyHead e t k fall) r := by
  have hF13 := hF.write (j := 25) (by rw [hlen]; decide) yw
  have hF14 := hF13.write (j := 26) (by rw [List.length_set, hlen]; decide)
    ((yw * yw + c) / (Bytes.toB256 [0x02] * yw + bw - D))
  have h13y : (ws.set 25 yw)[26]? = some yw := by rw [List.getElem?_set_ne (by decide)]; exact hy
  have h13c : (ws.set 25 yw)[19]? = some c := by rw [List.getElem?_set_ne (by decide)]; exact hc
  have h13b : (ws.set 25 yw)[24]? = some bw := by rw [List.getElem?_set_ne (by decide)]; exact hb
  have h13D : (ws.set 25 yw)[10]? = some D := by rw [List.getElem?_set_ne (by decide)]; exact hD
  have h14y : ((ws.set 25 yw).set 26 ((yw * yw + c) / (Bytes.toB256 [0x02] * yw + bw - D)))[25]? =
      some yw := by
    rw [List.getElem?_set_ne (by decide), List.getElem?_set_self (by rw [hlen]; decide)]
  have h14q : ((ws.set 25 yw).set 26 ((yw * yw + c) / (Bytes.toB256 [0x02] * yw + bw - D)))[26]? =
      some ((yw * yw + c) / (Bytes.toB256 [0x02] * yw + bw - D)) := by
    rw [List.getElem?_set_self (by rw [List.length_set, hlen]; decide)]
  unfold gyHead
  refine rxc_dest ?_
  refine rxc_pushMloadF hF 26 (by decide) hy (by vy_room) ?_
  refine rxc_pushMstoreF hF 25 (by decide) (by rw [hlen]; decide) (by vy_room) ?_
  refine rxc_pushMloadF hF13 26 (by decide) h13y (by vy_room) ?_
  refine rxc_pushMloadF hF13 26 (by decide) h13y (by vy_room) ?_
  refine rxc_vyMulT hm1 (by vy_room) ?_
  refine rxc_pushMloadF hF13 19 (by decide) h13c (by vy_room) ?_
  refine rxc_vyAddT ha1 (by vy_room) ?_
  refine rxc_push rfl (by vy_room) ?_
  refine rxc_pushMloadF hF13 26 (by decide) h13y (by vy_room) ?_
  refine rxc_vyMulT hm2 (by vy_room) ?_
  refine rxc_pushMloadF hF13 24 (by decide) h13b (by vy_room) ?_
  refine rxc_vyAddT ha2 (by vy_room) ?_
  refine rxc_pushMloadF hF13 10 (by decide) h13D (by vy_room) ?_
  refine rxc_vySubT hs (by vy_room) ?_
  refine rxc_vyDivT hd (by vy_room) ?_
  refine rxc_pushMstoreF hF13 26 (by decide) (by rw [List.length_set, hlen]; decide) (by vy_room) ?_
  refine rxc_pushMloadF hF14 25 (by decide) h14y (by vy_room) ?_
  refine rxc_pushMloadF hF14 26 (by decide) h14q (by vy_room) ?_
  refine rxc_binary (fn := B256.gtCheck) (c := gVerylow) (by rintro ⟨⟩) (fun _ => rfl) rfl
    (by vy_room) ?_
  refine rxc_iszero rfl (by vy_room) ?_
  exact rxc_push rfl (by vy_room) kk

-- SEGMENT: rxc_gyHeadBr
/-- **The stopping test, stopping**, forward: on to the exit `e`. -/
theorem rxc_gyHeadBr_close (hF : WordFrame M0 M 0x140 ws) {yw q : B256} {e t k : Nat}
    {fall : SFunc} (h13 : ws[25]? = some yw) (h14 : ws[26]? = some q)
    (hc : closeEnough 1 q.toNat yw.toNat) (he : progYD[e]? = some gyExit) (heC : e ∉ C)
    (hroom : S.length + 12 < 1024)
    (kk : SFunc.RunExactCut progYD sevm C (St b (gyStk S) M G) gyExit r) :
    SFunc.RunExactCut progYD sevm C (St b (Bytes.toB256 [0x1c, 0xc3] ::
      B256.eqCheck (B256.gtCheck q yw) 0 :: gyStk S) M
      (G + if yw.toNat < q.toNat then 103 else 104)) (gyHeadBr e t k fall) r := by
  unfold gyHeadBr
  have h1 : (Bytes.toB256 [0x01]).toNat = 1 := by decide
  by_cases hgt : yw.toNat < q.toNat
  · rw [ite_eq_left hgt, gtCheck_toNat, ite_eq_left hgt]
    refine rxc_branch_zero (d := Bytes.toB256 [0x1c, 0xc3]) ?_
    refine rxc_push rfl (by vy_room) ?_
    refine rxc_pushMloadF hF 26 (by decide) h14 (by vy_room) ?_
    refine rxc_pushMloadF hF 25 (by decide) h13 (by vy_room) ?_
    refine rxc_vySubT (x := q) (y := yw) (by omega) (by vy_room) ?_
    refine rxc_binary (fn := B256.gtCheck) (c := gVerylow) (by rintro ⟨⟩) (fun _ => rfl) rfl
      (by vy_room) ?_
    refine rxc_iszero rfl (by vy_room) ?_
    refine rxc_iszero rfl (by vy_room) ?_
    refine rxc_push rfl (by vy_room) ?_
    have hle : (q - yw).toNat ≤ 1 := by
      unfold closeEnough at hc; rw [ite_eq_left hgt] at hc
      rw [B256.toNat_sub_eq_of_le _ _ (B256.le_iff_toNat_le_toNat.mpr (by omega))]; exact hc
    rw [gtCheck_toNat, h1, ite_eq_right (by omega)]
    refine rxc_branch_zero (d := Bytes.toB256 [0x1c, 0xbe]) ?_
    refine rxc_push rfl (by vy_room) ?_
    exact rxc_jump he heC kk
  · rw [ite_eq_right hgt, gtCheck_toNat, ite_eq_right hgt]
    refine rxc_branch_succ (by decide) (rxc_dest ?_)
    refine rxc_push rfl (by vy_room) ?_
    refine rxc_pushMloadF hF 25 (by decide) h13 (by vy_room) ?_
    refine rxc_pushMloadF hF 26 (by decide) h14 (by vy_room) ?_
    refine rxc_vySubT (x := yw) (y := q) (by omega) (by vy_room) ?_
    refine rxc_binary (fn := B256.gtCheck) (c := gVerylow) (by rintro ⟨⟩) (fun _ => rfl) rfl
      (by vy_room) ?_
    refine rxc_iszero rfl (by vy_room) ?_
    refine rxc_iszero rfl (by vy_room) ?_
    refine rxc_push rfl (by vy_room) ?_
    have hle : (yw - q).toNat ≤ 1 := by
      unfold closeEnough at hc; rw [ite_eq_right (by omega)] at hc
      rw [B256.toNat_sub_eq_of_le _ _ (B256.le_iff_toNat_le_toNat.mpr (by omega))]; exact hc
    rw [gtCheck_toNat, h1, ite_eq_right (by omega)]
    refine rxc_branch_zero (d := Bytes.toB256 [0x1c, 0xed]) ?_
    refine rxc_push rfl (by vy_room) ?_
    exact rxc_jump he heC kk

/-- **The stopping test, going on**, forward: on to the counter tail. -/
theorem rxc_gyHeadBr_next (hF : WordFrame M0 M 0x140 ws) {yw q : B256} {e t k : Nat}
    {fall fall' : SFunc} (h13 : ws[25]? = some yw) (h14 : ws[26]? = some q)
    (hnc : ¬ closeEnough 1 q.toNat yw.toNat) (ht : progYD[t]? = some (gyTail k fall'))
    (htC : t ∉ C) (hroom : S.length + 12 < 1024)
    (kA : yw.toNat < q.toNat →
      SFunc.RunExactCut progYD sevm C (St b (gyStk S) M G) (gyTail k fall') r)
    (kB : ¬ yw.toNat < q.toNat →
      SFunc.RunExactCut progYD sevm C (St b (gyStk S) M G) (gyTail k fall) r) :
    SFunc.RunExactCut progYD sevm C (St b (Bytes.toB256 [0x1c, 0xc3] ::
      B256.eqCheck (B256.gtCheck q yw) 0 :: gyStk S) M
      (G + if yw.toNat < q.toNat then 104 else 94)) (gyHeadBr e t k fall) r := by
  unfold gyHeadBr
  have h1 : (Bytes.toB256 [0x01]).toNat = 1 := by decide
  by_cases hgt : yw.toNat < q.toNat
  · rw [ite_eq_left hgt, gtCheck_toNat, ite_eq_left hgt]
    refine rxc_branch_zero (d := Bytes.toB256 [0x1c, 0xc3]) ?_
    refine rxc_push rfl (by vy_room) ?_
    refine rxc_pushMloadF hF 26 (by decide) h14 (by vy_room) ?_
    refine rxc_pushMloadF hF 25 (by decide) h13 (by vy_room) ?_
    refine rxc_vySubT (x := q) (y := yw) (by omega) (by vy_room) ?_
    refine rxc_binary (fn := B256.gtCheck) (c := gVerylow) (by rintro ⟨⟩) (fun _ => rfl) rfl
      (by vy_room) ?_
    refine rxc_iszero rfl (by vy_room) ?_
    refine rxc_iszero rfl (by vy_room) ?_
    refine rxc_push rfl (by vy_room) ?_
    have hgt1 : 1 < (q - yw).toNat := by
      unfold closeEnough at hnc; rw [ite_eq_left hgt] at hnc
      rw [B256.toNat_sub_eq_of_le _ _ (B256.le_iff_toNat_le_toNat.mpr (by omega))]; omega
    rw [gtCheck_toNat, h1, ite_eq_left hgt1]
    refine rxc_branch_succ (by decide) (rxc_dest ?_)
    refine rxc_push rfl (by vy_room) ?_
    exact rxc_jump ht htC (kA hgt)
  · rw [ite_eq_right hgt, gtCheck_toNat, ite_eq_right hgt]
    refine rxc_branch_succ (by decide) (rxc_dest ?_)
    refine rxc_push rfl (by vy_room) ?_
    refine rxc_pushMloadF hF 25 (by decide) h13 (by vy_room) ?_
    refine rxc_pushMloadF hF 26 (by decide) h14 (by vy_room) ?_
    refine rxc_vySubT (x := yw) (y := q) (by omega) (by vy_room) ?_
    refine rxc_binary (fn := B256.gtCheck) (c := gVerylow) (by rintro ⟨⟩) (fun _ => rfl) rfl
      (by vy_room) ?_
    refine rxc_iszero rfl (by vy_room) ?_
    refine rxc_iszero rfl (by vy_room) ?_
    refine rxc_push rfl (by vy_room) ?_
    have hgt1 : 1 < (yw - q).toNat := by
      unfold closeEnough at hnc; rw [ite_eq_right (by omega)] at hnc
      rw [B256.toNat_sub_eq_of_le _ _ (B256.le_iff_toNat_le_toNat.mpr (by omega))]; omega
    rw [gtCheck_toNat, h1, ite_eq_left hgt1]
    refine rxc_branch_succ (by decide) (rxc_dest ?_)
    exact kB hgt

/-! ## The `y` loop, forward -/

/-- The `y` loop's head state with its gas: counter `n`, iterate `y`. -/
def gyAtX (b : Devm) (S : List B256) (M0 : Mem) (D ρ c bw : B256) (n y G : Nat) (d : Devm) :
    Prop :=
  y < 2 ^ 256 ∧ ∃ M i j x x0 x1 x2 amp w8 w9 w11 w12 w13 w14 w15 w16 w17 w18 s ann xv cc yp,
    d = St b (gyStk S) M G ∧
    WordFrame M0 M 0x140 (gyFrame i j x x0 x1 x2 ρ amp w8 w9 D w11 w12 w13 w14 w15 w16 w17 w18 c
      s ann xv cc bw yp (Nat.toB256 y) (Nat.toB256 n))

/-- How `get_y`'s loop (frame `[0x140, 0x4c0)`) returns `v` with `G` gas left. -/
def gyCalleeExit (b : Devm) (S : List B256) (M0 : Mem) (v G : Nat) (r : Seg) : Prop :=
  ∃ M, r = .done (.returned (St b (Nat.toB256 v :: S) M G)) ∧
    ScratchOut M0 M 0x140 0x4c0 (Nat.toB256 v)

-- SEGMENT: gyHead_fwd
/-- **A stopping Newton pass**, forward, at any copy. -/
theorem gyHead_stopX {D ρ c bw : B256} {e t k : Nat} {fall : SFunc}
    (he : progYD[e]? = some gyExit) (heC : e ∉ C) (hroom : S.length + 12 < 1024)
    {n y y' G : Nat} {d : Devm} (hb : bodyYChk c.toNat bw.toNat D.toNat y = some y')
    (hc : closeEnough 1 y' y) (hAt : gyAtX b S M0 D ρ c bw n y (G + ydStopC y y') d) :
    ∃ r, SFunc.RunExactCut progYD sevm C d (gyHead e t k fall) r ∧ (∀ d', r ≠ .at k d') ∧
      gyCalleeExit b S M0 y' G r := by
  obtain ⟨hy, M, i, j, x, x0, x1, x2, amp, w8, w9, w11, w12, w13, w14, w15, w16, w17, w18, s,
    ann, xv, cc, yp, rfl, hF⟩ := hAt
  have hyN : (Nat.toB256 y).toNat = y := B256.toNat_toB256_of_lt hy
  rw [← hyN] at hb hc
  obtain ⟨hm1, ha1, hm2, ha2, hs, hd, rfl⟩ := bodyYChk_inv hb
  have hF13 := hF.write (j := 25) (lt28 (by decide)) (Nat.toB256 y)
  have hF14 := hF13.write (j := 26) (lt28 (by decide))
    ((Nat.toB256 y * Nat.toB256 y + c) / (Bytes.toB256 [0x02] * Nat.toB256 y + bw - D))
  obtain ⟨M', hout, hex⟩ := rxc_gyExit (C := C) (G := G) (S := S) hF14 rfl rfl rfl (by omega)
  refine ⟨.done (.returned (St b (((Nat.toB256 y * Nat.toB256 y + c) / (Bytes.toB256 [0x02] * Nat.toB256 y + bw - D)) :: S) M' G)), ?_, fun d' h => (by cases h), M',
    by rw [toB256_toNat], by rw [toB256_toNat]; exact hout⟩
  have hg : G + ydStopC y
      ((Nat.toB256 y * Nat.toB256 y + c) / (Bytes.toB256 [0x02] * Nat.toB256 y + bw - D)).toNat =
      (G + 37 + if (Nat.toB256 y).toNat < ((Nat.toB256 y * Nat.toB256 y + c) /
        (Bytes.toB256 [0x02] * Nat.toB256 y + bw - D)).toNat then 103 else 104) + 402 := by
    rw [hyN]; unfold ydStopC; split <;> omega
  rw [hg]
  exact rxc_gyHeadPre hF rfl rfl rfl rfl rfl hm1 ha1 hm2 ha2 hs hd hroom
    (rxc_gyHeadBr_close hF14 rfl rfl hc he heC hroom hex)

/-- **A Newton pass that goes on**, forward, at any copy: back to the cut head `k`. -/
theorem gyHead_stepX {D ρ c bw : B256} {e t k : Nat} {fall fall' : SFunc}
    (ht : progYD[t]? = some (gyTail k fall')) (htC : t ∉ C) (hkC : k ∈ C)
    (hroom : S.length + 12 < 1024)
    {n y y' G : Nat} {d : Devm} (hn : n + 1 < 255)
    (hb : bodyYChk c.toNat bw.toNat D.toNat y = some y')
    (hc : ¬ closeEnough 1 y' y) (hAt : gyAtX b S M0 D ρ c bw n y (G + ydStepC y y') d) :
    ∃ d', SFunc.RunExactCut progYD sevm C d (gyHead e t k fall) (.at k d') ∧
      gyAtX b S M0 D ρ c bw (n + 1) y' G d' := by
  obtain ⟨hy, M, i, j, x, x0, x1, x2, amp, w8, w9, w11, w12, w13, w14, w15, w16, w17, w18, s,
    ann, xv, cc, yp, rfl, hF⟩ := hAt
  have hyN : (Nat.toB256 y).toNat = y := B256.toNat_toB256_of_lt hy
  rw [← hyN] at hb hc
  obtain ⟨hm1, ha1, hm2, ha2, hs, hd, rfl⟩ := bodyYChk_inv hb
  have hF13 := hF.write (j := 25) (lt28 (by decide)) (Nat.toB256 y)
  have hF14 := hF13.write (j := 26) (lt28 (by decide))
    ((Nat.toB256 y * Nat.toB256 y + c) / (Bytes.toB256 [0x02] * Nat.toB256 y + bw - D))
  have hF15 := hF14.write (j := 27) (lt28 (by decide)) (Nat.toB256 (n + 1))
  refine ⟨_, ?_, B256.toNat_lt _, _, i, j, x, x0, x1, x2, amp, w8, w9, w11, w12, w13, w14, w15,
    w16, w17, w18, s, ann, xv, cc, Nat.toB256 y, rfl,
    by rw [toB256_toNat]; exact hF15⟩
  have hg : G + ydStepC y
      ((Nat.toB256 y * Nat.toB256 y + c) / (Bytes.toB256 [0x02] * Nat.toB256 y + bw - D)).toNat =
      (G + 45 + if (Nat.toB256 y).toNat < ((Nat.toB256 y * Nat.toB256 y + c) /
        (Bytes.toB256 [0x02] * Nat.toB256 y + bw - D)).toNat then 104 else 94) + 402 := by
    rw [hyN]; unfold ydStepC; split <;> omega
  rw [hg]
  exact rxc_gyHeadPre hF rfl rfl rfl rfl rfl hm1 ha1 hm2 ha2 hs hd hroom
    (rxc_gyHeadBr_next hF14 rfl rfl hc ht htC hroom
      (fun _ => rxc_gyTail_next hF14 rfl rfl hn hkC (by omega))
      (fun _ => rxc_gyTail_next hF14 rfl rfl hn hkC (by omega)))

/-- **The last permitted pass**, forward, at the steady copy: through the tail to the exit. -/
theorem gyHead_capX {D ρ c bw : B256} {e t k : Nat}
    (ht : progYD[t]? = some (gyTail k gyExit)) (htC : t ∉ C)
    (hroom : S.length + 12 < 1024)
    {n y y' G : Nat} {d : Devm} (hn : n + 1 = 255)
    (hb : bodyYChk c.toNat bw.toNat D.toNat y = some y')
    (hc : ¬ closeEnough 1 y' y) (hAt : gyAtX b S M0 D ρ c bw n y (G + ydCapC y y') d) :
    ∃ r, SFunc.RunExactCut progYD sevm C d (gyHead e t k gyExit) r ∧ (∀ d', r ≠ .at k d') ∧
      gyCalleeExit b S M0 y' G r := by
  obtain ⟨hy, M, i, j, x, x0, x1, x2, amp, w8, w9, w11, w12, w13, w14, w15, w16, w17, w18, s,
    ann, xv, cc, yp, rfl, hF⟩ := hAt
  have hyN : (Nat.toB256 y).toNat = y := B256.toNat_toB256_of_lt hy
  rw [← hyN] at hb hc
  obtain ⟨hm1, ha1, hm2, ha2, hs, hd, rfl⟩ := bodyYChk_inv hb
  have hF13 := hF.write (j := 25) (lt28 (by decide)) (Nat.toB256 y)
  have hF14 := hF13.write (j := 26) (lt28 (by decide))
    ((Nat.toB256 y * Nat.toB256 y + c) / (Bytes.toB256 [0x02] * Nat.toB256 y + bw - D))
  have hF15 := hF14.write (j := 27) (lt28 (by decide)) (Nat.toB256 (n + 1))
  obtain ⟨M', hout, hex⟩ := rxc_gyExit (C := C) (G := G) (S := S) hF15 rfl rfl rfl (by omega)
  refine ⟨.done (.returned (St b (((Nat.toB256 y * Nat.toB256 y + c) /
    (Bytes.toB256 [0x02] * Nat.toB256 y + bw - D)) :: S) M' G)), ?_, fun d' h => (by cases h), M',
    by rw [toB256_toNat], by rw [toB256_toNat]; exact hout⟩
  have hg : G + ydCapC y
      ((Nat.toB256 y * Nat.toB256 y + c) / (Bytes.toB256 [0x02] * Nat.toB256 y + bw - D)).toNat =
      (G + 37 + 45 + if (Nat.toB256 y).toNat < ((Nat.toB256 y * Nat.toB256 y + c) /
        (Bytes.toB256 [0x02] * Nat.toB256 y + bw - D)).toNat then 104 else 94) + 402 := by
    rw [hyN]; unfold ydCapC; split <;> omega
  rw [hg]
  exact rxc_gyHeadPre hF rfl rfl rfl rfl rfl hm1 ha1 hm2 ha2 hs hd hroom
    (rxc_gyHeadBr_next hF14 rfl rfl hc ht htC hroom
      (fun _ => rxc_gyTail_last hF14 rfl rfl hn (by omega) hex)
      (fun _ => rxc_gyTail_last hF14 rfl rfl hn (by omega) hex))

-- SEGMENT: gyLoop_exact
/-- **The `y` loop, forward**, from its first (inline) pass: a successful fuel loop runs to the
return with the recursive charge `ydCost`. -/
theorem gyLoop_exact {D ρ c bw : B256} (hroom : S.length + 12 < 1024) :
    ∀ y v G d, ydLoop c bw D 255 y = some v →
      gyAtX b S M0 D ρ c bw 0 y (G + ydCost c bw D 255 y) d →
      ∃ r, SFunc.RunExactCut progYD sevm [] d (gyHead 136 137 138 .undefined) r ∧
        gyCalleeExit b S M0 v G r := by
  have h205 := RunExactCut_fuelLoop_exact (fs := progYD) (sevm := sevm) (C := []) progGY_201
    List.not_mem_nil (gyAtX b S M0 D ρ c bw) (gyCalleeExit b S M0)
    (fun _ _ _ _ _ hn hb hc hAt => gyHead_stepX progGY_200 (by decide) List.mem_cons_self hroom
      hn hb (of_decide_eq_false hc) hAt)
    (fun _ _ _ _ _ _ hb hc hAt => gyHead_stopX progGY_180 (by decide) hroom hb
      (of_decide_eq_true hc) hAt)
    (fun _ _ _ _ _ hn hb hc hAt => gyHead_capX progGY_200 (by decide) hroom hn hb
      (of_decide_eq_false hc) hAt)
  have h187 := RunExactCut_fuelLoop_peelAt (fs := progYD) (sevm := sevm) (C := [])
    (f := gyHead 180 200 201 .undefined) progGY_201 List.not_mem_nil (gyAtX b S M0 D ρ c bw)
    (gyCalleeExit b S M0) (n0 := 3) (by decide)
    (fun D v G d hv hAt => h205 4 D v G d (by decide) hv hAt)
    (fun _ _ _ _ hb hc hAt => gyHead_stepX progGY_200 (by decide) List.mem_cons_self hroom
      (by decide) hb (of_decide_eq_false hc) hAt)
    (fun _ _ _ _ hb hc hAt => gyHead_stopX progGY_180 (by decide) hroom hb
      (of_decide_eq_true hc) hAt)
  have h165 := RunExactCut_fuelLoop_peelAt (fs := progYD) (sevm := sevm) (C := [])
    (f := gyHead 180 181 182 .undefined) progGY_182 List.not_mem_nil (gyAtX b S M0 D ρ c bw)
    (gyCalleeExit b S M0) (n0 := 2) (by decide) h187
    (fun _ _ _ _ hb hc hAt => gyHead_stepX progGY_181 (by decide) List.mem_cons_self hroom
      (by decide) hb (of_decide_eq_false hc) hAt)
    (fun _ _ _ _ hb hc hAt => gyHead_stopX progGY_180 (by decide) hroom hb
      (of_decide_eq_true hc) hAt)
  have h143 := RunExactCut_fuelLoop_peelAt (fs := progYD) (sevm := sevm) (C := [])
    (f := gyHead 158 159 160 .undefined) progGY_160 List.not_mem_nil (gyAtX b S M0 D ρ c bw)
    (gyCalleeExit b S M0) (n0 := 1) (by decide) h165
    (fun _ _ _ _ hb hc hAt => gyHead_stepX progGY_159 (by decide) List.mem_cons_self hroom
      (by decide) hb (of_decide_eq_false hc) hAt)
    (fun _ _ _ _ hb hc hAt => gyHead_stopX progGY_158 (by decide) hroom hb
      (of_decide_eq_true hc) hAt)
  exact RunExactCut_fuelLoop_peelAt (fs := progYD) (sevm := sevm) (C := [])
    (f := gyHead 136 137 138 .undefined) progGY_138 List.not_mem_nil (gyAtX b S M0 D ρ c bw)
    (gyCalleeExit b S M0) (n0 := 0) (by decide) h143
    (fun _ _ _ _ hb hc hAt => gyHead_stepX progGY_137 (by decide) List.mem_cons_self hroom
      (by decide) hb (of_decide_eq_false hc) hAt)
    (fun _ _ _ _ hb hc hAt => gyHead_stopX progGY_136 (by decide) hroom hb
      (of_decide_eq_true hc) hAt)

/-! ## The coin loop and the set-up, forward -/

theorem iszero_eqCheck_ne {a b : B256} (h : a ≠ b) : B256.eqCheck (B256.eqCheck a b) 0 ≠ 0 := by
  unfold B256.eqCheck
  rw [if_neg h, if_pos rfl]
  decide

-- SEGMENT: rxc_gyTest
/-- **The coin-loop test at coin `i`**, forward (55 gas): `_x = x`. -/
theorem rxc_gyTest_i (hF : WordFrame M0 M 0x140 ws) (hlen : ws.length = 28) {k k1 k2 k3 : Nat}
    {g1 : SFunc} {x : B256} (hi : ws[0]? = some (Nat.toB256 k))
    (hc : ws[23]? = some (Nat.toB256 k)) (hx : ws[2]? = some x) (hk1C : k1 ∉ C)
    (hk1 : progYD[k1]? = some g1) (hroom : S.length + 8 < 1024)
    (kk : SFunc.RunExactCut progYD sevm C
      (St b (gyCStk S) (M.write (0x140 + 32 * 22) x.toBytes) G) g1 r) :
    SFunc.RunExactCut progYD sevm C (St b (gyCStk S) M (G + 55)) (gyTest k1 k2 k3) r := by
  unfold gyTest
  refine rxc_dest ?_
  refine rxc_pushMloadF hF 0 (by decide) hi (by vy_room) ?_
  refine rxc_pushMloadF hF 23 (by decide) hc (by vy_room) ?_
  refine rxc_eq rfl (by vy_room) ?_
  refine rxc_iszero rfl (by vy_room) ?_
  refine rxc_push rfl (by vy_room) ?_
  rw [eqCheck_self, show B256.eqCheck 1 0 = 0 by decide]
  refine rxc_branch_zero ?_
  refine rxc_pushMloadF hF 2 (by decide) hx (by vy_room) ?_
  refine rxc_pushMstoreF hF 22 (by decide) (by rw [hlen]; decide) (by vy_room) ?_
  refine rxc_push rfl (by vy_room) ?_
  exact rxc_jump hk1 hk1C kk

/-- **The coin-loop test at coin `j`**, forward (76 gas): skipped. -/
theorem rxc_gyTest_skip (hF : WordFrame M0 M 0x140 ws) {k k1 k2 k3 : Nat} {g3 : SFunc}
    {i : B256} (hi : ws[0]? = some i) (hne : i ≠ Nat.toB256 k)
    (hj : ws[1]? = some (Nat.toB256 k)) (hc : ws[23]? = some (Nat.toB256 k)) (hk3C : k3 ∉ C)
    (hk3 : progYD[k3]? = some g3) (hroom : S.length + 8 < 1024)
    (kk : SFunc.RunExactCut progYD sevm C (St b (gyCStk S) M G) g3 r) :
    SFunc.RunExactCut progYD sevm C (St b (gyCStk S) M (G + 76)) (gyTest k1 k2 k3) r := by
  unfold gyTest
  refine rxc_dest ?_
  refine rxc_pushMloadF hF 0 (by decide) hi (by vy_room) ?_
  refine rxc_pushMloadF hF 23 (by decide) hc (by vy_room) ?_
  refine rxc_eq rfl (by vy_room) ?_
  refine rxc_iszero rfl (by vy_room) ?_
  refine rxc_push rfl (by vy_room) ?_
  refine rxc_branch_succ (iszero_eqCheck_ne (Ne.symm hne)) (rxc_dest ?_)
  refine rxc_pushMloadF hF 1 (by decide) hj (by vy_room) ?_
  refine rxc_pushMloadF hF 23 (by decide) hc (by vy_room) ?_
  refine rxc_binary (fn := (· ^^^ ·)) (c := gVerylow) (by rintro ⟨⟩) (fun _ => rfl) rfl
    (by vy_room) ?_
  refine rxc_iszero rfl (by vy_room) ?_
  refine rxc_push rfl (by vy_room) ?_
  rw [(B256.xor_eq_zero_iff _ _).mpr rfl]
  refine rxc_branch_succ (by decide) (rxc_dest ?_)
  refine rxc_push rfl (by vy_room) ?_
  exact rxc_jump hk3 hk3C kk

/-- **The coin-loop test at another coin**, forward (127 gas): `_x = xp[k]`. -/
theorem rxc_gyTest_xp (hF : WordFrame M0 M 0x140 ws) (hlen : ws.length = 28) {k k1 k2 k3 : Nat}
    {g2 : SFunc} {i j xk : B256} (hk3 : k < 3) (hi : ws[0]? = some i) (hne : i ≠ Nat.toB256 k)
    (hj : ws[1]? = some j) (hnj : j ≠ Nat.toB256 k) (hc : ws[23]? = some (Nat.toB256 k))
    (hxk : ws[3 + k]? = some xk) (hk2C : k2 ∉ C) (hk2 : progYD[k2]? = some g2)
    (hroom : S.length + 8 < 1024)
    (kk : SFunc.RunExactCut progYD sevm C
      (St b (gyCStk S) (M.write (0x140 + 32 * 22) xk.toBytes) G) g2 r) :
    SFunc.RunExactCut progYD sevm C (St b (gyCStk S) M (G + 127)) (gyTest k1 k2 k3) r := by
  unfold gyTest
  refine rxc_dest ?_
  refine rxc_pushMloadF hF 0 (by decide) hi (by vy_room) ?_
  refine rxc_pushMloadF hF 23 (by decide) hc (by vy_room) ?_
  refine rxc_eq rfl (by vy_room) ?_
  refine rxc_iszero rfl (by vy_room) ?_
  refine rxc_push rfl (by vy_room) ?_
  refine rxc_branch_succ (iszero_eqCheck_ne (Ne.symm hne)) (rxc_dest ?_)
  refine rxc_pushMloadF hF 1 (by decide) hj (by vy_room) ?_
  refine rxc_pushMloadF hF 23 (by decide) hc (by vy_room) ?_
  refine rxc_binary (fn := (· ^^^ ·)) (c := gVerylow) (by rintro ⟨⟩) (fun _ => rfl) rfl
    (by vy_room) ?_
  refine rxc_iszero rfl (by vy_room) ?_
  refine rxc_push rfl (by vy_room) ?_
  rw [xor_toB256_ne hk3 hnj]
  refine rxc_branch_zero ?_
  refine rxc_push rfl (by vy_room) ?_
  refine rxc_pushMloadF hF 23 (by decide) hc (by vy_room) ?_
  refine rxc_push rfl (by vy_room) ?_
  refine rxc_dup (w := Nat.toB256 k) rfl (by vy_room) ?_
  refine rxc_lt rfl (by vy_room) ?_
  refine rxc_push rfl (by vy_room) ?_
  refine rxc_branch_succ (lt3_check hk3) (rxc_dest ?_)
  refine rxc_push rfl (by vy_room) ?_
  refine rxc_binary (fn := (· * ·)) (c := gLow) (by rintro ⟨⟩) (fun _ => rfl) rfl (by vy_room) ?_
  refine rxc_add (by vy_room) ?_
  refine rxc_mloadF hF (3 + k) (gyXpAddr hk3) hxk (by vy_room) ?_
  refine rxc_pushMstoreF hF 22 (by decide) (by rw [hlen]; decide) (by vy_room) ?_
  refine rxc_push rfl (by vy_room) ?_
  exact rxc_jump hk2 hk2C kk

-- SEGMENT: rxc_gyCoinTail
/-- **The coin-loop counter tail, on to entry `k`**, forward (44 gas). -/
theorem rxc_gyCoinTail_next (hF : WordFrame M0 M 0x140 ws) (hlen : ws.length = 28) {j k : Nat}
    {g : SFunc} (hj : ws[23]? = some (Nat.toB256 j)) (hj3 : j + 1 < 3) (hkC : k ∉ C)
    (hk : progYD[k]? = some g) (hroom : S.length + 8 < 1024)
    (kk : SFunc.RunExactCut progYD sevm C
      (St b (gyCStk S) (M.write (0x140 + 32 * 23) (Nat.toB256 (j + 1)).toBytes) G) g r) :
    SFunc.RunExactCut progYD sevm C (St b (gyCStk S) M (G + 44))
      (gyCoinTail (.branchTo .undefined k)) r := by
  unfold gyCoinTail
  refine rxc_dest ?_
  refine rxc_dup (w := Nat.toB256 0x420) rfl (by vy_room) ?_
  refine rxc_mloadF hF 23 (by decide) hj (by vy_room) ?_
  refine rxc_push rfl (by vy_room) ?_
  refine rxc_add' (one_add_toB256 (by omega)) (by vy_room) ?_
  refine rxc_dup (w := Nat.toB256 (j + 1)) rfl (by vy_room) ?_
  refine rxc_dup (w := Nat.toB256 0x420) rfl (by vy_room) ?_
  refine rxc_mstoreF hF 23 (by decide) (by rw [hlen]; decide) ?_
  refine rxc_dup (w := Nat.toB256 3) rfl (by vy_room) ?_
  refine rxc_eq rfl (by vy_room) ?_
  refine rxc_iszero rfl (by vy_room) ?_
  refine rxc_push rfl (by vy_room) ?_
  exact rxc_branchTo_taken (iszero_eq3_neX hj3) hkC hk kk

/-- **The last coin-loop counter tail, on to the set-up `g`**, forward (44 gas). -/
theorem rxc_gyCoinTail_last (hF : WordFrame M0 M 0x140 ws) (hlen : ws.length = 28) {j : Nat}
    {g : SFunc} (hj : ws[23]? = some (Nat.toB256 j)) (hj3 : j + 1 = 3)
    (hroom : S.length + 8 < 1024)
    (kk : SFunc.RunExactCut progYD sevm C
      (St b (gyCStk S) (M.write (0x140 + 32 * 23) (Nat.toB256 (j + 1)).toBytes) G) g r) :
    SFunc.RunExactCut progYD sevm C (St b (gyCStk S) M (G + 44))
      (gyCoinTail (.branch g .undefined)) r := by
  unfold gyCoinTail
  refine rxc_dest ?_
  refine rxc_dup (w := Nat.toB256 0x420) rfl (by vy_room) ?_
  refine rxc_mloadF hF 23 (by decide) hj (by vy_room) ?_
  refine rxc_push rfl (by vy_room) ?_
  refine rxc_add' (one_add_toB256 (by omega)) (by vy_room) ?_
  refine rxc_dup (w := Nat.toB256 (j + 1)) rfl (by vy_room) ?_
  refine rxc_dup (w := Nat.toB256 0x420) rfl (by vy_room) ?_
  refine rxc_mstoreF hF 23 (by decide) (by rw [hlen]; decide) ?_
  refine rxc_dup (w := Nat.toB256 3) rfl (by vy_room) ?_
  refine rxc_eq rfl (by vy_room) ?_
  refine rxc_iszero rfl (by vy_room) ?_
  refine rxc_push rfl (by vy_room) ?_
  have hw : B256.eqCheck (B256.eqCheck (Nat.toB256 3) (Nat.toB256 (j + 1))) 0 = 0 := by
    rw [hj3]; decide
  rw [hw]
  exact rxc_branch_zero kk

-- SEGMENT: rxc_gyAcc
/-- **The coin-loop accumulation**, forward (278 gas). -/
theorem rxc_gyAcc (hF : WordFrame M0 M 0x140 ws) (hlen : ws.length = 28) {c s x D : B256}
    (hc : ws[19]? = some c) (hs : ws[20]? = some s) (hx : ws[22]? = some x)
    (hD : ws[10]? = some D) (ha : s.toNat + x.toNat < 2 ^ 256) (hm1 : B256.Nofm c D)
    (hm2 : B256.Nofm x (Bytes.toB256 [0x03])) (hd : x * Bytes.toB256 [0x03] ≠ 0)
    (hroom : S.length + 12 < 1024) {tail : SFunc}
    (kk : SFunc.RunExactCut progYD sevm C (St b (gyCStk S)
      ((M.write (0x140 + 32 * 20) (s + x).toBytes).write (0x140 + 32 * 19)
        ((c * D) / (x * Bytes.toB256 [0x03])).toBytes) G) tail r) :
    SFunc.RunExactCut progYD sevm C (St b (gyCStk S) M (G + 278)) (gyAcc tail) r := by
  have hF8 := hF.write (j := 20) (by rw [hlen]; decide) (s + x)
  have hc1 : (ws.set 20 (s + x))[19]? = some c := by rw [List.getElem?_set_ne (by decide)]; exact hc
  have hD1 : (ws.set 20 (s + x))[10]? = some D := by rw [List.getElem?_set_ne (by decide)]; exact hD
  have hx1 : (ws.set 20 (s + x))[22]? = some x := by
    rw [List.getElem?_set_ne (by decide)]; exact hx
  unfold gyAcc
  refine rxc_dest ?_
  refine rxc_push rfl (by vy_room) ?_
  refine rxc_dup (w := Bytes.toB256 [0x03, 0xc0]) rfl (by vy_room) ?_
  refine rxc_mloadF hF 20 (by decide) hs (by vy_room) ?_
  refine rxc_pushMloadF hF 22 (by decide) hx (by vy_room) ?_
  refine rxc_vyAddT ha (by vy_room) ?_
  refine rxc_dup (w := Bytes.toB256 [0x03, 0xc0]) rfl (by vy_room) ?_
  refine rxc_mstoreF hF 20 (by decide) (by rw [hlen]; decide) ?_
  refine rxc_pop ?_
  refine rxc_pushMloadF hF8 19 (by decide) hc1 (by vy_room) ?_
  refine rxc_pushMloadF hF8 10 (by decide) hD1 (by vy_room) ?_
  refine rxc_vyMulT hm1 (by vy_room) ?_
  refine rxc_pushMloadF hF8 22 (by decide) hx1 (by vy_room) ?_
  refine rxc_push rfl (by vy_room) ?_
  refine rxc_vyMulT hm2 (by vy_room) ?_
  refine rxc_vyDivT hd (by vy_room) ?_
  exact rxc_pushMstoreF hF8 19 (by decide) (by rw [List.length_set, hlen]; decide) (by vy_room) kk

-- SEGMENT: rxc_gyPost
/-- **After the coin loop**, forward through the whole `y` loop: `363` gas plus the loop's
recursive charge. -/
theorem rxc_gyPost {i j x x0 x1 x2 ρ amp w8 w9 D w11 w12 w13 w14 w15 w16 w17 w18 c s ann xv cc w24 w25 w26
    w27 : B256} {y : Nat}
    (hF : WordFrame M0 M 0x140 (gyFrame i j x x0 x1 x2 ρ amp w8 w9 D w11 w12 w13 w14 w15 w16 w17 w18
      c s ann xv cc w24 w25 w26 w27))
    (hres : ydPostRes c.toNat s.toNat D.toNat ann.toNat = some y)
    (hroom : S.length + 12 < 1024) :
    ∃ r, SFunc.RunExactCut progYD sevm [] (St b (gyCStk S) M
      (G + 363 + ydCost ((c * D) / (ann * Bytes.toB256 [0x03])) (s + D / ann) D 255 D.toNat))
      gyPost0 r ∧ gyCalleeExit b S M0 y G r := by
  obtain ⟨hm1, hm2, hd1, hd2, ha, hloop⟩ := ydPostRes_inv hres
  set c' := (c * D) / (ann * Bytes.toB256 [0x03]) with hc'
  set b' := s + D / ann with hb'
  have hF1 := hF.write (j := 19) (lt28 (by decide)) c'
  have hF2 := hF1.write (j := 24) (lt28 (by decide)) b'
  have hF3 := hF2.write (j := 25) (lt28 (by decide)) (Nat.toB256 0)
  have hF4 := hF3.write (j := 26) (lt28 (by decide)) D
  have hF5 := hF4.write (j := 27) (lt28 (by decide)) (Nat.toB256 0)
  have hAt : gyAtX b S M0 D ρ c' b' 0 D.toNat (G + ydCost c' b' D 255 D.toNat)
      (St b (gyStk S) ((((((M.write (0x140 + 32 * 19) c'.toBytes).write (0x140 + 32 * 24)
        b'.toBytes).write (0x140 + 32 * 25) (Nat.toB256 0).toBytes).write (0x140 + 32 * 26)
        D.toBytes).write (0x140 + 32 * 27) (Nat.toB256 0).toBytes))
        (G + ydCost c' b' D 255 D.toNat)) := by
    refine ⟨B256.toNat_lt D, _, i, j, x, x0, x1, x2, amp, w8, w9, w11, w12, w13, w14, w15, w16, w17,
      w18, s, ann, xv, cc, Nat.toB256 0, rfl, ?_⟩
    rw [toB256_toNat]; exact hF5
  have hv : ydLoop c' b' D 255 D.toNat = some y := by
    rw [ydLoop, ← loopYChk_eq_fuelLoop]; exact hloop
  obtain ⟨r, hrun, hex⟩ := gyLoop_exact hroom D.toNat y G _ hv hAt
  refine ⟨r, ?_, hex⟩
  rw [show G + 363 + ydCost c' b' D 255 D.toNat = (G + ydCost c' b' D 255 D.toNat) + 363 by
    omega]
  unfold gyPost0 gyPost
  refine rxc_dest (rxc_pop (rxc_pop ?_))
  refine rxc_pushMloadF hF 19 (by decide) rfl (by vy_room) ?_
  refine rxc_pushMloadF hF 10 (by decide) rfl (by vy_room) ?_
  refine rxc_vyMulT hm1 (by vy_room) ?_
  refine rxc_pushMloadF hF 21 (by decide) rfl (by vy_room) ?_
  refine rxc_push rfl (by vy_room) ?_
  refine rxc_vyMulT hm2 (by vy_room) ?_
  refine rxc_vyDivT hd1 (by vy_room) ?_
  refine rxc_pushMstoreF hF 19 (by decide) (lt28 (by decide)) (by vy_room) ?_
  refine rxc_pushMloadF hF1 20 (by decide) rfl (by vy_room) ?_
  refine rxc_pushMloadF hF1 10 (by decide) rfl (by vy_room) ?_
  refine rxc_pushMloadF hF1 21 (by decide) rfl (by vy_room) ?_
  refine rxc_vyDivT hd2 (by vy_room) ?_
  refine rxc_vyAddT ha (by vy_room) ?_
  refine rxc_pushMstoreF hF1 24 (by decide) (lt28 (by decide)) (by vy_room) ?_
  refine rxc_push toB256_zero (by vy_room) ?_
  refine rxc_pushMstoreF hF2 25 (by decide) (lt28 (by decide)) (by vy_room) ?_
  refine rxc_pushMloadF hF3 10 (by decide) rfl (by vy_room) ?_
  refine rxc_pushMstoreF hF3 26 (by decide) (lt28 (by decide)) (by vy_room) ?_
  refine rxc_push toB256_0x4a0 (by vy_room) ?_
  refine rxc_push toB256_zero (by vy_room) ?_
  refine rxc_push rfl (by vy_room) ?_
  refine rxc_dup (w := Nat.toB256 0) rfl (by vy_room) ?_
  refine rxc_dup (w := Nat.toB256 0x4a0) rfl (by vy_room) ?_
  refine rxc_mstoreF hF4 27 (by decide) (lt28 (by decide)) ?_
  refine rxc_add' (show Bytes.toB256 [0xff] + Nat.toB256 0 = Nat.toB256 255 by decide)
    (by vy_room) ?_
  exact hrun

/-! ## Costs on naturals -/

/-- Gas of one coin-loop iteration of `get_y` at coin `k`: coin `i`, coin `j`, or another. -/
def gyCoinCost (i j k : Nat) : Nat := if i = k then 377 else if j = k then 120 else 450

/-- Gas from the coin-loop iteration `2` on. -/
def gyCostFrom2 (i j x x2 D ann : Nat) (cs : Nat × Nat) : Nat :=
  gyCoinCost i j 2 + match gyCoinStep i j 2 x x2 D cs with
    | some cs' => ydPostCost cs'.1 cs'.2 D ann
    | none => 0

/-- Gas from the coin-loop iteration `1` on. -/
def gyCostFrom1 (i j x x1 x2 D ann : Nat) (cs : Nat × Nat) : Nat :=
  gyCoinCost i j 1 + match gyCoinStep i j 1 x x1 D cs with
    | some cs' => gyCostFrom2 i j x x2 D ann cs'
    | none => 0

/-- Gas from the coin-loop iteration `0` on. -/
def gyCostFrom0 (i j x x0 x1 x2 D ann : Nat) (cs : Nat × Nat) : Nat :=
  gyCoinCost i j 0 + match gyCoinStep i j 0 x x0 D cs with
    | some cs' => gyCostFrom1 i j x x1 x2 D ann cs'
    | none => 0

-- SEGMENT: gyStage2X
/-- **Coin-loop iteration `2` and the rest**, forward. -/
theorem gyStage2X {i j x x0 x1 x2 ρ amp w8 w9 D w11 w12 w13 w14 w15 w16 w17 w18 c s ann xv w24 w25 w26 w27 : B256} {y : Nat}
    (hroom : S.length + 12 < 1024)
    (hF : WordFrame M0 M 0x140 (gyFrame i j x x0 x1 x2 ρ amp w8 w9 D w11 w12 w13 w14 w15 w16 w17 w18
      c s ann xv (Nat.toB256 2) w24 w25 w26 w27))
    (hres : ((gyCoinStep i.toNat j.toNat 2 x.toNat x2.toNat D.toNat (c.toNat, s.toNat)).bind
      fun cs => ydPostRes cs.1 cs.2 D.toNat ann.toNat) = some y) :
    ∃ r, SFunc.RunExactCut progYD sevm [] (St b (gyCStk S) M
      (G + gyCostFrom2 i.toNat j.toNat x.toNat x2.toNat D.toNat ann.toNat (c.toNat, s.toNat))) (gyTest 115 116 117) r ∧
      gyCalleeExit b S M0 y G r := by
  unfold gyCostFrom2 gyCoinCost
  by_cases hi : i.toNat = 2
  · have hiw : i = Nat.toB256 2 := by rw [← hi, toB256_toNat]
    rw [hi, gyCoinStep_i] at hres ⊢
    rw [if_pos rfl]
    obtain ⟨⟨c', s'⟩, hacc, hres⟩ := Option.bind_eq_some_iff.mp hres
    rw [hacc]
    obtain ⟨ha1, hma, hmb, hda, -, -⟩ := ydAccN_inv hacc
    obtain ⟨rfl, rfl⟩ := ydAccN_words hacc
    simp only at hres ⊢
    have hF22 := hF.write (j := 22) (lt28 (by decide)) x
    have hF20 := hF22.write (j := 20) (lt28 (by decide)) (s + x)
    have hF19 := hF20.write (j := 19) (lt28 (by decide)) ((c * D) / (x * Bytes.toB256 [0x03]))
    have hF23 := hF19.write (j := 23) (lt28 (by decide)) (Nat.toB256 (2 + 1))
    obtain ⟨hm1, hm2, hd1, hd2, ha, -⟩ := ydPostRes_inv hres
    obtain ⟨r, hrun, hex⟩ := rxc_gyPost (G := G) hF23 hres hroom
    refine ⟨r, ?_, hex⟩
    rw [ydPostCost_words hm1 hm2 hd1 hd2 ha]
    rw [show ∀ P : Nat, G + (377 + (363 + P)) = G + 363 + P + 44 + 278 + 55 from fun P => by omega]
    refine rxc_gyTest_i hF rfl (by rw [hiw]; rfl) rfl rfl List.not_mem_nil progGY_115
      (by omega) ?_
    refine rxc_gyAcc hF22 rfl rfl rfl rfl rfl ha1 hma hmb hda hroom ?_
    exact rxc_gyCoinTail_last hF19 rfl rfl (by decide) (by omega) hrun
  · have hne : i ≠ Nat.toB256 2 := fun h => hi (by rw [h]; decide)
    by_cases hj : j.toNat = 2
    · have hjw : j = Nat.toB256 2 := by rw [← hj, toB256_toNat]
      rw [hj, gyCoinStep_j hi] at hres ⊢
      rw [if_neg hi, if_pos rfl]
      dsimp only
      rw [Option.bind_some] at hres
      have hF23 := hF.write (j := 23) (lt28 (by decide)) (Nat.toB256 (2 + 1))
      obtain ⟨hm1, hm2, hd1, hd2, ha, -⟩ := ydPostRes_inv hres
      obtain ⟨r, hrun, hex⟩ := rxc_gyPost (G := G) hF23 hres hroom
      refine ⟨r, ?_, hex⟩
      rw [ydPostCost_words hm1 hm2 hd1 hd2 ha]
      rw [show ∀ P : Nat, G + (120 + (363 + P)) = G + 363 + P + 44 + 76 from fun P => by omega]
      refine rxc_gyTest_skip hF rfl hne (by rw [hjw]; rfl) rfl List.not_mem_nil progGY_117
        (by omega) ?_
      exact rxc_gyCoinTail_last hF rfl rfl (by decide) (by omega) hrun
    · have hnj : j ≠ Nat.toB256 2 := fun h => hj (by rw [h]; decide)
      rw [gyCoinStep_other hi hj] at hres ⊢
      rw [if_neg hi, if_neg hj]
      obtain ⟨⟨c', s'⟩, hacc, hres⟩ := Option.bind_eq_some_iff.mp hres
      rw [hacc]
      obtain ⟨ha1, hma, hmb, hda, -, -⟩ := ydAccN_inv hacc
      obtain ⟨rfl, rfl⟩ := ydAccN_words hacc
      simp only at hres ⊢
      have hF22 := hF.write (j := 22) (lt28 (by decide)) x2
      have hF20 := hF22.write (j := 20) (lt28 (by decide)) (s + x2)
      have hF19 := hF20.write (j := 19) (lt28 (by decide)) ((c * D) / (x2 * Bytes.toB256 [0x03]))
      have hF23 := hF19.write (j := 23) (lt28 (by decide)) (Nat.toB256 (2 + 1))
      obtain ⟨hm1, hm2, hd1, hd2, ha, -⟩ := ydPostRes_inv hres
      obtain ⟨r, hrun, hex⟩ := rxc_gyPost (G := G) hF23 hres hroom
      refine ⟨r, ?_, hex⟩
      rw [ydPostCost_words hm1 hm2 hd1 hd2 ha]
      rw [show ∀ P : Nat, G + (450 + (363 + P)) = G + 363 + P + 44 + 278 + 1 + 127 from fun P => by omega]
      refine rxc_gyTest_xp hF rfl (by decide) rfl hne rfl hnj rfl rfl List.not_mem_nil
        progGY_116 (by omega) ?_
      refine rxc_dest ?_
      refine rxc_gyAcc hF22 rfl rfl rfl rfl rfl ha1 hma hmb hda hroom ?_
      exact rxc_gyCoinTail_last hF19 rfl rfl (by decide) (by omega) hrun

-- SEGMENT: gyStage1X
/-- **Coin-loop iteration `1` and the rest**, forward. -/
theorem gyStage1X {i j x x0 x1 x2 ρ amp w8 w9 D w11 w12 w13 w14 w15 w16 w17 w18 c s ann xv w24 w25 w26 w27 : B256} {y : Nat}
    (hroom : S.length + 12 < 1024)
    (hF : WordFrame M0 M 0x140 (gyFrame i j x x0 x1 x2 ρ amp w8 w9 D w11 w12 w13 w14 w15 w16 w17 w18
      c s ann xv (Nat.toB256 1) w24 w25 w26 w27))
    (hres : ((gyCoinStep i.toNat j.toNat 1 x.toNat x1.toNat D.toNat (c.toNat, s.toNat)).bind
      fun cs =>
      (gyCoinStep i.toNat j.toNat 2 x.toNat x2.toNat D.toNat cs).bind fun cs =>
        ydPostRes cs.1 cs.2 D.toNat ann.toNat) = some y) :
    ∃ r, SFunc.RunExactCut progYD sevm [] (St b (gyCStk S) M
      (G + gyCostFrom1 i.toNat j.toNat x.toNat x1.toNat x2.toNat D.toNat ann.toNat
        (c.toNat, s.toNat))) (gyTest 70 71 72) r ∧
      gyCalleeExit b S M0 y G r := by
  unfold gyCostFrom1 gyCoinCost
  by_cases hi : i.toNat = 1
  · have hiw : i = Nat.toB256 1 := by rw [← hi, toB256_toNat]
    rw [hi, gyCoinStep_i] at hres ⊢
    rw [if_pos rfl]
    obtain ⟨⟨c', s'⟩, hacc, hres⟩ := Option.bind_eq_some_iff.mp hres
    rw [hacc]
    obtain ⟨ha1, hma, hmb, hda, -, -⟩ := ydAccN_inv hacc
    obtain ⟨rfl, rfl⟩ := ydAccN_words hacc
    simp only at hres ⊢
    have hF22 := hF.write (j := 22) (lt28 (by decide)) x
    have hF20 := hF22.write (j := 20) (lt28 (by decide)) (s + x)
    have hF19 := hF20.write (j := 19) (lt28 (by decide)) ((c * D) / (x * Bytes.toB256 [0x03]))
    have hF23 := hF19.write (j := 23) (lt28 (by decide)) (Nat.toB256 (1 + 1))
    obtain ⟨r, hrun, hex⟩ := gyStage2X (G := G) hroom hF23 (by rw [hi]; exact hres)
    refine ⟨r, ?_, hex⟩
    rw [hi] at hrun
    rw [show ∀ P : Nat, G + (377 + P) = G + P + 44 + 278 + 55 from fun P => by omega]
    refine rxc_gyTest_i hF rfl (by rw [hiw]; rfl) rfl rfl List.not_mem_nil progGY_70
      (by omega) ?_
    refine rxc_gyAcc hF22 rfl rfl rfl rfl rfl ha1 hma hmb hda hroom ?_
    exact rxc_gyCoinTail_next hF19 rfl rfl (by decide) List.not_mem_nil progGY_95 (by omega) hrun
  · have hne : i ≠ Nat.toB256 1 := fun h => hi (by rw [h]; decide)
    by_cases hj : j.toNat = 1
    · have hjw : j = Nat.toB256 1 := by rw [← hj, toB256_toNat]
      rw [hj, gyCoinStep_j hi] at hres ⊢
      rw [if_neg hi, if_pos rfl]
      dsimp only
      rw [Option.bind_some] at hres
      have hF23 := hF.write (j := 23) (lt28 (by decide)) (Nat.toB256 (1 + 1))
      obtain ⟨r, hrun, hex⟩ := gyStage2X (G := G) hroom hF23 (by rw [hj]; exact hres)
      refine ⟨r, ?_, hex⟩
      rw [hj] at hrun
      rw [show ∀ P : Nat, G + (120 + P) = G + P + 44 + 76 from fun P => by omega]
      refine rxc_gyTest_skip hF rfl hne (by rw [hjw]; rfl) rfl List.not_mem_nil progGY_72
        (by omega) ?_
      exact rxc_gyCoinTail_next hF rfl rfl (by decide) List.not_mem_nil progGY_95 (by omega) hrun
    · have hnj : j ≠ Nat.toB256 1 := fun h => hj (by rw [h]; decide)
      rw [gyCoinStep_other hi hj] at hres ⊢
      rw [if_neg hi, if_neg hj]
      obtain ⟨⟨c', s'⟩, hacc, hres⟩ := Option.bind_eq_some_iff.mp hres
      rw [hacc]
      obtain ⟨ha1, hma, hmb, hda, -, -⟩ := ydAccN_inv hacc
      obtain ⟨rfl, rfl⟩ := ydAccN_words hacc
      simp only at hres ⊢
      have hF22 := hF.write (j := 22) (lt28 (by decide)) x1
      have hF20 := hF22.write (j := 20) (lt28 (by decide)) (s + x1)
      have hF19 := hF20.write (j := 19) (lt28 (by decide)) ((c * D) / (x1 * Bytes.toB256 [0x03]))
      have hF23 := hF19.write (j := 23) (lt28 (by decide)) (Nat.toB256 (1 + 1))
      obtain ⟨r, hrun, hex⟩ := gyStage2X (G := G) hroom hF23 hres
      refine ⟨r, ?_, hex⟩
      rw [show ∀ P : Nat, G + (450 + P) = G + P + 44 + 278 + 1 + 127 from fun P => by omega]
      refine rxc_gyTest_xp hF rfl (by decide) rfl hne rfl hnj rfl rfl List.not_mem_nil
        progGY_71 (by omega) ?_
      refine rxc_dest ?_
      refine rxc_gyAcc hF22 rfl rfl rfl rfl rfl ha1 hma hmb hda hroom ?_
      exact rxc_gyCoinTail_next hF19 rfl rfl (by decide) List.not_mem_nil progGY_95 (by omega) hrun

-- SEGMENT: gyStage0X
/-- **Coin-loop iteration `0` and the rest**, forward. -/
theorem gyStage0X {i j x x0 x1 x2 ρ amp w8 w9 D w11 w12 w13 w14 w15 w16 w17 w18 c s ann xv w24 w25 w26 w27 : B256} {y : Nat}
    (hroom : S.length + 12 < 1024)
    (hF : WordFrame M0 M 0x140 (gyFrame i j x x0 x1 x2 ρ amp w8 w9 D w11 w12 w13 w14 w15 w16 w17 w18
      c s ann xv (Nat.toB256 0) w24 w25 w26 w27))
    (hres : ((gyCoinStep i.toNat j.toNat 0 x.toNat x0.toNat D.toNat (c.toNat, s.toNat)).bind
      fun cs =>
      (gyCoinStep i.toNat j.toNat 1 x.toNat x1.toNat D.toNat cs).bind fun cs =>
        (gyCoinStep i.toNat j.toNat 2 x.toNat x2.toNat D.toNat cs).bind fun cs =>
          ydPostRes cs.1 cs.2 D.toNat ann.toNat) = some y) :
    ∃ r, SFunc.RunExactCut progYD sevm [] (St b (gyCStk S) M
      (G + gyCostFrom0 i.toNat j.toNat x.toNat x0.toNat x1.toNat x2.toNat D.toNat ann.toNat
        (c.toNat, s.toNat))) (gyTest 559 560 9) r ∧
      gyCalleeExit b S M0 y G r := by
  unfold gyCostFrom0 gyCoinCost
  by_cases hi : i.toNat = 0
  · have hiw : i = Nat.toB256 0 := by rw [← hi, toB256_toNat]
    rw [hi, gyCoinStep_i] at hres ⊢
    rw [if_pos rfl]
    obtain ⟨⟨c', s'⟩, hacc, hres⟩ := Option.bind_eq_some_iff.mp hres
    rw [hacc]
    obtain ⟨ha1, hma, hmb, hda, -, -⟩ := ydAccN_inv hacc
    obtain ⟨rfl, rfl⟩ := ydAccN_words hacc
    simp only at hres ⊢
    have hF22 := hF.write (j := 22) (lt28 (by decide)) x
    have hF20 := hF22.write (j := 20) (lt28 (by decide)) (s + x)
    have hF19 := hF20.write (j := 19) (lt28 (by decide)) ((c * D) / (x * Bytes.toB256 [0x03]))
    have hF23 := hF19.write (j := 23) (lt28 (by decide)) (Nat.toB256 (0 + 1))
    obtain ⟨r, hrun, hex⟩ := gyStage1X (G := G) hroom hF23 (by rw [hi]; exact hres)
    refine ⟨r, ?_, hex⟩
    rw [hi] at hrun
    rw [show ∀ P : Nat, G + (377 + P) = G + P + 44 + 278 + 55 from fun P => by omega]
    refine rxc_gyTest_i hF rfl (by rw [hiw]; rfl) rfl rfl List.not_mem_nil progGY_559
      (by omega) ?_
    refine rxc_gyAcc hF22 rfl rfl rfl rfl rfl ha1 hma hmb hda hroom ?_
    exact rxc_gyCoinTail_next hF19 rfl rfl (by decide) List.not_mem_nil progGY_44 (by omega) hrun
  · have hne : i ≠ Nat.toB256 0 := fun h => hi (by rw [h]; decide)
    by_cases hj : j.toNat = 0
    · have hjw : j = Nat.toB256 0 := by rw [← hj, toB256_toNat]
      rw [hj, gyCoinStep_j hi] at hres ⊢
      rw [if_neg hi, if_pos rfl]
      dsimp only
      rw [Option.bind_some] at hres
      have hF23 := hF.write (j := 23) (lt28 (by decide)) (Nat.toB256 (0 + 1))
      obtain ⟨r, hrun, hex⟩ := gyStage1X (G := G) hroom hF23 (by rw [hj]; exact hres)
      refine ⟨r, ?_, hex⟩
      rw [hj] at hrun
      rw [show ∀ P : Nat, G + (120 + P) = G + P + 44 + 76 from fun P => by omega]
      refine rxc_gyTest_skip hF rfl hne (by rw [hjw]; rfl) rfl List.not_mem_nil progGY_9
        (by omega) ?_
      exact rxc_gyCoinTail_next hF rfl rfl (by decide) List.not_mem_nil progGY_44 (by omega) hrun
    · have hnj : j ≠ Nat.toB256 0 := fun h => hj (by rw [h]; decide)
      rw [gyCoinStep_other hi hj] at hres ⊢
      rw [if_neg hi, if_neg hj]
      obtain ⟨⟨c', s'⟩, hacc, hres⟩ := Option.bind_eq_some_iff.mp hres
      rw [hacc]
      obtain ⟨ha1, hma, hmb, hda, -, -⟩ := ydAccN_inv hacc
      obtain ⟨rfl, rfl⟩ := ydAccN_words hacc
      simp only at hres ⊢
      have hF22 := hF.write (j := 22) (lt28 (by decide)) x0
      have hF20 := hF22.write (j := 20) (lt28 (by decide)) (s + x0)
      have hF19 := hF20.write (j := 19) (lt28 (by decide)) ((c * D) / (x0 * Bytes.toB256 [0x03]))
      have hF23 := hF19.write (j := 23) (lt28 (by decide)) (Nat.toB256 (0 + 1))
      obtain ⟨r, hrun, hex⟩ := gyStage1X (G := G) hroom hF23 hres
      refine ⟨r, ?_, hex⟩
      rw [show ∀ P : Nat, G + (450 + P) = G + P + 44 + 278 + 1 + 127 from fun P => by omega]
      refine rxc_gyTest_xp hF rfl (by decide) rfl hne rfl hnj rfl rfl List.not_mem_nil
        progGY_560 (by omega) ?_
      refine rxc_dest ?_
      refine rxc_gyAcc hF22 rfl rfl rfl rfl rfl ha1 hma hmb hda hroom ?_
      exact rxc_gyCoinTail_next hF19 rfl rfl (by decide) List.not_mem_nil progGY_44 (by omega) hrun

end Fwd

/-! ## The model, read back -/

theorem getYChk_gyRes {amp i j x x0 x1 x2 v : Nat} (hi : i < 3) (hj : j < 3)
    (h : getYChk amp ⟨i, hi⟩ ⟨j, hj⟩ x (V3.mk x0 x1 x2).get = some v) :
    i ≠ j ∧ ∃ D ann, getDChk (V3.mk x0 x1 x2).get amp 1 = some D ∧ chkMul amp 3 = some ann ∧
      gyRes i j x x0 x1 x2 D ann = some v := by
  unfold getYChk at h
  by_cases hij : (⟨i, hi⟩ : Fin 3) = ⟨j, hj⟩
  · rw [if_pos hij] at h; cases h
  rw [if_neg hij] at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨D, hD, ann, hann, h⟩ := h
  refine ⟨fun he => hij (by subst he; rfl), D, ann, hD, hann, ?_⟩
  have hc := ydRes_of_core h
  unfold gyRes
  obtain rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  all_goals obtain rfl | rfl | rfl : j = 0 ∨ j = 1 ∨ j = 2 := by omega
  all_goals first
    | exact absurd rfl hij
    | (simp only [gyCoinStep, Nat.reduceEqDiff, ↓reduceIte, Option.bind_some]
       exact hc)

/-! ## The frame chains around `get_D`, forward -/

section FwdChains

variable {sevm : Sevm} {b : Devm} {S : List B256} {M : Mem} {G : Nat} {r : Seg}

theorem rxc_save_1971 (hsz : M.size % 32 = 0) (hcs : 0x2c0 ≤ M.size)
    (hctr : memWord M 0x2a0 = Nat.toB256 0x140) (hroom : S.length + 15 < 1024)
    (kk : SFunc.RunExactCut prog sevm [] (St b ((frameWords M 0x140 11).reverse ++ S)
      (saveMem M 0x2a0 0x140 11) G) t_1993_c402 r) :
    SFunc.RunExactCut prog sevm [] (St b S M (G + 726)) t_1971_c252 r := by
  rw [t_1971_c252_eq]
  have h := rxc_frameSave_chain (lo := 0x140) saveChain_1971 (fun _ _ h => by cases h) hsz
    (by rw [saveTpl_1971_c]; omega) (by rw [saveTpl_1971_c]; exact hctr) (by decide)
    (by decide) (by have : saveKs_1971.length = 10 := rfl; omega) kk
  rw [show saveKs_1971.length = 10 from rfl] at h
  exact h

theorem rxc_restore_19e0 {ts : List B256} (hts : ts.length = 11) (hsz : M.size % 32 = 0)
    (hcs : 0x2c0 ≤ M.size) (hctr : memWord M 0x2a0 = Nat.toB256 0x280)
    (hroom : S.length + 15 < 1024)
    (kk : SFunc.RunExactCut prog sevm [] (St b S (restoreMem 0x2a0 M 0x280 ts) G) t_1a03_c547 r) :
    SFunc.RunExactCut prog sevm [] (St b (ts ++ S) M (G + 759)) t_19e0_c402 r := by
  rw [t_19e0_c402_eq]
  have h := rxc_frameRestore_chain (lo := 0x140) restoreChain_19e0 (fun _ _ h => by cases h)
    (by rw [hts]; rfl) hsz (by rw [restoreTpl_19e0_c]; omega) (by decide) (by decide)
    (by rw [restoreTpl_19e0_c]; decide) (by rw [restoreTpl_19e0_c]; exact hctr)
    (by have : restoreKs_19e0.length = 10 := rfl; omega) kk
  rw [show restoreKs_19e0.length = 10 from rfl] at h
  exact h

end FwdChains

/-- Stack-room side goals over frame words. -/
macro "gylen" : tactic => `(tactic| (first | omega | (simp only [List.length_cons, List.length_append, List.length_reverse, length_frameWords]; omega)))

/-! ## The contract, forward -/

/-- **`get_y`'s gas** at `_A`'s value `amp`: the glue (`2100`), `_A`'s reads (`aGas`),
`get_D`'s `costGetD` and the coin and `y` loops, on the model's naturals (`0` past a model
revert). -/
def costGetY (sevm : Sevm) (b : Devm) (amp i j x x0 x1 x2 : Nat) : Nat :=
  2100 + aGas sevm b + match getDChk (V3.mk x0 x1 x2).get amp 1, chkMul amp 3 with
    | some D, some ann => costGetD x0 x1 x2 amp + gyCostFrom0 i j x x0 x1 x2 D ann (D, 0)
    | _, _ => 0

-- SEGMENT: getY_exact
/-- **`get_y`'s forward twin.**  When `_A` reads `amp` and the checked model returns `v`, the
entry tree runs from the call's state with `costGetY` gas over `G` to its return of `v` over the
caller's stack with `G` left and the world moved by `_A`'s reads (`aBase`), over a memory
already covering `[0, 0x4c0)`: kept off `get_y`'s windows, well formed, of the same size. -/
theorem getY_exact {sevm : Sevm} {b : Devm} {ρ i j x x0 x1 x2 : B256} {S : List B256} {M : Mem}
    {G n v amp : Nat} {s : State} (hfork : CoveredFork sevm.benvStat.fork)
    (ha : Abstracts (b.getStor sevm.currentTarget) s)
    (hA : aChk s sevm.benvStat.time.toNat = some amp) (hi : i.toNat < 3) (hj : j.toNat < 3)
    (hres : getYChk amp ⟨i.toNat, hi⟩ ⟨j.toNat, hj⟩ x.toNat
      (V3.mk x0.toNat x1.toNat x2.toNat).get = some v)
    (hwf : Mem.Wf M) (hS : M.size = n) (hn : n % 32 = 0) (htop : 0x4c0 ≤ n)
    (hroom : S.length + 64 < 1024) :
    ∃ M', SFunc.RunExact prog sevm (St b (ρ :: i :: j :: x :: x0 :: x1 :: x2 :: S) M
        (G + costGetY sevm b amp i.toNat j.toNat x.toNat x0.toNat x1.toNat x2.toNat)) t_18a4_c252
        (.returned (St (aBase sevm b) (Nat.toB256 v :: S) M' G)) ∧
      (Mem.KeepsOff M M' gyWin ∧ Mem.Wf M' ∧ M'.size = n) := by
  obtain ⟨hij, D, ann, hD, hann, hgy⟩ := getYChk_gyRes hi hj hres
  have hT := (MemTrack.init hwf gyWin).withWords (L' := [(0x220, memWord M 0x220)])
    (Words.cons.mpr ⟨⟨by omega, rfl⟩, Words.nil _⟩)
  have hcost : costGetY sevm b amp i.toNat j.toNat x.toNat x0.toNat x1.toNat x2.toNat =
      2100 + aGas sevm b + (costGetD x0.toNat x1.toNat x2.toNat amp +
        gyCostFrom0 i.toNat j.toNat x.toNat x0.toNat x1.toNat x2.toNat D ann (D, 0)) := by
    simp only [costGetY, hD, hann]
  rw [show G + costGetY sevm b amp i.toNat j.toNat x.toNat x0.toNat x1.toNat x2.toNat =
    G + gyCostFrom0 i.toNat j.toNat x.toNat x0.toNat x1.toNat x2.toNat D ann (D, 0) +
      costGetD x0.toNat x1.toNat x2.toNat amp + aGas sevm b + 2100 from by
    rw [hcost]; omega]
  simp only [SFunc.runExact_iff_runExactCut_nil]
  -- the arguments and the asserts
  xstep; xmstore 0x200; xmstore 0x140; xmstore 0x160; xmstore 0x180; xmstore 0x1a0
  xmstore 0x1c0; xmstore 0x1e0
  have hxor : i ^^^ j ≠ 0 := fun h => hij (by rw [(B256.xor_eq_zero_iff _ _).mp h])
  obtain ⟨hs0j, hs3j⟩ := slt_small hj
  obtain ⟨hs0i, hs3i⟩ := slt_small hi
  xmload 0x160; xmload 0x140; xstep; xstep
  xassert hxor
  xstep; xmload 0x160; xstep; xstep; xstep
  rw [hs0j]
  xassert (show B256.eqCheck 0 0 ≠ 0 by decide)
  xstep; xmload 0x160; xstep; xstep
  rw [hs3j]
  xassert (show (1 : B256) ≠ 0 by decide)
  xstep; xmload 0x140; xstep; xstep; xstep
  rw [hs0i]
  xassert (show B256.eqCheck 0 0 ≠ 0 by decide)
  xstep; xmload 0x140; xstep; xstep
  rw [hs3i]
  xassert (show (1 : B256) ≠ 0 by decide)
  -- `_A`, around the eight words `0x140 … 0x220`
  xmload 0x140; xmload 0x160; xmload 0x180; xmload 0x1a0; xmload 0x1c0; xmload 0x1e0
  xmload 0x200; xmload 0x220
  xname M1
  obtain ⟨w, ⟨MA, hcallA, hkA, hwfA, hSA⟩, hw⟩ := a_exact (sevm := sevm) (b := b)
    (ret := Nat.toB256 (0x1937 + 6))
    (G := G + gyCostFrom0 i.toNat j.toNat x.toNat x0.toNat x1.toNat x2.toNat D ann (D, 0) +
      costGetD x0.toNat x1.toNat x2.toNat amp + 1851)
    (S := memWord M 0x220 :: ρ :: x2 :: x1 :: x0 :: x :: j :: i :: S)
    hfork ha hA hT.wf hS hn (by omega) (by simp only [List.length_cons]; omega)
  rw [show G + gyCostFrom0 i.toNat j.toNat x.toNat x0.toNat x1.toNat x2.toNat D ann (D, 0) +
      costGetD x0.toNat x1.toNat x2.toNat amp + 1851 + aGas sevm b =
    G + gyCostFrom0 i.toNat j.toNat x.toNat x0.toNat x1.toNat x2.toNat D ann (D, 0) +
      costGetD x0.toNat x1.toNat x2.toNat amp + aGas sevm b + 1851 from by omega] at hcallA
  refine xlift (fun _ k => rxc_pcCall prog_27 (by decide) (by simp only [List.length_cons]; omega)
    hcallA k) ?_
  have hTA : MemTrack M MA gyWin [] :=
    ⟨hT.keeps.trans (hkA.widen (by decide)), Words.nil _, hwfA, fun _ => by rw [hSA]; exact hn⟩
  clear hT hS
  have hT := hTA
  have hS := hSA
  clear hTA hSA
  xstep; xmstore 0x260; xmstore 0x220; xmstore 0x200; xmstore 0x1e0; xmstore 0x1c0
  xmstore 0x1a0; xmstore 0x180; xmstore 0x160; xmstore 0x140
  xmload 0x260; xmstore 0x220
  xstep; xmstore 0x2a0
  xname M2
  -- the frame save, `[0x140, 0x2a0)`
  have hc2 := hT.words.memWord (o := 0x2a0) (v := Bytes.toB256 [1, 64]) (by wmem)
  have hi2 := hT.words.memWord (o := 0x140) (v := i) (by wmem)
  have hj2 := hT.words.memWord (o := 0x160) (v := j) (by wmem)
  have hx2 := hT.words.memWord (o := 0x180) (v := x) (by wmem)
  have hx02 := hT.words.memWord (o := 0x1a0) (v := x0) (by wmem)
  have hx12 := hT.words.memWord (o := 0x1c0) (v := x1) (by wmem)
  have hx22 := hT.words.memWord (o := 0x1e0) (v := x2) (by wmem)
  have hρ2 := hT.words.memWord (o := 0x200) (v := ρ) (by wmem)
  have hamp2 := hT.words.memWord (o := 0x220) (v := w) (by wmem)
  have hT2 := (hT.sub (L' := [(0x220, w), (0x1e0, x2), (0x1c0, x1), (0x1a0, x0)])
    (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
        rcases hx with rfl | rfl | rfl | rfl <;> simp only [true_or, or_true])).saveMem'
    (c := 0x2a0) (lo := 0x140) rfl rfl 11
  have hS2 : (saveMem M2 0x2a0 0x140 11).size = n := by
    rw [saveMem_size (by omega)]; exact hS
  refine xlift (fun _ k => rxc_save_1971 (by rw [hS]; exact hn) (by omega)
    (hc2.trans (by decide)) (by omega) k) ?_
  clear hT hS
  have hT := hT2
  have hS := hS2
  clear hT2 hS2
  generalize hF1 : (frameWords M2 0x140 11).reverse ++ S = S1
  have hS1l : S1.length = S.length + 11 := by
    rw [← hF1, List.length_append, List.length_reverse, length_frameWords]; omega
  -- `xp_` and `amp` to `0x2c0 … 0x320`, call `get_D`
  xstep; xstep; xstep; xstep; xmload' 0x1a0; xstep; xmstore' 0x2c0
  xstep; xstep; xstep; xmload' 0x1c0; xstep; xstep; xstep; xmstore' 0x2e0
  xstep; xstep; xstep; xmload' 0x1e0; xstep; xstep; xstep; xmstore' 0x300
  xstep; xstep; xmload 0x220; xmstore 0x320
  xmload 0x320; xmload 0x300; xmload 0x2e0; xmload 0x2c0
  xname M3
  have hDw : getDChk (V3.mk x0.toNat x1.toNat x2.toNat).get w.toNat 1 = some D := by
    rw [hw]; exact hD
  obtain ⟨M4, hso, hgD⟩ := getD_exact (sevm := sevm) (b := aBase sevm b)
    (ρ := Nat.toB256 (0x19ce + 6))
    (G := G + gyCostFrom0 i.toNat j.toNat x.toNat x0.toNat x1.toNat x2.toNat D ann (D, 0) + 923)
    (S := S1) (by rw [hS]; exact hn) (by omega) (by omega) hDw
  -- `D` is a word
  have hDlt : (Nat.toB256 D).toNat = D := by
    obtain ⟨d, hd, v', M', G', hd', hv', -⟩ := getD_spec (by rw [hS]; exact hn) (by omega)
      hgD.toRun
    have hd2 := Outcome.returned.inj hd
    rw [hd'] at hd2
    have hst := congrArg Devm.stack hd2
    rw [St.stack, St.stack] at hst
    have hv := (List.cons.inj hst).1
    rw [← hv, hDw] at hv'
    exact (Option.some.inj hv').symm
  rw [show G + gyCostFrom0 i.toNat j.toNat x.toNat x0.toNat x1.toNat x2.toNat D ann (D, 0) + 923 +
      costGetD x0.toNat x1.toNat x2.toNat w.toNat =
    G + gyCostFrom0 i.toNat j.toNat x.toNat x0.toNat x1.toNat x2.toNat D ann (D, 0) +
      costGetD x0.toNat x1.toNat x2.toNat amp + 923 from by rw [hw]; omega] at hgD
  refine xlift (fun _ k => rxc_pcCall prog_417 (by decide)
    (by simp only [List.length_cons]; omega) hgD k) ?_
  have hT4 : MemTrack M M4 gyWin [] :=
    ⟨hT.keeps.trans ((hso.keepsOff hT.wf).widen (by decide)), Words.nil _, hso.wf hT.wf,
      fun _ => by rw [hso.size, hS]; exact hn⟩
  have hS4 : M4.size = n := by rw [hso.size, hS]
  clear hT hS
  have hT := hT4
  have hS := hS4
  clear hT4 hS4
  -- park `D`, restore `[0x140, 0x2a0)`
  xstep; xmstore 0x380; xstep; xmstore 0x2a0
  xname M5
  have hc5 := hT.words.memWord (o := 0x2a0) (v := Bytes.toB256 [2, 0x80]) (by wmem)
  subst hF1
  refine xlift (fun _ k => rxc_restore_19e0 (by simp only [List.length_reverse, length_frameWords])
    (by rw [hS]; exact hn) (by omega) (hc5.trans (by decide)) (by omega) k) ?_
  have hfr := restoreMem_frameWords (c := 0x2a0) (lo := 0x140) (n := 11) (M := M5) (W := M2)
    (by omega) (by decide)
  have hw6 := Words.append.mpr ⟨Words.of_frameSlots hfr (j := 0) (by decide) hi2,
    Words.append.mpr ⟨Words.of_frameSlots hfr (j := 1) (by decide) hj2,
    Words.append.mpr ⟨Words.of_frameSlots hfr (j := 2) (by decide) hx2,
    Words.append.mpr ⟨Words.of_frameSlots hfr (j := 3) (by decide) hx02,
    Words.append.mpr ⟨Words.of_frameSlots hfr (j := 4) (by decide) hx12,
    Words.append.mpr ⟨Words.of_frameSlots hfr (j := 5) (by decide) hx22,
    Words.append.mpr ⟨Words.of_frameSlots hfr (j := 6) (by decide) hρ2,
    Words.append.mpr ⟨Words.of_frameSlots hfr (j := 7) (by decide) hamp2,
      Words.restoreMem' (c := 0x2a0) (p := 0x280) (ws := (frameWords M2 0x140 11).reverse)
        (hT.words.sub (L' := [(0x380, Nat.toB256 D)]) (by
          intro x hx
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rw [hx]; wmem)) (by decide)
        (by simp only [List.length_reverse, length_frameWords]; rfl)⟩⟩⟩⟩⟩⟩⟩⟩
  have hT6 := (MemTrack.restoreMem (c := 0x2a0) rfl (frameWords M2 0x140 11).reverse hT
    (p := 0x280) (fun k hk => by
      simp only [List.length_reverse, length_frameWords] at hk
      have h11 : ∀ k, k < 11 → coversWord gyWin (0x280 - 32 * k) = true := by decide
      exact h11 k hk)).withWords hw6
  have hS6 : (restoreMem 0x2a0 M5 0x280 (frameWords M2 0x140 11).reverse).size = n := by
    rw [restoreMem_size _ (by omega) (by omega)]; exact hS
  clear hT hS hw6
  have hT := hT6
  have hS := hS6
  clear hT6 hS6
  -- `c = D`, `S_ = 0`, `Ann`, `_x = 0`, the coin-loop counter
  rw [t_1a03_c547_eq]
  obtain ⟨hm, rfl⟩ := chkMul_inv (x := w) (y := Bytes.toB256 [0x03])
    (by rw [show (Bytes.toB256 [0x03]).toNat = 3 by decide, hw]; exact hann)
  xstep; xmload 0x380; xmstore 0x280; xmload 0x280; xmstore 0x3a0; xstep; xmstore 0x3c0
  xmload 0x220; xstep
  refine xlift (fun _ k => rxc_vyMulT hm (by vy_room) k) ?_
  xmstore 0x3e0; xstep; xmstore 0x400
  xstep; xstep; xstep; xstep; xstep; xmstore' 0x420
  xstep
  xname Mc
  rw [show Bytes.toB256 [0x03] + Bytes.toB256 [0x00] = Nat.toB256 3 by decide, toB256_0x420]
  have hi12 := hT.words.memWord (o := 0x140) (v := i) (by wmem)
  have hj12 := hT.words.memWord (o := 0x160) (v := j) (by wmem)
  have hx12 := hT.words.memWord (o := 0x180) (v := x) (by wmem)
  have hx012 := hT.words.memWord (o := 0x1a0) (v := x0) (by wmem)
  have hx112 := hT.words.memWord (o := 0x1c0) (v := x1) (by wmem)
  have hx212 := hT.words.memWord (o := 0x1e0) (v := x2) (by wmem)
  have hρ12 := hT.words.memWord (o := 0x200) (v := ρ) (by wmem)
  have hamp12 := hT.words.memWord (o := 0x220) (v := w) (by wmem)
  have hD12 := hT.words.memWord (o := 0x280) (v := Nat.toB256 D) (by wmem)
  have hc12 := hT.words.memWord (o := 0x3a0) (v := Nat.toB256 D) (by wmem)
  have hs12 := hT.words.memWord (o := 0x3c0) (v := Bytes.toB256 [0x00]) (by wmem)
  have hann12 := hT.words.memWord (o := 0x3e0) (v := w * Bytes.toB256 [0x03]) (by wmem)
  have hxv12 := hT.words.memWord (o := 0x400) (v := Bytes.toB256 [0x00]) (by wmem)
  have hcc12 := hT.words.memWord (o := 0x420) (v := Bytes.toB256 [0x00]) (by wmem)
  have hF := WordFrame.init (M0 := Mc) (lo := 0x140) (n := 28) (by rw [hS]; exact hn)
    (by omega)
  rw [show frameWords Mc 0x140 28 = [memWord Mc 0x140, memWord Mc 0x160, memWord Mc 0x180,
    memWord Mc 0x1a0, memWord Mc 0x1c0, memWord Mc 0x1e0, memWord Mc 0x200, memWord Mc 0x220,
    memWord Mc 0x240, memWord Mc 0x260, memWord Mc 0x280, memWord Mc 0x2a0, memWord Mc 0x2c0,
    memWord Mc 0x2e0, memWord Mc 0x300, memWord Mc 0x320, memWord Mc 0x340, memWord Mc 0x360,
    memWord Mc 0x380, memWord Mc 0x3a0, memWord Mc 0x3c0, memWord Mc 0x3e0, memWord Mc 0x400,
    memWord Mc 0x420, memWord Mc 0x440, memWord Mc 0x460, memWord Mc 0x480, memWord Mc 0x4a0]
    from rfl, hi12, hj12, hx12, hx012, hx112, hx212, hρ12, hamp12, hD12, hc12, hs12, hann12,
    hxv12, hcc12, toB256_zero] at hF
  have hres0 : ((gyCoinStep i.toNat j.toNat 0 x.toNat x0.toNat (Nat.toB256 D).toNat
      ((Nat.toB256 D).toNat, (Nat.toB256 0).toNat)).bind fun cs =>
      (gyCoinStep i.toNat j.toNat 1 x.toNat x1.toNat (Nat.toB256 D).toNat cs).bind fun cs =>
        (gyCoinStep i.toNat j.toNat 2 x.toNat x2.toNat (Nat.toB256 D).toNat cs).bind fun cs =>
          ydPostRes cs.1 cs.2 (Nat.toB256 D).toNat (w * Bytes.toB256 [0x03]).toNat) = some v := by
    rw [hDlt, show (Nat.toB256 0).toNat = 0 by decide]
    exact hgy
  obtain ⟨r, hrun, Mf, hr, hout⟩ := gyStage0X (G := G) (S := S) (by omega) hF hres0
  subst hr
  rw [hDlt, show (Nat.toB256 0).toNat = 0 by decide] at hrun
  refine ⟨Mf, hrun, hT.keeps.trans ((hout.keepsOff hT.wf).widen (by decide)), hout.wf hT.wf,
    by rw [hout.size, hS]⟩

end Blanc.Lift.Curve3Pool
