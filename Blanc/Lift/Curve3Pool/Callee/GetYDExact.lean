import Blanc.Lift.Curve3Pool.Callee.GetYD

/-!
# `get_y_D`, forward: exact gas

The forward twins of `GetYDLoop.lean`/`GetYDCoins.lean`/`GetYD.lean`: from the checked model's
success, the entry tree runs to its return with exact gas.  Costs: the exit `37`, the `y`-loop
counter tail `45` (`82` when it falls through to the exit), a Newton pass `ydStepC`/`ydStopC`/
`ydCapC` by the direction of the step, and the whole loop the recursive `fuelCost` over them.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune
open Blanc.StableSwapNewton

/-- Stack room, whatever the shape of the stack's known prefix. -/
macro "room" : tactic => `(tactic| first | omega | (simp only [List.length_cons]; omega))

theorem bodyYChk_inv {yw c bw D : B256} {y' : Nat}
    (h : bodyYChk c.toNat bw.toNat D.toNat yw.toNat = some y') :
    B256.Nofm yw yw ∧ (yw * yw).toNat + c.toNat < 2 ^ 256 ∧
      B256.Nofm (Bytes.toB256 [0x02]) yw ∧
      (Bytes.toB256 [0x02] * yw).toNat + bw.toNat < 2 ^ 256 ∧
      D.toNat ≤ (Bytes.toB256 [0x02] * yw + bw).toNat ∧
      Bytes.toB256 [0x02] * yw + bw - D ≠ 0 ∧
      y' = ((yw * yw + c) / (Bytes.toB256 [0x02] * yw + bw - D)).toNat := by
  have e2 : (2 : Nat) = (Bytes.toB256 [0x02]).toNat := by decide
  unfold bodyYChk at h
  rw [e2] at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨m1, h1, a1, h2, m2, h3, a2, h4, s1, h5, h6⟩ := h
  obtain ⟨hm1, rfl⟩ := chkMul_inv h1
  obtain ⟨ha1, rfl⟩ := chkAdd_inv h2
  obtain ⟨hm2, rfl⟩ := chkMul_inv h3
  obtain ⟨ha2, rfl⟩ := chkAdd_inv h4
  obtain ⟨hs, rfl⟩ := chkSub_inv h5
  obtain ⟨hd, rfl⟩ := chkDiv_inv h6
  exact ⟨hm1, ha1, hm2, ha2, hs, hd, rfl⟩

section Fwd

variable {sevm : Sevm} {C : List Nat} {b : Devm} {S : List B256} {M0 M : Mem} {G : Nat}
  {r : Seg} {ws : List B256}

theorem frame_size_pos (hF : WordFrame M0 M 0x140 ws) (hlen : ws.length = 16) :
    M.size % 32 = 0 ∧ 0x340 ≤ M.size := by
  have := hF.cover; rw [hlen] at this
  exact ⟨by rw [hF.size]; exact hF.aligned, by rw [hF.size]; omega⟩

-- SEGMENT: rxc_ydExit
/-- **The exit**, forward (37 gas). -/
theorem rxc_ydExit (hF : WordFrame M0 M 0x140 ws) (hlen : ws.length = 16) {yw ρ : B256}
    (hy : ws[14]? = some yw) (hρ : ws[6]? = some ρ) (hroom : S.length + 4 < 1024) :
    ∃ M', ScratchOut M0 M' 0x140 0x340 yw ∧
      SFunc.RunExactCut progYD sevm C (St b (ydStk S) M (G + 37)) ydExit
        (.done (.returned (St b (yw :: S) M' G))) := by
  obtain ⟨hout, hw⟩ := hF.scratch (by decide) yw
  rw [hlen] at hout
  obtain ⟨hsz, hcov⟩ := frame_size_pos hF hlen
  have hsz1 : (M.write 0 yw.toBytes).size % 32 = 0 := by rw [hout.size]; exact hF.aligned
  have hcov1 : 0x340 ≤ (M.write 0 yw.toBytes).size := by
    rw [hout.size, ← hF.size]; exact hcov
  refine ⟨_, hout, ?_⟩
  unfold ydExit
  refine rxc_dest (rxc_pop (rxc_pop ?_))
  refine rxc_pushMloadF hF 14 (by decide) hy (by omega) ?_
  refine rxc_push rfl (by room) ?_
  refine rxc_mstore (c := 3) (i := Bytes.toB256 [0x00]) (mstore_covered_cost' hsz
    (by rw [show (Bytes.toB256 [0x00]).toNat = 0 by decide]; omega))
    (by rw [show (Bytes.toB256 [0x00]).toNat = 0 by decide]) ?_
  refine rxc_push rfl (by room) ?_
  refine rxc_mload (c := 3) (i := Bytes.toB256 [0x00]) (v := yw) (mload_covered_cost' hsz1
    (by rw [show (Bytes.toB256 [0x00]).toNat = 0 by decide]; omega)) hout.word0
    (read_covered rfl hsz1 (by rw [show (Bytes.toB256 [0x00]).toNat = 0 by decide]; omega))
    (by omega) ?_
  refine rxc_push rfl (by room) ?_
  have e200 : (Bytes.toB256 [0x02, 0x00]).toNat = 0x140 + 32 * 6 := by decide
  refine rxc_mload (c := 3) (i := Bytes.toB256 [0x02, 0x00]) (v := ρ) (mload_covered_cost' hsz1
    (by rw [e200]; omega)) (by rw [e200]; exact hw 6 ρ hρ)
    (read_covered rfl hsz1 (by rw [e200]; omega)) (by room) ?_
  exact rxc_ret

/-- The tail's test word: nonzero below `255`. -/
theorem iszero_eq255_ne {m : Nat} (hm : m < 2 ^ 256) (h : m ≠ 255) :
    B256.eqCheck (B256.eqCheck (Nat.toB256 255) (Nat.toB256 m)) 0 ≠ 0 := by
  have : B256.eqCheck (Nat.toB256 255) (Nat.toB256 m) = 0 := by
    unfold B256.eqCheck
    rw [ite_eq_right (fun he => h ((toB256_eq_toB256_iff (by decide) hm).mp he).symm)]
  rw [this]; decide

-- SEGMENT: rxc_ydTail
/-- **The counter tail**, forward, re-entering the cut head (45 gas). -/
theorem rxc_ydTail_next (hF : WordFrame M0 M 0x140 ws) (hlen : ws.length = 16) {n k : Nat}
    {fall : SFunc} (hn : ws[15]? = some (Nat.toB256 n)) (hn1 : n + 1 < 255) (hk : k ∈ C)
    (hroom : S.length + 8 < 1024) :
    SFunc.RunExactCut progYD sevm C (St b (ydStk S) M (G + 45)) (ydTail k fall)
      (.at k (St b (ydStk S) (M.write (0x140 + 32 * 15) (Nat.toB256 (n + 1)).toBytes) G)) := by
  unfold ydTail
  refine rxc_dest (rxc_dest ?_)
  refine rxc_dup (w := Nat.toB256 0x320) rfl (by room) ?_
  refine rxc_mloadF hF 15 (by decide) hn (by room) ?_
  refine rxc_push rfl (by room) ?_
  refine rxc_add' (one_add_toB256 (by omega)) (by room) ?_
  refine rxc_dup (w := Nat.toB256 (n + 1)) rfl (by room) ?_
  refine rxc_dup (w := Nat.toB256 0x320) rfl (by room) ?_
  refine rxc_mstoreF hF 15 (by decide) (by rw [hlen]; decide) ?_
  refine rxc_dup (w := Nat.toB256 255) rfl (by room) ?_
  refine rxc_eq rfl (by room) ?_
  refine rxc_iszero rfl (by room) ?_
  refine rxc_push rfl (by room) ?_
  exact rxc_branchTo_cut (iszero_eq255_ne (by omega) (by omega)) hk

/-- **The counter tail**, forward, falling through after the last pass (45 gas). -/
theorem rxc_ydTail_last (hF : WordFrame M0 M 0x140 ws) (hlen : ws.length = 16) {n k : Nat}
    {fall : SFunc} (hn : ws[15]? = some (Nat.toB256 n)) (hn1 : n + 1 = 255)
    (hroom : S.length + 8 < 1024)
    (kk : SFunc.RunExactCut progYD sevm C
      (St b (ydStk S) (M.write (0x140 + 32 * 15) (Nat.toB256 (n + 1)).toBytes) G) fall r) :
    SFunc.RunExactCut progYD sevm C (St b (ydStk S) M (G + 45)) (ydTail k fall) r := by
  unfold ydTail
  refine rxc_dest (rxc_dest ?_)
  refine rxc_dup (w := Nat.toB256 0x320) rfl (by room) ?_
  refine rxc_mloadF hF 15 (by decide) hn (by room) ?_
  refine rxc_push rfl (by room) ?_
  refine rxc_add' (one_add_toB256 (by omega)) (by room) ?_
  refine rxc_dup (w := Nat.toB256 (n + 1)) rfl (by room) ?_
  refine rxc_dup (w := Nat.toB256 0x320) rfl (by room) ?_
  refine rxc_mstoreF hF 15 (by decide) (by rw [hlen]; decide) ?_
  refine rxc_dup (w := Nat.toB256 255) rfl (by room) ?_
  refine rxc_eq rfl (by room) ?_
  refine rxc_iszero rfl (by room) ?_
  refine rxc_push rfl (by room) ?_
  have hw : B256.eqCheck (B256.eqCheck (Nat.toB256 255) (Nat.toB256 (n + 1))) 0 = 0 := by
    rw [hn1]; decide
  rw [hw]
  exact rxc_branchTo_zero kk

-- SEGMENT: rxc_ydHeadPre
/-- **A Newton pass up to its stopping test**, forward (402 gas). -/
theorem rxc_ydHeadPre (hF : WordFrame M0 M 0x140 ws) (hlen : ws.length = 16) {yw c bw D : B256}
    (hy : ws[14]? = some yw) (hc : ws[7]? = some c) (hb : ws[12]? = some bw)
    (hD : ws[5]? = some D) (hm1 : B256.Nofm yw yw) (ha1 : (yw * yw).toNat + c.toNat < 2 ^ 256)
    (hm2 : B256.Nofm (Bytes.toB256 [0x02]) yw)
    (ha2 : (Bytes.toB256 [0x02] * yw).toNat + bw.toNat < 2 ^ 256)
    (hs : D.toNat ≤ (Bytes.toB256 [0x02] * yw + bw).toNat)
    (hd : Bytes.toB256 [0x02] * yw + bw - D ≠ 0) (hroom : S.length + 12 < 1024)
    {e t k : Nat} {fall : SFunc}
    (kk : SFunc.RunExactCut progYD sevm C (St b (Bytes.toB256 [0x3c, 0x72] ::
      B256.eqCheck (B256.gtCheck ((yw * yw + c) / (Bytes.toB256 [0x02] * yw + bw - D)) yw) 0 ::
      ydStk S) ((M.write (0x140 + 32 * 13) yw.toBytes).write (0x140 + 32 * 14)
        ((yw * yw + c) / (Bytes.toB256 [0x02] * yw + bw - D)).toBytes) G) (ydHeadBr e t k fall) r) :
    SFunc.RunExactCut progYD sevm C (St b (ydStk S) M (G + 402)) (ydHead e t k fall) r := by
  have hF13 := hF.write (j := 13) (by rw [hlen]; decide) yw
  have hF14 := hF13.write (j := 14) (by rw [List.length_set, hlen]; decide)
    ((yw * yw + c) / (Bytes.toB256 [0x02] * yw + bw - D))
  have h13y : (ws.set 13 yw)[14]? = some yw := by rw [List.getElem?_set_ne (by decide)]; exact hy
  have h13c : (ws.set 13 yw)[7]? = some c := by rw [List.getElem?_set_ne (by decide)]; exact hc
  have h13b : (ws.set 13 yw)[12]? = some bw := by rw [List.getElem?_set_ne (by decide)]; exact hb
  have h13D : (ws.set 13 yw)[5]? = some D := by rw [List.getElem?_set_ne (by decide)]; exact hD
  have h14y : ((ws.set 13 yw).set 14 ((yw * yw + c) / (Bytes.toB256 [0x02] * yw + bw - D)))[13]? =
      some yw := by
    rw [List.getElem?_set_ne (by decide), List.getElem?_set_self (by rw [hlen]; decide)]
  have h14q : ((ws.set 13 yw).set 14 ((yw * yw + c) / (Bytes.toB256 [0x02] * yw + bw - D)))[14]? =
      some ((yw * yw + c) / (Bytes.toB256 [0x02] * yw + bw - D)) := by
    rw [List.getElem?_set_self (by rw [List.length_set, hlen]; decide)]
  unfold ydHead
  refine rxc_dest ?_
  refine rxc_pushMloadF hF 14 (by decide) hy (by room) ?_
  refine rxc_pushMstoreF hF 13 (by decide) (by rw [hlen]; decide) (by room) ?_
  refine rxc_pushMloadF hF13 14 (by decide) h13y (by room) ?_
  refine rxc_pushMloadF hF13 14 (by decide) h13y (by room) ?_
  refine rxc_vyMulT hm1 (by room) ?_
  refine rxc_pushMloadF hF13 7 (by decide) h13c (by room) ?_
  refine rxc_vyAddT ha1 (by room) ?_
  refine rxc_push rfl (by room) ?_
  refine rxc_pushMloadF hF13 14 (by decide) h13y (by room) ?_
  refine rxc_vyMulT hm2 (by room) ?_
  refine rxc_pushMloadF hF13 12 (by decide) h13b (by room) ?_
  refine rxc_vyAddT ha2 (by room) ?_
  refine rxc_pushMloadF hF13 5 (by decide) h13D (by room) ?_
  refine rxc_vySubT hs (by room) ?_
  refine rxc_vyDivT hd (by room) ?_
  refine rxc_pushMstoreF hF13 14 (by decide) (by rw [List.length_set, hlen]; decide) (by room) ?_
  refine rxc_pushMloadF hF14 13 (by decide) h14y (by room) ?_
  refine rxc_pushMloadF hF14 14 (by decide) h14q (by room) ?_
  refine rxc_binary (fn := B256.gtCheck) (c := gVerylow) (by rintro ⟨⟩) (fun _ => rfl) rfl
    (by room) ?_
  refine rxc_iszero rfl (by room) ?_
  exact rxc_push rfl (by room) kk

theorem gtCheck_toNat (x y : B256) : B256.gtCheck x y = if y.toNat < x.toNat then 1 else 0 := by
  unfold B256.gtCheck
  by_cases h : y.toNat < x.toNat
  · rw [ite_eq_left h, ite_eq_left (by rw [gt_iff_lt, B256.lt_iff_toNat_lt_toNat]; exact h)]
  · rw [ite_eq_right h, ite_eq_right (by rw [gt_iff_lt, B256.lt_iff_toNat_lt_toNat]; exact h)]

-- SEGMENT: rxc_ydHeadBr
/-- **The stopping test, stopping**, forward: on to the exit `e`. -/
theorem rxc_ydHeadBr_close (hF : WordFrame M0 M 0x140 ws) {yw q : B256} {e t k : Nat}
    {fall : SFunc} (h13 : ws[13]? = some yw) (h14 : ws[14]? = some q)
    (hc : closeEnough 1 q.toNat yw.toNat) (he : progYD[e]? = some ydExit) (heC : e ∉ C)
    (hroom : S.length + 12 < 1024)
    (kk : SFunc.RunExactCut progYD sevm C (St b (ydStk S) M G) ydExit r) :
    SFunc.RunExactCut progYD sevm C (St b (Bytes.toB256 [0x3c, 0x72] ::
      B256.eqCheck (B256.gtCheck q yw) 0 :: ydStk S) M
      (G + if yw.toNat < q.toNat then 103 else 104)) (ydHeadBr e t k fall) r := by
  unfold ydHeadBr
  have h1 : (Bytes.toB256 [0x01]).toNat = 1 := by decide
  by_cases hgt : yw.toNat < q.toNat
  · rw [ite_eq_left hgt, gtCheck_toNat, ite_eq_left hgt]
    refine rxc_branch_zero (d := Bytes.toB256 [0x3c, 0x72]) ?_
    refine rxc_push rfl (by room) ?_
    refine rxc_pushMloadF hF 14 (by decide) h14 (by room) ?_
    refine rxc_pushMloadF hF 13 (by decide) h13 (by room) ?_
    refine rxc_vySubT (x := q) (y := yw) (by omega) (by room) ?_
    refine rxc_binary (fn := B256.gtCheck) (c := gVerylow) (by rintro ⟨⟩) (fun _ => rfl) rfl
      (by room) ?_
    refine rxc_iszero rfl (by room) ?_
    refine rxc_iszero rfl (by room) ?_
    refine rxc_push rfl (by room) ?_
    have hle : (q - yw).toNat ≤ 1 := by
      unfold closeEnough at hc; rw [ite_eq_left hgt] at hc
      rw [B256.toNat_sub_eq_of_le _ _ (B256.le_iff_toNat_le_toNat.mpr (by omega))]; exact hc
    rw [gtCheck_toNat, h1, ite_eq_right (by omega)]
    refine rxc_branch_zero (d := Bytes.toB256 [0x3c, 0x6d]) ?_
    refine rxc_push rfl (by room) ?_
    exact rxc_jump he heC kk
  · rw [ite_eq_right hgt, gtCheck_toNat, ite_eq_right hgt]
    refine rxc_branch_succ (by decide) (rxc_dest ?_)
    refine rxc_push rfl (by room) ?_
    refine rxc_pushMloadF hF 13 (by decide) h13 (by room) ?_
    refine rxc_pushMloadF hF 14 (by decide) h14 (by room) ?_
    refine rxc_vySubT (x := yw) (y := q) (by omega) (by room) ?_
    refine rxc_binary (fn := B256.gtCheck) (c := gVerylow) (by rintro ⟨⟩) (fun _ => rfl) rfl
      (by room) ?_
    refine rxc_iszero rfl (by room) ?_
    refine rxc_iszero rfl (by room) ?_
    refine rxc_push rfl (by room) ?_
    have hle : (yw - q).toNat ≤ 1 := by
      unfold closeEnough at hc; rw [ite_eq_right (by omega)] at hc
      rw [B256.toNat_sub_eq_of_le _ _ (B256.le_iff_toNat_le_toNat.mpr (by omega))]; exact hc
    rw [gtCheck_toNat, h1, ite_eq_right (by omega)]
    refine rxc_branch_zero (d := Bytes.toB256 [0x3c, 0x9c]) ?_
    refine rxc_push rfl (by room) ?_
    exact rxc_jump he heC kk

/-- **The stopping test, going on**, forward: on to the counter tail. -/
theorem rxc_ydHeadBr_next (hF : WordFrame M0 M 0x140 ws) {yw q : B256} {e t k : Nat}
    {fall fall' : SFunc} (h13 : ws[13]? = some yw) (h14 : ws[14]? = some q)
    (hnc : ¬ closeEnough 1 q.toNat yw.toNat) (ht : progYD[t]? = some (ydTail k fall'))
    (htC : t ∉ C) (hroom : S.length + 12 < 1024)
    (kA : yw.toNat < q.toNat →
      SFunc.RunExactCut progYD sevm C (St b (ydStk S) M G) (ydTail k fall') r)
    (kB : ¬ yw.toNat < q.toNat →
      SFunc.RunExactCut progYD sevm C (St b (ydStk S) M G) (ydTail k fall) r) :
    SFunc.RunExactCut progYD sevm C (St b (Bytes.toB256 [0x3c, 0x72] ::
      B256.eqCheck (B256.gtCheck q yw) 0 :: ydStk S) M
      (G + if yw.toNat < q.toNat then 104 else 94)) (ydHeadBr e t k fall) r := by
  unfold ydHeadBr
  have h1 : (Bytes.toB256 [0x01]).toNat = 1 := by decide
  by_cases hgt : yw.toNat < q.toNat
  · rw [ite_eq_left hgt, gtCheck_toNat, ite_eq_left hgt]
    refine rxc_branch_zero (d := Bytes.toB256 [0x3c, 0x72]) ?_
    refine rxc_push rfl (by room) ?_
    refine rxc_pushMloadF hF 14 (by decide) h14 (by room) ?_
    refine rxc_pushMloadF hF 13 (by decide) h13 (by room) ?_
    refine rxc_vySubT (x := q) (y := yw) (by omega) (by room) ?_
    refine rxc_binary (fn := B256.gtCheck) (c := gVerylow) (by rintro ⟨⟩) (fun _ => rfl) rfl
      (by room) ?_
    refine rxc_iszero rfl (by room) ?_
    refine rxc_iszero rfl (by room) ?_
    refine rxc_push rfl (by room) ?_
    have hgt1 : 1 < (q - yw).toNat := by
      unfold closeEnough at hnc; rw [ite_eq_left hgt] at hnc
      rw [B256.toNat_sub_eq_of_le _ _ (B256.le_iff_toNat_le_toNat.mpr (by omega))]; omega
    rw [gtCheck_toNat, h1, ite_eq_left hgt1]
    refine rxc_branch_succ (by decide) (rxc_dest ?_)
    refine rxc_push rfl (by room) ?_
    exact rxc_jump ht htC (kA hgt)
  · rw [ite_eq_right hgt, gtCheck_toNat, ite_eq_right hgt]
    refine rxc_branch_succ (by decide) (rxc_dest ?_)
    refine rxc_push rfl (by room) ?_
    refine rxc_pushMloadF hF 13 (by decide) h13 (by room) ?_
    refine rxc_pushMloadF hF 14 (by decide) h14 (by room) ?_
    refine rxc_vySubT (x := yw) (y := q) (by omega) (by room) ?_
    refine rxc_binary (fn := B256.gtCheck) (c := gVerylow) (by rintro ⟨⟩) (fun _ => rfl) rfl
      (by room) ?_
    refine rxc_iszero rfl (by room) ?_
    refine rxc_iszero rfl (by room) ?_
    refine rxc_push rfl (by room) ?_
    have hgt1 : 1 < (yw - q).toNat := by
      unfold closeEnough at hnc; rw [ite_eq_right (by omega)] at hnc
      rw [B256.toNat_sub_eq_of_le _ _ (B256.le_iff_toNat_le_toNat.mpr (by omega))]; omega
    rw [gtCheck_toNat, h1, ite_eq_left hgt1]
    refine rxc_branch_succ (by decide) (rxc_dest ?_)
    exact kB hgt

/-! ## The `y` loop, forward -/

/-- **One peeled pass, liveness, at one counter.**  The pass of a peeled copy `f` (whose back edge
targets `k`) at the single counter `n0` (`n0 + 1 < cap`), followed by the statement for the
continuation at `n0 + 1`.  Unlike `RunExactCut_fuelLoop_peel` it asks nothing of the copy at
other counters, so a copy whose last-pass fall-through is unreachable qualifies. -/
theorem RunExactCut_fuelLoop_peelAt {fs : List SFunc} {sevm : Sevm} {C : List Nat}
    {k : Nat} {g f : SFunc} (hk : fs[k]? = some g) (hkC : k ∉ C) {cap : Nat}
    {body : Nat → Option Nat} {close : Nat → Nat → Bool}
    {cStep cStop cCap : Nat → Nat → Nat}
    (At : Nat → Nat → Nat → Devm → Prop) (Exit : Nat → Nat → Seg → Prop) {n0 : Nat}
    (hn0 : n0 + 1 < cap)
    (next : ∀ D v G d, fuelLoop body close (cap - (n0 + 1)) D = some v →
      At (n0 + 1) D (G + fuelCost body close cStep cStop cCap (cap - (n0 + 1)) D) d →
      ∃ r, SFunc.RunExactCut fs sevm C d g r ∧ Exit v G r)
    (hstep : ∀ D D' G d, body D = some D' → close D' D = false →
      At n0 D (G + cStep D D') d →
      ∃ d', SFunc.RunExactCut fs sevm (k :: C) d f (.at k d') ∧ At (n0 + 1) D' G d')
    (hstop : ∀ D D' G d, body D = some D' → close D' D = true →
      At n0 D (G + cStop D D') d →
      ∃ r, SFunc.RunExactCut fs sevm (k :: C) d f r ∧ (∀ d', r ≠ .at k d') ∧ Exit D' G r) :
    ∀ D v G d, fuelLoop body close (cap - n0) D = some v →
      At n0 D (G + fuelCost body close cStep cStop cCap (cap - n0) D) d →
      ∃ r, SFunc.RunExactCut fs sevm C d f r ∧ Exit v G r := by
  intro D v G d hv hAt
  obtain ⟨m, hm⟩ : ∃ m, cap - n0 = m + 2 := ⟨cap - n0 - 2, by omega⟩
  rw [hm] at hv hAt
  cases hb : body D with
  | none => simp only [fuelLoop, hb, reduceCtorEq] at hv
  | some D' =>
    by_cases hc : close D' D = true
    · have hvD : v = D' := by
        simp only [fuelLoop, hb, hc, ↓reduceIte, Option.some.injEq] at hv
        exact hv.symm
      subst hvD
      have hcost : fuelCost body close cStep cStop cCap (m + 2) D = cStop D v := by
        simp only [fuelCost, hb, hc, ↓reduceIte]
      rw [hcost] at hAt
      obtain ⟨r, hrun, hne, hex⟩ := hstop D v G d hb hc hAt
      exact ⟨r, SFunc.RunExactCut.uncut hrun hne, hex⟩
    · have hc' : close D' D = false := by simpa only [Bool.not_eq_true] using hc
      have hv' : fuelLoop body close (m + 1) D' = some v := by
        simpa only [fuelLoop, hb, hc', Bool.false_eq_true, ↓reduceIte] using hv
      have hcost : G + fuelCost body close cStep cStop cCap (m + 2) D =
          (G + fuelCost body close cStep cStop cCap (m + 1) D') + cStep D D' := by
        simp only [fuelCost, hb, hc', Bool.false_eq_true, ↓reduceIte]
        omega
      rw [hcost] at hAt
      obtain ⟨d', hseg, hAt'⟩ := hstep D D' _ d hb hc' hAt
      have hm' : cap - (n0 + 1) = m + 1 := by omega
      obtain ⟨r, hrun, hex⟩ := next D' v G d' (by rw [hm']; exact hv') (by rw [hm']; exact hAt')
      exact ⟨r, SFunc.RunExactCut.resume hk hkC hseg hrun, hex⟩

/-- Gas of a Newton pass of the `y` loop that goes on, by the direction of the step. -/
def ydStepC (y y' : Nat) : Nat := if y < y' then 551 else 541

/-- Gas of a Newton pass of the `y` loop that stops. -/
def ydStopC (y y' : Nat) : Nat := if y < y' then 542 else 543

/-- Gas of the last permitted pass of the `y` loop. -/
def ydCapC (y y' : Nat) : Nat := if y < y' then 588 else 578

/-- The `y` loop's head state with its gas: counter `n`, iterate `y`. -/
def ydAtX (b : Devm) (S : List B256) (M0 : Mem) (D ρ c bw : B256) (n y G : Nat) (d : Devm) :
    Prop :=
  y < 2 ^ 256 ∧ ∃ M A i x0 x1 x2 s ann xv cc yp, d = St b (ydStk S) M G ∧
    WordFrame M0 M 0x140 (ydFrame A i x0 x1 x2 D ρ c s ann xv cc bw yp (Nat.toB256 y)
      (Nat.toB256 n))

/-- How a callee with the frame `[0x140, 0x340)` returns `v` with `G` gas left. -/
def calleeExit (b : Devm) (S : List B256) (M0 : Mem) (v G : Nat) (r : Seg) : Prop :=
  ∃ M, r = .done (.returned (St b (Nat.toB256 v :: S) M G)) ∧
    ScratchOut M0 M 0x140 0x340 (Nat.toB256 v)

-- SEGMENT: ydHead_fwd
/-- **A stopping Newton pass**, forward, at any copy. -/
theorem ydHead_stopX {D ρ c bw : B256} {e t k : Nat} {fall : SFunc}
    (he : progYD[e]? = some ydExit) (heC : e ∉ C) (hroom : S.length + 12 < 1024)
    {n y y' G : Nat} {d : Devm} (hb : bodyYChk c.toNat bw.toNat D.toNat y = some y')
    (hc : closeEnough 1 y' y) (hAt : ydAtX b S M0 D ρ c bw n y (G + ydStopC y y') d) :
    ∃ r, SFunc.RunExactCut progYD sevm C d (ydHead e t k fall) r ∧ (∀ d', r ≠ .at k d') ∧
      calleeExit b S M0 y' G r := by
  obtain ⟨hy, M, A, i, x0, x1, x2, s, ann, xv, cc, yp, rfl, hF⟩ := hAt
  have hyN : (Nat.toB256 y).toNat = y := B256.toNat_toB256_of_lt hy
  rw [← hyN] at hb hc
  obtain ⟨hm1, ha1, hm2, ha2, hs, hd, rfl⟩ := bodyYChk_inv hb
  have hF13 := hF.write (j := 13) (lt16 (by decide)) (Nat.toB256 y)
  have hF14 := hF13.write (j := 14) (lt16 (by decide))
    ((Nat.toB256 y * Nat.toB256 y + c) / (Bytes.toB256 [0x02] * Nat.toB256 y + bw - D))
  obtain ⟨M', hout, hex⟩ := rxc_ydExit (C := C) (G := G) (S := S) hF14 rfl rfl rfl (by omega)
  refine ⟨.done (.returned (St b (((Nat.toB256 y * Nat.toB256 y + c) / (Bytes.toB256 [0x02] * Nat.toB256 y + bw - D)) :: S) M' G)), ?_, fun d' h => (by cases h), M',
    by rw [toB256_toNat], by rw [toB256_toNat]; exact hout⟩
  have hg : G + ydStopC y
      ((Nat.toB256 y * Nat.toB256 y + c) / (Bytes.toB256 [0x02] * Nat.toB256 y + bw - D)).toNat =
      (G + 37 + if (Nat.toB256 y).toNat < ((Nat.toB256 y * Nat.toB256 y + c) /
        (Bytes.toB256 [0x02] * Nat.toB256 y + bw - D)).toNat then 103 else 104) + 402 := by
    rw [hyN]; unfold ydStopC; split <;> omega
  rw [hg]
  exact rxc_ydHeadPre hF rfl rfl rfl rfl rfl hm1 ha1 hm2 ha2 hs hd hroom
    (rxc_ydHeadBr_close hF14 rfl rfl hc he heC hroom hex)

/-- **A Newton pass that goes on**, forward, at any copy: back to the cut head `k`. -/
theorem ydHead_stepX {D ρ c bw : B256} {e t k : Nat} {fall fall' : SFunc}
    (ht : progYD[t]? = some (ydTail k fall')) (htC : t ∉ C) (hkC : k ∈ C)
    (hroom : S.length + 12 < 1024)
    {n y y' G : Nat} {d : Devm} (hn : n + 1 < 255)
    (hb : bodyYChk c.toNat bw.toNat D.toNat y = some y')
    (hc : ¬ closeEnough 1 y' y) (hAt : ydAtX b S M0 D ρ c bw n y (G + ydStepC y y') d) :
    ∃ d', SFunc.RunExactCut progYD sevm C d (ydHead e t k fall) (.at k d') ∧
      ydAtX b S M0 D ρ c bw (n + 1) y' G d' := by
  obtain ⟨hy, M, A, i, x0, x1, x2, s, ann, xv, cc, yp, rfl, hF⟩ := hAt
  have hyN : (Nat.toB256 y).toNat = y := B256.toNat_toB256_of_lt hy
  rw [← hyN] at hb hc
  obtain ⟨hm1, ha1, hm2, ha2, hs, hd, rfl⟩ := bodyYChk_inv hb
  have hF13 := hF.write (j := 13) (lt16 (by decide)) (Nat.toB256 y)
  have hF14 := hF13.write (j := 14) (lt16 (by decide))
    ((Nat.toB256 y * Nat.toB256 y + c) / (Bytes.toB256 [0x02] * Nat.toB256 y + bw - D))
  have hF15 := hF14.write (j := 15) (lt16 (by decide)) (Nat.toB256 (n + 1))
  refine ⟨_, ?_, B256.toNat_lt _, _, A, i, x0, x1, x2, s, ann, xv, cc, Nat.toB256 y, rfl,
    by rw [toB256_toNat]; exact hF15⟩
  have hg : G + ydStepC y
      ((Nat.toB256 y * Nat.toB256 y + c) / (Bytes.toB256 [0x02] * Nat.toB256 y + bw - D)).toNat =
      (G + 45 + if (Nat.toB256 y).toNat < ((Nat.toB256 y * Nat.toB256 y + c) /
        (Bytes.toB256 [0x02] * Nat.toB256 y + bw - D)).toNat then 104 else 94) + 402 := by
    rw [hyN]; unfold ydStepC; split <;> omega
  rw [hg]
  exact rxc_ydHeadPre hF rfl rfl rfl rfl rfl hm1 ha1 hm2 ha2 hs hd hroom
    (rxc_ydHeadBr_next hF14 rfl rfl hc ht htC hroom
      (fun _ => rxc_ydTail_next hF14 rfl rfl hn hkC (by omega))
      (fun _ => rxc_ydTail_next hF14 rfl rfl hn hkC (by omega)))

/-- **The last permitted pass**, forward, at the steady copy: through the tail to the exit. -/
theorem ydHead_capX {D ρ c bw : B256} {e t k : Nat}
    (ht : progYD[t]? = some (ydTail k ydExit)) (htC : t ∉ C)
    (hroom : S.length + 12 < 1024)
    {n y y' G : Nat} {d : Devm} (hn : n + 1 = 255)
    (hb : bodyYChk c.toNat bw.toNat D.toNat y = some y')
    (hc : ¬ closeEnough 1 y' y) (hAt : ydAtX b S M0 D ρ c bw n y (G + ydCapC y y') d) :
    ∃ r, SFunc.RunExactCut progYD sevm C d (ydHead e t k ydExit) r ∧ (∀ d', r ≠ .at k d') ∧
      calleeExit b S M0 y' G r := by
  obtain ⟨hy, M, A, i, x0, x1, x2, s, ann, xv, cc, yp, rfl, hF⟩ := hAt
  have hyN : (Nat.toB256 y).toNat = y := B256.toNat_toB256_of_lt hy
  rw [← hyN] at hb hc
  obtain ⟨hm1, ha1, hm2, ha2, hs, hd, rfl⟩ := bodyYChk_inv hb
  have hF13 := hF.write (j := 13) (lt16 (by decide)) (Nat.toB256 y)
  have hF14 := hF13.write (j := 14) (lt16 (by decide))
    ((Nat.toB256 y * Nat.toB256 y + c) / (Bytes.toB256 [0x02] * Nat.toB256 y + bw - D))
  have hF15 := hF14.write (j := 15) (lt16 (by decide)) (Nat.toB256 (n + 1))
  obtain ⟨M', hout, hex⟩ := rxc_ydExit (C := C) (G := G) (S := S) hF15 rfl rfl rfl (by omega)
  refine ⟨.done (.returned (St b (((Nat.toB256 y * Nat.toB256 y + c) /
    (Bytes.toB256 [0x02] * Nat.toB256 y + bw - D)) :: S) M' G)), ?_, fun d' h => (by cases h), M',
    by rw [toB256_toNat], by rw [toB256_toNat]; exact hout⟩
  have hg : G + ydCapC y
      ((Nat.toB256 y * Nat.toB256 y + c) / (Bytes.toB256 [0x02] * Nat.toB256 y + bw - D)).toNat =
      (G + 37 + 45 + if (Nat.toB256 y).toNat < ((Nat.toB256 y * Nat.toB256 y + c) /
        (Bytes.toB256 [0x02] * Nat.toB256 y + bw - D)).toNat then 104 else 94) + 402 := by
    rw [hyN]; unfold ydCapC; split <;> omega
  rw [hg]
  exact rxc_ydHeadPre hF rfl rfl rfl rfl rfl hm1 ha1 hm2 ha2 hs hd hroom
    (rxc_ydHeadBr_next hF14 rfl rfl hc ht htC hroom
      (fun _ => rxc_ydTail_last hF14 rfl rfl hn (by omega) hex)
      (fun _ => rxc_ydTail_last hF14 rfl rfl hn (by omega) hex))

/-- The `y` loop's gas: the fuel loop's recursive charge over the pass costs. -/
abbrev ydCost (c bw D : B256) (fuel y : Nat) : Nat :=
  fuelCost (bodyYChk c.toNat bw.toNat D.toNat) (fun new prev => decide (closeEnough 1 new prev))
    ydStepC ydStopC ydCapC fuel y

-- SEGMENT: ydLoop_exact
/-- **The `y` loop, forward**, from its first (inline) pass: a successful fuel loop runs to the
return with the recursive charge `ydCost`. -/
theorem ydLoop_exact {D ρ c bw : B256} (hroom : S.length + 12 < 1024) :
    ∀ y v G d, ydLoop c bw D 255 y = some v →
      ydAtX b S M0 D ρ c bw 0 y (G + ydCost c bw D 255 y) d →
      ∃ r, SFunc.RunExactCut progYD sevm [] d (ydHead 141 142 143 .undefined) r ∧
        calleeExit b S M0 v G r := by
  have h205 := RunExactCut_fuelLoop_exact (fs := progYD) (sevm := sevm) (C := []) progYD_205
    List.not_mem_nil (ydAtX b S M0 D ρ c bw) (calleeExit b S M0)
    (fun _ _ _ _ _ hn hb hc hAt => ydHead_stepX progYD_204 (by decide) List.mem_cons_self hroom
      hn hb (of_decide_eq_false hc) hAt)
    (fun _ _ _ _ _ _ hb hc hAt => ydHead_stopX progYD_185 (by decide) hroom hb
      (of_decide_eq_true hc) hAt)
    (fun _ _ _ _ _ hn hb hc hAt => ydHead_capX progYD_204 (by decide) hroom hn hb
      (of_decide_eq_false hc) hAt)
  have h187 := RunExactCut_fuelLoop_peelAt (fs := progYD) (sevm := sevm) (C := [])
    (f := ydHead 185 204 205 .undefined) progYD_205 List.not_mem_nil (ydAtX b S M0 D ρ c bw)
    (calleeExit b S M0) (n0 := 3) (by decide)
    (fun D v G d hv hAt => h205 4 D v G d (by decide) hv hAt)
    (fun _ _ _ _ hb hc hAt => ydHead_stepX progYD_204 (by decide) List.mem_cons_self hroom
      (by decide) hb (of_decide_eq_false hc) hAt)
    (fun _ _ _ _ hb hc hAt => ydHead_stopX progYD_185 (by decide) hroom hb
      (of_decide_eq_true hc) hAt)
  have h165 := RunExactCut_fuelLoop_peelAt (fs := progYD) (sevm := sevm) (C := [])
    (f := ydHead 185 186 187 .undefined) progYD_187 List.not_mem_nil (ydAtX b S M0 D ρ c bw)
    (calleeExit b S M0) (n0 := 2) (by decide) h187
    (fun _ _ _ _ hb hc hAt => ydHead_stepX progYD_186 (by decide) List.mem_cons_self hroom
      (by decide) hb (of_decide_eq_false hc) hAt)
    (fun _ _ _ _ hb hc hAt => ydHead_stopX progYD_185 (by decide) hroom hb
      (of_decide_eq_true hc) hAt)
  have h143 := RunExactCut_fuelLoop_peelAt (fs := progYD) (sevm := sevm) (C := [])
    (f := ydHead 163 164 165 .undefined) progYD_165 List.not_mem_nil (ydAtX b S M0 D ρ c bw)
    (calleeExit b S M0) (n0 := 1) (by decide) h165
    (fun _ _ _ _ hb hc hAt => ydHead_stepX progYD_164 (by decide) List.mem_cons_self hroom
      (by decide) hb (of_decide_eq_false hc) hAt)
    (fun _ _ _ _ hb hc hAt => ydHead_stopX progYD_163 (by decide) hroom hb
      (of_decide_eq_true hc) hAt)
  exact RunExactCut_fuelLoop_peelAt (fs := progYD) (sevm := sevm) (C := [])
    (f := ydHead 141 142 143 .undefined) progYD_143 List.not_mem_nil (ydAtX b S M0 D ρ c bw)
    (calleeExit b S M0) (n0 := 0) (by decide) h143
    (fun _ _ _ _ hb hc hAt => ydHead_stepX progYD_142 (by decide) List.mem_cons_self hroom
      (by decide) hb (of_decide_eq_false hc) hAt)
    (fun _ _ _ _ hb hc hAt => ydHead_stopX progYD_141 (by decide) hroom hb
      (of_decide_eq_true hc) hAt)

end Fwd

end Blanc.Lift.Curve3Pool
