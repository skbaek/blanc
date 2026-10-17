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

/-! ## The coin loop and the set-up, forward -/

theorem xor_toB256_ne {j : Nat} {i : B256} (hj : j < 3) (h : i ≠ Nat.toB256 j) :
    B256.eqCheck (Nat.toB256 j ^^^ i) 0 = 0 := by
  unfold B256.eqCheck
  rw [ite_eq_right (fun h0 => h ((B256.xor_eq_zero_iff _ _).mp h0).symm)]

theorem lt3_check {j : Nat} (hj : j < 3) : B256.ltCheck (Nat.toB256 j) (Bytes.toB256 [0x03]) ≠ 0 := by
  rcases j with _ | _ | _ | j
  · decide
  · decide
  · decide
  · omega

-- SEGMENT: rxc_ydTest
/-- **The coin-loop test, skipping coin `i`**, forward (44 gas). -/
theorem rxc_ydTest_skip (hF : WordFrame M0 M 0x140 ws) {j k1 k2 : Nat} {g2 : SFunc}
    (hi : ws[1]? = some (Nat.toB256 j)) (hj : ws[11]? = some (Nat.toB256 j))
    (hk2C : k2 ∉ C) (hk2 : progYD[k2]? = some g2) (hroom : S.length + 8 < 1024)
    (kk : SFunc.RunExactCut progYD sevm C (St b (ydCStk S) M G) g2 r) :
    SFunc.RunExactCut progYD sevm C (St b (ydCStk S) M (G + 44)) (ydTest k1 k2) r := by
  unfold ydTest
  refine rxc_dest ?_
  refine rxc_pushMloadF hF 1 (by decide) hi (by room) ?_
  refine rxc_pushMloadF hF 11 (by decide) hj (by room) ?_
  refine rxc_binary (fn := (· ^^^ ·)) (c := gVerylow) (by rintro ⟨⟩) (fun _ => rfl) rfl
    (by room) ?_
  refine rxc_iszero rfl (by room) ?_
  refine rxc_push rfl (by room) ?_
  rw [(B256.xor_eq_zero_iff _ _).mpr rfl]
  refine rxc_branch_succ (by decide) (rxc_dest ?_)
  refine rxc_push rfl (by room) ?_
  exact rxc_jump hk2 hk2C kk

/-- **The coin-loop test, loading `_x = xp[j]`**, forward (95 gas). -/
theorem rxc_ydTest_load (hF : WordFrame M0 M 0x140 ws) (hlen : ws.length = 16) {j k1 k2 : Nat}
    {g1 : SFunc} {i x : B256} (hj3 : j < 3) (hi : ws[1]? = some i) (hne : i ≠ Nat.toB256 j)
    (hj : ws[11]? = some (Nat.toB256 j)) (hx : ws[2 + j]? = some x)
    (hk1C : k1 ∉ C) (hk1 : progYD[k1]? = some g1) (hroom : S.length + 8 < 1024)
    (kk : SFunc.RunExactCut progYD sevm C
      (St b (ydCStk S) (M.write (0x140 + 32 * 10) x.toBytes) G) g1 r) :
    SFunc.RunExactCut progYD sevm C (St b (ydCStk S) M (G + 95)) (ydTest k1 k2) r := by
  unfold ydTest
  refine rxc_dest ?_
  refine rxc_pushMloadF hF 1 (by decide) hi (by room) ?_
  refine rxc_pushMloadF hF 11 (by decide) hj (by room) ?_
  refine rxc_binary (fn := (· ^^^ ·)) (c := gVerylow) (by rintro ⟨⟩) (fun _ => rfl) rfl
    (by room) ?_
  refine rxc_iszero rfl (by room) ?_
  refine rxc_push rfl (by room) ?_
  rw [xor_toB256_ne hj3 hne]
  refine rxc_branch_zero ?_
  refine rxc_push rfl (by room) ?_
  refine rxc_pushMloadF hF 11 (by decide) hj (by room) ?_
  refine rxc_push rfl (by room) ?_
  refine rxc_dup (w := Nat.toB256 j) rfl (by room) ?_
  refine rxc_lt rfl (by room) ?_
  refine rxc_push rfl (by room) ?_
  refine rxc_branch_succ (lt3_check hj3) (rxc_dest ?_)
  refine rxc_push rfl (by room) ?_
  refine rxc_binary (fn := (· * ·)) (c := gLow) (by rintro ⟨⟩) (fun _ => rfl) rfl (by room) ?_
  refine rxc_add (by room) ?_
  refine rxc_mloadF hF (2 + j) (ydXpAddr hj3) hx (by room) ?_
  refine rxc_pushMstoreF hF 10 (by decide) (by rw [hlen]; decide) (by room) ?_
  refine rxc_push rfl (by room) ?_
  exact rxc_jump hk1 hk1C kk

theorem iszero_eq3_neX {m : Nat} (hm : m < 3) :
    B256.eqCheck (B256.eqCheck (Nat.toB256 3) (Nat.toB256 m)) 0 ≠ 0 := by
  rcases m with _ | _ | _ | m
  · decide
  · decide
  · decide
  · omega

-- SEGMENT: rxc_ydCoinTail
/-- **The coin-loop counter tail, on to entry `k`**, forward (44 gas). -/
theorem rxc_ydCoinTail_next (hF : WordFrame M0 M 0x140 ws) (hlen : ws.length = 16) {j k : Nat}
    {g : SFunc} (hj : ws[11]? = some (Nat.toB256 j)) (hj3 : j + 1 < 3) (hkC : k ∉ C)
    (hk : progYD[k]? = some g) (hroom : S.length + 8 < 1024)
    (kk : SFunc.RunExactCut progYD sevm C
      (St b (ydCStk S) (M.write (0x140 + 32 * 11) (Nat.toB256 (j + 1)).toBytes) G) g r) :
    SFunc.RunExactCut progYD sevm C (St b (ydCStk S) M (G + 44))
      (ydCoinTail (.branchTo .undefined k)) r := by
  unfold ydCoinTail
  refine rxc_dest ?_
  refine rxc_dup (w := Nat.toB256 0x2a0) rfl (by room) ?_
  refine rxc_mloadF hF 11 (by decide) hj (by room) ?_
  refine rxc_push rfl (by room) ?_
  refine rxc_add' (one_add_toB256 (by omega)) (by room) ?_
  refine rxc_dup (w := Nat.toB256 (j + 1)) rfl (by room) ?_
  refine rxc_dup (w := Nat.toB256 0x2a0) rfl (by room) ?_
  refine rxc_mstoreF hF 11 (by decide) (by rw [hlen]; decide) ?_
  refine rxc_dup (w := Nat.toB256 3) rfl (by room) ?_
  refine rxc_eq rfl (by room) ?_
  refine rxc_iszero rfl (by room) ?_
  refine rxc_push rfl (by room) ?_
  exact rxc_branchTo_succ (iszero_eq3_neX hj3) hkC hk kk

/-- **The last coin-loop counter tail, on to the set-up `g`**, forward (44 gas). -/
theorem rxc_ydCoinTail_last (hF : WordFrame M0 M 0x140 ws) (hlen : ws.length = 16) {j : Nat}
    {g : SFunc} (hj : ws[11]? = some (Nat.toB256 j)) (hj3 : j + 1 = 3)
    (hroom : S.length + 8 < 1024)
    (kk : SFunc.RunExactCut progYD sevm C
      (St b (ydCStk S) (M.write (0x140 + 32 * 11) (Nat.toB256 (j + 1)).toBytes) G) g r) :
    SFunc.RunExactCut progYD sevm C (St b (ydCStk S) M (G + 44))
      (ydCoinTail (.branch g .undefined)) r := by
  unfold ydCoinTail
  refine rxc_dest ?_
  refine rxc_dup (w := Nat.toB256 0x2a0) rfl (by room) ?_
  refine rxc_mloadF hF 11 (by decide) hj (by room) ?_
  refine rxc_push rfl (by room) ?_
  refine rxc_add' (one_add_toB256 (by omega)) (by room) ?_
  refine rxc_dup (w := Nat.toB256 (j + 1)) rfl (by room) ?_
  refine rxc_dup (w := Nat.toB256 0x2a0) rfl (by room) ?_
  refine rxc_mstoreF hF 11 (by decide) (by rw [hlen]; decide) ?_
  refine rxc_dup (w := Nat.toB256 3) rfl (by room) ?_
  refine rxc_eq rfl (by room) ?_
  refine rxc_iszero rfl (by room) ?_
  refine rxc_push rfl (by room) ?_
  have hw : B256.eqCheck (B256.eqCheck (Nat.toB256 3) (Nat.toB256 (j + 1))) 0 = 0 := by
    rw [hj3]; decide
  rw [hw]
  exact rxc_branch_zero kk

theorem ydAccN_inv {c s x D : B256} {c' s' : Nat}
    (h : ydAccN c.toNat s.toNat x.toNat D.toNat = some (c', s')) :
    s.toNat + x.toNat < 2 ^ 256 ∧ B256.Nofm c D ∧ B256.Nofm x (Bytes.toB256 [0x03]) ∧
      x * Bytes.toB256 [0x03] ≠ 0 ∧ s' = (s + x).toNat ∧
      c' = ((c * D) / (x * Bytes.toB256 [0x03])).toNat := by
  have e3 : (3 : Nat) = (Bytes.toB256 [0x03]).toNat := by decide
  unfold ydAccN at h
  rw [e3] at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
    Prod.mk.injEq] at h
  obtain ⟨sa, hsa, ma, hma, mb, hmb, ca, hca, rfl, rfl⟩ := h
  obtain ⟨h1, rfl⟩ := chkAdd_inv hsa
  obtain ⟨h2, rfl⟩ := chkMul_inv hma
  obtain ⟨h3, rfl⟩ := chkMul_inv hmb
  obtain ⟨h4, rfl⟩ := chkDiv_inv hca
  exact ⟨h1, h2, h3, h4, rfl, rfl⟩

-- SEGMENT: rxc_ydAcc
/-- **The coin-loop accumulation**, forward (278 gas). -/
theorem rxc_ydAcc (hF : WordFrame M0 M 0x140 ws) (hlen : ws.length = 16) {c s x D : B256}
    (hc : ws[7]? = some c) (hs : ws[8]? = some s) (hx : ws[10]? = some x)
    (hD : ws[5]? = some D) (ha : s.toNat + x.toNat < 2 ^ 256) (hm1 : B256.Nofm c D)
    (hm2 : B256.Nofm x (Bytes.toB256 [0x03])) (hd : x * Bytes.toB256 [0x03] ≠ 0)
    (hroom : S.length + 12 < 1024) {tail : SFunc}
    (kk : SFunc.RunExactCut progYD sevm C (St b (ydCStk S)
      ((M.write (0x140 + 32 * 8) (s + x).toBytes).write (0x140 + 32 * 7)
        ((c * D) / (x * Bytes.toB256 [0x03])).toBytes) G) tail r) :
    SFunc.RunExactCut progYD sevm C (St b (ydCStk S) M (G + 278)) (ydAcc tail) r := by
  have hF8 := hF.write (j := 8) (by rw [hlen]; decide) (s + x)
  have hc1 : (ws.set 8 (s + x))[7]? = some c := by rw [List.getElem?_set_ne (by decide)]; exact hc
  have hD1 : (ws.set 8 (s + x))[5]? = some D := by rw [List.getElem?_set_ne (by decide)]; exact hD
  have hx1 : (ws.set 8 (s + x))[10]? = some x := by
    rw [List.getElem?_set_ne (by decide)]; exact hx
  unfold ydAcc
  refine rxc_dest ?_
  refine rxc_push rfl (by room) ?_
  refine rxc_dup (w := Bytes.toB256 [0x02, 0x40]) rfl (by room) ?_
  refine rxc_mloadF hF 8 (by decide) hs (by room) ?_
  refine rxc_pushMloadF hF 10 (by decide) hx (by room) ?_
  refine rxc_vyAddT ha (by room) ?_
  refine rxc_dup (w := Bytes.toB256 [0x02, 0x40]) rfl (by room) ?_
  refine rxc_mstoreF hF 8 (by decide) (by rw [hlen]; decide) ?_
  refine rxc_pop ?_
  refine rxc_pushMloadF hF8 7 (by decide) hc1 (by room) ?_
  refine rxc_pushMloadF hF8 5 (by decide) hD1 (by room) ?_
  refine rxc_vyMulT hm1 (by room) ?_
  refine rxc_pushMloadF hF8 10 (by decide) hx1 (by room) ?_
  refine rxc_push rfl (by room) ?_
  refine rxc_vyMulT hm2 (by room) ?_
  refine rxc_vyDivT hd (by room) ?_
  exact rxc_pushMstoreF hF8 7 (by decide) (by rw [List.length_set, hlen]; decide) (by room) kk

theorem ydPostRes_inv {c s D ann : B256} {y : Nat}
    (h : ydPostRes c.toNat s.toNat D.toNat ann.toNat = some y) :
    B256.Nofm c D ∧ B256.Nofm ann (Bytes.toB256 [0x03]) ∧ ann * Bytes.toB256 [0x03] ≠ 0 ∧
      ann ≠ 0 ∧ s.toNat + (D / ann).toNat < 2 ^ 256 ∧
      loopYChk ((c * D) / (ann * Bytes.toB256 [0x03])).toNat (s + D / ann).toNat D.toNat 1 255
        D.toNat = some y := by
  have e3 : (3 : Nat) = (Bytes.toB256 [0x03]).toNat := by decide
  unfold ydPostRes at h
  rw [e3] at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨m1, h1, m2, h2, c', h3, q, h4, b', h5, h6⟩ := h
  obtain ⟨hm1, rfl⟩ := chkMul_inv h1
  obtain ⟨hm2, rfl⟩ := chkMul_inv h2
  obtain ⟨hd1, rfl⟩ := chkDiv_inv h3
  obtain ⟨hd2, rfl⟩ := chkDiv_inv h4
  obtain ⟨ha, rfl⟩ := chkAdd_inv h5
  exact ⟨hm1, hm2, hd1, hd2, ha, h6⟩

-- SEGMENT: rxc_ydPost
/-- **After the coin loop**, forward through the whole `y` loop: `363` gas plus the loop's
recursive charge. -/
theorem rxc_ydPost {A i x0 x1 x2 D ρ c s ann xv cc w12 w13 w14 w15 : B256} {y : Nat}
    (hF : WordFrame M0 M 0x140 (ydFrame A i x0 x1 x2 D ρ c s ann xv cc w12 w13 w14 w15))
    (hres : ydPostRes c.toNat s.toNat D.toNat ann.toNat = some y)
    (hroom : S.length + 12 < 1024) :
    ∃ r, SFunc.RunExactCut progYD sevm [] (St b (ydCStk S) M
      (G + 363 + ydCost ((c * D) / (ann * Bytes.toB256 [0x03])) (s + D / ann) D 255 D.toNat))
      ydPost0 r ∧ calleeExit b S M0 y G r := by
  obtain ⟨hm1, hm2, hd1, hd2, ha, hloop⟩ := ydPostRes_inv hres
  set c' := (c * D) / (ann * Bytes.toB256 [0x03]) with hc'
  set b' := s + D / ann with hb'
  have hF1 := hF.write (j := 7) (lt16 (by decide)) c'
  have hF2 := hF1.write (j := 12) (lt16 (by decide)) b'
  have hF3 := hF2.write (j := 13) (lt16 (by decide)) (Nat.toB256 0)
  have hF4 := hF3.write (j := 14) (lt16 (by decide)) D
  have hF5 := hF4.write (j := 15) (lt16 (by decide)) (Nat.toB256 0)
  have hAt : ydAtX b S M0 D ρ c' b' 0 D.toNat (G + ydCost c' b' D 255 D.toNat)
      (St b (ydStk S) ((((((M.write (0x140 + 32 * 7) c'.toBytes).write (0x140 + 32 * 12)
        b'.toBytes).write (0x140 + 32 * 13) (Nat.toB256 0).toBytes).write (0x140 + 32 * 14)
        D.toBytes).write (0x140 + 32 * 15) (Nat.toB256 0).toBytes))
        (G + ydCost c' b' D 255 D.toNat)) := by
    refine ⟨B256.toNat_lt D, _, A, i, x0, x1, x2, s, ann, xv, cc, Nat.toB256 0, rfl, ?_⟩
    rw [toB256_toNat]; exact hF5
  have hv : ydLoop c' b' D 255 D.toNat = some y := by
    rw [ydLoop, ← loopYChk_eq_fuelLoop]; exact hloop
  obtain ⟨r, hrun, hex⟩ := ydLoop_exact hroom D.toNat y G _ hv hAt
  refine ⟨r, ?_, hex⟩
  rw [show G + 363 + ydCost c' b' D 255 D.toNat = (G + ydCost c' b' D 255 D.toNat) + 363 by
    omega]
  unfold ydPost0 ydPost
  refine rxc_dest (rxc_pop (rxc_pop ?_))
  refine rxc_pushMloadF hF 7 (by decide) rfl (by room) ?_
  refine rxc_pushMloadF hF 5 (by decide) rfl (by room) ?_
  refine rxc_vyMulT hm1 (by room) ?_
  refine rxc_pushMloadF hF 9 (by decide) rfl (by room) ?_
  refine rxc_push rfl (by room) ?_
  refine rxc_vyMulT hm2 (by room) ?_
  refine rxc_vyDivT hd1 (by room) ?_
  refine rxc_pushMstoreF hF 7 (by decide) (lt16 (by decide)) (by room) ?_
  refine rxc_pushMloadF hF1 8 (by decide) rfl (by room) ?_
  refine rxc_pushMloadF hF1 5 (by decide) rfl (by room) ?_
  refine rxc_pushMloadF hF1 9 (by decide) rfl (by room) ?_
  refine rxc_vyDivT hd2 (by room) ?_
  refine rxc_vyAddT ha (by room) ?_
  refine rxc_pushMstoreF hF1 12 (by decide) (lt16 (by decide)) (by room) ?_
  refine rxc_push toB256_zero (by room) ?_
  refine rxc_pushMstoreF hF2 13 (by decide) (lt16 (by decide)) (by room) ?_
  refine rxc_pushMloadF hF3 5 (by decide) rfl (by room) ?_
  refine rxc_pushMstoreF hF3 14 (by decide) (lt16 (by decide)) (by room) ?_
  refine rxc_push toB256_0x320 (by room) ?_
  refine rxc_push toB256_zero (by room) ?_
  refine rxc_push rfl (by room) ?_
  refine rxc_dup (w := Nat.toB256 0) rfl (by room) ?_
  refine rxc_dup (w := Nat.toB256 0x320) rfl (by room) ?_
  refine rxc_mstoreF hF4 15 (by decide) (lt16 (by decide)) ?_
  refine rxc_add' (show Bytes.toB256 [0xff] + Nat.toB256 0 = Nat.toB256 255 by decide)
    (by room) ?_
  exact hrun

/-! ## Costs on naturals -/

/-- Gas of the set-up after the coin loop and the `y` loop, on naturals. -/
def ydPostCost (c s D ann : Nat) : Nat :=
  363 + fuelCost (bodyYChk (c * D / (ann * 3)) (s + D / ann) D)
    (fun new prev => decide (closeEnough 1 new prev)) ydStepC ydStopC ydCapC 255 D

/-- Gas of one coin-loop iteration: skipping coin `i`, or accumulating. -/
def ydCoinCost (i j : Nat) : Nat := if i = j then 88 else 417

/-- Gas from the coin-loop iteration `2` on. -/
def ydCostFrom2 (i x2 D ann : Nat) (cs : Nat × Nat) : Nat :=
  ydCoinCost i 2 + match ydCoinStep i 2 x2 D cs with
    | some cs' => ydPostCost cs'.1 cs'.2 D ann
    | none => 0

/-- Gas from the coin-loop iteration `1` on. -/
def ydCostFrom1 (i x1 x2 D ann : Nat) (cs : Nat × Nat) : Nat :=
  ydCoinCost i 1 + match ydCoinStep i 1 x1 D cs with
    | some cs' => ydCostFrom2 i x2 D ann cs'
    | none => 0

/-- Gas from the coin-loop iteration `0` on. -/
def ydCostFrom0 (i x0 x1 x2 D ann : Nat) (cs : Nat × Nat) : Nat :=
  ydCoinCost i 0 + match ydCoinStep i 0 x0 D cs with
    | some cs' => ydCostFrom1 i x1 x2 D ann cs'
    | none => 0

theorem ydPostCost_words {c s D ann : B256} (hm1 : B256.Nofm c D)
    (hm2 : B256.Nofm ann (Bytes.toB256 [0x03])) (hd1 : ann * Bytes.toB256 [0x03] ≠ 0)
    (hd2 : ann ≠ 0) (ha : s.toNat + (D / ann).toNat < 2 ^ 256) :
    ydPostCost c.toNat s.toNat D.toNat ann.toNat =
      363 + ydCost ((c * D) / (ann * Bytes.toB256 [0x03])) (s + D / ann) D 255 D.toNat := by
  unfold ydPostCost ydCost
  rw [B256.toNat_div hd1, B256.toNat_mul_eq_of_nofm hm1, B256.toNat_mul_eq_of_nofm hm2,
    B256.toNat_add, Nat.lo, Nat.mod_eq_of_lt ha, B256.toNat_div hd2,
    show (Bytes.toB256 [0x03]).toNat = 3 by decide]

theorem ydAccN_words {c s x D : B256} {c' s' : Nat}
    (h : ydAccN c.toNat s.toNat x.toNat D.toNat = some (c', s')) :
    c' = ((c * D) / (x * Bytes.toB256 [0x03])).toNat ∧ s' = (s + x).toNat := by
  obtain ⟨-, -, -, -, h1, h2⟩ := ydAccN_inv h
  exact ⟨h2, h1⟩

-- SEGMENT: ydStage2X
/-- **Coin-loop iteration `2` and the rest**, forward. -/
theorem ydStage2X {A i x0 x1 x2 D ρ c s ann xv w12 w13 w14 w15 : B256} {y : Nat}
    (hi3 : i.toNat < 3) (hroom : S.length + 12 < 1024)
    (hF : WordFrame M0 M 0x140 (ydFrame A i x0 x1 x2 D ρ c s ann xv (Nat.toB256 2) w12 w13 w14
      w15))
    (hres : ((ydCoinStep i.toNat 2 x2.toNat D.toNat (c.toNat, s.toNat)).bind fun cs =>
      ydPostRes cs.1 cs.2 D.toNat ann.toNat) = some y) :
    ∃ r, SFunc.RunExactCut progYD sevm [] (St b (ydCStk S) M
      (G + ydCostFrom2 i.toNat x2.toNat D.toNat ann.toNat (c.toNat, s.toNat))) (ydTest 120 121) r ∧
      calleeExit b S M0 y G r := by
  unfold ydCostFrom2 ydCoinCost
  by_cases hi : i.toNat = 2
  · have hiw : i = Nat.toB256 2 := by rw [← hi, toB256_toNat]
    rw [hi, ydCoinStep_eq, Option.bind_some] at hres
    rw [hi, ydCoinStep_eq, ite_eq_left rfl]
    obtain ⟨hm1, hm2, hd1, hd2, ha, -⟩ := ydPostRes_inv hres
    have hF11 := hF.write (j := 11) (lt16 (by decide)) (Nat.toB256 (2 + 1))
    obtain ⟨r, hrun, hex⟩ := rxc_ydPost (G := G) hF11 hres hroom
    refine ⟨r, ?_, hex⟩
    dsimp only
    rw [ydPostCost_words hm1 hm2 hd1 hd2 ha,
      show G + (88 + (363 + ydCost ((c * D) / (ann * Bytes.toB256 [0x03])) (s + D / ann) D 255
        D.toNat)) = G + 363 + ydCost ((c * D) / (ann * Bytes.toB256 [0x03])) (s + D / ann) D 255
        D.toNat + 44 + 44 by omega]
    refine rxc_ydTest_skip (j := 2) hF (by rw [hiw]; rfl) rfl List.not_mem_nil progYD_121 (by omega) ?_
    exact rxc_ydCoinTail_last hF rfl rfl (by decide) (by omega) hrun
  · have hne : i ≠ Nat.toB256 2 := fun h => hi (by rw [h]; decide)
    rw [ydCoinStep_ne hi] at hres ⊢
    rw [ite_eq_right hi]
    obtain ⟨⟨c', s'⟩, hacc, hres⟩ := Option.bind_eq_some_iff.mp hres
    rw [hacc]
    obtain ⟨ha1, hma, hmb, hda, -, -⟩ := ydAccN_inv hacc
    obtain ⟨rfl, rfl⟩ := ydAccN_words hacc
    simp only at hres ⊢
    obtain ⟨hm1, hm2, hd1, hd2, ha, -⟩ := ydPostRes_inv hres
    have hF10 := hF.write (j := 10) (lt16 (by decide)) x2
    have hF8 := hF10.write (j := 8) (lt16 (by decide)) (s + x2)
    have hF7 := hF8.write (j := 7) (lt16 (by decide)) ((c * D) / (x2 * Bytes.toB256 [0x03]))
    have hF11 := hF7.write (j := 11) (lt16 (by decide)) (Nat.toB256 (2 + 1))
    obtain ⟨r, hrun, hex⟩ := rxc_ydPost (G := G) hF11 hres hroom
    refine ⟨r, ?_, hex⟩
    rw [ydPostCost_words hm1 hm2 hd1 hd2 ha]
    rw [show ∀ P : Nat, G + (417 + (363 + P)) = G + 363 + P + 44 + 278 + 95 from
      fun P => by omega]
    refine rxc_ydTest_load hF rfl (by decide) rfl hne rfl rfl List.not_mem_nil progYD_120
      (by omega) ?_
    refine rxc_ydAcc hF10 rfl rfl rfl rfl rfl ha1 hma hmb hda hroom ?_
    exact rxc_ydCoinTail_last hF7 rfl rfl (by decide) (by omega) hrun

-- SEGMENT: ydStage1X
/-- **Coin-loop iteration `1` and the rest**, forward. -/
theorem ydStage1X {A i x0 x1 x2 D ρ c s ann xv w12 w13 w14 w15 : B256} {y : Nat}
    (hi3 : i.toNat < 3) (hroom : S.length + 12 < 1024)
    (hF : WordFrame M0 M 0x140 (ydFrame A i x0 x1 x2 D ρ c s ann xv (Nat.toB256 1) w12 w13 w14
      w15))
    (hres : ((ydCoinStep i.toNat 1 x1.toNat D.toNat (c.toNat, s.toNat)).bind fun cs =>
      (ydCoinStep i.toNat 2 x2.toNat D.toNat cs).bind fun cs =>
        ydPostRes cs.1 cs.2 D.toNat ann.toNat) = some y) :
    ∃ r, SFunc.RunExactCut progYD sevm [] (St b (ydCStk S) M
      (G + ydCostFrom1 i.toNat x1.toNat x2.toNat D.toNat ann.toNat (c.toNat, s.toNat))) (ydTest 76 77) r ∧
      calleeExit b S M0 y G r := by
  unfold ydCostFrom1 ydCoinCost
  by_cases hi : i.toNat = 1
  · have hiw : i = Nat.toB256 1 := by rw [← hi, toB256_toNat]
    rw [hi, ydCoinStep_eq, Option.bind_some] at hres
    rw [hi, ydCoinStep_eq, ite_eq_left rfl]
    have hF11 := hF.write (j := 11) (lt16 (by decide)) (Nat.toB256 (1 + 1))
    obtain ⟨r, hrun, hex⟩ := ydStage2X (G := G) (by rw [hi]; decide) hroom hF11 (by rw [hi]; exact hres)
    refine ⟨r, ?_, hex⟩
    dsimp only
    rw [show ∀ P : Nat, G + (88 + P) = G + P + 44 + 44 from fun P => by omega]
    refine rxc_ydTest_skip (j := 1) hF (by rw [hiw]; rfl) rfl List.not_mem_nil progYD_77
      (by omega) ?_
    rw [hi] at hrun
    exact rxc_ydCoinTail_next hF rfl rfl (by decide) List.not_mem_nil progYD_99 (by omega) hrun
  · have hne : i ≠ Nat.toB256 1 := fun h => hi (by rw [h]; decide)
    rw [ydCoinStep_ne hi] at hres ⊢
    rw [ite_eq_right hi]
    obtain ⟨⟨c', s'⟩, hacc, hres⟩ := Option.bind_eq_some_iff.mp hres
    rw [hacc]
    obtain ⟨ha1, hma, hmb, hda, -, -⟩ := ydAccN_inv hacc
    obtain ⟨rfl, rfl⟩ := ydAccN_words hacc
    simp only at hres ⊢
    have hF10 := hF.write (j := 10) (lt16 (by decide)) x1
    have hF8 := hF10.write (j := 8) (lt16 (by decide)) (s + x1)
    have hF7 := hF8.write (j := 7) (lt16 (by decide)) ((c * D) / (x1 * Bytes.toB256 [0x03]))
    have hF11 := hF7.write (j := 11) (lt16 (by decide)) (Nat.toB256 (1 + 1))
    obtain ⟨r, hrun, hex⟩ := ydStage2X (G := G) hi3 hroom hF11 hres
    refine ⟨r, ?_, hex⟩
    rw [show ∀ P : Nat, G + (417 + P) = G + P + 44 + 278 + 95 from fun P => by omega]
    refine rxc_ydTest_load hF rfl (by decide) rfl hne rfl rfl List.not_mem_nil progYD_76
      (by omega) ?_
    refine rxc_ydAcc hF10 rfl rfl rfl rfl rfl ha1 hma hmb hda hroom ?_
    exact rxc_ydCoinTail_next hF7 rfl rfl (by decide) List.not_mem_nil progYD_99 (by omega) hrun

-- SEGMENT: ydStage0X
/-- **Coin-loop iteration `0` and the rest**, forward. -/
theorem ydStage0X {A i x0 x1 x2 D ρ c s ann xv w12 w13 w14 w15 : B256} {y : Nat}
    (hi3 : i.toNat < 3) (hroom : S.length + 12 < 1024)
    (hF : WordFrame M0 M 0x140 (ydFrame A i x0 x1 x2 D ρ c s ann xv (Nat.toB256 0) w12 w13 w14
      w15))
    (hres : ((ydCoinStep i.toNat 0 x0.toNat D.toNat (c.toNat, s.toNat)).bind fun cs =>
      (ydCoinStep i.toNat 1 x1.toNat D.toNat cs).bind fun cs =>
        (ydCoinStep i.toNat 2 x2.toNat D.toNat cs).bind fun cs =>
          ydPostRes cs.1 cs.2 D.toNat ann.toNat) = some y) :
    ∃ r, SFunc.RunExactCut progYD sevm [] (St b (ydCStk S) M
      (G + ydCostFrom0 i.toNat x0.toNat x1.toNat x2.toNat D.toNat ann.toNat (c.toNat, s.toNat))) (ydTest 763 18) r ∧
      calleeExit b S M0 y G r := by
  unfold ydCostFrom0 ydCoinCost
  by_cases hi : i.toNat = 0
  · have hiw : i = Nat.toB256 0 := by rw [← hi, toB256_toNat]
    rw [hi, ydCoinStep_eq, Option.bind_some] at hres
    rw [hi, ydCoinStep_eq, ite_eq_left rfl]
    have hF11 := hF.write (j := 11) (lt16 (by decide)) (Nat.toB256 (0 + 1))
    obtain ⟨r, hrun, hex⟩ := ydStage1X (G := G) (by rw [hi]; decide) hroom hF11 (by rw [hi]; exact hres)
    refine ⟨r, ?_, hex⟩
    dsimp only
    rw [show ∀ P : Nat, G + (88 + P) = G + P + 44 + 44 from fun P => by omega]
    refine rxc_ydTest_skip (j := 0) hF (by rw [hiw]; rfl) rfl List.not_mem_nil progYD_18
      (by omega) ?_
    rw [hi] at hrun
    exact rxc_ydCoinTail_next hF rfl rfl (by decide) List.not_mem_nil progYD_49 (by omega) hrun
  · have hne : i ≠ Nat.toB256 0 := fun h => hi (by rw [h]; decide)
    rw [ydCoinStep_ne hi] at hres ⊢
    rw [ite_eq_right hi]
    obtain ⟨⟨c', s'⟩, hacc, hres⟩ := Option.bind_eq_some_iff.mp hres
    rw [hacc]
    obtain ⟨ha1, hma, hmb, hda, -, -⟩ := ydAccN_inv hacc
    obtain ⟨rfl, rfl⟩ := ydAccN_words hacc
    simp only at hres ⊢
    have hF10 := hF.write (j := 10) (lt16 (by decide)) x0
    have hF8 := hF10.write (j := 8) (lt16 (by decide)) (s + x0)
    have hF7 := hF8.write (j := 7) (lt16 (by decide)) ((c * D) / (x0 * Bytes.toB256 [0x03]))
    have hF11 := hF7.write (j := 11) (lt16 (by decide)) (Nat.toB256 (0 + 1))
    obtain ⟨r, hrun, hex⟩ := ydStage1X (G := G) hi3 hroom hF11 hres
    refine ⟨r, ?_, hex⟩
    rw [show ∀ P : Nat, G + (417 + P) = G + P + 44 + 278 + 95 from fun P => by omega]
    refine rxc_ydTest_load hF rfl (by decide) rfl hne rfl rfl List.not_mem_nil progYD_763
      (by omega) ?_
    refine rxc_ydAcc hF10 rfl rfl rfl rfl rfl ha1 hma hmb hda hroom ?_
    exact rxc_ydCoinTail_next hF7 rfl rfl (by decide) List.not_mem_nil progYD_49 (by omega) hrun

theorem slt_small {i : B256} (hi : i.toNat < 3) :
    B256.sltCheck i (Bytes.toB256 [0x00]) = 0 ∧ B256.sltCheck i (Bytes.toB256 [0x03]) = 1 := by
  have e : i = Nat.toB256 i.toNat := (toB256_toNat i).symm
  rw [e]
  generalize i.toNat = k at hi
  rcases k with _ | _ | _ | k
  · exact ⟨by decide, by decide⟩
  · exact ⟨by decide, by decide⟩
  · exact ⟨by decide, by decide⟩
  · omega

-- SEGMENT: rxc_ydPro
/-- **The prologue**, forward (233 gas): the arguments into the frame, the range checks of `i`,
`c = D`, `S_ = 0`, `Ann`, the coin-loop counter. -/
theorem rxc_ydPro {ρ A i x0 x1 x2 D : B256} (hsz : M.size % 32 = 0) (hcov : 0x340 ≤ M.size)
    (hi : i.toNat < 3) (hm : B256.Nofm A (Bytes.toB256 [0x03])) (hroom : S.length + 12 < 1024)
    {rest : SFunc} {M7 : Mem}
    (hM7 : M7 = (((((((((((M.write (0x140 + 32 * 6) ρ.toBytes).write (0x140 + 32 * 0)
      A.toBytes).write (0x140 + 32 * 1) i.toBytes).write (0x140 + 32 * 2) x0.toBytes).write
      (0x140 + 32 * 3) x1.toBytes).write (0x140 + 32 * 4) x2.toBytes).write (0x140 + 32 * 5)
      D.toBytes).write (0x140 + 32 * 7) D.toBytes).write (0x140 + 32 * 8)
      (Nat.toB256 0).toBytes).write (0x140 + 32 * 9) (A * Bytes.toB256 [0x03]).toBytes).write
      (0x140 + 32 * 10) (Nat.toB256 0).toBytes).write (0x140 + 32 * 11) (Nat.toB256 0).toBytes)
    (kk : WordFrame M M7 0x140 (ydFrame A i x0 x1 x2 D ρ D (Nat.toB256 0)
        (A * Bytes.toB256 [0x03]) (Nat.toB256 0) (Nat.toB256 0) (memWord M (0x140 + 32 * 12))
        (memWord M (0x140 + 32 * 13)) (memWord M (0x140 + 32 * 14))
        (memWord M (0x140 + 32 * 15))) →
      SFunc.RunExactCut progYD sevm [] (St b (ydCStk S) M7 G) rest r) :
    SFunc.RunExactCut progYD sevm [] (St b (ρ :: A :: i :: x0 :: x1 :: x2 :: D :: S) M (G + 233))
      (ydEntry rest) r := by
  have hF := WordFrame.init (lo := 0x140) (n := 16) hsz hcov
  have h6 := hF.write (j := 6) (lt16 (by decide)) ρ
  have h0 := h6.write (j := 0) (lt16 (by decide)) A
  have h1 := h0.write (j := 1) (lt16 (by decide)) i
  have h2 := h1.write (j := 2) (lt16 (by decide)) x0
  have h3 := h2.write (j := 3) (lt16 (by decide)) x1
  have h4 := h3.write (j := 4) (lt16 (by decide)) x2
  have h5 := h4.write (j := 5) (lt16 (by decide)) D
  have h7 := h5.write (j := 7) (lt16 (by decide)) D
  have h8 := h7.write (j := 8) (lt16 (by decide)) (Nat.toB256 0)
  have h9 := h8.write (j := 9) (lt16 (by decide)) (A * Bytes.toB256 [0x03])
  have h10 := h9.write (j := 10) (lt16 (by decide)) (Nat.toB256 0)
  have h11 := h10.write (j := 11) (lt16 (by decide)) (Nat.toB256 0)
  have kk' := kk (by rw [hM7]; exact h11)
  rw [hM7] at kk'
  obtain ⟨hs0, hs3⟩ := slt_small hi
  unfold ydEntry
  refine rxc_dest ?_
  refine rxc_pushMstoreF hF 6 (by decide) (lt16 (by decide)) (by room) ?_
  refine rxc_pushMstoreF h6 0 (by decide) (lt16 (by decide)) (by room) ?_
  refine rxc_pushMstoreF h0 1 (by decide) (lt16 (by decide)) (by room) ?_
  refine rxc_pushMstoreF h1 2 (by decide) (lt16 (by decide)) (by room) ?_
  refine rxc_pushMstoreF h2 3 (by decide) (lt16 (by decide)) (by room) ?_
  refine rxc_pushMstoreF h3 4 (by decide) (lt16 (by decide)) (by room) ?_
  refine rxc_pushMstoreF h4 5 (by decide) (lt16 (by decide)) (by room) ?_
  refine rxc_push rfl (by room) ?_
  refine rxc_pushMloadF h5 1 (by decide) rfl (by room) ?_
  refine rxc_binary (fn := B256.sltCheck) (c := gVerylow) (by rintro ⟨⟩) (fun _ => rfl) rfl
    (by room) ?_
  refine rxc_iszero rfl (by room) ?_
  refine rxc_push rfl (by room) ?_
  rw [hs0]
  refine rxc_branch_succ (by decide) (rxc_dest ?_)
  refine rxc_push rfl (by room) ?_
  refine rxc_pushMloadF h5 1 (by decide) rfl (by room) ?_
  refine rxc_binary (fn := B256.sltCheck) (c := gVerylow) (by rintro ⟨⟩) (fun _ => rfl) rfl
    (by room) ?_
  refine rxc_push rfl (by room) ?_
  rw [hs3]
  refine rxc_branch_succ (by decide) (rxc_dest ?_)
  refine rxc_pushMloadF h5 5 (by decide) rfl (by room) ?_
  refine rxc_pushMstoreF h5 7 (by decide) (lt16 (by decide)) (by room) ?_
  refine rxc_push toB256_zero (by room) ?_
  refine rxc_pushMstoreF h7 8 (by decide) (lt16 (by decide)) (by room) ?_
  refine rxc_pushMloadF h8 0 (by decide) rfl (by room) ?_
  refine rxc_push rfl (by room) ?_
  refine rxc_vyMulT hm (by room) ?_
  refine rxc_pushMstoreF h8 9 (by decide) (lt16 (by decide)) (by room) ?_
  refine rxc_push toB256_zero (by room) ?_
  refine rxc_pushMstoreF h9 10 (by decide) (lt16 (by decide)) (by room) ?_
  refine rxc_push toB256_0x2a0 (by room) ?_
  refine rxc_push toB256_zero (by room) ?_
  refine rxc_push rfl (by room) ?_
  refine rxc_dup (w := Nat.toB256 0) rfl (by room) ?_
  refine rxc_dup (w := Nat.toB256 0x2a0) rfl (by room) ?_
  refine rxc_mstoreF h10 11 (by decide) (lt16 (by decide)) ?_
  refine rxc_add' (show Bytes.toB256 [0x03] + Nat.toB256 0 = Nat.toB256 3 by decide) (by room) ?_
  exact kk'

theorem ydPro_frame {ρ A i x0 x1 x2 D : B256} (hsz : M.size % 32 = 0) (hcov : 0x340 ≤ M.size) :
    WordFrame M ((((((((((((M.write (0x140 + 32 * 6) ρ.toBytes).write (0x140 + 32 * 0)
      A.toBytes).write (0x140 + 32 * 1) i.toBytes).write (0x140 + 32 * 2) x0.toBytes).write
      (0x140 + 32 * 3) x1.toBytes).write (0x140 + 32 * 4) x2.toBytes).write (0x140 + 32 * 5)
      D.toBytes).write (0x140 + 32 * 7) D.toBytes).write (0x140 + 32 * 8)
      (Nat.toB256 0).toBytes).write (0x140 + 32 * 9) (A * Bytes.toB256 [0x03]).toBytes).write
      (0x140 + 32 * 10) (Nat.toB256 0).toBytes).write (0x140 + 32 * 11) (Nat.toB256 0).toBytes)
      0x140 (ydFrame A i x0 x1 x2 D ρ D (Nat.toB256 0)
        (A * Bytes.toB256 [0x03]) (Nat.toB256 0) (Nat.toB256 0) (memWord M (0x140 + 32 * 12))
        (memWord M (0x140 + 32 * 13)) (memWord M (0x140 + 32 * 14))
        (memWord M (0x140 + 32 * 15))) := by
  have hF := WordFrame.init (lo := 0x140) (n := 16) hsz hcov
  have h6 := hF.write (j := 6) (lt16 (by decide)) ρ
  have h0 := h6.write (j := 0) (lt16 (by decide)) A
  have h1 := h0.write (j := 1) (lt16 (by decide)) i
  have h2 := h1.write (j := 2) (lt16 (by decide)) x0
  have h3 := h2.write (j := 3) (lt16 (by decide)) x1
  have h4 := h3.write (j := 4) (lt16 (by decide)) x2
  have h5 := h4.write (j := 5) (lt16 (by decide)) D
  have h7 := h5.write (j := 7) (lt16 (by decide)) D
  have h8 := h7.write (j := 8) (lt16 (by decide)) (Nat.toB256 0)
  have h9 := h8.write (j := 9) (lt16 (by decide)) (A * Bytes.toB256 [0x03])
  have h10 := h9.write (j := 10) (lt16 (by decide)) (Nat.toB256 0)
  exact h10.write (j := 11) (lt16 (by decide)) (Nat.toB256 0)

end Fwd

/-! ## The contract, forward -/

/-- **`get_y_D`'s gas**: the prologue, the three coin-loop iterations, the set-up and the `y`
loop's recursive charge, on the model's naturals (`0` where the model reverts). -/
def costGetYD (amp i x0 x1 x2 D : Nat) : Nat :=
  233 + match chkMul amp 3 with
    | some ann => ydCostFrom0 i x0 x1 x2 D ann (D, 0)
    | none => 0

-- SEGMENT: getYD_exact
/-- **`get_y_D`'s forward twin.**  When the checked model returns `v`, the entry tree runs from the
call's state with `costGetYD` gas over `G` to its return of `v` over the caller's stack with `G`
left, the memory changed only in `get_y_D`'s windows (`ScratchOut`). -/
theorem getYD_exact {sevm : Sevm} {b : Devm} {ρ A i x0 x1 x2 D : B256} {S : List B256} {M : Mem}
    {G v : Nat} (hsz : M.size % 32 = 0) (hcov : 0x340 ≤ M.size) (hroom : S.length + 12 < 1024)
    (hi : i.toNat < 3)
    (hres : getYDChk A.toNat ⟨i.toNat, hi⟩ (V3.mk x0.toNat x1.toNat x2.toNat).get D.toNat =
      some v) :
    ∃ M', ScratchOut M M' 0x140 0x340 (Nat.toB256 v) ∧
      SFunc.RunExact cert.prog sevm (St b (ρ :: A :: i :: x0 :: x1 :: x2 :: D :: S) M
        (G + costGetYD A.toNat i.toNat x0.toNat x1.toNat x2.toNat D.toNat)) t_3999_c753
        (.returned (St b (Nat.toB256 v :: S) M' G)) := by
  obtain ⟨ann, hann, hyd⟩ := getYDChk_ydRes hi hres
  obtain ⟨hm, rfl⟩ := chkMul_inv (x := A) (y := Bytes.toB256 [0x03])
    (by rw [show (Bytes.toB256 [0x03]).toNat = 3 by decide]; exact hann)
  have hF := ydPro_frame (ρ := ρ) (A := A) (i := i) (x0 := x0) (x1 := x1) (x2 := x2) (D := D)
    hsz hcov
  have hyd' : ((ydCoinStep i.toNat 0 x0.toNat D.toNat (D.toNat, (Nat.toB256 0).toNat)).bind
      fun cs => (ydCoinStep i.toNat 1 x1.toNat D.toNat cs).bind fun cs =>
        (ydCoinStep i.toNat 2 x2.toNat D.toNat cs).bind fun cs =>
          ydPostRes cs.1 cs.2 D.toNat (A * Bytes.toB256 [0x03]).toNat) = some v := by
    rw [show (Nat.toB256 0).toNat = 0 by decide]; exact hyd
  obtain ⟨r, hrun, M', hr, hout⟩ := ydStage0X (G := G) hi hroom hF hyd'
  subst hr
  refine ⟨M', hout, ?_⟩
  apply SFunc.runExact_iff_runExactCut_nil.mpr
  rw [t_3999_c753_eq]
  unfold costGetYD
  rw [show chkMul A.toNat 3 = some (A * Bytes.toB256 [0x03]).toNat from hann]
  dsimp only
  rw [show (Nat.toB256 0).toNat = 0 by decide] at hrun
  rw [show G + (233 + ydCostFrom0 i.toNat x0.toNat x1.toNat x2.toNat D.toNat
    (A * Bytes.toB256 [0x03]).toNat (D.toNat, 0)) = (G + ydCostFrom0 i.toNat x0.toNat x1.toNat
    x2.toNat D.toNat (A * Bytes.toB256 [0x03]).toNat (D.toNat, 0)) + 233 by omega]
  exact rxc_ydPro hsz hcov hi hm hroom rfl (fun _ => hrun)


end Blanc.Lift.Curve3Pool
