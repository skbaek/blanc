import Blanc.Lift.Curve3Pool.Callee.GetD
import Blanc.Lift.Curve3Pool.Callee.GetYDExact

/-!
# `get_D`, forward: exact gas

The forward twins of `GetDLoop.lean`/`GetD.lean`: from the checked model's success, the entry tree
runs to its return with exact gas.  A Newton pass is the outer head (`34`), three inner `D_P`
iterations (`277` each, with their `JUMPI`), and the rest of the body (`625`) with its stopping
test, so `gdStepC`/`gdStopC`/`gdCapC` by the direction of the step; the whole loop is the
recursive `fuelCost` over them.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune
open Blanc.StableSwapNewton

/-- The inner `D_P` loop's word, step by step. -/
abbrev gdP (p d x : B256) : B256 := (p * d) / (x * Bytes.toB256 [0x03])

theorem gdPStep_inv {p d x : B256} {p' : Nat} (h : gdPStep p.toNat d.toNat x.toNat = some p') :
    B256.Nofm p d ∧ B256.Nofm x (Bytes.toB256 [0x03]) ∧ x * Bytes.toB256 [0x03] ≠ 0 ∧
      p' = (gdP p d x).toNat := by
  have e3 : (3 : Nat) = (Bytes.toB256 [0x03]).toNat := by decide
  unfold gdPStep at h
  rw [e3] at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨m1, h1, m2, h2, h3⟩ := h
  obtain ⟨hm1, rfl⟩ := chkMul_inv h1
  obtain ⟨hm2, rfl⟩ := chkMul_inv h2
  obtain ⟨hd, rfl⟩ := chkDiv_inv h3
  exact ⟨hm1, hm2, hd, rfl⟩

theorem dPChk_steps {x0 x1 x2 : B256} {D p : Nat} (h : dPChk (gdX x0 x1 x2) D = some p) :
    ∃ p0 p1, gdPStep D D x0.toNat = some p0 ∧ gdPStep p0 D x1.toNat = some p1 ∧
      gdPStep p1 D x2.toNat = some p := by
  unfold dPChk at h
  rw [show gdX x0 x1 x2 0 = x0.toNat from rfl, show gdX x0 x1 x2 1 = x1.toNat from rfl,
    show gdX x0 x1 x2 2 = x2.toNat from rfl] at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨m1, h1, m2, h2, p0, h3, m3, h4, m4, h5, p1, h6, m5, h7, m6, h8, h9⟩ := h
  refine ⟨p0, p1, ?_, ?_, ?_⟩
  · unfold gdPStep; simp only [Option.bind_eq_bind, h1, h2, Option.bind_some, h3]
  · unfold gdPStep; simp only [Option.bind_eq_bind, h4, h5, Option.bind_some, h6]
  · unfold gdPStep; simp only [Option.bind_eq_bind, h7, h8, Option.bind_some, h9]

theorem bodyDChk_inv {x : Fin 3 → Nat} {ann s p dw : B256} {D' : Nat}
    (hdp : dPChk x dw.toNat = some p.toNat)
    (h : bodyDChk x ann.toNat s.toNat dw.toNat = some D') :
    B256.Nofm ann s ∧ B256.Nofm p (Bytes.toB256 [0x03]) ∧
      (ann * s).toNat + (p * Bytes.toB256 [0x03]).toNat < 2 ^ 256 ∧
      B256.Nofm (ann * s + p * Bytes.toB256 [0x03]) dw ∧
      (Bytes.toB256 [0x01]).toNat ≤ ann.toNat ∧ B256.Nofm (ann - Bytes.toB256 [0x01]) dw ∧
      B256.Nofm (Bytes.toB256 [0x04]) p ∧
      ((ann - Bytes.toB256 [0x01]) * dw).toNat + (Bytes.toB256 [0x04] * p).toNat < 2 ^ 256 ∧
      (ann - Bytes.toB256 [0x01]) * dw + Bytes.toB256 [0x04] * p ≠ 0 ∧
      D' = (((ann * s + p * Bytes.toB256 [0x03]) * dw) /
        ((ann - Bytes.toB256 [0x01]) * dw + Bytes.toB256 [0x04] * p)).toNat := by
  have e3 : (3 : Nat) = (Bytes.toB256 [0x03]).toNat := by decide
  have e1 : (1 : Nat) = (Bytes.toB256 [0x01]).toNat := by decide
  have e4 : (4 : Nat) = (Bytes.toB256 [0x04]).toNat := by decide
  unfold bodyDChk at h
  rw [hdp, e3, e1, e4] at h
  simp only [Option.bind_eq_bind, Option.bind_some, Option.bind_eq_some_iff] at h
  obtain ⟨m1, h1, m2, h2, a1, h3, num, h4, s1, h5, m3, h6, m4, h7, den, h8, h9⟩ := h
  obtain ⟨hm1, rfl⟩ := chkMul_inv h1
  obtain ⟨hm2, rfl⟩ := chkMul_inv h2
  obtain ⟨ha1, rfl⟩ := chkAdd_inv h3
  obtain ⟨hm3, rfl⟩ := chkMul_inv h4
  obtain ⟨hs, rfl⟩ := chkSub_inv h5
  obtain ⟨hm4, rfl⟩ := chkMul_inv h6
  obtain ⟨hm5, rfl⟩ := chkMul_inv h7
  obtain ⟨ha2, rfl⟩ := chkAdd_inv h8
  obtain ⟨hdv, rfl⟩ := chkDiv_inv h9
  exact ⟨hm1, hm2, ha1, hm3, hs, hm4, hm5, ha2, hdv, rfl⟩

section Fwd

variable {sevm : Sevm} {C : List Nat} {b : Devm} {S : List B256} {M0 M : Mem} {G : Nat}
  {r : Seg} {ws : List B256}

-- SEGMENT: rxc_gdInner
/-- **One inner `D_P` iteration**, forward up to its `JUMPI` (267 gas). -/
theorem rxc_gdInner (hF : WordFrame M0 M 0x140 ws) (hlen : ws.length = 16) {j : Nat}
    {x p d : B256} (hj : ws[15]? = some (Nat.toB256 j)) (hj3 : j < 3) (hx : ws[j]? = some x)
    (hp : ws[13]? = some p) (hd : ws[10]? = some d) (hm1 : B256.Nofm p d)
    (hm2 : B256.Nofm x (Bytes.toB256 [0x03])) (hdv : x * Bytes.toB256 [0x03] ≠ 0)
    (hroom : S.length + 16 < 1024) {jmp : SFunc}
    (kk : SFunc.RunExactCut progYD sevm C (St b (Bytes.toB256 [0x05, 0xa0] ::
      B256.eqCheck (B256.eqCheck (Nat.toB256 3) (Nat.toB256 (j + 1))) 0 :: gdIStk S)
      (((M.write (0x140 + 32 * 14) x.toBytes).write (0x140 + 32 * 13)
        ((p * d) / (x * Bytes.toB256 [0x03])).toBytes).write (0x140 + 32 * 15)
        (Nat.toB256 (j + 1)).toBytes) G) jmp r) :
    SFunc.RunExactCut progYD sevm C (St b (gdIStk S) M (G + 267)) (gdInner jmp) r := by
  have h14 := hF.write (j := 14) (by rw [hlen]; decide) x
  have h13 := h14.write (j := 13) (by rw [List.length_set, hlen]; decide)
    ((p * d) / (x * Bytes.toB256 [0x03]))
  have hp1 : (ws.set 14 x)[13]? = some p := by rw [List.getElem?_set_ne (by decide)]; exact hp
  have hd1 : (ws.set 14 x)[10]? = some d := by rw [List.getElem?_set_ne (by decide)]; exact hd
  have hx1 : (ws.set 14 x)[14]? = some x := by
    rw [List.getElem?_set_self (by rw [hlen]; decide)]
  have hj2 : ((ws.set 14 x).set 13 ((p * d) / (x * Bytes.toB256 [0x03])))[15]? =
      some (Nat.toB256 j) := by
    rw [List.getElem?_set_ne (by decide), List.getElem?_set_ne (by decide)]; exact hj
  unfold gdInner
  refine rxc_dest ?_
  refine rxc_push rfl (by room) ?_
  refine rxc_pushMloadF hF 15 (by decide) hj (by room) ?_
  refine rxc_binary (fn := (· * ·)) (c := gLow) (by rintro ⟨⟩) (fun _ => rfl) rfl (by room) ?_
  refine rxc_push rfl (by room) ?_
  refine rxc_add (by room) ?_
  refine rxc_mloadF hF j (gdXpAddr hj3) hx (by room) ?_
  refine rxc_pushMstoreF hF 14 (by decide) (by rw [hlen]; decide) (by room) ?_
  refine rxc_pushMloadF h14 13 (by decide) hp1 (by room) ?_
  refine rxc_pushMloadF h14 10 (by decide) hd1 (by room) ?_
  refine rxc_vyMulT hm1 (by room) ?_
  refine rxc_pushMloadF h14 14 (by decide) hx1 (by room) ?_
  refine rxc_push rfl (by room) ?_
  refine rxc_vyMulT hm2 (by room) ?_
  refine rxc_vyDivT hdv (by room) ?_
  refine rxc_pushMstoreF h14 13 (by decide) (by rw [List.length_set, hlen]; decide) (by room) ?_
  refine rxc_dest ?_
  refine rxc_dup (w := Nat.toB256 0x320) rfl (by room) ?_
  refine rxc_mloadF h13 15 (by decide) hj2 (by room) ?_
  refine rxc_push rfl (by room) ?_
  refine rxc_add' (one_add_toB256 (by omega)) (by room) ?_
  refine rxc_dup (w := Nat.toB256 (j + 1)) rfl (by room) ?_
  refine rxc_dup (w := Nat.toB256 0x320) rfl (by room) ?_
  refine rxc_mstoreF h13 15 (by decide) (by rw [List.length_set, List.length_set, hlen]; decide) ?_
  refine rxc_dup (w := Nat.toB256 3) rfl (by room) ?_
  refine rxc_eq rfl (by room) ?_
  refine rxc_iszero rfl (by room) ?_
  exact rxc_push rfl (by room) kk

-- SEGMENT: rxc_gdHeadPre
/-- **The outer head up to the inner loop**, forward (34 gas). -/
theorem rxc_gdHeadPre (hF : WordFrame M0 M 0x140 ws) (hlen : ws.length = 16) {d : B256}
    (hd : ws[10]? = some d) (hroom : S.length + 16 < 1024) {jmp : SFunc}
    (kk : SFunc.RunExactCut progYD sevm C (St b (gdIStk S)
      ((M.write (0x140 + 32 * 13) d.toBytes).write (0x140 + 32 * 15) (Nat.toB256 0).toBytes) G)
      (gdInner jmp) r) :
    SFunc.RunExactCut progYD sevm C (St b (gdStk S) M (G + 34)) (gdHead jmp) r := by
  have h13 := hF.write (j := 13) (by rw [hlen]; decide) d
  unfold gdHead
  refine rxc_dest ?_
  refine rxc_pushMloadF hF 10 (by decide) hd (by room) ?_
  refine rxc_pushMstoreF hF 13 (by decide) (by rw [hlen]; decide) (by room) ?_
  refine rxc_push toB256_0x320 (by room) ?_
  refine rxc_push toB256_zero (by room) ?_
  refine rxc_push rfl (by room) ?_
  refine rxc_dup (w := Nat.toB256 0) rfl (by room) ?_
  refine rxc_dup (w := Nat.toB256 0x320) rfl (by room) ?_
  refine rxc_mstoreF h13 15 (by decide) (by rw [List.length_set, hlen]; decide) ?_
  refine rxc_add' (show Bytes.toB256 [0x03] + Nat.toB256 0 = Nat.toB256 3 by decide) (by room) ?_
  exact kk

-- SEGMENT: rxc_gdRestPre
/-- **The rest of a Newton pass up to its stopping test**, forward (625 gas). -/
theorem rxc_gdRestPre (hF : WordFrame M0 M 0x140 ws) (hlen : ws.length = 16)
    {dw ann s p : B256} (hd : ws[10]? = some dw) (ha : ws[11]? = some ann)
    (hs5 : ws[5]? = some s) (hp : ws[13]? = some p)
    (hm1 : B256.Nofm ann s) (hm2 : B256.Nofm p (Bytes.toB256 [0x03]))
    (ha1 : (ann * s).toNat + (p * Bytes.toB256 [0x03]).toNat < 2 ^ 256)
    (hm3 : B256.Nofm (ann * s + p * Bytes.toB256 [0x03]) dw)
    (hs : (Bytes.toB256 [0x01]).toNat ≤ ann.toNat)
    (hm4 : B256.Nofm (ann - Bytes.toB256 [0x01]) dw)
    (hm5 : B256.Nofm (Bytes.toB256 [0x04]) p)
    (ha2 : ((ann - Bytes.toB256 [0x01]) * dw).toNat + (Bytes.toB256 [0x04] * p).toNat < 2 ^ 256)
    (hdv : (ann - Bytes.toB256 [0x01]) * dw + Bytes.toB256 [0x04] * p ≠ 0)
    (hroom : S.length + 16 < 1024) {e t k : Nat} {fall : SFunc}
    (kk : SFunc.RunExactCut progYD sevm C (St b (Bytes.toB256 [0x07, 0x5f] ::
      B256.eqCheck (B256.gtCheck (((ann * s + p * Bytes.toB256 [0x03]) * dw) /
        ((ann - Bytes.toB256 [0x01]) * dw + Bytes.toB256 [0x04] * p)) dw) 0 :: gdStk S)
      ((M.write (0x140 + 32 * 9) dw.toBytes).write (0x140 + 32 * 10)
        (((ann * s + p * Bytes.toB256 [0x03]) * dw) /
          ((ann - Bytes.toB256 [0x01]) * dw + Bytes.toB256 [0x04] * p)).toBytes) G)
      (gdRestBr e t k fall) r) :
    SFunc.RunExactCut progYD sevm C (St b (gdIStk S) M (G + 625)) (gdRest e t k fall) r := by
  have h9 := hF.write (j := 9) (by rw [hlen]; decide) dw
  have h10 := h9.write (j := 10) (by rw [List.length_set, hlen]; decide)
    (((ann * s + p * Bytes.toB256 [0x03]) * dw) /
      ((ann - Bytes.toB256 [0x01]) * dw + Bytes.toB256 [0x04] * p))
  have hd9 : (ws.set 9 dw)[10]? = some dw := by rw [List.getElem?_set_ne (by decide)]; exact hd
  have ha9 : (ws.set 9 dw)[11]? = some ann := by rw [List.getElem?_set_ne (by decide)]; exact ha
  have hs9 : (ws.set 9 dw)[5]? = some s := by rw [List.getElem?_set_ne (by decide)]; exact hs5
  have hp9 : (ws.set 9 dw)[13]? = some p := by rw [List.getElem?_set_ne (by decide)]; exact hp
  have hd10 : ((ws.set 9 dw).set 10 (((ann * s + p * Bytes.toB256 [0x03]) * dw) /
      ((ann - Bytes.toB256 [0x01]) * dw + Bytes.toB256 [0x04] * p)))[9]? = some dw := by
    rw [List.getElem?_set_ne (by decide), List.getElem?_set_self (by rw [hlen]; decide)]
  have hq10 : ((ws.set 9 dw).set 10 (((ann * s + p * Bytes.toB256 [0x03]) * dw) /
      ((ann - Bytes.toB256 [0x01]) * dw + Bytes.toB256 [0x04] * p)))[10]? =
      some (((ann * s + p * Bytes.toB256 [0x03]) * dw) /
        ((ann - Bytes.toB256 [0x01]) * dw + Bytes.toB256 [0x04] * p)) := by
    rw [List.getElem?_set_self (by rw [List.length_set, hlen]; decide)]
  unfold gdRest
  refine rxc_dest (rxc_pop (rxc_pop ?_))
  refine rxc_pushMloadF hF 10 (by decide) hd (by room) ?_
  refine rxc_pushMstoreF hF 9 (by decide) (by rw [hlen]; decide) (by room) ?_
  refine rxc_pushMloadF h9 11 (by decide) ha9 (by room) ?_
  refine rxc_pushMloadF h9 5 (by decide) hs9 (by room) ?_
  refine rxc_vyMulT hm1 (by room) ?_
  refine rxc_pushMloadF h9 13 (by decide) hp9 (by room) ?_
  refine rxc_push rfl (by room) ?_
  refine rxc_vyMulT hm2 (by room) ?_
  refine rxc_vyAddT ha1 (by room) ?_
  refine rxc_pushMloadF h9 10 (by decide) hd9 (by room) ?_
  refine rxc_vyMulT hm3 (by room) ?_
  refine rxc_pushMloadF h9 11 (by decide) ha9 (by room) ?_
  refine rxc_push rfl (by room) ?_
  refine rxc_vySubT hs (by room) ?_
  refine rxc_pushMloadF h9 10 (by decide) hd9 (by room) ?_
  refine rxc_vyMulT hm4 (by room) ?_
  refine rxc_push rfl (by room) ?_
  refine rxc_pushMloadF h9 13 (by decide) hp9 (by room) ?_
  refine rxc_vyMulT hm5 (by room) ?_
  refine rxc_vyAddT ha2 (by room) ?_
  refine rxc_vyDivT hdv (by room) ?_
  refine rxc_pushMstoreF h9 10 (by decide) (by rw [List.length_set, hlen]; decide) (by room) ?_
  refine rxc_pushMloadF h10 9 (by decide) hd10 (by room) ?_
  refine rxc_pushMloadF h10 10 (by decide) hq10 (by room) ?_
  refine rxc_binary (fn := B256.gtCheck) (c := gVerylow) (by rintro ⟨⟩) (fun _ => rfl) rfl
    (by room) ?_
  refine rxc_iszero rfl (by room) ?_
  exact rxc_push rfl (by room) kk
-- SEGMENT: rxc_gdExit
/-- **The exit**, forward (37 gas). -/
theorem rxc_gdExit (hF : WordFrame M0 M 0x140 ws) (hlen : ws.length = 16) {yw ρ : B256}
    (hy : ws[10]? = some yw) (hρ : ws[4]? = some ρ) (hroom : S.length + 4 < 1024) :
    ∃ M', ScratchOut M0 M' 0x140 0x340 yw ∧
      SFunc.RunExactCut progYD sevm C (St b (gdStk S) M (G + 37)) gdExit
        (.done (.returned (St b (yw :: S) M' G))) := by
  obtain ⟨hout, hw⟩ := hF.scratch (by decide) yw
  rw [hlen] at hout
  obtain ⟨hsz, hcov⟩ := frame_size_pos hF hlen
  have hsz1 : (M.write 0 yw.toBytes).size % 32 = 0 := by rw [hout.size]; exact hF.aligned
  have hcov1 : 0x340 ≤ (M.write 0 yw.toBytes).size := by
    rw [hout.size, ← hF.size]; exact hcov
  refine ⟨_, hout, ?_⟩
  unfold gdExit
  refine rxc_dest (rxc_pop (rxc_pop ?_))
  refine rxc_pushMloadF hF 10 (by decide) hy (by omega) ?_
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
  have e200 : (Bytes.toB256 [0x01, 0xc0]).toNat = 0x140 + 32 * 4 := by decide
  refine rxc_mload (c := 3) (i := Bytes.toB256 [0x01, 0xc0]) (v := ρ) (mload_covered_cost' hsz1
    (by rw [e200]; omega)) (by rw [e200]; exact hw 4 ρ hρ)
    (read_covered rfl hsz1 (by rw [e200]; omega)) (by room) ?_
  exact rxc_ret

-- SEGMENT: rxc_gdTail
/-- **The counter tail**, forward, re-entering the cut head (45 gas). -/
theorem rxc_gdTail_next (hF : WordFrame M0 M 0x140 ws) (hlen : ws.length = 16) {n k : Nat}
    {fall : SFunc} (hn : ws[12]? = some (Nat.toB256 n)) (hn1 : n + 1 < 255) (hk : k ∈ C)
    (hroom : S.length + 8 < 1024) :
    SFunc.RunExactCut progYD sevm C (St b (gdStk S) M (G + 45)) (gdTail k fall)
      (.at k (St b (gdStk S) (M.write (0x140 + 32 * 12) (Nat.toB256 (n + 1)).toBytes) G)) := by
  unfold gdTail
  refine rxc_dest (rxc_dest ?_)
  refine rxc_dup (w := Nat.toB256 0x2c0) rfl (by room) ?_
  refine rxc_mloadF hF 12 (by decide) hn (by room) ?_
  refine rxc_push rfl (by room) ?_
  refine rxc_add' (one_add_toB256 (by omega)) (by room) ?_
  refine rxc_dup (w := Nat.toB256 (n + 1)) rfl (by room) ?_
  refine rxc_dup (w := Nat.toB256 0x2c0) rfl (by room) ?_
  refine rxc_mstoreF hF 12 (by decide) (by rw [hlen]; decide) ?_
  refine rxc_dup (w := Nat.toB256 255) rfl (by room) ?_
  refine rxc_eq rfl (by room) ?_
  refine rxc_iszero rfl (by room) ?_
  refine rxc_push rfl (by room) ?_
  exact rxc_branchTo_cut (iszero_eq255_ne (by omega) (by omega)) hk

/-- **The counter tail**, forward, falling through after the last pass (45 gas). -/
theorem rxc_gdTail_last (hF : WordFrame M0 M 0x140 ws) (hlen : ws.length = 16) {n k : Nat}
    {fall : SFunc} (hn : ws[12]? = some (Nat.toB256 n)) (hn1 : n + 1 = 255)
    (hroom : S.length + 8 < 1024)
    (kk : SFunc.RunExactCut progYD sevm C
      (St b (gdStk S) (M.write (0x140 + 32 * 12) (Nat.toB256 (n + 1)).toBytes) G) fall r) :
    SFunc.RunExactCut progYD sevm C (St b (gdStk S) M (G + 45)) (gdTail k fall) r := by
  unfold gdTail
  refine rxc_dest (rxc_dest ?_)
  refine rxc_dup (w := Nat.toB256 0x2c0) rfl (by room) ?_
  refine rxc_mloadF hF 12 (by decide) hn (by room) ?_
  refine rxc_push rfl (by room) ?_
  refine rxc_add' (one_add_toB256 (by omega)) (by room) ?_
  refine rxc_dup (w := Nat.toB256 (n + 1)) rfl (by room) ?_
  refine rxc_dup (w := Nat.toB256 0x2c0) rfl (by room) ?_
  refine rxc_mstoreF hF 12 (by decide) (by rw [hlen]; decide) ?_
  refine rxc_dup (w := Nat.toB256 255) rfl (by room) ?_
  refine rxc_eq rfl (by room) ?_
  refine rxc_iszero rfl (by room) ?_
  refine rxc_push rfl (by room) ?_
  have hw : B256.eqCheck (B256.eqCheck (Nat.toB256 255) (Nat.toB256 (n + 1))) 0 = 0 := by
    rw [hn1]; decide
  rw [hw]
  exact rxc_branchTo_zero kk

-- SEGMENT: rxc_gdRestBr
/-- **The stopping test, stopping**, forward: on to the exit `e`. -/
theorem rxc_gdRestBr_close (hF : WordFrame M0 M 0x140 ws) {yw q : B256} {e t k : Nat}
    {fall : SFunc} (h13 : ws[9]? = some yw) (h14 : ws[10]? = some q)
    (hc : closeEnough 1 q.toNat yw.toNat) (he : progYD[e]? = some gdExit) (heC : e ∉ C)
    (hroom : S.length + 12 < 1024)
    (kk : SFunc.RunExactCut progYD sevm C (St b (gdStk S) M G) gdExit r) :
    SFunc.RunExactCut progYD sevm C (St b (Bytes.toB256 [0x07, 0x5f] ::
      B256.eqCheck (B256.gtCheck q yw) 0 :: gdStk S) M
      (G + if yw.toNat < q.toNat then 103 else 104)) (gdRestBr e t k fall) r := by
  unfold gdRestBr
  have h1 : (Bytes.toB256 [0x01]).toNat = 1 := by decide
  by_cases hgt : yw.toNat < q.toNat
  · rw [ite_eq_left hgt, gtCheck_toNat, ite_eq_left hgt]
    refine rxc_branch_zero (d := Bytes.toB256 [0x07, 0x5f]) ?_
    refine rxc_push rfl (by room) ?_
    refine rxc_pushMloadF hF 10 (by decide) h14 (by room) ?_
    refine rxc_pushMloadF hF 9 (by decide) h13 (by room) ?_
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
    refine rxc_branch_zero (d := Bytes.toB256 [0x07, 0x5a]) ?_
    refine rxc_push rfl (by room) ?_
    exact rxc_jump he heC kk
  · rw [ite_eq_right hgt, gtCheck_toNat, ite_eq_right hgt]
    refine rxc_branch_succ (by decide) (rxc_dest ?_)
    refine rxc_push rfl (by room) ?_
    refine rxc_pushMloadF hF 9 (by decide) h13 (by room) ?_
    refine rxc_pushMloadF hF 10 (by decide) h14 (by room) ?_
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
    refine rxc_branch_zero (d := Bytes.toB256 [0x07, 0x89]) ?_
    refine rxc_push rfl (by room) ?_
    exact rxc_jump he heC kk

/-- **The stopping test, going on**, forward: on to the counter tail. -/
theorem rxc_gdRestBr_next (hF : WordFrame M0 M 0x140 ws) {yw q : B256} {e t k : Nat}
    {fall fall' : SFunc} (h13 : ws[9]? = some yw) (h14 : ws[10]? = some q)
    (hnc : ¬ closeEnough 1 q.toNat yw.toNat) (ht : progYD[t]? = some (gdTail k fall'))
    (htC : t ∉ C) (hroom : S.length + 12 < 1024)
    (kA : yw.toNat < q.toNat →
      SFunc.RunExactCut progYD sevm C (St b (gdStk S) M G) (gdTail k fall') r)
    (kB : ¬ yw.toNat < q.toNat →
      SFunc.RunExactCut progYD sevm C (St b (gdStk S) M G) (gdTail k fall) r) :
    SFunc.RunExactCut progYD sevm C (St b (Bytes.toB256 [0x07, 0x5f] ::
      B256.eqCheck (B256.gtCheck q yw) 0 :: gdStk S) M
      (G + if yw.toNat < q.toNat then 104 else 94)) (gdRestBr e t k fall) r := by
  unfold gdRestBr
  have h1 : (Bytes.toB256 [0x01]).toNat = 1 := by decide
  by_cases hgt : yw.toNat < q.toNat
  · rw [ite_eq_left hgt, gtCheck_toNat, ite_eq_left hgt]
    refine rxc_branch_zero (d := Bytes.toB256 [0x07, 0x5f]) ?_
    refine rxc_push rfl (by room) ?_
    refine rxc_pushMloadF hF 10 (by decide) h14 (by room) ?_
    refine rxc_pushMloadF hF 9 (by decide) h13 (by room) ?_
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
    refine rxc_pushMloadF hF 9 (by decide) h13 (by room) ?_
    refine rxc_pushMloadF hF 10 (by decide) h14 (by room) ?_
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

/-- What the head and the inner loop of a copy `f` of the Newton pass do, forward: from the head
state with `dPChk` succeeding, three inner iterations (865 gas) bring the run to the rest of the
pass `rest` with `D_P` the model's. -/
def GdInner (C : List Nat) (b : Devm) (S : List B256) (M0 : Mem) (x0 x1 x2 ρ s ann : B256)
    (f rest : SFunc) : Prop :=
  ∀ (M : Mem) (G : Nat) (amp xs sc w8 dp p xv ic : B256) (D n pN : Nat), D < 2 ^ 256 →
    S.length + 16 < 1024 →
    WordFrame M0 M 0x140 (gdFrame x0 x1 x2 amp ρ s xs sc w8 dp (Nat.toB256 D) ann (Nat.toB256 n)
      p xv ic) →
    dPChk (gdX x0 x1 x2) D = some pN →
    ∃ M3 pw, pw.toNat = pN ∧ WordFrame M0 M3 0x140 (gdFrame x0 x1 x2 amp ρ s xs sc w8 dp
      (Nat.toB256 D) ann (Nat.toB256 n) pw x2 (Nat.toB256 3)) ∧
      ∀ r, SFunc.RunExactCut progYD sevm C (St b (gdIStk S) M3 G) rest r →
        SFunc.RunExactCut progYD sevm C (St b (gdStk S) M (G + 865)) f r

-- SEGMENT: gdInner_533
theorem gdInner_533 {x0 x1 x2 ρ s ann : B256} :
    GdInner (sevm := sevm) [533] b S M0 x0 x1 x2 ρ s ann (gdHead (.branchTo .undefined 517))
      (gdRest 531 532 533 gdExit) := by
  intro M G amp xs sc w8 dp p xv ic D n pN hD hroom hF hdp
  obtain ⟨p0, p1, h0, h1, h2⟩ := dPChk_steps hdp
  have hDN : (Nat.toB256 D).toNat = D := B256.toNat_toB256_of_lt hD
  rw [← hDN] at h0 h1 h2
  obtain ⟨hm1, hm2, hdv, rfl⟩ := gdPStep_inv (p := Nat.toB256 D) h0
  obtain ⟨hm3, hm4, hdv2, rfl⟩ := gdPStep_inv h1
  obtain ⟨hm5, hm6, hdv3, rfl⟩ := gdPStep_inv h2
  have hA := hF.write (j := 13) (lt16 (by decide)) (Nat.toB256 D)
  have hB := hA.write (j := 15) (lt16 (by decide)) (Nat.toB256 0)
  have hC := hB.write (j := 14) (lt16 (by decide)) x0
  have hD' := hC.write (j := 13) (lt16 (by decide)) (gdP (Nat.toB256 D) (Nat.toB256 D) x0)
  have hE := hD'.write (j := 15) (lt16 (by decide)) (Nat.toB256 (0 + 1))
  have hF1 := hE.write (j := 14) (lt16 (by decide)) x1
  have hG := hF1.write (j := 13) (lt16 (by decide))
    (gdP (gdP (Nat.toB256 D) (Nat.toB256 D) x0) (Nat.toB256 D) x1)
  have hH := hG.write (j := 15) (lt16 (by decide)) (Nat.toB256 (1 + 1))
  have hI := hH.write (j := 14) (lt16 (by decide)) x2
  have hJ := hI.write (j := 13) (lt16 (by decide))
    (gdP (gdP (gdP (Nat.toB256 D) (Nat.toB256 D) x0) (Nat.toB256 D) x1) (Nat.toB256 D) x2)
  have hK := hJ.write (j := 15) (lt16 (by decide)) (Nat.toB256 (2 + 1))
  refine ⟨_, _, rfl, hK, fun r kk => ?_⟩
  refine rxc_gdHeadPre hF rfl rfl (by omega) ?_
  refine rxc_gdInner (j := 0) hB rfl rfl (by decide) rfl rfl rfl hm1 hm2 hdv (by omega) ?_
  refine rxc_branchTo_succ (iszero_eq3_neX (by decide)) (by decide) progGD_517 ?_
  refine rxc_gdInner (j := 1) hE rfl rfl (by decide) rfl rfl rfl hm3 hm4 hdv2 (by omega) ?_
  refine rxc_branchTo_succ (iszero_eq3_neX (by decide)) (by decide) progGD_517 ?_
  refine rxc_gdInner (j := 2) hH rfl rfl (by decide) rfl rfl rfl hm5 hm6 hdv3 (by omega) ?_
  rw [show B256.eqCheck (B256.eqCheck (Nat.toB256 3) (Nat.toB256 (2 + 1))) 0 = 0 by decide]
  exact rxc_branchTo_zero kk

-- SEGMENT: gdInner_489
theorem gdInner_489 {x0 x1 x2 ρ s ann : B256} :
    GdInner (sevm := sevm) [533] b S M0 x0 x1 x2 ρ s ann (gdHead (.branchTo .undefined 503))
      (gdRest 531 532 533 gdExit) := by
  intro M G amp xs sc w8 dp p xv ic D n pN hD hroom hF hdp
  obtain ⟨p0, p1, h0, h1, h2⟩ := dPChk_steps hdp
  have hDN : (Nat.toB256 D).toNat = D := B256.toNat_toB256_of_lt hD
  rw [← hDN] at h0 h1 h2
  obtain ⟨hm1, hm2, hdv, rfl⟩ := gdPStep_inv (p := Nat.toB256 D) h0
  obtain ⟨hm3, hm4, hdv2, rfl⟩ := gdPStep_inv h1
  obtain ⟨hm5, hm6, hdv3, rfl⟩ := gdPStep_inv h2
  have hA := hF.write (j := 13) (lt16 (by decide)) (Nat.toB256 D)
  have hB := hA.write (j := 15) (lt16 (by decide)) (Nat.toB256 0)
  have hC := hB.write (j := 14) (lt16 (by decide)) x0
  have hD' := hC.write (j := 13) (lt16 (by decide)) (gdP (Nat.toB256 D) (Nat.toB256 D) x0)
  have hE := hD'.write (j := 15) (lt16 (by decide)) (Nat.toB256 (0 + 1))
  have hF1 := hE.write (j := 14) (lt16 (by decide)) x1
  have hG := hF1.write (j := 13) (lt16 (by decide))
    (gdP (gdP (Nat.toB256 D) (Nat.toB256 D) x0) (Nat.toB256 D) x1)
  have hH := hG.write (j := 15) (lt16 (by decide)) (Nat.toB256 (1 + 1))
  have hI := hH.write (j := 14) (lt16 (by decide)) x2
  have hJ := hI.write (j := 13) (lt16 (by decide))
    (gdP (gdP (gdP (Nat.toB256 D) (Nat.toB256 D) x0) (Nat.toB256 D) x1) (Nat.toB256 D) x2)
  have hK := hJ.write (j := 15) (lt16 (by decide)) (Nat.toB256 (2 + 1))
  refine ⟨_, _, rfl, hK, fun r kk => ?_⟩
  refine rxc_gdHeadPre hF rfl rfl (by omega) ?_
  refine rxc_gdInner (j := 0) hB rfl rfl (by decide) rfl rfl rfl hm1 hm2 hdv (by omega) ?_
  refine rxc_branchTo_succ (iszero_eq3_neX (by decide)) (by decide) progGD_503 ?_
  refine rxc_gdInner (j := 1) hE rfl rfl (by decide) rfl rfl rfl hm3 hm4 hdv2 (by omega) ?_
  refine rxc_branchTo_succ (iszero_eq3_neX (by decide)) (by decide) progGD_517 ?_
  refine rxc_gdInner (j := 2) hH rfl rfl (by decide) rfl rfl rfl hm5 hm6 hdv3 (by omega) ?_
  rw [show B256.eqCheck (B256.eqCheck (Nat.toB256 3) (Nat.toB256 (2 + 1))) 0 = 0 by decide]
  exact rxc_branchTo_zero kk

-- SEGMENT: gdInner_0
theorem gdInner_0 {x0 x1 x2 ρ s ann : B256} :
    GdInner (sevm := sevm) [489] b S M0 x0 x1 x2 ρ s ann (gdHead (.branchTo .undefined 459))
      (gdRest 487 488 489 .undefined) := by
  intro M G amp xs sc w8 dp p xv ic D n pN hD hroom hF hdp
  obtain ⟨p0, p1, h0, h1, h2⟩ := dPChk_steps hdp
  have hDN : (Nat.toB256 D).toNat = D := B256.toNat_toB256_of_lt hD
  rw [← hDN] at h0 h1 h2
  obtain ⟨hm1, hm2, hdv, rfl⟩ := gdPStep_inv (p := Nat.toB256 D) h0
  obtain ⟨hm3, hm4, hdv2, rfl⟩ := gdPStep_inv h1
  obtain ⟨hm5, hm6, hdv3, rfl⟩ := gdPStep_inv h2
  have hA := hF.write (j := 13) (lt16 (by decide)) (Nat.toB256 D)
  have hB := hA.write (j := 15) (lt16 (by decide)) (Nat.toB256 0)
  have hC := hB.write (j := 14) (lt16 (by decide)) x0
  have hD' := hC.write (j := 13) (lt16 (by decide)) (gdP (Nat.toB256 D) (Nat.toB256 D) x0)
  have hE := hD'.write (j := 15) (lt16 (by decide)) (Nat.toB256 (0 + 1))
  have hF1 := hE.write (j := 14) (lt16 (by decide)) x1
  have hG := hF1.write (j := 13) (lt16 (by decide))
    (gdP (gdP (Nat.toB256 D) (Nat.toB256 D) x0) (Nat.toB256 D) x1)
  have hH := hG.write (j := 15) (lt16 (by decide)) (Nat.toB256 (1 + 1))
  have hI := hH.write (j := 14) (lt16 (by decide)) x2
  have hJ := hI.write (j := 13) (lt16 (by decide))
    (gdP (gdP (gdP (Nat.toB256 D) (Nat.toB256 D) x0) (Nat.toB256 D) x1) (Nat.toB256 D) x2)
  have hK := hJ.write (j := 15) (lt16 (by decide)) (Nat.toB256 (2 + 1))
  refine ⟨_, _, rfl, hK, fun r kk => ?_⟩
  refine rxc_gdHeadPre hF rfl rfl (by omega) ?_
  refine rxc_gdInner (j := 0) hB rfl rfl (by decide) rfl rfl rfl hm1 hm2 hdv (by omega) ?_
  refine rxc_branchTo_succ (iszero_eq3_neX (by decide)) (by decide) progGD_459 ?_
  refine rxc_gdInner (j := 1) hE rfl rfl (by decide) rfl rfl rfl hm3 hm4 hdv2 (by omega) ?_
  refine rxc_branchTo_succ (iszero_eq3_neX (by decide)) (by decide) progGD_473 ?_
  refine rxc_gdInner (j := 2) hH rfl rfl (by decide) rfl rfl rfl hm5 hm6 hdv3 (by omega) ?_
  rw [show B256.eqCheck (B256.eqCheck (Nat.toB256 3) (Nat.toB256 (2 + 1))) 0 = 0 by decide]
  exact rxc_branch_zero kk

/-- Gas of a Newton pass of the `D` loop that goes on, by the direction of the step. -/
def gdStepC (D D' : Nat) : Nat := if D < D' then 1639 else 1629

/-- Gas of a Newton pass of the `D` loop that stops. -/
def gdStopC (D D' : Nat) : Nat := if D < D' then 1630 else 1631

/-- Gas of the last permitted pass of the `D` loop. -/
def gdCapC (D D' : Nat) : Nat := if D < D' then 1676 else 1666

/-- The `D` loop's head state with its gas. -/
def gdAtX (b : Devm) (S : List B256) (M0 : Mem) (x0 x1 x2 ρ s ann : B256) (n D G : Nat)
    (d : Devm) : Prop :=
  D < 2 ^ 256 ∧ ∃ M amp xs sc w8 dp p xv ic, d = St b (gdStk S) M G ∧
    WordFrame M0 M 0x140 (gdFrame x0 x1 x2 amp ρ s xs sc w8 dp (Nat.toB256 D) ann (Nat.toB256 n)
      p xv ic)

theorem dPChk_of_bodyDChk {x : Fin 3 → Nat} {ann s D D' : Nat}
    (h : bodyDChk x ann s D = some D') : ∃ p, dPChk x D = some p := by
  unfold bodyDChk at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨p, hp, -⟩ := h
  exact ⟨p, hp⟩

variable {x0 x1 x2 ρ s ann : B256}

-- SEGMENT: gdPass_fwd
/-- **A stopping Newton pass of the `D` loop**, forward, at any copy. -/
theorem gdPass_stop {e t k : Nat} {fall f : SFunc}
    (hinner : GdInner (sevm := sevm) C b S M0 x0 x1 x2 ρ s ann f (gdRest e t k fall))
    (he : progYD[e]? = some gdExit) (heC : e ∉ C) (hroom : S.length + 16 < 1024)
    {n D D' G : Nat} {d : Devm}
    (hb : bodyDChk (gdX x0 x1 x2) ann.toNat s.toNat D = some D')
    (hc : closeEnough 1 D' D) (hAt : gdAtX b S M0 x0 x1 x2 ρ s ann n D (G + gdStopC D D') d) :
    ∃ r, SFunc.RunExactCut progYD sevm C d f r ∧ (∀ d', r ≠ .at k d') ∧
      calleeExit b S M0 D' G r := by
  obtain ⟨hD, M, amp, xs, sc, w8, dp, p, xv, ic, rfl, hF⟩ := hAt
  have hDN : (Nat.toB256 D).toNat = D := B256.toNat_toB256_of_lt hD
  obtain ⟨pN, hdp⟩ := dPChk_of_bodyDChk hb
  obtain ⟨M3, pw, rfl, hF3, hrun⟩ := hinner M
    (G + 37 + (if (Nat.toB256 D).toNat < D' then 103 else 104) + 625)
    amp xs sc w8 dp p xv ic D n pN hD hroom hF hdp
  rw [← hDN] at hdp hb hc
  obtain ⟨hm1, hm2, ha1, hm3, hs, hm4, hm5, ha2, hdv, rfl⟩ := bodyDChk_inv hdp hb
  have h9 := hF3.write (j := 9) (lt16 (by decide)) (Nat.toB256 D)
  have h10 := h9.write (j := 10) (lt16 (by decide))
    (((ann * s + pw * Bytes.toB256 [0x03]) * Nat.toB256 D) /
      ((ann - Bytes.toB256 [0x01]) * Nat.toB256 D + Bytes.toB256 [0x04] * pw))
  obtain ⟨M', hout, hex⟩ := rxc_gdExit (C := C) (G := G) (S := S) h10 rfl rfl rfl (by omega)
  refine ⟨.done (.returned (St b ((((ann * s + pw * Bytes.toB256 [0x03]) * Nat.toB256 D) /
      ((ann - Bytes.toB256 [0x01]) * Nat.toB256 D + Bytes.toB256 [0x04] * pw)) :: S) M' G)),
    ?_, fun d' h => (by cases h), M', by rw [toB256_toNat], by rw [toB256_toNat]; exact hout⟩
  have hg : G + gdStopC D (((ann * s + pw * Bytes.toB256 [0x03]) * Nat.toB256 D) /
      ((ann - Bytes.toB256 [0x01]) * Nat.toB256 D + Bytes.toB256 [0x04] * pw)).toNat =
      (G + 37 + (if (Nat.toB256 D).toNat < (((ann * s + pw * Bytes.toB256 [0x03]) * Nat.toB256 D) /
        ((ann - Bytes.toB256 [0x01]) * Nat.toB256 D + Bytes.toB256 [0x04] * pw)).toNat then 103
        else 104) + 625) + 865 := by
    rw [hDN]; unfold gdStopC; split <;> omega
  rw [hg]
  refine hrun _ (rxc_gdRestPre hF3 rfl rfl rfl rfl rfl hm1 hm2 ha1 hm3 hs hm4 hm5 ha2 hdv
    (by omega) ?_)
  exact rxc_gdRestBr_close h10 rfl rfl hc he heC (by omega) hex

/-- **A Newton pass of the `D` loop that goes on**, forward, at any copy. -/
theorem gdPass_step {e t k : Nat} {fall fall' f : SFunc}
    (hinner : GdInner (sevm := sevm) C b S M0 x0 x1 x2 ρ s ann f (gdRest e t k fall))
    (ht : progYD[t]? = some (gdTail k fall')) (htC : t ∉ C) (hkC : k ∈ C)
    (hroom : S.length + 16 < 1024)
    {n D D' G : Nat} {d : Devm} (hn : n + 1 < 255)
    (hb : bodyDChk (gdX x0 x1 x2) ann.toNat s.toNat D = some D')
    (hc : ¬ closeEnough 1 D' D) (hAt : gdAtX b S M0 x0 x1 x2 ρ s ann n D (G + gdStepC D D') d) :
    ∃ d', SFunc.RunExactCut progYD sevm C d f (.at k d') ∧
      gdAtX b S M0 x0 x1 x2 ρ s ann (n + 1) D' G d' := by
  obtain ⟨hD, M, amp, xs, sc, w8, dp, p, xv, ic, rfl, hF⟩ := hAt
  have hDN : (Nat.toB256 D).toNat = D := B256.toNat_toB256_of_lt hD
  obtain ⟨pN, hdp⟩ := dPChk_of_bodyDChk hb
  obtain ⟨M3, pw, rfl, hF3, hrun⟩ := hinner M
    (G + 45 + (if (Nat.toB256 D).toNat < D' then 104 else 94) + 625)
    amp xs sc w8 dp p xv ic D n pN hD hroom hF hdp
  rw [← hDN] at hdp hb hc
  obtain ⟨hm1, hm2, ha1, hm3, hs, hm4, hm5, ha2, hdv, rfl⟩ := bodyDChk_inv hdp hb
  have h9 := hF3.write (j := 9) (lt16 (by decide)) (Nat.toB256 D)
  have h10 := h9.write (j := 10) (lt16 (by decide))
    (((ann * s + pw * Bytes.toB256 [0x03]) * Nat.toB256 D) /
      ((ann - Bytes.toB256 [0x01]) * Nat.toB256 D + Bytes.toB256 [0x04] * pw))
  have h12 := h10.write (j := 12) (lt16 (by decide)) (Nat.toB256 (n + 1))
  refine ⟨_, ?_, B256.toNat_lt _, _, amp, xs, sc, w8, Nat.toB256 D, pw, x2, Nat.toB256 3, rfl,
    by rw [toB256_toNat]; exact h12⟩
  have hg : G + gdStepC D (((ann * s + pw * Bytes.toB256 [0x03]) * Nat.toB256 D) /
      ((ann - Bytes.toB256 [0x01]) * Nat.toB256 D + Bytes.toB256 [0x04] * pw)).toNat =
      (G + 45 + (if (Nat.toB256 D).toNat < (((ann * s + pw * Bytes.toB256 [0x03]) * Nat.toB256 D) /
        ((ann - Bytes.toB256 [0x01]) * Nat.toB256 D + Bytes.toB256 [0x04] * pw)).toNat then 104
        else 94) + 625) + 865 := by
    rw [hDN]; unfold gdStepC; split <;> omega
  rw [hg]
  refine hrun _ (rxc_gdRestPre hF3 rfl rfl rfl rfl rfl hm1 hm2 ha1 hm3 hs hm4 hm5 ha2 hdv
    (by omega) ?_)
  exact rxc_gdRestBr_next h10 rfl rfl hc ht htC (by omega)
    (fun _ => rxc_gdTail_next h10 rfl rfl hn hkC (by omega))
    (fun _ => rxc_gdTail_next h10 rfl rfl hn hkC (by omega))

/-- **The last permitted pass of the `D` loop**, forward, at the steady copy. -/
theorem gdPass_cap {e t k : Nat} {f : SFunc}
    (hinner : GdInner (sevm := sevm) C b S M0 x0 x1 x2 ρ s ann f (gdRest e t k gdExit))
    (ht : progYD[t]? = some (gdTail k gdExit)) (htC : t ∉ C)
    (hroom : S.length + 16 < 1024)
    {n D D' G : Nat} {d : Devm} (hn : n + 1 = 255)
    (hb : bodyDChk (gdX x0 x1 x2) ann.toNat s.toNat D = some D')
    (hc : ¬ closeEnough 1 D' D) (hAt : gdAtX b S M0 x0 x1 x2 ρ s ann n D (G + gdCapC D D') d) :
    ∃ r, SFunc.RunExactCut progYD sevm C d f r ∧ (∀ d', r ≠ .at k d') ∧
      calleeExit b S M0 D' G r := by
  obtain ⟨hD, M, amp, xs, sc, w8, dp, p, xv, ic, rfl, hF⟩ := hAt
  have hDN : (Nat.toB256 D).toNat = D := B256.toNat_toB256_of_lt hD
  obtain ⟨pN, hdp⟩ := dPChk_of_bodyDChk hb
  obtain ⟨M3, pw, rfl, hF3, hrun⟩ := hinner M
    (G + 37 + 45 + (if (Nat.toB256 D).toNat < D' then 104 else 94) + 625)
    amp xs sc w8 dp p xv ic D n pN hD hroom hF hdp
  rw [← hDN] at hdp hb hc
  obtain ⟨hm1, hm2, ha1, hm3, hs, hm4, hm5, ha2, hdv, rfl⟩ := bodyDChk_inv hdp hb
  have h9 := hF3.write (j := 9) (lt16 (by decide)) (Nat.toB256 D)
  have h10 := h9.write (j := 10) (lt16 (by decide))
    (((ann * s + pw * Bytes.toB256 [0x03]) * Nat.toB256 D) /
      ((ann - Bytes.toB256 [0x01]) * Nat.toB256 D + Bytes.toB256 [0x04] * pw))
  have h12 := h10.write (j := 12) (lt16 (by decide)) (Nat.toB256 (n + 1))
  obtain ⟨M', hout, hex⟩ := rxc_gdExit (C := C) (G := G) (S := S) h12 rfl rfl rfl (by omega)
  refine ⟨.done (.returned (St b ((((ann * s + pw * Bytes.toB256 [0x03]) * Nat.toB256 D) /
      ((ann - Bytes.toB256 [0x01]) * Nat.toB256 D + Bytes.toB256 [0x04] * pw)) :: S) M' G)),
    ?_, fun d' h => (by cases h), M', by rw [toB256_toNat], by rw [toB256_toNat]; exact hout⟩
  have hg : G + gdCapC D (((ann * s + pw * Bytes.toB256 [0x03]) * Nat.toB256 D) /
      ((ann - Bytes.toB256 [0x01]) * Nat.toB256 D + Bytes.toB256 [0x04] * pw)).toNat =
      (G + 37 + 45 + (if (Nat.toB256 D).toNat < (((ann * s + pw * Bytes.toB256 [0x03]) * Nat.toB256 D) /
        ((ann - Bytes.toB256 [0x01]) * Nat.toB256 D + Bytes.toB256 [0x04] * pw)).toNat then 104
        else 94) + 625) + 865 := by
    rw [hDN]; unfold gdCapC; split <;> omega
  rw [hg]
  refine hrun _ (rxc_gdRestPre hF3 rfl rfl rfl rfl rfl hm1 hm2 ha1 hm3 hs hm4 hm5 ha2 hdv
    (by omega) ?_)
  exact rxc_gdRestBr_next h10 rfl rfl hc ht htC (by omega)
    (fun _ => rxc_gdTail_last h10 rfl rfl hn (by omega) hex)
    (fun _ => rxc_gdTail_last h10 rfl rfl hn (by omega) hex)

end Fwd

end Blanc.Lift.Curve3Pool
