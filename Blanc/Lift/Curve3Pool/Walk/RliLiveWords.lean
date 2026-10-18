import Blanc.Lift.Curve3Pool.Walk.RliLiveModel

/-!
# `remove_liquidity_imbalance`: the model as the frame's words

`rli_words`: the model's success in the environment `rliEnvW sevm T` (3Crv's `totalSupply()`
answering `T`) gives every word check `rx_rli_frame` needs, the model's output in those words, and
the closed sufficient-gas bound `costImbalance` in terms of the three `get_D_mem` runs.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

section Words

variable {sevm : Sevm} {σ : Stor} {s : State} {T : B256} {o : Out}

theorem rli_ofFnM_some {f : Fin 3 → Option Nat} {a b c : Nat} (h0 : f 0 = some a) (h1 : f 1 = some b)
    (h2 : f 2 = some c) : V3.ofFnM f = some ⟨a, b, c⟩ := by
  unfold V3.ofFnM; rw [h0, h1, h2]; rfl

/-- **The model's `remove_liquidity_imbalance`, as the frame's words.** -/
theorem rli_words (ha : Abstracts σ s)
    (hrl : removeLiquidityImbalance s (rliEnvW sevm T.toNat) (argV3 sevm 0) (arg sevm 3) = some o) :
    ∃ (amp v0 v1 v2 : Nat) (xa xb xc : V3) (f0 f1 f2 s0 s1 s2 x0 x1 x2 : B256),
      s.isKilled = false ∧ aChk s sevm.benvStat.time.toNat = some amp ∧
      (σ.get feeSlot * Bytes.toB256 [0x03] / σ.get feeSlot = Bytes.toB256 [0x03] ∨
        σ.get feeSlot = 0) ∧ T ≠ 0 ∧
      xpChk ⟨(balAt σ 0).toNat, (balAt σ 1).toNat, (balAt σ 2).toNat⟩ = some xa ∧
      getDChk xa.get amp 1 = some v0 ∧
      ¬ balAt σ 0 < rliAmt sevm 0 ∧ ¬ balAt σ 1 < rliAmt sevm 1 ∧ ¬ balAt σ 2 < rliAmt sevm 2 ∧
      xpChk ⟨(balAt σ 0 - rliAmt sevm 0).toNat, (balAt σ 1 - rliAmt sevm 1).toNat,
        (balAt σ 2 - rliAmt sevm 2).toNat⟩ = some xb ∧
      getDChk xb.get amp 1 = some v1 ∧
      RliFeeIter (cwFee (σ.get feeSlot)) (σ.get adminFeeSlot) (Nat.toB256 v0) (Nat.toB256 v1)
        (balAt σ 0) (balAt σ 0 - rliAmt sevm 0) f0 s0 x0 ∧
      RliFeeIter (cwFee (σ.get feeSlot)) (σ.get adminFeeSlot) (Nat.toB256 v0) (Nat.toB256 v1)
        (balAt σ 1) (balAt σ 1 - rliAmt sevm 1) f1 s1 x1 ∧
      RliFeeIter (cwFee (σ.get feeSlot)) (σ.get adminFeeSlot) (Nat.toB256 v0) (Nat.toB256 v1)
        (balAt σ 2) (balAt σ 2 - rliAmt sevm 2) f2 s2 x2 ∧
      xpChk ⟨x0.toNat, x1.toNat, x2.toNat⟩ = some xc ∧ getDChk xc.get amp 1 = some v2 ∧
      ¬ Nat.toB256 v0 < Nat.toB256 v2 ∧ (Nat.toB256 v0 - Nat.toB256 v2).Nofm T ∧
      (Nat.toB256 v0 - Nat.toB256 v2) * T / Nat.toB256 v0 ≠ 0 ∧
      ¬ rliBurnW (Nat.toB256 v0) (Nat.toB256 v2) T <
        (Nat.toB256 v0 - Nat.toB256 v2) * T / Nat.toB256 v0 ∧
      ¬ Sevm.dataWord sevm (Bytes.toB256 [0x64]) < rliBurnW (Nat.toB256 v0) (Nat.toB256 v2) T ∧
      ¬ T < rliBurnW (Nat.toB256 v0) (Nat.toB256 v2) T ∧
      o = ⟨{ s with balances := ⟨s0.toNat, s1.toNat, s2.toNat⟩ }, none,
        [.removeLiquidityImbalance sevm.caller.toB256.toNat (argV3 sevm 0) ⟨f0.toNat, f1.toNat,
          f2.toNat⟩ v1 (T - rliBurnW (Nat.toB256 v0) (Nat.toB256 v2) T).toNat],
        .burn sevm.caller.toB256.toNat (rliBurnW (Nat.toB256 v0) (Nat.toB256 v2) T).toNat ::
          pushCalls sevm.caller.toB256.toNat (argV3 sevm 0)⟩ ∧
      costImbalance s (rliEnvW sevm T.toNat) (argV3 sevm 0) =
        costGetDMem xa amp + costGetDMem xb amp + costGetDMem xc amp + 240000 := by
  obtain ⟨hk, Tn, fee, amp, D0n, new, D1n, fees, stored, after, D2n, d, m, b0, b, T', hT, hT0, hfee,
    hamp, hD0, hnew, hD1, hfl, hD2, hd, hm, hb0, hbn, hb, hmx, -, -, hT', ho⟩ :=
    removeLiquidityImbalance_inv hrl
  have hTn : Tn = T.toNat := (Option.some.inj hT).symm
  subst hTn
  have hbal : s.balances = ⟨(balAt σ 0).toNat, (balAt σ 1).toNat, (balAt σ 2).toNat⟩ :=
    (V3.ext_get fun k => by rw [← ex_w3_nat]; exact ex_bal_nat ha k).symm
  have hav := rli_argV3 sevm
  -- the adjusted fee
  have hfee0 := hfee
  unfold feeAdj at hfee
  obtain ⟨pf, hpf, hfee⟩ := Option.bind_eq_some_iff.mp hfee
  rw [← ha.fee, show (3 : Nat) = (Bytes.toB256 [0x03]).toNat by decide] at hpf
  obtain ⟨hmfn, rfl⟩ := chkMul_inv hpf
  rw [show (8 : Nat) = (Bytes.toB256 [0x08]).toNat by decide] at hfee
  obtain ⟨-, rfl⟩ := chkDiv_word hfee
  -- `D0`
  obtain ⟨xa, hxa, hD0'⟩ := rli_getDMem hD0
  rw [hbal] at hxa
  -- `new_balances`
  rw [hbal, hav] at hnew
  obtain ⟨hn0, hn1, hn2⟩ := cw_ofFnM_parts hnew
  obtain ⟨hu0, e0⟩ := chkSub_word hn0
  obtain ⟨hu1, e1⟩ := chkSub_word hn1
  obtain ⟨hu2, e2⟩ := chkSub_word hn2
  obtain ⟨n0, n1, n2⟩ := new
  dsimp only at e0 e1 e2
  subst e0 e1 e2
  obtain ⟨xb, hxb, hD1'⟩ := rli_getDMem hD1
  -- the fee loop
  have hv0 : D0n < 2 ^ 256 := getDChk_lt hD0'
  have hv1 : D1n < 2 ^ 256 := getDChk_lt hD1'
  have hfl0 := hfl
  unfold feeLoop at hfl
  obtain ⟨r0, hr0, hfl⟩ := Option.bind_eq_some_iff.mp hfl
  obtain ⟨r1, hr1, hfl⟩ := Option.bind_eq_some_iff.mp hfl
  obtain ⟨r2, hr2, hfl⟩ := Option.bind_eq_some_iff.mp hfl
  cases hfl
  obtain ⟨g0, st0, a0⟩ := r0
  obtain ⟨g1, st1, a1⟩ := r1
  obtain ⟨g2, st2, a2⟩ := r2
  rw [← ha.adminFee, hbal, ← B256.toNat_toB256_of_lt hv0, ← B256.toNat_toB256_of_lt hv1] at hr0 hr1 hr2
  obtain ⟨i0, g0l, st0l, a0l⟩ := rli_feeIter_of (B := balAt σ 0) (N := balAt σ 0 - rliAmt sevm 0)
    hr0 rfl rfl
  obtain ⟨i1, g1l, st1l, a1l⟩ := rli_feeIter_of (B := balAt σ 1) (N := balAt σ 1 - rliAmt sevm 1)
    hr1 rfl rfl
  obtain ⟨i2, g2l, st2l, a2l⟩ := rli_feeIter_of (B := balAt σ 2) (N := balAt σ 2 - rliAmt sevm 2)
    hr2 rfl rfl
  -- `D2`
  obtain ⟨xc, hxc, hD2'⟩ := rli_getDMem hD2
  dsimp only at hxc
  have hxc0 := hxc
  rw [← B256.toNat_toB256_of_lt a0l, ← B256.toNat_toB256_of_lt a1l,
    ← B256.toNat_toB256_of_lt a2l] at hxc
  -- the burn
  have hv2 : D2n < 2 ^ 256 := getDChk_lt hD2'
  have hd' : chkSub (Nat.toB256 D0n).toNat (Nat.toB256 D2n).toNat = some d := by
    rw [B256.toNat_toB256_of_lt hv0, B256.toNat_toB256_of_lt hv2]; exact hd
  obtain ⟨hD02, rfl⟩ := chkSub_word hd'
  obtain ⟨hmT, rfl⟩ := chkMul_inv hm
  have hb0' : chkDiv ((Nat.toB256 D0n - Nat.toB256 D2n) * T).toNat (Nat.toB256 D0n).toNat =
      some b0 := by
    rw [B256.toNat_toB256_of_lt hv0]; exact hb0
  obtain ⟨-, rfl⟩ := chkDiv_word hb0'
  rw [show (1 : Nat) = (Bytes.toB256 [1]).toNat by decide] at hb
  obtain ⟨hadd, rfl⟩ := chkAdd_inv hb
  obtain ⟨hTX, rfl⟩ := chkSub_word hT'
  rw [rli_arg3] at hmx
  refine ⟨amp, D0n, D1n, D2n, xa, xb, xc, Nat.toB256 g0, Nat.toB256 g1, Nat.toB256 g2,
    Nat.toB256 st0, Nat.toB256 st1, Nat.toB256 st2, Nat.toB256 a0, Nat.toB256 a1, Nat.toB256 a2,
    hk, hamp, mulEq_of_nofm hmfn, fun h => hT0 (by rw [h]; rfl), hxa, hD0',
    fun h => absurd (B256.lt_iff_toNat_lt_toNat.mp h) (Nat.not_lt.mpr hu0),
    fun h => absurd (B256.lt_iff_toNat_lt_toNat.mp h) (Nat.not_lt.mpr hu1),
    fun h => absurd (B256.lt_iff_toNat_lt_toNat.mp h) (Nat.not_lt.mpr hu2), hxb, hD1', i0, i1, i2,
    hxc, hD2', fun h => absurd (B256.lt_iff_toNat_lt_toNat.mp h) (Nat.not_lt.mpr hD02), hmT,
    fun h => hbn (by rw [h]; rfl), (B256.nof_iff_not_add_lt _ _).mp hadd,
    fun h => absurd (B256.lt_iff_toNat_lt_toNat.mp h) (Nat.not_lt.mpr hmx),
    fun h => absurd (B256.lt_iff_toNat_lt_toNat.mp h) (Nat.not_lt.mpr hTX), ?_, ?_⟩
  · rw [ho]
    simp only [B256.toNat_toB256_of_lt g0l, B256.toNat_toB256_of_lt g1l, B256.toNat_toB256_of_lt g2l,
      B256.toNat_toB256_of_lt st0l, B256.toNat_toB256_of_lt st1l, B256.toNat_toB256_of_lt st2l,
      B256.toNat_toB256_of_lt hv1]
    rfl
  · unfold costImbalance
    rw [hamp, hfee0]
    simp only [cw_some_bind]
    rw [hbal, hxa]
    simp only [cw_some_bind]
    rw [hD0', hav, hnew]
    simp only [cw_some_bind]
    rw [hxb]
    simp only [cw_some_bind]
    rw [hD1']
    simp only [cw_some_bind]
    rw [← hbal, hfl0]
    simp only [cw_some_bind]
    rw [hxc0]
    simp only [cw_some_bind, Option.getD_some]

end Words

end Blanc.Lift.Curve3Pool
