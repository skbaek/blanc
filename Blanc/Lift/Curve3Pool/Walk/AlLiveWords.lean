import Blanc.Lift.Curve3Pool.Walk.AlLiveModel

/-!
# `add_liquidity`: the model as the frame's words

`al_words_new`: in the premised environment `alEnvW sevm T B1 B2`, a successful model step's new
balances are the forward run's `alLiveNew` words, with the deposit loop's word checks
(`AlLoopOk`'s word fields). `al_words`: every word check `rx_al_frame1` / `rx_al_frame0` needs,
the model's output in those words, and the closed sufficient-gas bound `costAddLiquidity`.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

section Words

variable {sevm : Sevm} {σ : Stor} {s : State} {T B1 B2 : B256}

theorem al_liveNew_eq (sevm : Sevm) (σ : Stor) (B1 B2 : B256) :
    alLiveNew sevm (alOld σ) B1 B2 0 = balAt σ 0 + alCrK sevm B1 B2 0 ∧
    alLiveNew sevm (alOld σ) B1 B2 1 = balAt σ 1 + alCrK sevm B1 B2 1 ∧
    alLiveNew sevm (alOld σ) B1 B2 2 = balAt σ 2 + alCrK sevm B1 B2 2 :=
  ⟨rfl, rfl, rfl⟩

/-- **The new balances in the premised environment, as words.** -/
theorem al_words_new (ha : Abstracts σ s) {new : V3}
    (hnew : V3.ofFnM (pullAdd (alEnvW sevm T.toNat B1.toNat B2.toNat) T.toNat s.balances
      (argV3 sevm 0)) = some new) :
    new = ⟨(alLiveNew sevm (alOld σ) B1 B2 0).toNat, (alLiveNew sevm (alOld σ) B1 B2 1).toNat,
      (alLiveNew sevm (alOld σ) B1 B2 2).toNat⟩ ∧
    (T = 0 → alAmt sevm 0 ≠ 0 ∧ alAmt sevm 1 ≠ 0 ∧ alAmt sevm 2 ≠ 0) ∧
    (alAmt sevm 2 ≠ 0 → ¬ B2 < B1) ∧
    ¬ balAt σ 0 + alAmt sevm 0 < balAt σ 0 ∧ ¬ balAt σ 1 + alAmt sevm 1 < balAt σ 1 ∧
    ¬ balAt σ 2 + alCr2 sevm B1 B2 < balAt σ 2 := by
  have hbal : s.balances = ⟨(balAt σ 0).toNat, (balAt σ 1).toNat, (balAt σ 2).toNat⟩ :=
    (V3.ext_get fun k => by rw [← ex_w3_nat]; exact ex_bal_nat ha k).symm
  rw [hbal] at hnew
  obtain ⟨h0, h1, h2⟩ := cw_ofFnM_parts hnew
  obtain ⟨t0, -, a0, e0⟩ := al_coin_words (k := 0) (σ := σ) h0 rfl
  obtain ⟨t1, -, a1, e1⟩ := al_coin_words (k := 1) (σ := σ) h1 rfl
  obtain ⟨t2, sub, a2, e2⟩ := al_coin_words (k := 2) (σ := σ) h2 rfl
  have hT0 : T = 0 → T.toNat = 0 := fun h => by rw [h]; rfl
  obtain ⟨n0, n1, n2⟩ := al_liveNew_eq sevm σ B1 B2
  refine ⟨?_, fun h => ⟨t0 (hT0 h), t1 (hT0 h), t2 (hT0 h)⟩, sub rfl, a0, a1, a2⟩
  obtain ⟨v0, v1, v2⟩ := new
  dsimp only at e0 e1 e2
  subst e0 e1 e2
  rw [n0, n1, n2]
  rfl

/-- The closed sufficient-gas bound of `add_liquidity`'s frame (beyond `7 U` for the calls):
the `get_D_mem` runs at their actual inputs plus a constant (`0` when the model fails). -/
def costAddLiquidity (s : State) (e : Env) (a : V3) : Nat :=
  (do
    let amp ← aChk s e.time
    let T ← e.supply
    let new ← V3.ofFnM (pullAdd e T s.balances a)
    let xb ← xpChk new
    if T = 0 then some (costGetDMem xb amp + 400000) else do
      let fee ← feeAdj s
      let xa ← xpChk s.balances
      let D0 ← getDChk xa.get amp 1
      let D1 ← getDChk xb.get amp 1
      let r ← feeLoop fee s.adminFee D0 D1 s.balances new
      let xc ← xpChk r.2.2
      some (costGetDMem xa amp + costGetDMem xb amp + costGetDMem xc amp + 400000)).getD 0

/-- The new balances as the model's numbers. -/
abbrev alNewW (sevm : Sevm) (σ : Stor) (B1 B2 : B256) : V3 :=
  ⟨(alLiveNew sevm (alOld σ) B1 B2 0).toNat, (alLiveNew sevm (alOld σ) B1 B2 1).toNat,
    (alLiveNew sevm (alOld σ) B1 B2 2).toNat⟩

/-- **The model's `add_liquidity` in the premised environment, common words.** -/
theorem al_words_common {o : Out} (ha : Abstracts σ s)
    (hal : addLiquidity s (alEnvW sevm T.toNat B1.toNat B2.toNat) (argV3 sevm 0) (arg sevm 3) =
      some o) :
    ∃ (amp v1 : Nat) (xb : V3) (mint T' : Nat), s.isKilled = false ∧
      aChk s sevm.benvStat.time.toNat = some amp ∧
      feeAdj s = some (cwFee (σ.get feeSlot)).toNat ∧
      V3.ofFnM (pullAdd (alEnvW sevm T.toNat B1.toNat B2.toNat) T.toNat s.balances
        (argV3 sevm 0)) = some (alNewW sevm σ B1 B2) ∧
      (σ.get feeSlot * Bytes.toB256 [0x03] / σ.get feeSlot = Bytes.toB256 [0x03] ∨
        σ.get feeSlot = 0) ∧
      (T = 0 → alAmt sevm 0 ≠ 0 ∧ alAmt sevm 1 ≠ 0 ∧ alAmt sevm 2 ≠ 0) ∧
      (alAmt sevm 2 ≠ 0 → ¬ B2 < B1) ∧
      ¬ balAt σ 0 + alAmt sevm 0 < balAt σ 0 ∧ ¬ balAt σ 1 + alAmt sevm 1 < balAt σ 1 ∧
      ¬ balAt σ 2 + alCr2 sevm B1 B2 < balAt σ 2 ∧
      xpChk (alNewW sevm σ B1 B2) = some xb ∧ getDChk xb.get amp 1 = some v1 ∧
      arg sevm 3 ≤ mint ∧ chkAdd T.toNat mint = some T' ∧
      ((T = 0 ∧ 0 < v1 ∧ mint = v1 ∧ o = ⟨{ s with balances := alNewW sevm σ B1 B2 }, none,
          [.addLiquidity sevm.caller.toB256.toNat (argV3 sevm 0) V3.zero v1 T'],
          pullCalls sevm.caller.toB256.toNat (argV3 sevm 0) ++
            [.mint sevm.caller.toB256.toNat v1]⟩) ∨
        (T ≠ 0 ∧ ∃ D0 fees stored after D2 x y, getDMem s.balances amp = some D0 ∧ D0 < v1 ∧
          feeLoop (cwFee (σ.get feeSlot)).toNat (σ.get adminFeeSlot).toNat D0 v1 s.balances
            (alNewW sevm σ B1 B2) = some (fees, stored, after) ∧
          getDMem after amp = some D2 ∧ chkSub D2 D0 = some x ∧ chkMul T.toNat x = some y ∧
          chkDiv y D0 = some mint ∧
          o = ⟨{ s with balances := stored }, none,
            [.addLiquidity sevm.caller.toB256.toNat (argV3 sevm 0) fees v1 T'],
            pullCalls sevm.caller.toB256.toNat (argV3 sevm 0) ++
              [.mint sevm.caller.toB256.toNat mint]⟩)) := by
  obtain ⟨hk, fee, amp, Tn, new, D1, mint, T', hfee, hamp, hT, hnew, hD1, hmin, -, hT', hbr⟩ :=
    addLiquidity_inv hal
  obtain rfl : Tn = T.toNat := (Option.some.inj hT).symm
  obtain ⟨rfl, t0, sub, a0, a1, a2⟩ := al_words_new ha hnew
  -- the adjusted fee
  have hfee0 := hfee
  unfold feeAdj at hfee
  obtain ⟨pf, hpf, hfee⟩ := Option.bind_eq_some_iff.mp hfee
  rw [← ha.fee, show (3 : Nat) = (Bytes.toB256 [0x03]).toNat by decide] at hpf
  obtain ⟨hmfn, rfl⟩ := chkMul_inv hpf
  rw [show (8 : Nat) = (Bytes.toB256 [0x08]).toNat by decide] at hfee
  obtain ⟨-, rfl⟩ := chkDiv_word hfee
  obtain ⟨xb, hxb, hD1'⟩ := rli_getDMem hD1
  refine ⟨amp, D1, xb, mint, T', hk, hamp, hfee0, hnew, mulEq_of_nofm hmfn, t0, sub, a0, a1, a2,
    hxb, hD1',
    hmin, hT', ?_⟩
  rcases hbr with ⟨h0, hpos, rfl, ho⟩ | ⟨h0, D0, fees, stored, after, D2, x, y, hD0, hlt, hfl, hD2,
    hx, hy, hm, ho⟩
  · exact .inl ⟨by rw [← B256.toNat_zero] at h0; exact B256.toNat_inj _ _ h0, hpos, rfl, ho⟩
  · refine .inr ⟨fun h => h0 (by rw [h]; rfl), D0, fees, stored, after, D2, x, y, hD0, hlt, ?_, hD2,
      hx, hy, hm, ho⟩
    rw [← ha.adminFee] at hfl
    exact hfl

/-- **The fee path's words** (positive supply). -/
theorem al_words1 (ha : Abstracts σ s) {amp v1 D0 D2 x y mint T' : Nat} {fees stored after xb : V3}
    (hD1 : getDChk xb.get amp 1 = some v1)
    (hD0 : getDMem s.balances amp = some D0) (hlt : D0 < v1)
    (hfl : feeLoop (cwFee (σ.get feeSlot)).toNat (σ.get adminFeeSlot).toNat D0 v1 s.balances
      (alNewW sevm σ B1 B2) = some (fees, stored, after))
    (hD2 : getDMem after amp = some D2) (hx : chkSub D2 D0 = some x)
    (hy : chkMul T.toNat x = some y) (hm : chkDiv y D0 = some mint) (hmin : arg sevm 3 ≤ mint)
    (hT' : chkAdd T.toNat mint = some T') :
    ∃ (xa xc : V3) (v0 v2 : Nat) (f0 f1 f2 s0 s1 s2 x0 x1 x2 : B256),
      xpChk ⟨(balAt σ 0).toNat, (balAt σ 1).toNat, (balAt σ 2).toNat⟩ = some xa ∧
      getDChk xa.get amp 1 = some v0 ∧ Nat.toB256 v0 < Nat.toB256 v1 ∧
      RliFeeIter (cwFee (σ.get feeSlot)) (σ.get adminFeeSlot) (Nat.toB256 v0) (Nat.toB256 v1)
        (balAt σ 0) (alLiveNew sevm (alOld σ) B1 B2 0) f0 s0 x0 ∧
      RliFeeIter (cwFee (σ.get feeSlot)) (σ.get adminFeeSlot) (Nat.toB256 v0) (Nat.toB256 v1)
        (balAt σ 1) (alLiveNew sevm (alOld σ) B1 B2 1) f1 s1 x1 ∧
      RliFeeIter (cwFee (σ.get feeSlot)) (σ.get adminFeeSlot) (Nat.toB256 v0) (Nat.toB256 v1)
        (balAt σ 2) (alLiveNew sevm (alOld σ) B1 B2 2) f2 s2 x2 ∧
      xpChk ⟨x0.toNat, x1.toNat, x2.toNat⟩ = some xc ∧ getDChk xc.get amp 1 = some v2 ∧
      ¬ Nat.toB256 v2 < Nat.toB256 v0 ∧ B256.Nofm T (Nat.toB256 v2 - Nat.toB256 v0) ∧
      Nat.toB256 v0 ≠ 0 ∧
      ¬ alMintW T (Nat.toB256 v0) (Nat.toB256 v2) < Sevm.dataWord sevm (Bytes.toB256 [0x64]) ∧
      ¬ T + alMintW T (Nat.toB256 v0) (Nat.toB256 v2) < T ∧
      mint = (alMintW T (Nat.toB256 v0) (Nat.toB256 v2)).toNat ∧
      T' = (T + alMintW T (Nat.toB256 v0) (Nat.toB256 v2)).toNat ∧
      fees = ⟨f0.toNat, f1.toNat, f2.toNat⟩ ∧ stored = ⟨s0.toNat, s1.toNat, s2.toNat⟩ ∧
      D0 = v0 ∧ xpChk after = some xc := by
  have hbal : s.balances = ⟨(balAt σ 0).toNat, (balAt σ 1).toNat, (balAt σ 2).toNat⟩ :=
    (V3.ext_get fun k => by rw [← ex_w3_nat]; exact ex_bal_nat ha k).symm
  obtain ⟨xa, hxa, hD0'⟩ := rli_getDMem hD0
  rw [hbal] at hxa
  have hv0 : D0 < 2 ^ 256 := getDChk_lt hD0'
  have hv1 : v1 < 2 ^ 256 := getDChk_lt hD1
  have hfl0 := hfl
  unfold feeLoop at hfl
  obtain ⟨r0, hr0, hfl⟩ := Option.bind_eq_some_iff.mp hfl
  obtain ⟨r1, hr1, hfl⟩ := Option.bind_eq_some_iff.mp hfl
  obtain ⟨r2, hr2, hfl⟩ := Option.bind_eq_some_iff.mp hfl
  cases hfl
  obtain ⟨g0, st0, a0⟩ := r0
  obtain ⟨g1, st1, a1⟩ := r1
  obtain ⟨g2, st2, a2⟩ := r2
  rw [hbal, ← B256.toNat_toB256_of_lt hv0, ← B256.toNat_toB256_of_lt hv1] at hr0 hr1 hr2
  obtain ⟨i0, g0l, st0l, a0l⟩ := rli_feeIter_of (B := balAt σ 0)
    (N := alLiveNew sevm (alOld σ) B1 B2 0) hr0 rfl rfl
  obtain ⟨i1, g1l, st1l, a1l⟩ := rli_feeIter_of (B := balAt σ 1)
    (N := alLiveNew sevm (alOld σ) B1 B2 1) hr1 rfl rfl
  obtain ⟨i2, g2l, st2l, a2l⟩ := rli_feeIter_of (B := balAt σ 2)
    (N := alLiveNew sevm (alOld σ) B1 B2 2) hr2 rfl rfl
  obtain ⟨xc, hxc, hD2'⟩ := rli_getDMem hD2
  have hxc0 := hxc
  dsimp only at hxc
  rw [← B256.toNat_toB256_of_lt a0l, ← B256.toNat_toB256_of_lt a1l,
    ← B256.toNat_toB256_of_lt a2l] at hxc
  have hv2 : D2 < 2 ^ 256 := getDChk_lt hD2'
  have hx' : chkSub (Nat.toB256 D2).toNat (Nat.toB256 D0).toNat = some x := by
    rw [B256.toNat_toB256_of_lt hv0, B256.toNat_toB256_of_lt hv2]; exact hx
  obtain ⟨hD02, rfl⟩ := chkSub_word hx'
  obtain ⟨hmT, rfl⟩ := chkMul_inv hy
  have hm' : chkDiv (T * (Nat.toB256 D2 - Nat.toB256 D0)).toNat (Nat.toB256 D0).toNat =
      some mint := by
    rw [B256.toNat_toB256_of_lt hv0]; exact hm
  obtain ⟨hD0ne, rfl⟩ := chkDiv_word hm'
  obtain ⟨hadd, rfl⟩ := chkAdd_inv hT'
  rw [al_minArg] at hmin
  refine ⟨xa, xc, D0, D2, Nat.toB256 g0, Nat.toB256 g1, Nat.toB256 g2, Nat.toB256 st0,
    Nat.toB256 st1, Nat.toB256 st2, Nat.toB256 a0, Nat.toB256 a1, Nat.toB256 a2, hxa, hD0',
    ?_, i0, i1, i2, hxc, hD2',
    fun h => absurd (B256.lt_iff_toNat_lt_toNat.mp h) (Nat.not_lt.mpr hD02), hmT, hD0ne,
    fun h => absurd (B256.lt_iff_toNat_lt_toNat.mp h) (Nat.not_lt.mpr hmin),
    (B256.nof_iff_not_add_lt _ _).mp hadd, rfl, rfl, ?_, ?_, rfl, hxc0⟩
  · rw [B256.lt_iff_toNat_lt_toNat, B256.toNat_toB256_of_lt hv0, B256.toNat_toB256_of_lt hv1]
    exact hlt
  · rw [B256.toNat_toB256_of_lt g0l, B256.toNat_toB256_of_lt g1l, B256.toNat_toB256_of_lt g2l]
  · rw [B256.toNat_toB256_of_lt st0l, B256.toNat_toB256_of_lt st1l,
      B256.toNat_toB256_of_lt st2l]

/-- **The first deposit's words.** -/
theorem al_words0 {amp v1 T' : Nat} {xb : V3} (hD1 : getDChk xb.get amp 1 = some v1)
    (hpos : 0 < v1) (hmin : arg sevm 3 ≤ v1) (hT' : chkAdd (0 : B256).toNat v1 = some T') :
    0 < Nat.toB256 v1 ∧ ¬ Nat.toB256 v1 < Sevm.dataWord sevm (Bytes.toB256 [0x64]) ∧
      ¬ 0 + Nat.toB256 v1 < 0 ∧ T' = (0 + Nat.toB256 v1).toNat ∧ v1 = (Nat.toB256 v1).toNat := by
  have hv1 : v1 < 2 ^ 256 := getDChk_lt hD1
  have e1 : (Nat.toB256 v1).toNat = v1 := B256.toNat_toB256_of_lt hv1
  have hT'' : chkAdd (0 : B256).toNat (Nat.toB256 v1).toNat = some T' := by rw [e1]; exact hT'
  obtain ⟨hadd, rfl⟩ := chkAdd_inv hT''
  rw [al_minArg] at hmin
  have hmin' : (Sevm.dataWord sevm (Bytes.toB256 [0x64])).toNat ≤ (Nat.toB256 v1).toNat := by
    rw [e1]; exact hmin
  refine ⟨?_, fun h => absurd (B256.lt_iff_toNat_lt_toNat.mp h) (Nat.not_lt.mpr hmin'),
    (B256.nof_iff_not_add_lt _ _).mp hadd, rfl, e1.symm⟩
  rw [B256.lt_iff_toNat_lt_toNat, e1, B256.toNat_zero]
  exact hpos

/-- **The positive-supply cost.** -/
theorem al_cost1 {amp D0 v1 : Nat} {fee : Nat} {xa xb xc : V3} {r : V3 × V3 × V3}
    (hT : T ≠ 0) (hamp : aChk s sevm.benvStat.time.toNat = some amp) (hfee : feeAdj s = some fee)
    (hnew : V3.ofFnM (pullAdd (alEnvW sevm T.toNat B1.toNat B2.toNat) T.toNat s.balances
      (argV3 sevm 0)) = some (alNewW sevm σ B1 B2))
    (hxb : xpChk (alNewW sevm σ B1 B2) = some xb) (hxa : xpChk s.balances = some xa)
    (hD0 : getDChk xa.get amp 1 = some D0) (hD1 : getDChk xb.get amp 1 = some v1)
    (hfl : feeLoop fee s.adminFee D0 v1 s.balances (alNewW sevm σ B1 B2) = some r)
    (hxc : xpChk r.2.2 = some xc) :
    costAddLiquidity s (alEnvW sevm T.toNat B1.toNat B2.toNat) (argV3 sevm 0) =
      costGetDMem xa amp + costGetDMem xb amp + costGetDMem xc amp + 400000 := by
  have hT0 : T.toNat ≠ 0 := toNat_ne_zero hT
  unfold costAddLiquidity
  rw [show (alEnvW sevm T.toNat B1.toNat B2.toNat).time = sevm.benvStat.time.toNat from rfl, hamp,
    show (alEnvW sevm T.toNat B1.toNat B2.toNat).supply = some T.toNat from rfl]
  simp only [cw_some_bind]
  rw [hnew]
  simp only [cw_some_bind]
  rw [hxb]
  simp only [cw_some_bind, hT0, ↓reduceIte]
  rw [hfee]
  simp only [cw_some_bind]
  rw [hxa]
  simp only [cw_some_bind]
  rw [hD0]
  simp only [cw_some_bind]
  rw [hD1]
  simp only [cw_some_bind]
  rw [hfl]
  simp only [cw_some_bind]
  rw [hxc]
  simp only [cw_some_bind, Option.getD_some]

/-- **The first deposit's cost.** -/
theorem al_cost0 {amp : Nat} {xb : V3}
    (hamp : aChk s sevm.benvStat.time.toNat = some amp)
    (hnew : V3.ofFnM (pullAdd (alEnvW sevm (0 : B256).toNat B1.toNat B2.toNat) (0 : B256).toNat
      s.balances (argV3 sevm 0)) = some (alNewW sevm σ B1 B2))
    (hxb : xpChk (alNewW sevm σ B1 B2) = some xb) :
    costAddLiquidity s (alEnvW sevm (0 : B256).toNat B1.toNat B2.toNat) (argV3 sevm 0) =
      costGetDMem xb amp + 400000 := by
  unfold costAddLiquidity
  rw [show (alEnvW sevm (0 : B256).toNat B1.toNat B2.toNat).time = sevm.benvStat.time.toNat
    from rfl, hamp,
    show (alEnvW sevm (0 : B256).toNat B1.toNat B2.toNat).supply = some (0 : B256).toNat from rfl]
  simp only [cw_some_bind]
  rw [hnew]
  simp only [cw_some_bind]
  rw [hxb]
  simp only [cw_some_bind, B256.toNat_zero, ↓reduceIte, Option.getD_some]

end Words

end Blanc.Lift.Curve3Pool
