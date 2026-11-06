import Blanc.Composition.Curve3PoolSwapMain

/-!
# `AddRequest` is what the model's `add_liquidity` asks

`getDChk_pos`: the Newton loop's `D` is positive when the balances' sum is. `add_accepts`: the model accepts a deposit
`addOutcome` computes. `add_words`: `addCalldata`'s decoded words.
-/

namespace Blanc.Composition.Curve3PoolPublic

open Jaune Blanc Blanc.Lift
open Blanc.Lift.Curve3Pool (V3 Env Out rates precision feeDen xpChk aChk pullIn pullAdd feeAdj feeLoop getDMem addLiquidity
  alMintAmt alMintAmt_eq)
open Blanc.StableSwapNewton (chkAdd chkMul chkDiv chkSub getDChk loopDChk bodyDChk dPChk)

/-! ## `D` is positive -/

/-- `D_P` at `D = 1` is `0`: the first division's numerator is below its denominator. -/
theorem dPChk_one {x : Fin 3 → Nat} {p : Nat} (h : dPChk x 1 = some p) : p = 0 := by
  unfold dPChk at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨a, ha, b, hb, p0, hp0, c, hc, d, hd, p1, hp1, e, he, f, hf, hp⟩ := h
  have ea := Blanc.StableSwapNewton.chkMul_some ha
  have eb := Blanc.StableSwapNewton.chkMul_some hb
  obtain ⟨e0, n0⟩ := Blanc.StableSwapNewton.chkDiv_some hp0
  have ec := Blanc.StableSwapNewton.chkMul_some hc
  obtain ⟨e1, -⟩ := Blanc.StableSwapNewton.chkDiv_some hp1
  have ee := Blanc.StableSwapNewton.chkMul_some he
  obtain ⟨e2, -⟩ := Blanc.StableSwapNewton.chkDiv_some hp
  have hb3 : 3 ≤ b := by
    have : x 0 ≠ 0 := fun z => n0 (by rw [eb, z])
    rw [eb]
    omega
  have h0 : p0 = 0 := by
    rw [e0, ea]
    exact Nat.div_eq_of_lt (by omega)
  have h1 : p1 = 0 := by rw [e1, ec, h0]; simp only [Nat.zero_mul, Nat.zero_div]
  rw [e2, ee, h1]
  simp only [Nat.zero_mul, Nat.zero_div]

/-- One checked body keeps `D` positive when the sum is. -/
theorem bodyDChk_pos {x : Fin 3 → Nat} {ann S D D' : Nat} (hS : 0 < S) (hD : 0 < D) (h : bodyDChk x ann S D = some D') :
    0 < D' := by
  unfold bodyDChk at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨p, hp, a, ha, b, hb, c, hc, n, hn, u, hu, v, hv, m, hm, den, hden, hdiv⟩ := h
  have ea := Blanc.StableSwapNewton.chkMul_some ha
  have eb := Blanc.StableSwapNewton.chkMul_some hb
  have ec := Blanc.StableSwapNewton.chkAdd_some hc
  have en := Blanc.StableSwapNewton.chkMul_some hn
  obtain ⟨eu, hle⟩ := Blanc.StableSwapNewton.chkSub_some hu
  have ev := Blanc.StableSwapNewton.chkMul_some hv
  have em := Blanc.StableSwapNewton.chkMul_some hm
  have ed := Blanc.StableSwapNewton.chkAdd_some hden
  obtain ⟨eD, hne⟩ := Blanc.StableSwapNewton.chkDiv_some hdiv
  rw [eD]
  refine Nat.div_pos ?_ (Nat.pos_of_ne_zero hne)
  rw [en, ec, ea, eb, ed, ev, em, eu]
  have hann : ann - 1 ≤ ann * S := Nat.le_trans (Nat.sub_le _ _) (Nat.le_mul_of_pos_right _ hS)
  have h1 : (ann - 1) * D ≤ ann * S * D := Nat.mul_le_mul_right _ hann
  by_cases hD1 : D = 1
  · subst hD1
    rw [dPChk_one hp]
    simpa only [Nat.mul_zero, Nat.add_zero, Nat.zero_mul] using h1
  · have h2 : 4 * p ≤ p * 3 * D := by
      have : 2 ≤ D := by omega
      calc 4 * p ≤ p * 3 * 2 := by omega
        _ ≤ p * 3 * D := Nat.mul_le_mul_left _ this
    rw [Nat.add_mul]
    omega

theorem loopDChk_pos {x : Fin 3 → Nat} {ann S tol : Nat} (hS : 0 < S) :
    ∀ {fuel D v}, 0 < D → loopDChk x ann S tol fuel D = some v → 0 < v := by
  intro fuel
  induction fuel with
  | zero =>
    intro D v hD h
    obtain rfl := Option.some.inj h
    exact hD
  | succ n ih =>
    intro D v hD h
    unfold loopDChk at h
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨D', hb, hl⟩ := h
    have hD' := bodyDChk_pos hS hD hb
    split at hl
    · obtain rfl := Option.some.inj hl
      exact hD'
    · exact ih hD' hl

/-- **`D` is positive when the balances' sum is.** -/
theorem getDChk_pos {x : Fin 3 → Nat} {amp tol v : Nat} (hx : 0 < x 0) (h : getDChk x amp tol = some v) : 0 < v := by
  unfold getDChk at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨a, ha, b, hb, S, hS, hl⟩ := h
  have e1 := Blanc.StableSwapNewton.chkAdd_some ha
  have e2 := Blanc.StableSwapNewton.chkAdd_some hb
  have e3 := Blanc.StableSwapNewton.chkAdd_some hS
  have hpos : 0 < S := by
    omega
  rw [if_neg (by omega)] at hl
  simp only [Option.bind_eq_some_iff] at hl
  obtain ⟨ann, -, hl⟩ := hl
  exact loopDChk_pos hpos hpos hl

/-! ## The model -/

/-- The books a deposit of `am` reaches, before fees. -/
abbrev afterDeposit (w : State) (am : V3) : V3 := v3Of fun k => recorded w k + netOf w k (am.get k)

theorem v3_ofFnM_v3Of {f : Fin 3 → Option Nat} {g : Fin 3 → Nat} (h : ∀ k, f k = some (g k)) :
    V3.ofFnM f = some (v3Of g) := by
  simp only [V3.ofFnM, h, Option.bind_eq_bind, Option.bind_some]
  rfl

/-- `getDMem`'s positivity on a first deposit: coin 0's scaled balance is positive. -/
theorem getDMem_pos {b : V3} {amp v : Nat} (h0 : 0 < b.v0) (h : getDMem b amp = some v) : 0 < v := by
  unfold getDMem at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨xp, hxp, hd⟩ := h
  refine getDChk_pos ?_ hd
  rw [Curve3Pool.xpChk_some hxp]
  show 0 < Curve3Pool.precMul.get 0 * b.v0
  exact Nat.mul_pos (precMul_pos 0) h0

/-- The adjusted fee, within its limit. -/
theorem feeAdj_of {s : Curve3Pool.State} (h : s.fee ≤ feeDen) : feeAdj s = some (s.fee * 3 / 8) := by
  have hd : feeDen = 10000000000 := rfl
  have h1 : chkMul s.fee 3 = some (s.fee * 3) := ite_eq_left (by rw [hd] at h; show s.fee * 3 < 2 ^ 256; omega)
  have h2 : chkDiv (s.fee * 3) 8 = some (s.fee * 3 / 8) := ite_eq_right (by decide)
  unfold feeAdj
  rw [h1]
  exact h2

variable {w : State} {s : Curve3Pool.State} {e : Env} {am : V3} {minMint minted amp : Nat} {stored : V3}

/-- **The model accepts the deposit `addOutcome` computes.** -/
theorem add_accepts (hab : Curve3Pool.Abstracts (w.getStor pool) s) (hk : s.isKilled = false) (hfee : word w pool Curve3Pool.feeSlot ≤ feeDen)
    (hA : aChk s e.time = some amp) (hsup : e.supply = some (supply w)) (hok : e.mintOk = true)
    (hpull : ∀ k, pullAdd e (supply w) s.balances am k = some (recorded w k + netOf w k (am.get k)))
    (hout : addOutcome w amp (afterDeposit w am) = some (minted, stored))
    (hmin : minMint ≤ minted) (hfit : supply w + minted < 2 ^ 256) (hpos : supply w = 0 → 0 < am.get 0) :
    ∃ o, addLiquidity s e am minMint = some o ∧ o.state.balances = stored ∧ alMintAmt o = minted := by
  have hsf : word w pool Curve3Pool.feeSlot = s.fee := hab.fee
  have hsa : word w pool Curve3Pool.adminFeeSlot = s.adminFee := hab.adminFee
  have hbk : books w = s.balances := books_of_abstracts hab
  have hfa := feeAdj_of (s := s) (by rw [← hsf]; exact hfee)
  have hnew : V3.ofFnM (pullAdd e (supply w) s.balances am) = some (afterDeposit w am) := v3_ofFnM_v3Of hpull
  have hreqk : Curve3Pool.req (s.isKilled = false) = some () := ite_eq_left hk
  have hreqm : Curve3Pool.req (e.mintOk = true) = some () := ite_eq_left hok
  have hreqmin : Curve3Pool.req (minted ≥ minMint) = some () := ite_eq_left hmin
  have haddT : chkAdd (supply w) minted = some (supply w + minted) := ite_eq_left hfit
  by_cases hT : supply w = 0
  · have hout0 := hout
    unfold addOutcome at hout0
    rw [if_pos hT] at hout0
    obtain ⟨D1, hD1, hp⟩ := Option.map_eq_some_iff.1 hout0
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp
    have hv0 : 0 < (afterDeposit w am).v0 := by
      have h := hpos hT
      show 0 < recorded w 0 + netOf w 0 (am.get 0)
      have : netOf w 0 (am.get 0) = am.get 0 := if_neg (by decide)
      omega
    have hD1pos : 0 < D1 := getDMem_pos hv0 hD1
    have hreqd : Curve3Pool.req (0 < D1) = some () := ite_eq_left hD1pos
    refine ⟨⟨{ s with balances := afterDeposit w am }, none, [.addLiquidity e.caller am V3.zero D1 (0 + D1)],
      Curve3Pool.pullCalls e.caller am ++ [.mint e.caller D1]⟩, ?_, rfl, alMintAmt_eq⟩
    rw [hT] at hnew haddT
    unfold addLiquidity
    simp only [hreqk, hfa, hA, hsup, hT, hnew, hD1, hreqd, hreqmin, hreqm, haddT, Option.bind_eq_bind, Option.bind_some, gt_iff_lt, Nat.lt_irrefl,
      ↓reduceIte]
  · have hout1 := hout
    unfold addOutcome at hout1
    rw [if_neg hT] at hout1
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hout1
    obtain ⟨r, hrun, D0, hinv, D2, hD2, hgate⟩ := hout1
    split at hgate
    · cases hgate
    rename_i hgt
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hgate
    obtain ⟨x, hsb, y, hmu, m, hdv, hp⟩ := hgate
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj hp)
    have hrun0 := hrun
    unfold feeRun at hrun0
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hrun0
    obtain ⟨D0', hinv', D1, hD1, pf, hm, f, hf, r3, hloop, hr3⟩ := hrun0
    have eD : D0 = D0' := Option.some.inj (hinv.symm.trans hinv')
    subst eD
    obtain rfl := Option.some.inj hr3
    have ef : f = s.fee * 3 / 8 := by
      rw [(Blanc.StableSwapNewton.chkDiv_some hf).1, Blanc.StableSwapNewton.chkMul_some hm, hsf]
    rw [ef, hsa, hbk] at hloop
    rw [hD1] at hgt
    have hlt : D0 < D1 := by
      simp only [Option.getD_some] at hgt
      omega
    have hinv2 : getDMem s.balances amp = some D0 := by rw [← hbk]; exact hinv
    have hreqd : Curve3Pool.req (D1 > D0) = some () := ite_eq_left hlt
    obtain ⟨fe, st, af⟩ := r3
    refine ⟨⟨{ s with balances := st }, none, [.addLiquidity e.caller am fe D1 (supply w + m)],
      Curve3Pool.pullCalls e.caller am ++ [.mint e.caller m]⟩, ?_, rfl, alMintAmt_eq⟩
    have hTp : 0 < supply w := Nat.pos_of_ne_zero hT
    dsimp only at hD2 haddT hreqmin ⊢
    unfold addLiquidity
    simp only [hreqk, hfa, hA, hsup, hTp, hT, hinv2, hnew, hD1, hreqd, hloop, hD2, hsb, hmu, hdv, hreqmin, hreqm, haddT, Option.bind_eq_bind, Option.bind_some,
      gt_iff_lt, ↓reduceIte]

/-! ## The calldata -/

section Args

variable {e : Sevm} {am : V3} {minMint : Nat}

theorem addCalldata_length : (addCalldata am minMint).length = 132 := by
  simp only [addCalldata, Curve3Pool.word, List.length_append, B256.length_toBytes, abiSelectorBytes_length]

theorem add_selector (h : e.data = addCalldata am minMint) : Sevm.selector e = Curve3Pool.selAddLiquidity := by
  refine selector_eq_of_data_eq_abiSelectorBytes_append (by decide)
    (tail := Curve3Pool.word am.v0 ++ Curve3Pool.word am.v1 ++ Curve3Pool.word am.v2 ++ Curve3Pool.word minMint) ?_
  rw [h]
  simp only [addCalldata, List.append_assoc]

/-- `addCalldata`'s four words. -/
theorem add_words (h : e.data = addCalldata am minMint) :
    Sevm.dataWord e 4 = Nat.toB256 am.v0 ∧ Sevm.dataWord e 36 = Nat.toB256 am.v1 ∧
      Sevm.dataWord e 68 = Nat.toB256 am.v2 ∧ Sevm.dataWord e 100 = Nat.toB256 minMint := by
  have l4 := abiSelectorBytes_length Curve3Pool.selAddLiquidity
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine Curve3PoolSupply.dataWord_eq_of_append (pre := abiSelectorBytes Curve3Pool.selAddLiquidity)
      (rest := Curve3Pool.word am.v1 ++ Curve3Pool.word am.v2 ++ Curve3Pool.word minMint) ?_ (by rw [l4]; rfl)
    rw [h]; simp only [addCalldata, Curve3Pool.word, List.append_assoc]
  · refine Curve3PoolSupply.dataWord_eq_of_append (pre := abiSelectorBytes Curve3Pool.selAddLiquidity ++ Curve3Pool.word am.v0)
      (rest := Curve3Pool.word am.v2 ++ Curve3Pool.word minMint) ?_
      (by simp only [Curve3Pool.word, List.length_append, B256.length_toBytes, l4]; rfl)
    rw [h]; simp only [addCalldata, Curve3Pool.word, List.append_assoc]
  · refine Curve3PoolSupply.dataWord_eq_of_append
      (pre := abiSelectorBytes Curve3Pool.selAddLiquidity ++ Curve3Pool.word am.v0 ++ Curve3Pool.word am.v1)
      (rest := Curve3Pool.word minMint) ?_
      (by simp only [Curve3Pool.word, List.length_append, B256.length_toBytes, l4]; rfl)
    rw [h]; simp only [addCalldata, Curve3Pool.word, List.append_assoc]
  · refine Curve3PoolSupply.dataWord_eq_of_append
      (pre := abiSelectorBytes Curve3Pool.selAddLiquidity ++ Curve3Pool.word am.v0 ++ Curve3Pool.word am.v1 ++
        Curve3Pool.word am.v2) (rest := []) ?_
      (by simp only [Curve3Pool.word, List.length_append, B256.length_toBytes, l4]; rfl)
    rw [h]; simp only [addCalldata, Curve3Pool.word, List.append_assoc, List.append_nil]

end Args

end Blanc.Composition.Curve3PoolPublic
