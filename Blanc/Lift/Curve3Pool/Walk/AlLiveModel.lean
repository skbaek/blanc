import Blanc.Lift.Curve3Pool.Walk.RliLiveWords
import Blanc.Lift.Curve3Pool.Walk.AlLiveFrame
import Blanc.Lift.Curve3Pool.Walk.AddLiquiditySafe

/-!
# `add_liquidity`: the model, inverted

`addLiquidity_inv`: a successful model `add_liquidity` in any environment, as its steps: the
first deposit (supply `0`: `mint_amount = D1`, no fee) or the fee path (supply positive).
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

/-- **The model's `add_liquidity`, inverted.** -/
theorem addLiquidity_inv {s : State} {e : Env} {a : V3} {m : Nat} {o : Out}
    (h : addLiquidity s e a m = some o) :
    s.isKilled = false ∧ ∃ fee amp T new D1 mint T', feeAdj s = some fee ∧
      aChk s e.time = some amp ∧ e.supply = some T ∧
      V3.ofFnM (pullAdd e T s.balances a) = some new ∧ getDMem new amp = some D1 ∧
      m ≤ mint ∧ e.mintOk = true ∧ chkAdd T mint = some T' ∧
      ((T = 0 ∧ 0 < D1 ∧ mint = D1 ∧ o = ⟨{ s with balances := new }, none,
          [.addLiquidity e.caller a V3.zero D1 T'], pullCalls e.caller a ++ [.mint e.caller D1]⟩) ∨
        (T ≠ 0 ∧ ∃ D0 fees stored after D2 x y, getDMem s.balances amp = some D0 ∧ D0 < D1 ∧
          feeLoop fee s.adminFee D0 D1 s.balances new = some (fees, stored, after) ∧
          getDMem after amp = some D2 ∧ chkSub D2 D0 = some x ∧ chkMul T x = some y ∧
          chkDiv y D0 = some mint ∧
          o = ⟨{ s with balances := stored }, none, [.addLiquidity e.caller a fees D1 T'],
            pullCalls e.caller a ++ [.mint e.caller mint]⟩)) := by
  unfold addLiquidity req at h
  obtain ⟨u0, hk, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨fee, hfee, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨amp, hamp, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨T, hT, h⟩ := Option.bind_eq_some_iff.mp h
  split_ifs at hk with c1
  dsimp only at h
  by_cases hT0 : T = 0
  · subst hT0
    simp only [gt_iff_lt, Nat.lt_irrefl, ↓reduceIte] at h
    obtain ⟨D0, hD0, h⟩ := Option.bind_eq_some_iff.mp h
    obtain rfl := (Option.some.inj hD0).symm
    obtain ⟨new, hnew, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨D1, hD1, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨u1, hlt, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨x3, hx3, h⟩ := Option.bind_eq_some_iff.mp h
    obtain rfl := (Option.some.inj hx3).symm
    obtain ⟨mint, hmint, h⟩ := Option.bind_eq_some_iff.mp h
    obtain rfl := (Option.some.inj hmint).symm
    obtain ⟨u2, hmin, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨u3, hok, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨T', hT', h⟩ := Option.bind_eq_some_iff.mp h
    obtain rfl := (Option.some.inj h).symm
    split_ifs at hlt hmin hok with c2 c3 c4
    exact ⟨c1, fee, amp, 0, new, mint, mint, T', hfee, hamp, hT, hnew, hD1, c3, c4, hT',
      .inl ⟨rfl, c2, rfl, rfl⟩⟩
  · have hTp : 0 < T := Nat.pos_of_ne_zero hT0
    simp only [gt_iff_lt, hTp, hT0, ↓reduceIte] at h
    obtain ⟨D0, hD0, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨new, hnew, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨D1, hD1, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨u1, hlt, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨⟨fees, stored, after⟩, hfl, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨D2, hD2, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨x3, hx3, h⟩ := Option.bind_eq_some_iff.mp h
    obtain rfl := (Option.some.inj hx3).symm
    obtain ⟨x, hx, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨y, hy, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨mint, hmint, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨u2, hmin, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨u3, hok, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨T', hT', h⟩ := Option.bind_eq_some_iff.mp h
    obtain rfl := (Option.some.inj h).symm
    split_ifs at hlt hmin hok with c2 c3 c4
    exact ⟨c1, fee, amp, T, new, D1, mint, T', hfee, hamp, hT, hnew, hD1, c3, c4, hT',
      .inr ⟨hT0, D0, fees, stored, after, D2, x, y, hD0, c2, hfl, hD2, hx, hy, hmint, rfl⟩⟩

/-- One coin's credit, inverted: on a first deposit the amount is positive; the credited value
`c` is `pullIn`'s answer for a positive amount and `0` otherwise, and the new balance is
`old + c`, checked. -/
theorem al_pullAdd_inv {e : Env} {T : Nat} {old amounts : V3} {k : Fin 3} {n : Nat}
    {B amt : B256} (hp : pullAdd e T old amounts k = some n) (hamt : amounts.get k = amt.toNat)
    (hold : old.get k = B.toNat) :
    (T = 0 → amt ≠ 0) ∧ ∃ c, (amt ≠ 0 → pullIn e k amt.toNat = some c) ∧ (amt = 0 → c = 0) ∧
      chkAdd B.toNat c = some n := by
  have hpos : amt.toNat > 0 ↔ amt ≠ 0 := by
    constructor
    · intro h ha; rw [ha] at h; exact Nat.lt_irrefl 0 h
    · intro h; exact Nat.pos_of_ne_zero (toNat_ne_zero h)
  unfold pullAdd req at hp
  rw [hamt, hold] at hp
  dsimp only at hp
  by_cases ha : amt = 0
  · have hn : ¬ amt.toNat > 0 := fun h => hpos.mp h ha
    simp only [hn, ↓reduceIte] at hp
    by_cases hT : T = 0
    · simp only [hT, ↓reduceIte] at hp
      obtain ⟨u, hu, -⟩ := Option.bind_eq_some_iff.mp hp
      cases hu
    · simp only [hT, ↓reduceIte] at hp
      obtain ⟨u, -, hp⟩ := Option.bind_eq_some_iff.mp hp
      obtain ⟨c, hc, hp⟩ := Option.bind_eq_some_iff.mp hp
      obtain rfl := (Option.some.inj hc).symm
      exact ⟨fun h => absurd h hT, 0, fun h => absurd ha h, fun _ => rfl, hp⟩
  · have hn : amt.toNat > 0 := hpos.mpr ha
    simp only [hn, ↓reduceIte] at hp
    have key : ∀ {X : Option Unit}, (X = some () ) →
        (do let __r ← X; let credited ← pullIn e k amt.toNat; chkAdd B.toNat credited) = some n →
        ∃ c, pullIn e k amt.toNat = some c ∧ chkAdd B.toNat c = some n := by
      intro X hX h
      subst hX
      obtain ⟨u, -, h⟩ := Option.bind_eq_some_iff.mp h
      exact Option.bind_eq_some_iff.mp h
    by_cases hT : T = 0
    · simp only [hT, ↓reduceIte] at hp
      obtain ⟨c, hc, hp⟩ := key rfl hp
      exact ⟨fun _ => ha, c, fun _ => hc, fun h => absurd h ha, hp⟩
    · simp only [hT, ↓reduceIte] at hp
      obtain ⟨c, hc, hp⟩ := key rfl hp
      exact ⟨fun h => absurd h hT, c, fun _ => hc, fun h => absurd h ha, hp⟩

/-- **The premised environment**: 3Crv's `totalSupply()` answers `T`; every `transferFrom` is
accepted; the fee coin's `balanceOf(self)` answers `B1` before and `B2` after its pull; `mint` is
accepted. -/
def alEnvW (sevm : Sevm) (T B1 B2 : Nat) : Env :=
  ⟨sevm.benvStat.time.toNat, sevm.caller.toB256.toNat, sevm.value.toNat,
    fun k => if k = feeIndex then ⟨some B1, some B2, true, false⟩ else ⟨none, none, true, false⟩,
    some T, true, false⟩

theorem alEnvW_pullIn01 {sevm : Sevm} {T B1 B2 : Nat} {k : Fin 3} (hk : k ≠ feeIndex) (amt : Nat) :
    pullIn (alEnvW sevm T B1 B2) k amt = some amt := by
  unfold pullIn alEnvW req
  simp only [hk, ↓reduceIte]
  rfl

theorem alEnvW_pullIn2 {sevm : Sevm} {T B1 B2 : Nat} (amt : Nat) :
    pullIn (alEnvW sevm T B1 B2) feeIndex amt = chkSub B2 B1 := by
  unfold pullIn alEnvW req
  simp only [↓reduceIte]
  rfl

/-- The model's step on the decoded call is `addLiquidity`, once the selector is known. -/
theorem al_body {sevm : Sevm} {s : State} {e : Env} {o : Out} (hlen : 4 ≤ sevm.data.length)
    (hsel : Sevm.selector sevm = selAddLiquidity)
    (h : step s e (decodeCall sevm) = some o) :
    e.value = 0 ∧ addLiquidity s e (argV3 sevm 0) (arg sevm 3) = some o := by
  rw [decodeCall_at (k := 3) rfl hsel hlen] at h
  have h' : (if e.value = 0 then body s e (.addLiquidity (argV3 sevm 0) (arg sevm 3))
      else none) = some o := h
  split_ifs at h' with hv
  exact ⟨hv, h'⟩

/-- The credit the forward run adds to coin `j`: the amount, or for the fee coin the balance
difference (`alCr2`). -/
abbrev alCrK (sevm : Sevm) (B1 B2 : B256) (j : Nat) : B256 :=
  if j = 2 then alCr2 sevm B1 B2 else alAmt sevm j

/-- **One coin's credit in the premised environment, as words.** -/
theorem al_coin_words {sevm : Sevm} {T : Nat} {B1 B2 : B256} {old : V3} {σ : Stor} {k : Fin 3}
    {n : Nat} (hp : pullAdd (alEnvW sevm T B1.toNat B2.toNat) T old (argV3 sevm 0) k = some n)
    (hold : old.get k = (balAt σ k.val).toNat) :
    (T = 0 → alAmt sevm k.val ≠ 0) ∧ (k = feeIndex → alAmt sevm 2 ≠ 0 → ¬ B2 < B1) ∧
      ¬ balAt σ k.val + alCrK sevm B1 B2 k.val < balAt σ k.val ∧
      n = (balAt σ k.val + alCrK sevm B1 B2 k.val).toNat := by
  obtain ⟨ht, c, hin, hz, hadd⟩ := al_pullAdd_inv hp (al_amt sevm k) hold
  have fin : c = (alCrK sevm B1 B2 k.val).toNat →
      ¬ balAt σ k.val + alCrK sevm B1 B2 k.val < balAt σ k.val ∧
        n = (balAt σ k.val + alCrK sevm B1 B2 k.val).toNat := by
    intro hc
    rw [hc] at hadd
    obtain ⟨hlt, rfl⟩ := chkAdd_inv hadd
    exact ⟨(B256.nof_iff_not_add_lt _ _).mp hlt, rfl⟩
  by_cases hk : k = feeIndex
  · subst hk
    have hk2 : (feeIndex : Fin 3).val = 2 := rfl
    rw [hk2] at ht hin hz fin ⊢
    by_cases ha : alAmt sevm 2 = 0
    · refine ⟨ht, fun _ h => absurd ha h, fin ?_⟩
      rw [hz ha]
      simp only [alCrK, alCr2, ↓reduceIte, ha]
      rfl
    · have h2 := hin ha
      rw [alEnvW_pullIn2] at h2
      obtain ⟨hle, rfl⟩ := chkSub_word h2
      have hge : ¬ B2 < B1 := fun h => absurd (B256.lt_iff_toNat_lt_toNat.mp h) (Nat.not_lt.mpr hle)
      refine ⟨ht, fun _ _ => hge, fin ?_⟩
      simp only [alCrK, alCr2, ↓reduceIte, ha]
  · have hk2 : k.val ≠ 2 := fun h => hk (Fin.ext h)
    refine ⟨ht, fun h => absurd h hk, fin ?_⟩
    simp only [alCrK, hk2, ↓reduceIte]
    by_cases ha : alAmt sevm k.val = 0
    · rw [hz ha, ha]; rfl
    · have h2 := hin ha
      rw [alEnvW_pullIn01 hk] at h2
      exact (Option.some.inj h2).symm

end Blanc.Lift.Curve3Pool
