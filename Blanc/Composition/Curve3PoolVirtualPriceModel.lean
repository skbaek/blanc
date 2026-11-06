import Blanc.Lift.Curve3Pool.U3Ledger
import Blanc.Lift.Curve3Pool.Decode

/-!
# The virtual-price bound's literal model facts

`U3Ledger`'s `add_liquidity` and `remove_liquidity_imbalance` arms name their fee-loop balances only
through an existential. The public bound names them literally, as `feeLoop`'s third component:

* `addLiquidity_literal`, `removeLiquidityImbalance_literal`: the bound at that literal witness, with
  the fee loop's inputs exposed;
* `step_quiet`: an accepted step of an entry other than the five that move the books and the two that
  mint or burn leaves the books and the supply as they were.
-/

namespace Blanc.Composition.Curve3PoolVirtualPrice

open Blanc.Lift.Curve3Pool
open Blanc.StableSwapNewton

/-- **`add_liquidity`'s bound at its literal fee-loop balances.** -/
theorem addLiquidity_literal {s : State} {e : Env} {am : V3} {mm : Nat} {o : Out}
    {T amp D D' : Nat} (h : addLiquidity s e am mm = some o) (hA : aChk s e.time = some amp)
    (hT : e.supply = some T) (hT0 : 0 < T) (hadm : s.adminFee ≤ feeDen)
    (hD : getDMem s.balances amp = some D) (hD' : getDMem o.state.balances amp = some D') :
    ∃ new D1 fee fees stored mid D2, V3.ofFnM (pullAdd e T s.balances am) = some new ∧
      getDMem new amp = some D1 ∧ feeAdj s = some fee ∧
      feeLoop fee s.adminFee D D1 s.balances new = some (fees, stored, mid) ∧
      getDMem mid amp = some D2 ∧
      D * supplyAfter T o.calls ≤ (D' + (D2 - floorRoot (xpOf mid) (amp * 3))) * T := by
  unfold addLiquidity at h
  obtain ⟨_, -, h⟩ := bind_some h
  obtain ⟨fee, hfee, h⟩ := bind_some h
  obtain ⟨amp', hA', h⟩ := bind_some h
  rw [hA] at hA'
  cases Option.some.inj hA'
  obtain ⟨T', hT', h⟩ := bind_some h
  rw [hT] at hT'
  cases Option.some.inj hT'
  dsimp only at h
  simp only [hT0, ↓reduceIte] at h
  obtain ⟨D0, hD0, h⟩ := bind_some h
  rw [hD] at hD0
  cases Option.some.inj hD0
  obtain ⟨new, hnew, h⟩ := bind_some h
  obtain ⟨D1, hD1, h⟩ := bind_some h
  obtain ⟨_, -, h⟩ := bind_some h
  obtain ⟨x3, hfl, h⟩ := bind_some h
  obtain ⟨fees, stored, mid⟩ := x3
  obtain ⟨D2, hD2, h⟩ := bind_some h
  obtain ⟨x4, hx4, h⟩ := bind_some h
  cases Option.some.inj hx4
  simp only [Nat.pos_iff_ne_zero.mp hT0, ↓reduceIte] at h
  obtain ⟨d, hd, h⟩ := bind_some h
  obtain ⟨p, hp, h⟩ := bind_some h
  obtain ⟨mint, hmint, h⟩ := bind_some h
  obtain ⟨_, -, h⟩ := bind_some h
  obtain ⟨_, -, h⟩ := bind_some h
  obtain ⟨_, -, h⟩ := bind_some h
  cases Option.some.inj h
  refine ⟨new, D1, fee, fees, stored, mid, D2, hnew, hD1, hfee, hfl, hD2, ?_⟩
  rw [supplyAfter_pullCalls]
  simp only [supplyAfter]
  have hm := floorRoot_le_of_below (feeLoop_some hfl hadm) hD'
  obtain ⟨rfl, hDD2⟩ := chkSub_some hd
  rw [chkMul_some hp] at hmint
  obtain ⟨rfl, -⟩ := chkDiv_some hmint
  have h1 : D * (T * (D2 - D) / D) ≤ T * (D2 - D) := Nat.mul_div_le _ _
  generalize floorRoot (xpOf mid) (amp * 3) = m at hm ⊢
  generalize T * (D2 - D) / D = q at h1 ⊢
  have e1 : D * (T + q) = D * T + D * q := Nat.mul_add _ _ _
  have e2 : T * (D2 - D) + T * D = T * D2 := by rw [← Nat.mul_add, Nat.sub_add_cancel hDD2]
  have e3 : D2 * T ≤ (D' + (D2 - m)) * T := Nat.mul_le_mul_right _ (by omega)
  have e4 : D * T = T * D := Nat.mul_comm _ _
  have e5 : D2 * T = T * D2 := Nat.mul_comm _ _
  omega

/-- **`remove_liquidity_imbalance`'s bound at its literal fee-loop balances.** -/
theorem removeLiquidityImbalance_literal {s : State} {e : Env} {am : V3} {mb : Nat} {o : Out}
    {T amp D D' : Nat} (h : removeLiquidityImbalance s e am mb = some o)
    (hA : aChk s e.time = some amp) (hT : e.supply = some T) (hadm : s.adminFee ≤ feeDen)
    (hD : getDMem s.balances amp = some D) (hD' : getDMem o.state.balances amp = some D') :
    ∃ new D1 fee fees stored mid D2, V3.ofFnM (fun k => chkSub (s.balances.get k) (am.get k)) = some new ∧
      getDMem new amp = some D1 ∧ feeAdj s = some fee ∧
      feeLoop fee s.adminFee D D1 s.balances new = some (fees, stored, mid) ∧
      getDMem mid amp = some D2 ∧
      D * supplyAfter T o.calls ≤ (D' + (D2 - floorRoot (xpOf mid) (amp * 3))) * T := by
  unfold removeLiquidityImbalance at h
  obtain ⟨_, -, h⟩ := bind_some h
  obtain ⟨T', hT', h⟩ := bind_some h
  rw [hT] at hT'
  cases Option.some.inj hT'
  obtain ⟨_, -, h⟩ := bind_some h
  obtain ⟨fee, hfee, h⟩ := bind_some h
  obtain ⟨amp', hA', h⟩ := bind_some h
  rw [hA] at hA'
  cases Option.some.inj hA'
  obtain ⟨D0, hD0, h⟩ := bind_some h
  rw [hD] at hD0
  cases Option.some.inj hD0
  obtain ⟨new, hnew, h⟩ := bind_some h
  obtain ⟨D1, hD1, h⟩ := bind_some h
  obtain ⟨x3, hfl, h⟩ := bind_some h
  obtain ⟨fees, stored, mid⟩ := x3
  obtain ⟨D2, hD2, h⟩ := bind_some h
  obtain ⟨d, hd, h⟩ := bind_some h
  obtain ⟨p, hp, h⟩ := bind_some h
  obtain ⟨q, hq, h⟩ := bind_some h
  obtain ⟨_, -, h⟩ := bind_some h
  obtain ⟨burn, hburn, h⟩ := bind_some h
  obtain ⟨_, -, h⟩ := bind_some h
  obtain ⟨_, -, h⟩ := bind_some h
  obtain ⟨_, -, h⟩ := bind_some h
  obtain ⟨T'', hT'', h⟩ := bind_some h
  cases Option.some.inj h
  refine ⟨new, D1, fee, fees, stored, mid, D2, hnew, hD1, hfee, hfl, hD2, ?_⟩
  simp only [supplyAfter, supplyAfter_pushCalls]
  have hm := floorRoot_le_of_below (feeLoop_some hfl hadm) hD'
  obtain ⟨rfl, hD2D⟩ := chkSub_some hd
  rw [chkMul_some hp] at hq
  obtain ⟨rfl, hD0⟩ := chkDiv_some hq
  rw [chkAdd_some hburn] at hT''
  have hle := (chkSub_some hT'').2
  have h1 : (D - D2) * T < D * ((D - D2) * T / D + 1) :=
    Nat.lt_mul_div_succ _ (Nat.pos_of_ne_zero hD0)
  rw [chkAdd_some hburn]
  generalize floorRoot (xpOf mid) (amp * 3) = m at hm ⊢
  generalize (D - D2) * T / D + 1 = b at h1 hle ⊢
  have e1 : D * (T - b) + D * b = D * T := by rw [← Nat.mul_add, Nat.sub_add_cancel hle]
  have e2 : (D - D2) * T + D2 * T = D * T := by rw [← Nat.add_mul, Nat.sub_add_cancel hD2D]
  have e3 : D2 * T ≤ (D' + (D2 - m)) * T := Nat.mul_le_mul_right _ (by omega)
  omega

/-- The entries that leave the books and the supply alone. -/
def Call.quiet : Call → Bool
  | .addLiquidity .. | .exchange .. | .removeLiquidity .. | .removeLiquidityImbalance ..
  | .removeLiquidityOneCoin .. | .donateAdminFees => false
  | _ => true

/-- **An accepted body of a quiet entry keeps the books, and its calls keep the supply.** -/
theorem body_quiet (s : State) (e : Env) (c : Call) (hc : Call.quiet c = true) :
    OptAll (fun o => o.state.balances = s.balances ∧ ∀ T, supplyAfter T o.calls = T) (body s e c) := by
  cases c <;> first
    | exact Bool.noConfusion hc
    | (simp only [body, viewOut, Blanc.Lift.Curve3Pool.rampA, Blanc.Lift.Curve3Pool.stopRampA, Blanc.Lift.Curve3Pool.commitNewFee,
        Blanc.Lift.Curve3Pool.applyNewFee, Blanc.Lift.Curve3Pool.revertNewParameters, Blanc.Lift.Curve3Pool.commitTransferOwnership,
        Blanc.Lift.Curve3Pool.applyTransferOwnership, Blanc.Lift.Curve3Pool.revertTransferOwnership,
        Blanc.Lift.Curve3Pool.withdrawAdminFees, Blanc.Lift.Curve3Pool.killMe, Blanc.Lift.Curve3Pool.unkillMe] <;> opt_walk
       all_goals first
         | exact OptAll.none'
         | exact OptAll.some' ⟨rfl, fun _ => rfl⟩
         | exact OptAll.some' ⟨rfl, fun T => supplyAfter_pushCalls T _ _⟩)

/-- **An accepted step of a quiet entry keeps the books and the supply.** -/
theorem step_quiet {s : State} {e : Env} {c : Call} {o : Out} (hc : Call.quiet c = true)
    (h : step s e c = some o) (T : Nat) :
    o.state.balances = s.balances ∧ supplyAfter T o.calls = T := by
  obtain ⟨hb, hT⟩ := body_quiet s e c hc o (pool_step_body h)
  exact ⟨hb, hT T⟩

/-- A dispatcher position outside the six that move the books decodes to a quiet entry. -/
theorem callAt_quiet (e : Jaune.Sevm) {k : Nat} (hk : k ∉ [3, 6, 7, 8, 10, 21]) :
    Call.quiet (callAt e k) = true := by
  unfold callAt
  split <;> first | rfl | exact absurd (by decide) hk

theorem sels_six_or_quiet :
    ∀ sel ∈ sels, sel = selAddLiquidity ∨ sel = selExchange ∨ sel = selRemoveLiquidity ∨
      sel = selRemoveLiquidityImbalance ∨ sel = selRemoveLiquidityOneCoin ∨ sel = selDonateAdminFees ∨
      (sels.findIdx? (· = sel)).all (fun k => decide (k ∉ [3, 6, 7, 8, 10, 21])) = true := by
  decide +kernel

/-- **A selector other than the six decodes to a quiet entry.** -/
theorem decodeCall_quiet {e : Jaune.Sevm}
    (h1 : Blanc.Sevm.selector e ≠ selAddLiquidity) (h2 : Blanc.Sevm.selector e ≠ selExchange)
    (h3 : Blanc.Sevm.selector e ≠ selRemoveLiquidity)
    (h4 : Blanc.Sevm.selector e ≠ selRemoveLiquidityImbalance)
    (h5 : Blanc.Sevm.selector e ≠ selRemoveLiquidityOneCoin)
    (h6 : Blanc.Sevm.selector e ≠ selDonateAdminFees) : Call.quiet (decodeCall e) = true := by
  rw [decodeCall]
  split
  · rfl
  · split
    · rename_i k hk
      have hin : Blanc.Sevm.selector e ∈ sels := by
        obtain ⟨hlt, heq⟩ := List.findIdx?_eq_some_iff_getElem.mp hk
        have := of_decide_eq_true heq.1
        rw [← this]
        exact List.getElem_mem hlt
      rcases sels_six_or_quiet _ hin with h | h | h | h | h | h | h
      · exact absurd h h1
      · exact absurd h h2
      · exact absurd h h3
      · exact absurd h h4
      · exact absurd h h5
      · exact absurd h h6
      · rw [hk] at h
        exact callAt_quiet e (of_decide_eq_true h)
    · rfl

/-- What `pullAdd` adds at a nonzero supply: the amount, or for USDT its two replies' difference. -/
theorem pullAdd_value {e : Env} {T : Nat} {old am : V3} {k : Fin 3} {v : Nat} (hT : T ≠ 0)
    (h : pullAdd e T old am k = some v) :
    (¬ (k = 2 ∧ am.get k > 0) → v = old.get k + am.get k) ∧
      (k = 2 → am.get k > 0 → ∃ w w', (e.coin 2).balPre = some w ∧ (e.coin 2).balPost = some w' ∧
        v = old.get 2 + (w' - w)) := by
  unfold pullAdd at h
  simp only [hT, ↓reduceIte] at h
  obtain ⟨_, -, h⟩ := bind_some h
  by_cases hpos : am.get k > 0
  · simp only [hpos, ↓reduceIte] at h
    obtain ⟨credited, hc, h⟩ := bind_some h
    have hv := chkAdd_some h
    subst hv
    unfold pullIn at hc
    by_cases hk : k = 2
    · subst hk
      simp only [feeIndex, ↓reduceIte] at hc
      obtain ⟨w, hw, hc⟩ := bind_some hc
      obtain ⟨_, -, hc⟩ := bind_some hc
      obtain ⟨w', hw', hc⟩ := bind_some hc
      obtain ⟨rfl, -⟩ := chkSub_some hc
      exact ⟨fun hn => absurd ⟨rfl, hpos⟩ hn, fun _ _ => ⟨w, w', hw, hw', rfl⟩⟩
    · have hne : k ≠ feeIndex := hk
      simp only [hne, ↓reduceIte] at hc
      obtain ⟨_, -, hc⟩ := bind_some hc
      cases Option.some.inj hc
      exact ⟨fun _ => rfl, fun e => absurd e hk⟩
  · simp only [hpos, ↓reduceIte] at h
    obtain ⟨credited, hc, h⟩ := bind_some h
    have hv := chkAdd_some h
    subst hv
    cases Option.some.inj hc
    have hz : am.get k = 0 := by omega
    exact ⟨fun _ => by rw [hz], fun _ p => absurd p hpos⟩

end Blanc.Composition.Curve3PoolVirtualPrice
