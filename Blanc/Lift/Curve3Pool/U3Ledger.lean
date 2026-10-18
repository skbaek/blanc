import Blanc.Lift.Curve3Pool.U3History
import Blanc.Lift.Curve3Pool.SupplyMoves

/-!
# The six U3 bounds at a ledger supply (pure)

`U3Step` (`U3History.lean`) states the six U3 bounds of goal §11 with `T` the supply the step
observed (`e.supply = some T`) and `T' = supplyAfter T o.calls`.  `U3Ledger s e c o T T'` states the
same bounds at given pre- and post-supplies `T` and `T'`, with no supply premise: it follows from an
accepted step whose observed supply, if any, is `T` and whose own calls take `T` to `T'`
(`u3Ledger_of_step`).  The composed U3 theorem instantiates `T`, `T'` with 3Crv's ledger supply at
the frame's entry and post.
-/

namespace Blanc.Lift.Curve3Pool

open Blanc.StableSwapNewton

/-- **The six U3 bounds at pre-supply `T` and post-supply `T'`** (goal §11), each at fixed `amp`,
`D` the stored balances' `get_D` and `D'` the result's. -/
def U3Ledger (s : State) (e : Env) (c : Call) (o : Out) (T T' : Nat) : Prop :=
  (∀ a mins, c = .removeLiquidity a mins → ∀ amp D D', 0 < T →
    getDMem s.balances amp = some D → getDMem o.state.balances amp = some D' →
    (∀ t, aChk o.state t = aChk s t) ∧
    D * T' ≤ (D' + 1) * T + (D - floorRoot (xpOf s.balances) (amp * 3)) * T') ∧
  (c = .donateAdminFees → (∀ k v, (e.coin k).balPre = some v → s.balances.get k ≤ v) →
    ∀ amp D D', getDMem o.state.balances amp = some D' →
    (∀ t, aChk o.state t = aChk s t) ∧ T' = T ∧
      floorRoot (xpOf s.balances) (amp * 3) ≤ D' ∧
      D ≤ D' + (D - floorRoot (xpOf s.balances) (amp * 3))) ∧
  (∀ am mm, c = .addLiquidity am mm → ∀ amp D D', aChk s e.time = some amp →
    0 < T → s.adminFee ≤ feeDen →
    getDMem s.balances amp = some D → getDMem o.state.balances amp = some D' →
    (∀ t, aChk o.state t = aChk s t) ∧ ∃ mid D2, getDMem mid amp = some D2 ∧
      (∀ k, mid.get k ≤ o.state.balances.get k) ∧
      D * T' ≤ (D' + (D2 - floorRoot (xpOf mid) (amp * 3))) * T) ∧
  (∀ am mb, c = .removeLiquidityImbalance am mb → ∀ amp D D', aChk s e.time = some amp →
    s.adminFee ≤ feeDen →
    getDMem s.balances amp = some D → getDMem o.state.balances amp = some D' →
    (∀ t, aChk o.state t = aChk s t) ∧ ∃ mid D2, getDMem mid amp = some D2 ∧
      (∀ k, mid.get k ≤ o.state.balances.get k) ∧
      D * T' ≤ (D' + (D2 - floorRoot (xpOf mid) (amp * 3))) * T) ∧
  (∀ i j dx md, c = .exchange i j dx md → ∃ i' j' : Fin 3, idx i = some i' ∧ idx j = some j' ∧
    ∀ amp D D', aChk s e.time = some amp → s.adminFee ≤ feeDen →
    getDMem s.balances amp = some D → getDMem o.state.balances amp = some D' →
    (∀ t, aChk o.state t = aChk s t) ∧ T' = T ∧
      D ≤ D' + yGap (xpOf s.balances) i' j' (xpOf o.state.balances i') D (amp * 3)) ∧
  (∀ a i mn, c = .removeLiquidityOneCoin a i mn → ∃ i' : Fin 3, idx i = some i' ∧
    ∀ amp D D', aChk s e.time = some amp → s.adminFee ≤ feeDen →
    getDMem s.balances amp = some D → getDMem o.state.balances amp = some D' →
    (∀ t, aChk o.state t = aChk s t) ∧
    D * T' ≤ (D' + oneGap (xpOf s.balances) i' (D - a * D / T) (amp * 3)) * T)

/-! ## The supply-reading steps read a supply -/

theorem addLiquidity_supply {s : State} {e : Env} {am : V3} {mm : Nat} {o : Out}
    (h : addLiquidity s e am mm = some o) : ∃ T, e.supply = some T := by
  unfold addLiquidity at h
  obtain ⟨_, -, h⟩ := bind_some h
  obtain ⟨_, -, h⟩ := bind_some h
  obtain ⟨_, -, h⟩ := bind_some h
  obtain ⟨T, hT, -⟩ := bind_some h
  exact ⟨T, hT⟩

theorem removeLiquidityImbalance_supply {s : State} {e : Env} {am : V3} {mb : Nat} {o : Out}
    (h : removeLiquidityImbalance s e am mb = some o) : ∃ T, e.supply = some T := by
  unfold removeLiquidityImbalance at h
  obtain ⟨_, -, h⟩ := bind_some h
  obtain ⟨T, hT, -⟩ := bind_some h
  exact ⟨T, hT⟩

theorem removeLiquidityOneCoin_supply {s : State} {e : Env} {a : Nat} {i : Fin 3} {mn : Nat}
    {o : Out} (h : removeLiquidityOneCoin s e a i mn = some o) : ∃ T, e.supply = some T := by
  unfold removeLiquidityOneCoin at h
  obtain ⟨_, -, h⟩ := bind_some h
  obtain ⟨_, hc, -⟩ := bind_some h
  unfold calcWithdrawOne at hc
  obtain ⟨_, -, hc⟩ := bind_some hc
  obtain ⟨_, -, hc⟩ := bind_some hc
  obtain ⟨T, hT, -⟩ := bind_some hc
  exact ⟨T, hT⟩

/-- **The six U3 bounds at the step's supplies.**  An accepted step whose observed supply, if any,
is `T`, and whose calls take `T` to `T'`, satisfies the six U3 bounds at `T` and `T'`. -/
theorem u3Ledger_of_step {s : State} {e : Env} {c : Call} {o : Out} {T T' : Nat}
    (h : step s e c = some o) (hT : ∀ T₀, e.supply = some T₀ → T₀ = T)
    (hT' : supplyAfter T o.calls = T') : U3Ledger s e c o T T' := by
  have hb := pool_step_body h
  obtain ⟨u1, u2, u3, u4, u5, u6⟩ := u3Step_of_step h
  subst hT'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro a mins rfl amp D D' hT0 hD hD'
    obtain ⟨-, T₀, hT₀, -⟩ := removeLiquidity_some hb
    have e₀ := hT T₀ hT₀
    subst e₀
    exact u1 a mins rfl T₀ amp D D' hT₀ hT0 hD hD'
  · rintro rfl hcoin amp D D' hD'
    exact u2 rfl hcoin T amp D D' hD'
  · rintro am mm rfl amp D D' hA hT0 hadm hD hD'
    obtain ⟨T₀, hT₀⟩ := addLiquidity_supply hb
    have e₀ := hT T₀ hT₀
    subst e₀
    exact u3 am mm rfl T₀ amp D D' hA hT₀ hT0 hadm hD hD'
  · rintro am mb rfl amp D D' hA hadm hD hD'
    obtain ⟨T₀, hT₀⟩ := removeLiquidityImbalance_supply hb
    have e₀ := hT T₀ hT₀
    subst e₀
    exact u4 am mb rfl T₀ amp D D' hA hT₀ hadm hD hD'
  · rintro i j dx md rfl
    obtain ⟨i', j', hi, hj, k⟩ := u5 i j dx md rfl
    exact ⟨i', j', hi, hj, fun amp D D' hA hadm hD hD' => k T amp D D' hA hadm hD hD'⟩
  · rintro a i mn rfl
    obtain ⟨i', hi, k⟩ := u6 a i mn rfl
    refine ⟨i', hi, fun amp D D' hA hadm hD hD' => ?_⟩
    simp only [body, Option.bind_eq_bind, Option.bind_eq_some_iff] at hb
    obtain ⟨i'', hi'', hx⟩ := hb
    rw [hi] at hi''
    cases Option.some.inj hi''
    obtain ⟨T₀, hT₀⟩ := removeLiquidityOneCoin_supply hx
    have e₀ := hT T₀ hT₀
    subst e₀
    exact k T₀ amp D D' hA hT₀ hadm hD hD'

/-! ## The admin fee stays bounded -/

/-- The admin fee and the committed future admin fee are at most `MAX_ADMIN_FEE`. -/
def FeeBounded (s : State) : Prop := s.adminFee ≤ maxAdminFee ∧ s.futureAdminFee ≤ maxAdminFee

/-- **Every accepted body keeps the admin fees bounded**: only `commit_new_fee` (which asserts
`new_admin_fee ≤ MAX_ADMIN_FEE`) writes the future admin fee, and only `apply_new_fee` (which
copies it) writes the admin fee. -/
theorem body_feeBounded (s : State) (e : Env) (c : Call) (hs : FeeBounded s) :
    OptAll (fun o => FeeBounded o.state) (body s e c) := by
  cases c <;> simp only [body, Curve3Pool.addLiquidity, Curve3Pool.exchange,
    Curve3Pool.removeLiquidity, Curve3Pool.removeLiquidityImbalance,
    Curve3Pool.removeLiquidityOneCoin, Curve3Pool.rampA, Curve3Pool.stopRampA,
    Curve3Pool.commitNewFee, Curve3Pool.applyNewFee, Curve3Pool.revertNewParameters,
    Curve3Pool.commitTransferOwnership, Curve3Pool.applyTransferOwnership,
    Curve3Pool.revertTransferOwnership, Curve3Pool.withdrawAdminFees,
    Curve3Pool.donateAdminFees, Curve3Pool.killMe, Curve3Pool.unkillMe] <;> opt_walk
  all_goals first
    | exact OptAll.none'
    | exact OptAll.some' hs
    | exact OptAll.some' ⟨hs.1, ‹_ ≤ maxAdminFee›⟩
    | exact OptAll.some' ⟨hs.2, hs.2⟩

/-- Every accepted step keeps the admin fees bounded. -/
theorem feeBounded_keeps : StepKeeps FeeBounded := by
  intro s e c o h hs
  exact body_feeBounded s e c hs o (pool_step_body h)

theorem FeeBounded.le_feeDen {s : State} (h : FeeBounded s) : s.adminFee ≤ feeDen := by
  have := h.1
  simp only [maxAdminFee, feeDen] at this ⊢
  omega

end Blanc.Lift.Curve3Pool
