import Blanc.Lift.Curve3Pool.AmpHistory
import Blanc.Lift.Curve3Pool.U3Bounds

/-!
# Curve 3pool: the U3 bounds over the committed history (goal §11, design §3.1)

The six proved bounds "monotone up to the Newton loop error" of `U3Bounds.lean` hold of every
committed step of the replay: at the state `sᵢ` the replay reaches before an invocation, with the
amplification `amp` the model reads at the invocation's recorded time (its block's header timestamp,
`AmpHistory.lean`) held fixed, `D = get_D(xp(sᵢ), amp)`, `D' = get_D(xp(o), amp)` and `T` the 3Crv
supply the frame observed (`EnvOf.supply`, a child reply), the decoded operation's bound holds.

* `U3Step s e c o` — the six bounds for an accepted step `step s e c = some o`, one conjunct per
  operation, each under exactly the premises its `u3_bound_*` theorem takes;
* `u3Step_of_step` — every accepted step satisfies them (inverting `step` to `body`);
* `pool_history_u3` — the history form: every invocation of the replay is an accepted step with
  `U3Step`, at its header time.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc Blanc.ExecutionTrace Blanc.StableSwapNewton

/-- **The six U3 bounds for one accepted step** (goal §11), each at fixed `amp`, `D` the stored
balances' `get_D` and `D'` the result's, `T` the observed supply. -/
def U3Step (s : State) (e : Env) (c : Call) (o : Out) : Prop :=
  (∀ a mins, c = .removeLiquidity a mins → ∀ T amp D D', e.supply = some T → 0 < T →
    getDMem s.balances amp = some D → getDMem o.state.balances amp = some D' →
    (∀ t, aChk o.state t = aChk s t) ∧
    D * supplyAfter T o.calls ≤
      (D' + 1) * T + (D - floorRoot (xpOf s.balances) (amp * 3)) * supplyAfter T o.calls) ∧
  (c = .donateAdminFees → (∀ k v, (e.coin k).balPre = some v → s.balances.get k ≤ v) →
    ∀ T amp D D', getDMem o.state.balances amp = some D' →
    (∀ t, aChk o.state t = aChk s t) ∧ supplyAfter T o.calls = T ∧
      floorRoot (xpOf s.balances) (amp * 3) ≤ D' ∧
      D ≤ D' + (D - floorRoot (xpOf s.balances) (amp * 3))) ∧
  (∀ am mm, c = .addLiquidity am mm → ∀ T amp D D', aChk s e.time = some amp →
    e.supply = some T → 0 < T → s.adminFee ≤ feeDen →
    getDMem s.balances amp = some D → getDMem o.state.balances amp = some D' →
    (∀ t, aChk o.state t = aChk s t) ∧ ∃ mid D2, getDMem mid amp = some D2 ∧
      (∀ k, mid.get k ≤ o.state.balances.get k) ∧
      D * supplyAfter T o.calls ≤ (D' + (D2 - floorRoot (xpOf mid) (amp * 3))) * T) ∧
  (∀ am mb, c = .removeLiquidityImbalance am mb → ∀ T amp D D', aChk s e.time = some amp →
    e.supply = some T → s.adminFee ≤ feeDen →
    getDMem s.balances amp = some D → getDMem o.state.balances amp = some D' →
    (∀ t, aChk o.state t = aChk s t) ∧ ∃ mid D2, getDMem mid amp = some D2 ∧
      (∀ k, mid.get k ≤ o.state.balances.get k) ∧
      D * supplyAfter T o.calls ≤ (D' + (D2 - floorRoot (xpOf mid) (amp * 3))) * T) ∧
  (∀ i j dx md, c = .exchange i j dx md → ∃ i' j' : Fin 3, idx i = some i' ∧ idx j = some j' ∧
    ∀ T amp D D', aChk s e.time = some amp → s.adminFee ≤ feeDen →
    getDMem s.balances amp = some D → getDMem o.state.balances amp = some D' →
    (∀ t, aChk o.state t = aChk s t) ∧ supplyAfter T o.calls = T ∧
      D ≤ D' + yGap (xpOf s.balances) i' j' (xpOf o.state.balances i') D (amp * 3)) ∧
  (∀ a i mn, c = .removeLiquidityOneCoin a i mn → ∃ i' : Fin 3, idx i = some i' ∧
    ∀ T amp D D', aChk s e.time = some amp → e.supply = some T → s.adminFee ≤ feeDen →
    getDMem s.balances amp = some D → getDMem o.state.balances amp = some D' →
    (∀ t, aChk o.state t = aChk s t) ∧
    D * supplyAfter T o.calls ≤ (D' + oneGap (xpOf s.balances) i' (D - a * D / T) (amp * 3)) * T)

/-- An accepted step is its body. -/
theorem pool_step_body {s : State} {e : Env} {c : Call} {o : Out} (h : step s e c = some o) :
    body s e c = some o := by
  unfold step at h
  split at h
  · cases h
  · split at h
    · exact h
    · cases h

/-- **Every accepted step satisfies the six U3 bounds.** -/
theorem u3Step_of_step {s : State} {e : Env} {c : Call} {o : Out} (h : step s e c = some o) :
    U3Step s e c o := by
  have hb := pool_step_body h
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro a mins rfl T amp D D' hT hT0 hD hD'
    exact u3_bound_remove_liquidity hb hT hT0 hD hD'
  · rintro rfl hcoin T amp D D' hD'
    exact u3_bound_donate_admin_fees hb hcoin hD'
  · rintro am mm rfl T amp D D' hA hT hT0 hadm hD hD'
    exact u3_bound_add_liquidity hb hA hT hT0 hadm hD hD'
  · rintro am mb rfl T amp D D' hA hT hadm hD hD'
    exact u3_bound_remove_liquidity_imbalance hb hA hT hadm hD hD'
  · rintro i j dx md rfl
    simp only [body, Option.bind_eq_bind, Option.bind_eq_some_iff] at hb
    obtain ⟨i', hi, j', hj, hx⟩ := hb
    exact ⟨i', j', hi, hj, fun T amp D D' hA hadm hD hD' =>
      u3_bound_exchange hx hA hadm hD hD'⟩
  · rintro a i mn rfl
    simp only [body, Option.bind_eq_bind, Option.bind_eq_some_iff] at hb
    obtain ⟨i', hi, hx⟩ := hb
    exact ⟨i', hi, fun T amp D D' hA hT hadm hD hD' =>
      u3_bound_remove_liquidity_one_coin hx hA hT hadm hD hD'⟩

/-- **U3 at history level.**  In the committed replay of `pool_history_committed_env`, every
invocation `i`, at the state `sᵢ` its prefix reaches, ran at its block's header timestamp (its
recorded time) and is an accepted step whose result satisfies the six U3 bounds of goal §11. -/
theorem pool_history_u3 {pool : Adr} {cfg : ChainConfig}
    {checkpoint future : BlockChain} {s₀ : State}
    (trace : ConfiguredHistoryTrace cfg checkpoint future)
    (installed : some (checkpoint.state.getCode pool).toList = poolSem.image)
    (initial : Checkpoint (checkpoint.state.getStor pool) s₀)
    (env : PoolTraceEnv trace pool s₀.coins s₀.token) :
    ∃ invs : List PoolInvocation,
      invs.flatMap (fun i => poolSubtreeFrames pool i.frame) = committedPoolFrames pool trace ∧
      (∀ i ∈ invs, i.Authentic pool) ∧
      (∃ s, PoolRun s₀ invs s ∧ Checkpoint (future.state.getStor pool) s) ∧
      ∀ (pre : List PoolInvocation) (i : PoolInvocation) (post : List PoolInvocation)
        (sᵢ : State), invs = pre ++ i :: post → PoolRun s₀ pre sᵢ →
        (∃ blk : Block, (blk, i.frame) ∈ trace.blockFrames ∧
          i.env.time = blk.header.timestamp.toB256.toNat) ∧
        ∃ o, step sᵢ i.env (decodeCall i.frame.sevm) = some o ∧
          RawEffect (Exec.Frame.rootDeriv i.frame) i.frame.post i.env o ∧
          U3Step sᵢ i.env (decodeCall i.frame.sevm) o := by
  obtain ⟨-, invs, hobs, auth, s, run, -, hc, -⟩ :=
    pool_history_committed_env trace installed initial env
  refine ⟨invs, hobs, auth, ⟨s, run, hc⟩, ?_⟩
  intro pre i post sᵢ hsplit hpre
  have hi : i ∈ invs := by
    rw [hsplit]
    exact List.mem_append_right _ (List.mem_cons_self ..)
  obtain ⟨o, hstep, hraw, -⟩ := PoolRun.split (hsplit ▸ run) hpre
  exact ⟨pool_invocation_time hobs hi (auth i hi), o, hstep, hraw, u3Step_of_step hstep⟩

end Blanc.Lift.Curve3Pool
