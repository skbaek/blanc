import Blanc.Composition.Curve3Pool3CrvLiveEndEntry
import Blanc.Lift.Curve3Pool.OneCoinLive

/-!
# `remove_liquidity_one_coin` end to end at the concrete entry

* `ocw_step`: the model step at the concrete entry `cSevm ocwData` (calldata
  `remove_liquidity_one_coin(600, 1, 0)`), by kernel evaluation: `ocOut`, which burns `600` and
  pushes `531` of coin `1`.
* `ocw_cost`: the closed sufficient-gas bound `costOneCoin` at that step.
* `oc_frame_live_of_keep`: the end-to-end instance — every premise of
  `removeLiquidityOneCoin_live` discharged at the concrete entry (the callee premises by
  `removeLiquidityOneCoin_premises_satisfiable` at the model's push amount) except the per-child
  keep, which stays a hypothesis.
-/

namespace Blanc.Composition.Curve3Pool3CrvInstance

open Jaune Blanc Blanc.Lift Blanc.Lift.Curve3Pool Blanc.Composition.Curve3PoolCalleeLive
open Blanc.Composition.Curve3Pool3CrvJoint

/-- The `remove_liquidity_one_coin` calldata: burn `600`, coin `1`, minimum `0`. -/
def ocwData : Bytes := abiSelectorBytes selRemoveLiquidityOneCoin ++ (600 : B256).toBytes ++
  (1 : B256).toBytes ++ (0 : B256).toBytes

/-- **The model's output of `remove_liquidity_one_coin(600, 1, 0)`** at `poolState` with supply
`6000`. -/
def ocOut : Out :=
  ⟨{ poolState with balances := ⟨1000, 1469, 3000⟩ }, none,
    [.removeLiquidityOne traderN 600 531], [.burn traderN 600, .push 1 traderN 531]⟩

theorem ocw_len : 4 ≤ (cSevm ocwData).data.length ∧ (cSevm ocwData).data.length < 2 ^ 256 := by
  decide +kernel

theorem ocw_sel : Sevm.selector (cSevm ocwData) = selRemoveLiquidityOneCoin := by
  decide +kernel

theorem ocw_amt : (ocAmt (cSevm ocwData)).toNat = 600 := by
  decide +kernel

theorem ocw_i : (ocI (cSevm ocwData)).toNat = 1 := by
  decide +kernel

theorem ocw_decode : decodeCall (cSevm ocwData) = .removeLiquidityOneCoin 600 1 0 := by
  rw [oc_decode ocw_len.1 ocw_sel]
  decide +kernel

/-- **The model step at the concrete `remove_liquidity_one_coin` entry** (kernel evaluation). -/
theorem ocw_step :
    step poolState (ocEnv (cSevm ocwData) 1 (6000 : B256).toNat) (decodeCall (cSevm ocwData)) =
      some ocOut := by
  rw [ocw_decode]
  unfold ocEnv
  rw [cSevm_time, cSevm_caller, cSevm_value]
  decide +kernel

/-- The closed sufficient-gas bound at the step. -/
theorem ocw_cost :
    costOneCoin poolState (ocEnv (cSevm ocwData) 1 (6000 : B256).toNat) 600 1 ≤ 180312 := by
  unfold ocEnv
  rw [cSevm_time, cSevm_caller, cSevm_value]
  decide +kernel

/-- **`remove_liquidity_one_coin` end to end at the concrete entry**, given the per-child keep:
an actual successful execution of the pool's runtime from `wPre ocwData` at gas `878400`, whose
effect is the model's `remove_liquidity_one_coin(600, 1, 0)` (`ocOut`: burn `600`, push `531`
of coin `1`), with the pool's checkpoint at the post. -/
theorem oc_frame_live_of_keep
    (hkeep : ∀ post (exc : Exec 0 (cSevm ocwData) (St (wPre ocwData) [] Mem.empty 878400)
        (.ok post)),
      PoolCallsKeep ⟨0, cSevm ocwData, St (wPre ocwData) [] Mem.empty 878400, .ok post, exc⟩ ∧
        ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4) :
    ∃ post, ∃ exc : Exec 0 (cSevm ocwData) (St (wPre ocwData) [] Mem.empty 878400) (.ok post),
      ∃ T' : Nat,
      RawEffect ⟨0, cSevm ocwData, St (wPre ocwData) [] Mem.empty 878400, .ok post, exc⟩ post
          (ocEnv (cSevm ocwData) 1 T') ocOut ∧
        Checkpoint (post.getStor poolAddr) ocOut.state := by
  have hc3 := wPre_c3Entry ocwData
  have hcoin1 : coinOf (cSevm ocwData) (wPre ocwData) 1 = coin1Addr := wPre_coin ocwData 1
  obtain ⟨hWc, hW'c, hWb, hsup, hburn, hW''c, hpush⟩ := removeLiquidityOneCoin_premises_satisfiable
    (sevm := cSevm ocwData) (pre := wPre ocwData) (T := 6000)
    (v := Nat.toB256 (ocPushAmt ocOut)) (i := 1) (cSevm_fork _) rfl (by decide +kernel) hc3
    (by rw [wPre_getCode, hcoin1]; exact cState_code_coin1) (by rw [hcoin1]; decide +kernel)
    (by rw [hcoin1]; decide +kernel) (by rw [hcoin1]; decide +kernel)
    (by unfold BurnFits; decide +kernel) (by unfold T20MoveFits; decide +kernel)
  have hcost := ocw_cost
  rw [← ocw_amt] at hcost
  obtain ⟨post, exc, T', hr, hc, -⟩ := removeLiquidityOneCoin_live (pre := wPre ocwData)
    (G := 878400) (U := 80000) (T := 6000) (i := 1) rfl (cSevm_fork _) rfl (by decide +kernel)
    ocw_len.1 ocw_len.2 ocw_sel ocw_i.symm (wPre_checkpoint _) ocw_step hc3.prec
    (wPre_coins ocwData).prec (wPre_poolCode _) (wPre_id _) hkeep hWc hW'c hWb hsup hburn hW''c
    hpush (Nat.le_trans (Nat.add_le_add_right hcost _) (by decide))
    (wPre_gas ocwData 878400 (by decide +kernel))
  exact ⟨post, exc, T', hr, hc⟩

end Blanc.Composition.Curve3Pool3CrvInstance
