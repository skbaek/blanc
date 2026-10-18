import Blanc.Composition.Curve3Pool3CrvLiveEndEntry
import Blanc.Lift.Curve3Pool.RemoveLiquidityLiveness
import Blanc.Lift.Curve3Pool.Walk.RemoveLiquidityRawK

/-!
# `remove_liquidity` end to end at the concrete entry

* `rlw_step`: the model step at the concrete entry `cSevm rlwData` (calldata
  `remove_liquidity(600, [0, 0, 0])`), by kernel evaluation: `rlOut`, balances
  `[900, 1800, 2700]`, pushes `100, 200, 300` (each `balances[k] * 600 / 6000`), burn `600`.
* `rl_frame_live_of_keep`: the end-to-end instance — every premise of `removeLiquidity_live`
  discharged at the concrete entry except the per-child keep, which stays a hypothesis.
-/

namespace Blanc.Composition.Curve3Pool3CrvInstance

open Jaune Blanc Blanc.Lift Blanc.Lift.Curve3Pool Blanc.Composition.Curve3PoolCalleeLive
open Blanc.Composition.Curve3Pool3CrvJoint

/-- The `remove_liquidity` calldata: burn `600`, minimum amounts `0, 0, 0`. -/
def rlwData : Bytes := abiSelectorBytes selRemoveLiquidity ++ (600 : B256).toBytes ++
  (0 : B256).toBytes ++ (0 : B256).toBytes ++ (0 : B256).toBytes

/-- **The model's output of `remove_liquidity(600, [0, 0, 0])`** at `poolState` with supply
`6000`. -/
def rlOut : Out :=
  ⟨{ poolState with balances := ⟨900, 1800, 2700⟩ }, none,
    [.removeLiquidity traderN ⟨100, 200, 300⟩ V3.zero 5400],
    [.push 0 traderN 100, .push 1 traderN 200, .push 2 traderN 300, .burn traderN 600]⟩

theorem rlw_len : 4 ≤ (cSevm rlwData).data.length ∧ (cSevm rlwData).data.length < 2 ^ 256 := by
  decide +kernel

theorem rlw_sel : Sevm.selector (cSevm rlwData) = selRemoveLiquidity := by
  decide +kernel

theorem rlw_amt : rlAmt (cSevm rlwData) = 600 := by
  decide +kernel

theorem rlw_decode : decodeCall (cSevm rlwData) = .removeLiquidity 600 ⟨0, 0, 0⟩ := by
  rw [decodeCall_at (k := 7) rfl rlw_sel rlw_len.1]
  decide +kernel

/-- **The model step at the concrete `remove_liquidity` entry** (kernel evaluation). -/
theorem rlw_step :
    step poolState (rlEnv (cSevm rlwData) 6000) (decodeCall (cSevm rlwData)) = some rlOut := by
  rw [rlw_decode]
  unfold rlEnv
  rw [cSevm_time, cSevm_caller, cSevm_value]
  decide +kernel

/-- **`remove_liquidity` end to end at the concrete entry**, given the per-child keep: an actual
successful execution of the pool's runtime from `wPre rlwData` at gas `878400`, whose effect is
the model's `remove_liquidity(600, [0, 0, 0])` (`rlOut`: pushes `100, 200, 300`, burn `600`),
with the pool's checkpoint at the post. -/
theorem rl_frame_live_of_keep
    (hkeep : ∀ post (exc : Exec 0 (cSevm rlwData) (St (wPre rlwData) [] Mem.empty 878400)
        (.ok post)),
      PoolCallsKeep ⟨0, cSevm rlwData, St (wPre rlwData) [] Mem.empty 878400, .ok post, exc⟩ ∧
        ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4) :
    ∃ post, ∃ exc : Exec 0 (cSevm rlwData) (St (wPre rlwData) [] Mem.empty 878400) (.ok post),
      RawEffect ⟨0, cSevm rlwData, St (wPre rlwData) [] Mem.empty 878400, .ok post, exc⟩ post
          (rlEnv (cSevm rlwData) 6000) rlOut ∧
        Checkpoint (post.getStor poolAddr) rlOut.state := by
  have hc3 := wPre_c3Entry rlwData
  have hcoins := wPre_coins rlwData
  obtain ⟨hWc, hWb, hsup, hpush, hburn⟩ := removeLiquidity_premises_satisfiable
    (sevm := cSevm rlwData) (pre := wPre rlwData) (T := 6000) (cSevm_fork _) rfl
    (by decide +kernel) hc3 hcoins (by unfold BurnFits; decide +kernel)
    (by unfold T20MoveFits; decide +kernel)
  exact removeLiquidity_live (pre := wPre rlwData) (G := 878400) (U := 80000) rfl (cSevm_fork _)
    rfl (by decide +kernel) rlw_len.1 rlw_len.2 rlw_sel (wPre_checkpoint _) rlw_step hc3.prec
    hcoins.prec (wPre_poolCode _) (wPre_id _) hkeep hWc hWb hsup hpush hburn (by decide)
    (Nat.lt_of_le_of_lt (Nat.le_add_right _ 2000) (wPre_gas rlwData 878400 (by decide +kernel)))

end Blanc.Composition.Curve3Pool3CrvInstance
