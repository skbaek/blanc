import Blanc.Composition.Curve3Pool3CrvLiveEndEntry
import Blanc.Lift.Curve3Pool.RemoveImbalanceLive

/-!
# `remove_liquidity_imbalance` end to end at the concrete entry

* `rli_stepW`: the model step at the concrete entry `cSevm rliDataW` (calldata
  `remove_liquidity_imbalance([90, 180, 270], 600)` with the real selector), by kernel
  evaluation: `rliOutW`, which burns `541` and pushes `90, 180, 270` (the burn exceeds the old
  `600`-capped choice by one, so the amounts move to keep the burn at `541 ≤ 600`).
* `rli_costW`: the closed sufficient-gas bound `costImbalance` at that step.
* `rli_frame_live_of_keep`: the end-to-end instance — every premise of
  `removeLiquidityImbalance_live` discharged at the concrete entry (the callee premises by
  `removeLiquidityImbalance_premises_satisfiable` at the model's burn amount) except the
  per-child keep, which stays a hypothesis.
-/

namespace Blanc.Composition.Curve3Pool3CrvInstance

open Jaune Blanc Blanc.Lift Blanc.Lift.Curve3Pool Blanc.Composition.Curve3PoolCalleeLive
open Blanc.Composition.Curve3Pool3CrvJoint

/-- The `remove_liquidity_imbalance` calldata: amounts `90, 180, 270`, max burn `600`. -/
def rliDataW : Bytes := abiSelectorBytes selRemoveLiquidityImbalance ++ (90 : B256).toBytes ++
  (180 : B256).toBytes ++ (270 : B256).toBytes ++ (600 : B256).toBytes

/-- **The model's output of `remove_liquidity_imbalance([90, 180, 270], 600)`** at `poolState`
with supply `6000`. -/
def rliOutW : Out :=
  ⟨{ poolState with balances := ⟨910, 1820, 2730⟩ }, none,
    [.removeLiquidityImbalance traderN ⟨90, 180, 270⟩ ⟨0, 0, 0⟩ 20181893721304 5459],
    [.burn traderN 541, .push 0 traderN 90, .push 1 traderN 180, .push 2 traderN 270]⟩

theorem rli_lenW :
    4 ≤ (cSevm rliDataW).data.length ∧ (cSevm rliDataW).data.length < 2 ^ 256 := by
  decide +kernel

theorem rli_selW : Sevm.selector (cSevm rliDataW) = selRemoveLiquidityImbalance := by
  decide +kernel

theorem rli_amtsW :
    rliAmt (cSevm rliDataW) 0 = 90 ∧ rliAmt (cSevm rliDataW) 1 = 180 ∧
      rliAmt (cSevm rliDataW) 2 = 270 := by
  decide +kernel

theorem rli_posW :
    0 < (rliAmt (cSevm rliDataW) 0).toNat ∧ 0 < (rliAmt (cSevm rliDataW) 1).toNat ∧
      0 < (rliAmt (cSevm rliDataW) 2).toNat := by
  rw [rli_amtsW.1, rli_amtsW.2.1, rli_amtsW.2.2]
  decide +kernel

theorem rli_decodeW :
    decodeCall (cSevm rliDataW) = .removeLiquidityImbalance ⟨90, 180, 270⟩ 600 := by
  rw [rli_decode rli_selW rli_lenW.1]
  decide +kernel

/-- **The model step at the concrete `remove_liquidity_imbalance` entry** (kernel
evaluation). -/
theorem rli_stepW :
    step poolState (rliEnvW (cSevm rliDataW) (6000 : B256).toNat) (decodeCall (cSevm rliDataW)) =
      some rliOutW := by
  rw [rli_decodeW]
  unfold rliEnvW
  rw [cSevm_time, cSevm_caller, cSevm_value]
  decide +kernel

/-- The closed sufficient-gas bound at the step. -/
theorem rli_costW :
    costImbalance poolState (rliEnvW (cSevm rliDataW) (6000 : B256).toNat)
      (argV3 (cSevm rliDataW) 0) ≤ 379308 := by
  decide +kernel

/-- **`remove_liquidity_imbalance` end to end at the concrete entry**, given the per-child keep:
an actual successful execution of the pool's runtime from `wPre rliDataW` at gas `878400`,
whose effect is the model's `remove_liquidity_imbalance([90, 180, 270], 600)` (`rliOutW`: burn
`541`, pushes `90, 180, 270`), with the pool's checkpoint at the post. -/
theorem rli_frame_live_of_keep
    (hkeep : ∀ post (exc : Exec 0 (cSevm rliDataW) (St (wPre rliDataW) [] Mem.empty 878400)
        (.ok post)),
      PoolCallsKeep ⟨0, cSevm rliDataW, St (wPre rliDataW) [] Mem.empty 878400, .ok post, exc⟩ ∧
        ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4) :
    ∃ post, ∃ exc : Exec 0 (cSevm rliDataW) (St (wPre rliDataW) [] Mem.empty 878400) (.ok post),
      RawEffect ⟨0, cSevm rliDataW, St (wPre rliDataW) [] Mem.empty 878400, .ok post, exc⟩ post
          (rliEnvW (cSevm rliDataW) (6000 : B256).toNat) rliOutW ∧
        Checkpoint (post.getStor poolAddr) rliOutW.state ∧
        rliWorld (cSevm rliDataW) (wPre rliDataW) (Nat.toB256 (rliBurnAmt rliOutW)) 4 post := by
  have hc3 := wPre_c3Entry rliDataW
  have hcoins := wPre_coins rliDataW
  obtain ⟨hWc, hWb, hsup, hburn, hpush, hskip⟩ :=
    removeLiquidityImbalance_premises_satisfiable (sevm := cSevm rliDataW) (pre := wPre rliDataW)
      (T := 6000) (m := Nat.toB256 (rliBurnAmt rliOutW)) (cSevm_fork _) rfl (by decide +kernel)
      hc3 hcoins (by unfold BurnFits; decide +kernel) (by unfold T20MoveFits; decide +kernel)
  obtain ⟨post, exc, hr, hc, hw⟩ := removeLiquidityImbalance_live (pre := wPre rliDataW)
    (G := 878400) (U := 80000) (T := 6000) rfl (cSevm_fork _) rfl (by decide +kernel)
    rli_lenW.1 rli_lenW.2 rli_selW (wPre_checkpoint _) rli_stepW hc3.prec hcoins.prec
    (wPre_poolCode _) (wPre_id _) hkeep hWc hWb hsup hburn hpush hskip
    (Nat.le_trans (Nat.add_le_add_right rli_costW _) (by decide))
    (by decide +kernel)
  exact ⟨post, exc, hr, hc, hw⟩

end Blanc.Composition.Curve3Pool3CrvInstance
