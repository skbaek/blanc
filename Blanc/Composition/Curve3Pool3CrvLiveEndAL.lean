import Blanc.Composition.Curve3Pool3CrvLiveEndEntry
import Blanc.Lift.Curve3Pool.AddLiquidityLive
import Blanc.Lift.Curve3Pool.Walk.AlLiveModel
import Blanc.Lift.Curve3Pool.Walk.AlLiveWords

/-!
# `add_liquidity` end to end at the concrete entry

* `al_stepW`: the model step at the concrete entry `cSevm alDataW` (calldata
  `add_liquidity([100, 200, 300], 599)` with the real selector), by kernel evaluation:
  `alOutW`, which mints `599` (the old minimum `1000` exceeds the model's mint, so it moves
  to the model's output).
* `al_costW`: the closed sufficient-gas bound `costAddLiquidity` at that step (`542566`, so
  with `U = 80000` every frame gas `G ≥ 1102566` works; the frame below runs at `1110000`).
* `al_frame_live_of_keep`: the end-to-end instance — every premise of `addLiquidity_live`
  discharged at the concrete entry (the callee premises by `addLiquidity_premises_satisfiable`
  at the model's mint amount) except the per-child keep, which stays a hypothesis.
-/

namespace Blanc.Composition.Curve3Pool3CrvInstance

open Jaune Blanc Blanc.Lift Blanc.Lift.Curve3Pool Blanc.Composition.Curve3PoolCalleeLive
open Blanc.Composition.Curve3Pool3CrvJoint

/-- The `add_liquidity` calldata: pulls `100, 200, 300`, minimum mint `599`. -/
def alDataW : Bytes := abiSelectorBytes selAddLiquidity ++ (100 : B256).toBytes ++
  (200 : B256).toBytes ++ (300 : B256).toBytes ++ (599 : B256).toBytes

/-- **The model's output of `add_liquidity([100, 200, 300], 599)`** at `poolState` with supply
`6000`. -/
def alOutW : Out :=
  ⟨{ poolState with balances := ⟨1100, 2200, 3300⟩ }, none,
    [.addLiquidity traderN ⟨100, 200, 300⟩ ⟨0, 0, 0⟩ 24395695707071 6599],
    [.pull 0 traderN 100, .pull 1 traderN 200, .pull 2 traderN 300, .mint traderN 599]⟩

theorem al_lenW :
    4 ≤ (cSevm alDataW).data.length ∧ (cSevm alDataW).data.length < 2 ^ 256 := by
  decide +kernel

theorem al_selW : Sevm.selector (cSevm alDataW) = selAddLiquidity := by
  decide +kernel

theorem al_amtsW :
    alAmt (cSevm alDataW) 0 = 100 ∧ alAmt (cSevm alDataW) 1 = 200 ∧
      alAmt (cSevm alDataW) 2 = 300 := by
  decide +kernel

theorem al_posW :
    0 < (alAmt (cSevm alDataW) 0).toNat ∧ 0 < (alAmt (cSevm alDataW) 1).toNat ∧
      0 < (alAmt (cSevm alDataW) 2).toNat := by
  rw [al_amtsW.1, al_amtsW.2.1, al_amtsW.2.2]
  decide +kernel

theorem al_decodeW :
    decodeCall (cSevm alDataW) = .addLiquidity ⟨100, 200, 300⟩ 599 := by
  rw [decodeCall_at (k := 3) rfl al_selW al_lenW.1]
  decide +kernel

/-- **The model step at the concrete `add_liquidity` entry** (kernel evaluation). -/
theorem al_stepW :
    step poolState (alEnvW (cSevm alDataW) (6000 : B256).toNat (3000 : B256).toNat
      (3300 : B256).toNat) (decodeCall (cSevm alDataW)) = some alOutW := by
  rw [al_decodeW]
  unfold alEnvW
  rw [cSevm_time, cSevm_caller, cSevm_value]
  decide +kernel

/-- The closed sufficient-gas bound at the step. -/
theorem al_costW :
    costAddLiquidity poolState (alEnvW (cSevm alDataW) (6000 : B256).toNat (3000 : B256).toNat
      (3300 : B256).toNat) (argV3 (cSevm alDataW) 0) ≤ 542566 := by
  decide +kernel

/-- The fee coin's pre-pull balance at the entry is `3000`. -/
theorem al_B1W : ((wPre alDataW).getStor (coinOf (cSevm alDataW) (wPre alDataW) 2)).get
    (VyperNonreentrantDeployed.Token20.balSlot (cSevm alDataW).currentTarget) =
      (3000 : B256) := by
  decide +kernel

/-- The fee coin's post-pull balance at the entry is `3300`. -/
theorem al_B2W : ((alFeeStor (cSevm alDataW) (wPre alDataW)).get
    (VyperNonreentrantDeployed.Token20.balSlot (cSevm alDataW).currentTarget)) =
      (3300 : B256) := by
  decide +kernel

/-- **`add_liquidity` end to end at the concrete entry**, given the per-child keep: an actual
successful execution of the pool's runtime from `wPre alDataW` at gas `1110000`, whose effect
is the model's `add_liquidity([100, 200, 300], 599)` (`alOutW`: mint `599`), with the pool's
checkpoint at the post. -/
theorem al_frame_live_of_keep
    (hkeep : ∀ post (exc : Exec 0 (cSevm alDataW) (St (wPre alDataW) [] Mem.empty 1110000)
        (.ok post)),
      PoolCallsKeep ⟨0, cSevm alDataW, St (wPre alDataW) [] Mem.empty 1110000, .ok post, exc⟩ ∧
        ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4) :
    ∃ post, ∃ exc : Exec 0 (cSevm alDataW) (St (wPre alDataW) [] Mem.empty 1110000) (.ok post),
      ∃ e : Env,
      e.supply = some (6000 : B256).toNat ∧
        step poolState e (decodeCall (cSevm alDataW)) = some alOutW ∧
        RawEffect ⟨0, cSevm alDataW, St (wPre alDataW) [] Mem.empty 1110000, .ok post, exc⟩ post
          e alOutW ∧
        Checkpoint (post.getStor poolAddr) alOutW.state := by
  have hc3 := wPre_c3Entry alDataW
  have hcoins := wPre_coins alDataW
  obtain ⟨hWc, hWb, hsup, hpull, hskip, hfee, hmint⟩ :=
    addLiquidity_premises_satisfiable (sevm := cSevm alDataW) (pre := wPre alDataW)
      (T := 6000) (m := Nat.toB256 (alMintAmt alOutW)) (cSevm_fork _) rfl (by decide +kernel)
      hc3 hcoins (by unfold MintFits; decide +kernel)
      (by unfold T20PullFits t20Allow T20MoveFits; decide +kernel)
  have hfeeW := hfee
  rw [al_B1W, al_B2W] at hfeeW
  obtain ⟨post, exc, e, he, hstep', hr, hc⟩ := addLiquidity_live (pre := wPre alDataW)
    (G := 1110000) (U := 80000) (T := 6000) (B1 := (3000 : B256)) (B2 := (3300 : B256)) rfl
    (cSevm_fork _) rfl (by decide +kernel) al_lenW.1 al_lenW.2 al_selW (wPre_checkpoint _)
    al_stepW hc3.prec hcoins.prec (wPre_poolCode _) (wPre_id _) hkeep hWc hWb hsup hpull hskip
    hfeeW hmint (Nat.le_trans (Nat.add_le_add_right al_costW _) (by decide))
    (by decide +kernel)
  exact ⟨post, exc, e, he, hstep', hr, hc⟩

end Blanc.Composition.Curve3Pool3CrvInstance
