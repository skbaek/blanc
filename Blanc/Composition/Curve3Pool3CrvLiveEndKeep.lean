import Blanc.Composition.Curve3Pool3CrvLiveEndRL
import Blanc.Composition.Curve3Pool3CrvLiveEndOC
import Blanc.Lift.ChildFrameDepth
import Blanc.Lift.Curve3Pool.Walk.RemoveLiquidity
import Blanc.Lift.Curve3Pool.Walk.OneCoin
import Blanc.Lift.Curve3Pool.Bridge

/-!
# The per-child keep at a depth-`1` pool frame

* `pool_childFrames_keepC`: every direct committed child of a successful pool frame at depth `1`
  that is at neither the pool nor `4` keeps the pool's storage and the code at `4`
  (`RlKeepC`), whatever code it runs: it sits at depth `0`, so it enters no frame
  (`Exec.childFrames_keeps_of_depth_one`).  Generic over the entry.
* `rlw_keep`, `ocw_keep`: the per-execution keep premise of `removeLiquidity_live` /
  `removeLiquidityOneCoin_live` at the concrete entries.  The walk under the conditional keep
  (`xa_removeLiquidity`'s `RlKeepC` branch, `xa_oneCoin2C`) names every child's target — 3Crv
  or a coin, neither the pool nor `4` — so `RlKeepC` gives every child's keep.
* `rl_frame_live`, `oc_frame_live`: the end-to-end instances with no hypothesis.
-/

namespace Blanc.Composition.Curve3Pool3CrvInstance

open Jaune Blanc Blanc.Lift Blanc.Lift.Curve3Pool
open Blanc.Composition.Curve3Pool3CrvJoint

/-- **Every child of a depth-`1` pool frame at neither the pool nor `4` keeps the pool.** -/
theorem pool_childFrames_keepC {sevm : Sevm} {b post : Devm} (exc : Exec 0 sevm b (.ok post))
    (hcode : sevm.code = Curve3Pool.code) (hfork : CoveredFork sevm.benvStat.fork)
    (hd : sevm.depth = 1) (hpc : (b.getCode sevm.currentTarget).toList ≠ []) :
    RlKeepC sevm (Exec.childFrames exc) := by
  intro c hc ht h4
  obtain ⟨-, cpre, -⟩ := Exec.childFrames_code exc hfork (exRoot_callKinds hcode exc) c hc
  have k1 := Exec.childFrames_keeps_of_depth_one exc hfork hd c hc sevm.currentTarget (Ne.symm ht)
  have k2 := Exec.childFrames_keeps_of_depth_one exc hfork hd c hc 4 (Ne.symm h4)
  exact ⟨k1.1 (by rw [cpre _ hpc]; exact hpc), k2.2⟩

theorem cState_poolCode_ne : (cState.getCode poolAddr).toList ≠ [] := by
  rw [cState_code_pool]; exact pool_code_ne

theorem wPre_gas' (d : Bytes) : (St (wPre d) [] Mem.empty 878400).gasMeasure < 2 ^ 256 :=
  Nat.lt_of_le_of_lt (Nat.le_add_right _ 2000) (wPre_gas d 878400 (by decide +kernel))

/-- The pool's coins and 3Crv are neither the pool nor `4`. -/
theorem poolStor_targets :
    (∀ i, i < 3 → (coinAt poolStor i).toAdr ≠ poolAddr ∧ (coinAt poolStor i).toAdr ≠ 4) ∧
      (poolStor.get tokenSlot).toAdr ≠ poolAddr ∧ (poolStor.get tokenSlot).toAdr ≠ 4 := by
  refine ⟨fun i hi => ?_, by decide +kernel, by decide +kernel⟩
  obtain rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  all_goals decide +kernel

/-- **The per-child keep at the concrete `remove_liquidity` entry.** -/
theorem rlw_keep (post : Devm)
    (exc : Exec 0 (cSevm rlwData) (St (wPre rlwData) [] Mem.empty 878400) (.ok post)) :
    PoolCallsKeep ⟨0, cSevm rlwData, St (wPre rlwData) [] Mem.empty 878400, .ok post, exc⟩ ∧
      ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4 := by
  have hKC := pool_childFrames_keepC exc rfl (cSevm_fork _) rfl cState_poolCode_ne
  have hx := XAt.of_eq (St.self (d := St (wPre rlwData) [] Mem.empty 878400) rfl rfl)
    (XAt.of_exec exc (wPre_gas' rlwData))
  have hst : (St (St (wPre rlwData) [] Mem.empty 878400) [] Mem.empty 878400).getStor
      (cSevm rlwData).currentTarget = poolStor := cState_stor_pool
  obtain ⟨hct, htt, ht4⟩ := poolStor_targets
  rw [← hst] at hct htt ht4
  obtain ⟨-, -, c0, c1, c2, c3, c4, hL, h0t, -, -, -, -, hp1, hp2, hp3, -, h4t, -⟩ :=
    xa_removeLiquidity rfl (cSevm_fork _) rlw_len.1 rlw_len.2 rlw_sel (wPre_c3Entry _).prec
      (fun i hi => (wPre_coins _).prec ⟨i, hi⟩) (wPre_poolCode _) (wPre_id _)
      (.inl ⟨hct, htt, ht4, hKC⟩) hx
  have hall : ∀ c ∈ Exec.childFrames exc,
      c.sevm.currentTarget ≠ (cSevm rlwData).currentTarget ∧ c.sevm.currentTarget ≠ 4 := by
    intro c hc
    rw [hL] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    · rw [h0t]; exact ⟨htt, ht4⟩
    · rw [hp1.target]; exact hct 0 (by decide)
    · rw [hp2.target]; exact hct 1 (by decide)
    · rw [hp3.target]; exact hct 2 (by decide)
    · rw [h4t]; exact ⟨htt, ht4⟩
  exact ⟨fun c hc => (hKC c hc (hall c hc).1 (hall c hc).2).1,
    fun c hc => (hKC c hc (hall c hc).1 (hall c hc).2).2⟩

/-- **The per-child keep at the concrete `remove_liquidity_one_coin` entry.** -/
theorem ocw_keep (post : Devm)
    (exc : Exec 0 (cSevm ocwData) (St (wPre ocwData) [] Mem.empty 878400) (.ok post)) :
    PoolCallsKeep ⟨0, cSevm ocwData, St (wPre ocwData) [] Mem.empty 878400, .ok post, exc⟩ ∧
      ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4 := by
  have hKC := pool_childFrames_keepC exc rfl (cSevm_fork _) rfl cState_poolCode_ne
  have hx := XAt.of_eq (St.self (d := St (wPre ocwData) [] Mem.empty 878400) rfl rfl)
    (XAt.of_exec exc (wPre_gas' ocwData))
  have hst : (St (St (wPre ocwData) [] Mem.empty 878400) [] Mem.empty 878400).getStor
      (cSevm ocwData).currentTarget = poolStor := cState_stor_pool
  have htk : (poolStor.get tokenSlot).toAdr ≠ poolAddr ∧ (poolStor.get tokenSlot).toAdr ≠ 4 :=
    ⟨poolStor_targets.2.1, poolStor_targets.2.2⟩
  have hcn : (poolStor.get (coinsBase + exJ (cSevm ocwData))).toAdr ≠ poolAddr ∧
      (poolStor.get (coinsBase + exJ (cSevm ocwData))).toAdr ≠ 4 := by
    decide +kernel
  rw [← hst] at htk hcn
  have hck := wPre_checkpoint ocwData
  obtain ⟨-, -, -, cs, cb, cp, -, -, -, hL, hsw, -, -, -, -, -, hbt, -, -, -, -, hpt, -⟩ :=
    xa_oneCoin2C checkedM rfl (cSevm_fork _) ocw_len.1 ocw_len.2 ocw_sel rfl hck.abs
      (wPre_c3Entry _).prec (fun hi => by
        have := (wPre_coins ocwData).prec ⟨_, hi⟩
        simpa only [coinOf, coinSlot, toB256_toNat] using this)
      (wPre_poolCode _) (wPre_id _) htk hcn hKC hx
  have hall : ∀ c ∈ Exec.childFrames exc,
      c.sevm.currentTarget ≠ (cSevm ocwData).currentTarget ∧ c.sevm.currentTarget ≠ 4 := by
    intro c hc
    rw [hL] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · rw [hsw.target]; exact htk
    · rw [hbt]; exact htk
    · rw [hpt]; exact hcn
  exact ⟨fun c hc => (hKC c hc (hall c hc).1 (hall c hc).2).1,
    fun c hc => (hKC c hc (hall c hc).1 (hall c hc).2).2⟩

/-- **`remove_liquidity` end to end at the concrete entry**: an actual successful execution of
the pool's runtime from `wPre rlwData` at gas `878400`, whose effect is the model's
`remove_liquidity(600, [0, 0, 0])` (`rlOut`: pushes `100, 200, 300`, burn `600`), with the pool's
checkpoint at the post. -/
theorem rl_frame_live :
    ∃ post, ∃ exc : Exec 0 (cSevm rlwData) (St (wPre rlwData) [] Mem.empty 878400) (.ok post),
      RawEffect ⟨0, cSevm rlwData, St (wPre rlwData) [] Mem.empty 878400, .ok post, exc⟩ post
          (rlEnv (cSevm rlwData) 6000) rlOut ∧
        Checkpoint (post.getStor poolAddr) rlOut.state :=
  rl_frame_live_of_keep rlw_keep

/-- **`remove_liquidity_one_coin` end to end at the concrete entry**: an actual successful
execution of the pool's runtime from `wPre ocwData` at gas `878400`, whose effect is the model's
`remove_liquidity_one_coin(600, 1, 0)` (`ocOut`: burn `600`, push `531` of coin `1`), with the
pool's checkpoint at the post. -/
theorem oc_frame_live :
    ∃ post, ∃ exc : Exec 0 (cSevm ocwData) (St (wPre ocwData) [] Mem.empty 878400) (.ok post),
      ∃ T' : Nat,
      RawEffect ⟨0, cSevm ocwData, St (wPre ocwData) [] Mem.empty 878400, .ok post, exc⟩ post
          (ocEnv (cSevm ocwData) 1 T') ocOut ∧
        Checkpoint (post.getStor poolAddr) ocOut.state :=
  oc_frame_live_of_keep ocw_keep

end Blanc.Composition.Curve3Pool3CrvInstance
