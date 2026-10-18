import Blanc.Composition.Curve3Pool3CrvLiveEndKeep
import Blanc.Composition.Curve3Pool3CrvLiveEndRLI
import Blanc.Lift.Curve3Pool.Walk.RemoveImbalanceWalk

/-!
# The per-child keep for `remove_liquidity_imbalance` at a depth-`1` pool frame

* `rliw_keep`: the per-execution keep premise of `removeLiquidityImbalance_live` at the
  concrete entry. The walk under the conditional keep (`xa_rliC`) names every child's target —
  3Crv or a coin, neither the pool nor `4` — so `RlKeepC` gives every child's keep.
* `rli_frame_live`: the end-to-end instance with no hypothesis.
-/

namespace Blanc.Composition.Curve3Pool3CrvInstance

open Jaune Blanc Blanc.Lift Blanc.Lift.Curve3Pool
open Blanc.Composition.Curve3Pool3CrvJoint

/-- **The per-child keep at the concrete `remove_liquidity_imbalance` entry.** -/
theorem rliw_keep (post : Devm)
    (exc : Exec 0 (cSevm rliDataW) (St (wPre rliDataW) [] Mem.empty 878400) (.ok post)) :
    PoolCallsKeep ⟨0, cSevm rliDataW, St (wPre rliDataW) [] Mem.empty 878400, .ok post, exc⟩ ∧
      ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4 := by
  have hKC := pool_childFrames_keepC exc rfl (cSevm_fork _) rfl cState_poolCode_ne
  have hx := XAt.of_eq (St.self (d := St (wPre rliDataW) [] Mem.empty 878400) rfl rfl)
    (XAt.of_exec exc (wPre_gas' rliDataW))
  have hst : (St (St (wPre rliDataW) [] Mem.empty 878400) [] Mem.empty 878400).getStor
      (cSevm rliDataW).currentTarget = poolStor := cState_stor_pool
  obtain ⟨hct, htt, ht4⟩ := poolStor_targets
  rw [← hst] at hct htt ht4
  obtain ⟨-, -, -, cs, cb, L0, L1, L2, A, D0, D1, D2, f0, f1, f2, hL, hsw, hT0, hm3, hA,
    hD0, hu0, hu1, hu2, hD1, h0, h1, h2, hD2, hD02, hmT, hbn, hb1, hslip, hTX, hbt, hbd, hbv,
    hbs, hblen, hP0, hP1, hP2, hstor, hlogs, hout⟩ :=
    xa_rliC checkedM rfl (cSevm_fork _) rli_lenW.1 rli_lenW.2 rli_selW rfl
      (wPre_checkpoint rliDataW).abs (wPre_c3Entry _).prec
      (fun k hk => (wPre_coins _).prec ⟨k, hk⟩) (wPre_poolCode _) (wPre_id _) ⟨htt, ht4⟩
      hct hKC hx
  have hall : ∀ c ∈ Exec.childFrames exc,
      c.sevm.currentTarget ≠ (cSevm rliDataW).currentTarget ∧ c.sevm.currentTarget ≠ 4 := by
    intro c hc
    rw [hL] at hc
    simp only [List.mem_cons, List.mem_append] at hc
    rcases hc with rfl | rfl | m01 | m2
    · rw [hsw.target]; exact ⟨htt, ht4⟩
    · rw [hbt]; exact ⟨htt, ht4⟩
    · rcases m01 with m0 | m1
      · rcases hP0 with ⟨-, rfl⟩ | ⟨-, w, rfl, ht, _, _, _, _⟩
        · simp only [List.not_mem_nil] at m0
        · simp only [List.mem_singleton] at m0
          subst m0
          rw [ht]; exact hct 0 (by decide)
      · rcases hP1 with ⟨-, rfl⟩ | ⟨-, w, rfl, ht, _, _, _, _⟩
        · simp only [List.not_mem_nil] at m1
        · simp only [List.mem_singleton] at m1
          subst m1
          rw [ht]; exact hct 1 (by decide)
    · rcases hP2 with ⟨-, rfl⟩ | ⟨-, w, rfl, ht, _, _, _, _⟩
      · simp only [List.not_mem_nil] at m2
      · simp only [List.mem_singleton] at m2
        subst m2
        rw [ht]; exact hct 2 (by decide)
  exact ⟨fun c hc => (hKC c hc (hall c hc).1 (hall c hc).2).1,
    fun c hc => (hKC c hc (hall c hc).1 (hall c hc).2).2⟩

/-- **`remove_liquidity_imbalance` end to end at the concrete entry**: an actual successful
execution of the pool's runtime from `wPre rliDataW` at gas `878400`, whose effect is the
model's `remove_liquidity_imbalance([90, 180, 270], 600)` (`rliOutW`: burn `541`, pushes
`90, 180, 270`), with the pool's checkpoint at the post. -/
theorem rli_frame_live :
    ∃ post, ∃ exc : Exec 0 (cSevm rliDataW) (St (wPre rliDataW) [] Mem.empty 878400) (.ok post),
      RawEffect ⟨0, cSevm rliDataW, St (wPre rliDataW) [] Mem.empty 878400, .ok post, exc⟩ post
          (rliEnvW (cSevm rliDataW) (6000 : B256).toNat) rliOutW ∧
        Checkpoint (post.getStor poolAddr) rliOutW.state ∧
        rliWorld (cSevm rliDataW) (wPre rliDataW) (Nat.toB256 (rliBurnAmt rliOutW)) 4 post :=
  rli_frame_live_of_keep rliw_keep

end Blanc.Composition.Curve3Pool3CrvInstance
