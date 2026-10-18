import Blanc.Composition.Curve3Pool3CrvLiveEndKeep
import Blanc.Composition.Curve3Pool3CrvLiveEndAL
import Blanc.Lift.Curve3Pool.Walk.AddLiquidityBack

/-!
# The per-child keep at the concrete `add_liquidity` entry

* `alw_keep`: the per-execution keep premise of `al_frame_live_of_keep`.  The walk under the
  conditional keep (`xa_al_frontC`, `xa_al_backC` at the predicate "neither the pool nor `4`")
  names every child's target — 3Crv (`totalSupply`, `mint`) or a coin (`balanceOf`,
  `transferFrom`), neither the pool nor `4` — so `RlKeepC` (`pool_childFrames_keepC`, the frame
  sits at depth `1`) gives every child's keep.
* `al_frame_live`: the end-to-end instance with no hypothesis.
-/

namespace Blanc.Composition.Curve3Pool3CrvInstance

open Jaune Blanc Blanc.Lift Blanc.Lift.Curve3Pool
open Blanc.Composition.Curve3Pool3CrvJoint

/-- **The per-child keep at the concrete `add_liquidity` entry.** -/
theorem alw_keep (post : Devm)
    (exc : Exec 0 (cSevm alDataW) (St (wPre alDataW) [] Mem.empty 1110000) (.ok post)) :
    PoolCallsKeep ⟨0, cSevm alDataW, St (wPre alDataW) [] Mem.empty 1110000, .ok post, exc⟩ ∧
      ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4 := by
  have hKC := pool_childFrames_keepC exc rfl (cSevm_fork _) rfl cState_poolCode_ne
  have hx := XAt.of_eq (St.self (d := St (wPre alDataW) [] Mem.empty 1110000) rfl rfl)
    (XAt.of_exec exc (Nat.lt_of_le_of_lt (Nat.le_add_right _ 2000)
      (wPre_gas alDataW 1110000 (by decide +kernel))))
  have hst : (St (St (wPre alDataW) [] Mem.empty 1110000) [] Mem.empty 1110000).getStor
      (cSevm alDataW).currentTarget = poolStor := cState_stor_pool
  obtain ⟨hct, htt, ht4⟩ := poolStor_targets
  rw [← hst] at hct htt ht4
  obtain ⟨-, -, -, -, A, cT, L0, L1, L2, L', D0, D1, cr0, cr1, cr2, b', M, img, G', -, hL, hTt,
    -, -, -, -, -, -, hk0, hk1, hk2, -, -, -, -, -, -, hst', -, -, hcd', -, hR, hW, hA, hm, w900,
    h⟩ :=
    xa_al_frontC (P := fun a => a ≠ (cSevm alDataW).currentTarget ∧ a ≠ 4) checkedM rfl
      (cSevm_fork _) al_lenW.1 al_lenW.2 al_selW (wPre_checkpoint _).abs (wPre_c3Entry _).prec
      (fun i hi => (wPre_coins _).prec ⟨i, hi⟩) (wPre_poolCode _) (wPre_id _) ⟨htt, ht4⟩
      (fun i hi => hct i hi) (fun c hc hp => hKC c hc hp.1 hp.2) hx
  have htokB : ∀ k : Nat, k < 3 → balancesBase + Nat.toB256 k ≠ tokenSlot := fun k hk => by
    rcases three_cases hk with rfl | rfl | rfl <;> decide
  obtain ⟨-, -, -, -, -, -, -, -, cm, rfl, -, -, -, -, hmt, -⟩ :=
    xa_al_backC (P := fun a => a ≠ (cSevm alDataW).currentTarget ∧ a ≠ 4) checkedM rfl
      (cSevm_fork _) hR hW hA hm w900 hst'
      (by rw [Stor.get_set_ne _ lock_ne_token]; exact (wPre_c3Entry _).prec) htokB
      (by rw [hcd']; exact wPre_poolCode _)
      (by rw [Stor.get_set_ne _ lock_ne_token]; exact ⟨htt, ht4⟩)
      (fun c hc hp => (hKC c (by rw [hL]; exact List.mem_cons_of_mem _ (List.mem_append_right _ hc))
        hp.1 hp.2).1) h
  have hcoin : ∀ i, i < 3 → ∀ c : Exec.Frame, c.sevm.currentTarget =
      (coinAt (alLocked ((St (St (wPre alDataW) [] Mem.empty 1110000) [] Mem.empty 1110000).getStor
        (cSevm alDataW).currentTarget)) i).toAdr →
      c.sevm.currentTarget ≠ (cSevm alDataW).currentTarget ∧ c.sevm.currentTarget ≠ 4 :=
    fun i hi c ht => by
      rw [ht, coinAt, Stor.get_set_ne _ (coin_ne_lock hi)]
      exact hct i hi
  have hall : ∀ c ∈ Exec.childFrames exc,
      c.sevm.currentTarget ≠ (cSevm alDataW).currentTarget ∧ c.sevm.currentTarget ≠ 4 := by
    intro c hc
    rw [hL] at hc
    simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | ((hc | hc) | hc) | rfl
    · rw [hTt]; exact ⟨htt, ht4⟩
    · exact hcoin 0 (by decide) c (hk0.target c hc)
    · exact hcoin 1 (by decide) c (hk1.target c hc)
    · exact hcoin 2 (by decide) c (hk2.target c hc)
    · rw [hmt, Stor.get_set_ne _ lock_ne_token]; exact ⟨htt, ht4⟩
  exact ⟨fun c hc => (hKC c hc (hall c hc).1 (hall c hc).2).1,
    fun c hc => (hKC c hc (hall c hc).1 (hall c hc).2).2⟩

/-- **`add_liquidity` end to end at the concrete entry**: an actual successful execution of the
pool's runtime from `wPre alDataW` at gas `1110000`, whose effect is the model's
`add_liquidity([100, 200, 300], 599)` (`alOutW`: mint `599`), with the pool's checkpoint at the
post. -/
theorem al_frame_live :
    ∃ post, ∃ exc : Exec 0 (cSevm alDataW) (St (wPre alDataW) [] Mem.empty 1110000) (.ok post),
      ∃ e : Env,
      e.supply = some (6000 : B256).toNat ∧
        step poolState e (decodeCall (cSevm alDataW)) = some alOutW ∧
        RawEffect ⟨0, cSevm alDataW, St (wPre alDataW) [] Mem.empty 1110000, .ok post, exc⟩ post
          e alOutW ∧
        Checkpoint (post.getStor poolAddr) alOutW.state :=
  al_frame_live_of_keep alw_keep

end Blanc.Composition.Curve3Pool3CrvInstance
