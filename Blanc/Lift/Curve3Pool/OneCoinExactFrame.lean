import Blanc.Lift.Curve3Pool.OneCoinLive
import Blanc.Lift.Curve3Pool.Walk.OneCoinExactWalk

/-!
# Exact-gas liveness of `remove_liquidity_one_coin`

`removeLiquidityOneCoin_live_exact`: at a `Checkpoint`, when the model's
`remove_liquidity_one_coin` succeeds in `ocEnv sevm i T` and the three calls are exact profiles
with the data `P` (`OCExactPremises`: 3Crv's `totalSupply()`, its `burnFrom` of the amount, coin
`i`'s `transfer` of the model's `dy`), the model's words the cost reads (`amp`, `_xp`'s words, the
checked `get_D` and `get_y_D` results, the fee loop's `xp_reduced`) are pinned by the model's own
checks (`aChk`, `xpChk`, `getDChk`, `getYDChk`, `CwStep`), and the closed cost `ocExactCost` at
them is fixed before the residual gas: for every `R ≥ 131000 + 3 U` (headroom, not cost) at which
the entry's gas measure is a word (with the bounded theorem's `2000` of room) and every execution
from that entry keeps the pool's storage and the code at `4` (`hkeep`, as
`removeLiquidityOneCoin_live` takes it), the frame entered with `R + ocExactCost …` has an actual
successful execution that ends with exactly `R` gas, whose effect is the model's step: the
`RawEffect`, `Checkpoint` and `W''` of `removeLiquidityOneCoin_live`.

The route is the one of `removeLiquidity_live_exact`: the exact byte walk `rx_oc_frame_exact`
gives a run ending with `R`; `lift_exactM` makes it an `Exec`; `removeLiquidityOneCoin_live`,
applied at the same entry gas with the exact profiles' bounded projections, gives an `Exec` with
the effect; executions from one entry have one result (`Exec.result_unique`), so that post is the
exact walk's.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

/-- The closed exact cost covers the bounded sufficient-gas terms of the Newton callees. -/
theorem ocExactCost_ge (sevm : Sevm) (pre : Devm) (T : B256) (P : OCExactCalls) (amp : Nat)
    (x0 x1 x2 D0 y r0 r1 r2 y2 : B256) :
    costGetD x0.toNat x1.toNat x2.toNat amp +
      costGetYD amp (ocI sevm).toNat x0.toNat x1.toNat x2.toNat (D0 - ocAmt sevm * D0 / T).toNat +
      costGetYD amp (ocI sevm).toNat r0.toNat r1.toNat r2.toNat (D0 - ocAmt sevm * D0 / T).toNat ≤
      ocExactCost sevm pre T P amp x0 x1 x2 D0 y r0 r1 r2 y2 := by
  unfold ocExactCost ocCwCost cwRestCost
  omega

/-- **Exact-gas liveness of `remove_liquidity_one_coin`** (see the module note). -/
theorem removeLiquidityOneCoin_live_exact {sevm : Sevm} {pre : Devm} {s : State} {o : Out}
    {i : Fin 3} {T : B256} {W W' W'' : Devm → Prop} {U : Nat} (P : OCExactCalls)
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hstatic : sevm.isStatic = false) (hdepth : sevm.depth ≠ 0)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selRemoveLiquidityOneCoin)
    (hi : i.val = (ocI sevm).toNat)
    (hck : Checkpoint (pre.getStor sevm.currentTarget) s)
    (hstep : step s (ocEnv sevm i T.toNat) (decodeCall sevm) = some o)
    (htok : ¬ sevm.benvStat.rules.isPrecomp
      ((pre.getStor sevm.currentTarget).get tokenSlot).toAdr)
    (hcoin : ∀ k : Fin 3,
      ¬ sevm.benvStat.rules.isPrecomp ((pre.getStor sevm.currentTarget).get (coinSlot k)).toAdr)
    (hpc : pre.getCode sevm.currentTarget ≠ .empty) (hid : IdReady sevm pre)
    (hWc : WClosed sevm W) (hW'c : WClosed sevm W') (hWb : W pre) (hW''c : WClosed sevm W'')
    (hP : OCExactPremises sevm pre T (Nat.toB256 (ocPushAmt o)) W W' W'' U P) :
    ∃ (amp : Nat) (x0 x1 x2 D0 y r0 r1 r2 y2 : B256) (hi3 : (ocI sevm).toNat < 3),
      aChk s sevm.benvStat.time.toNat = some amp ∧
      xpChk s.balances = some ⟨x0.toNat, x1.toNat, x2.toNat⟩ ∧
      getDChk (V3.mk x0.toNat x1.toNat x2.toNat).get amp 1 = some D0.toNat ∧
      getYDChk amp ⟨(ocI sevm).toNat, hi3⟩ (V3.mk x0.toNat x1.toNat x2.toNat).get
        (D0 - ocAmt sevm * D0 / T).toNat = some y.toNat ∧
      CwStep (Bytes.toB256 [0] = ocI sevm) x0 (D0 - ocAmt sevm * D0 / T) D0 y
        (cwFee ((pre.getStor sevm.currentTarget).get feeSlot)) x0 r0 ∧
      CwStep (Bytes.toB256 [1] = ocI sevm) x1 (D0 - ocAmt sevm * D0 / T) D0 y
        (cwFee ((pre.getStor sevm.currentTarget).get feeSlot)) x1 r1 ∧
      CwStep (Bytes.toB256 [2] = ocI sevm) x2 (D0 - ocAmt sevm * D0 / T) D0 y
        (cwFee ((pre.getStor sevm.currentTarget).get feeSlot)) x2 r2 ∧
      getYDChk amp ⟨(ocI sevm).toNat, hi3⟩ (V3.mk r0.toNat r1.toNat r2.toNat).get
        (D0 - ocAmt sevm * D0 / T).toNat = some y2.toNat ∧
      ∀ R, 131000 + 3 * U ≤ R →
      (St pre [] Mem.empty (R + ocExactCost sevm pre T P amp x0 x1 x2 D0 y r0 r1 r2 y2)).gasMeasure +
        2000 < 2 ^ 256 →
      (∀ post (exc : Exec 0 sevm
          (St pre [] Mem.empty (R + ocExactCost sevm pre T P amp x0 x1 x2 D0 y r0 r1 r2 y2))
          (.ok post)),
        PoolCallsKeep ⟨0, sevm,
          St pre [] Mem.empty (R + ocExactCost sevm pre T P amp x0 x1 x2 D0 y r0 r1 r2 y2), .ok post,
          exc⟩ ∧
          ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4) →
      ∃ post, ∃ exc : Exec 0 sevm
          (St pre [] Mem.empty (R + ocExactCost sevm pre T P amp x0 x1 x2 D0 y r0 r1 r2 y2))
          (.ok post), ∃ T' : Nat,
        post.gasLeft = R ∧
        RawEffect ⟨0, sevm,
          St pre [] Mem.empty (R + ocExactCost sevm pre T P amp x0 x1 x2 D0 y r0 r1 r2 y2), .ok post,
          exc⟩ post (ocEnv sevm i T') o ∧
        Checkpoint (post.getStor sevm.currentTarget) o.state ∧ W'' post := by
  have hi3 : (ocI sevm).toNat < 3 := hi ▸ i.isLt
  obtain rfl : i = ⟨(ocI sevm).toNat, hi3⟩ := Fin.ext hi
  obtain ⟨hv0, hrl⟩ := oc_body hi3 hlen hsel hstep
  have hval : sevm.value = 0 := B256.toNat_inj _ _ (by rw [show sevm.value.toNat = 0 from hv0]; rfl)
  obtain ⟨amp, x0, x1, x2, D0, y, r0, r1, r2, y2, hi3', hk, hA, hmf, hX, hD0, hm, hT0, hle, hy, hyl,
    h0, h1, h2, hy2, hs0, hs1, hs2, hmin, hma, hadd, hsub, ho, hcost⟩ := oc_words hck.abs rfl hrl
  refine ⟨amp, x0, x1, x2, D0, y, r0, r1, r2, y2, hi3', hA, hX, hD0, hy, h0, h1, h2, hy2,
    fun R hR hGm hkeep => ?_⟩
  have hG256 : R + ocExactCost sevm pre T P amp x0 x1 x2 D0 y r0 r1 r2 y2 + 2000 < 2 ^ 256 := by
    have e : (St pre [] Mem.empty
        (R + ocExactCost sevm pre T P amp x0 x1 x2 D0 y r0 r1 r2 y2)).gasMeasure =
      R + ocExactCost sevm pre T P amp x0 x1 x2 D0 y r0 r1 r2 y2 + pre.mach.stateGas.spilled +
        pre.mach.stateGas.committedSpill := rfl
    omega
  have hpa : ocPushAmt o = (cwDy (ocI sevm) r0 r1 r2 y2).toNat := by rw [ho]; rfl
  have hP' := hP
  rw [hpa, toB256_toNat] at hP'
  obtain ⟨hsup, hburn, hpush⟩ := hP
  have hci : coinSlot ⟨(ocI sevm).toNat, hi3'⟩ = coinsBase + ocI sevm := by
    simp only [coinSlot, toB256_toNat]
  -- the exact run
  obtain ⟨r, hr, D, rfl, hDg⟩ := rx_oc_frame_exact (pre := pre) (s := s)
    (Q := fun r => ∃ D', r = .halted D' ∧ D'.gasLeft = R) P hfork hstatic hdepth hlen hcd hsel hid
    hWc hW'c hWb hck.abs hck.unlocked hval (by rw [hck.abs.isKilled, hk]; rfl) hi3' hA hP' hmf hX
    hD0 hm hT0 hle hy hyl h0 h1 h2 hy2 hs0 hs1 hs2 hmin hma hadd hsub hW''c hR hG256
    (fun D' _ _ hg => ⟨D', rfl, hg⟩)
  obtain ⟨exD⟩ := lift_exactM cert_checkM cert_jumpsOkM hcode hfork ⟨t_0000_c0, rfl, hr⟩
  -- the effect, at the same entry gas
  obtain ⟨post, exc, T', hraw, hckp, hW''⟩ := removeLiquidityOneCoin_live
    (G := R + ocExactCost sevm pre T P amp x0 x1 x2 D0 y r0 r1 r2 y2) hcode hfork hstatic hdepth
    hlen hcd hsel rfl hck hstep htok hcoin hpc hid hkeep hWc hW'c hWb
    (StaticWordExactAt.bounded ⟨_, _, hsup⟩) (MutCallExactAt.bounded ⟨_, _, hburn⟩) hW''c
    (by rw [hci]; exact MutCallExactAt.bounded ⟨_, _, hpush⟩)
    (by have := ocExactCost_ge sevm pre T P amp x0 x1 x2 D0 y r0 r1 r2 y2; rw [hcost]; omega) hGm
  have hpost : post = D := by
    have := Exec.result_unique exc exD
    injection this
  subst hpost
  exact ⟨post, exc, T', hDg, hraw, hckp, hW''⟩

end Blanc.Lift.Curve3Pool
