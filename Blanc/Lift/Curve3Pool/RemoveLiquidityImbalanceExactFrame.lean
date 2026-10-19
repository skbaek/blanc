import Blanc.Lift.Curve3Pool.RemoveImbalanceLive
import Blanc.Lift.Curve3Pool.Walk.RliExactWalk
import Blanc.ExecDeterminism

/-!
# Exact-gas liveness of `remove_liquidity_imbalance`

`removeLiquidityImbalance_live_exact`: at a `Checkpoint`, when the model's
`remove_liquidity_imbalance` succeeds in `rliEnvW sevm T` and the calls are exact profiles with
the data `P` (`RLIExactPremises`: 3Crv's `totalSupply()`, its `burnFrom` of the model's amount,
and coin `k`'s `transfer` only where its amount is nonzero), the model's words `w` (pinned by
`RliWordsPin`: `aChk`, the three `xpChk`/`getDChk` runs and the three fee iterations) and with
them the cost `c = rliExactCost sevm pre P T w` are fixed before any residual gas. For every
`R ≥ 66000 + 3 U` at which the old sufficient bound `costImbalance … + 5 U` fits the entry gas
`R + c` (headroom, not cost), the entry's gas measure is a word and every execution's children
keep the pool's storage and the code at `4` (`hkeep`, at that entry gas, as
`removeLiquidityImbalance_live` takes it), the frame entered with `R + c` has an actual
successful execution ending with exactly `R` gas, whose effect is `removeLiquidityImbalance_live`'s:
the same `RawEffect` in `rliEnvW sevm T`, `Checkpoint post o.state` and `W 4 post`.

The route is `removeLiquidity_live_exact`'s: the exact byte walk `rx_rli_frame_exact` gives a run
ending with `R`; `lift_exactM` makes it an `Exec`; `removeLiquidityImbalance_live`, applied at the
same entry gas with the exact profiles' bounded projections, gives an `Exec` with the effect;
executions from one entry have one result (`Exec.result_unique`), so that post is the exact
walk's. `RliWordsPin.unique`: the pinned words are unique.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

/-- **The model's words, pinned by the model's own checks** at the entry storage and timestamp:
`_A`, the three `get_D_mem` inputs (`xpChk`) and results (`getDChk`), and the three fee
iterations. -/
def RliWordsPin (sevm : Sevm) (pre : Devm) (s : State) (w : RliWords) : Prop :=
  aChk s sevm.benvStat.time.toNat = some w.amp ∧
    xpChk ⟨(balAt (rliσ sevm pre) 0).toNat, (balAt (rliσ sevm pre) 1).toNat,
      (balAt (rliσ sevm pre) 2).toNat⟩ = some w.xa ∧
    getDChk w.xa.get w.amp 1 = some w.v0 ∧
    xpChk ⟨(rliNew sevm pre 0).toNat, (rliNew sevm pre 1).toNat,
      (rliNew sevm pre 2).toNat⟩ = some w.xb ∧
    getDChk w.xb.get w.amp 1 = some w.v1 ∧
    RliFeeIter (cwFee ((rliσ sevm pre).get feeSlot)) ((rliσ sevm pre).get adminFeeSlot)
      (Nat.toB256 w.v0) (Nat.toB256 w.v1) (balAt (rliσ sevm pre) 0) (rliNew sevm pre 0) w.f0 w.s0
      w.x0 ∧
    RliFeeIter (cwFee ((rliσ sevm pre).get feeSlot)) ((rliσ sevm pre).get adminFeeSlot)
      (Nat.toB256 w.v0) (Nat.toB256 w.v1) (balAt (rliσ sevm pre) 1) (rliNew sevm pre 1) w.f1 w.s1
      w.x1 ∧
    RliFeeIter (cwFee ((rliσ sevm pre).get feeSlot)) ((rliσ sevm pre).get adminFeeSlot)
      (Nat.toB256 w.v0) (Nat.toB256 w.v1) (balAt (rliσ sevm pre) 2) (rliNew sevm pre 2) w.f2 w.s2
      w.x2 ∧
    xpChk ⟨w.x0.toNat, w.x1.toNat, w.x2.toNat⟩ = some w.xc ∧
    getDChk w.xc.get w.amp 1 = some w.v2

/-- **The pinned words are unique**: two witnesses of the model's checks are the same words. -/
theorem RliWordsPin.unique {sevm : Sevm} {pre : Devm} {s : State} {w w' : RliWords}
    (h : RliWordsPin sevm pre s w) (h' : RliWordsPin sevm pre s w') : w = w' := by
  obtain ⟨a, b, c, d, e, f0, f1, f2, g, i⟩ := h
  obtain ⟨a', b', c', d', e', f0', f1', f2', g', i'⟩ := h'
  cases w with
  | mk amp v0 v1 v2 xa xb xc g0 g1 g2 t0 t1 t2 y0 y1 y2 =>
  cases w' with
  | mk amp' v0' v1' v2' xa' xb' xc' g0' g1' g2' t0' t1' t2' y0' y1' y2' =>
  simp only at a b c d e f0 f1 f2 g i a' b' c' d' e' f0' f1' f2' g' i'
  obtain rfl := Option.some.inj (a.symm.trans a')
  obtain rfl := Option.some.inj (b.symm.trans b')
  obtain rfl := Option.some.inj (c.symm.trans c')
  obtain rfl := Option.some.inj (d.symm.trans d')
  obtain rfl := Option.some.inj (e.symm.trans e')
  obtain ⟨rfl, rfl, rfl⟩ := f0.unique f0'
  obtain ⟨rfl, rfl, rfl⟩ := f1.unique f1'
  obtain ⟨rfl, rfl, rfl⟩ := f2.unique f2'
  obtain rfl := Option.some.inj (g.symm.trans g')
  obtain rfl := Option.some.inj (i.symm.trans i')
  rfl

/-- **Exact-gas liveness of `remove_liquidity_imbalance`** (see the module note). -/
theorem removeLiquidityImbalance_live_exact {sevm : Sevm} {pre : Devm} {s : State} {o : Out}
    {T : B256} {W : Nat → Devm → Prop} {U : Nat} (P : RLIExactCalls)
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hstatic : sevm.isStatic = false) (hdepth : sevm.depth ≠ 0)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selRemoveLiquidityImbalance)
    (hck : Checkpoint (pre.getStor sevm.currentTarget) s)
    (hstep : step s (rliEnvW sevm T.toNat) (decodeCall sevm) = some o)
    (htok : ¬ sevm.benvStat.rules.isPrecomp
      ((pre.getStor sevm.currentTarget).get tokenSlot).toAdr)
    (hcoin : ∀ k : Fin 3,
      ¬ sevm.benvStat.rules.isPrecomp ((pre.getStor sevm.currentTarget).get (coinSlot k)).toAdr)
    (hpc : pre.getCode sevm.currentTarget ≠ .empty) (hid : IdReady sevm pre)
    (hWc : ∀ j, j ≤ 4 → WClosed sevm (W j)) (hWb : W 0 pre)
    (hP : RLIExactPremises sevm (pre.getStor sevm.currentTarget) T (Nat.toB256 (rliBurnAmt o)) W
      U P)
    (hskip : ∀ k : Fin 3, rliAmt sevm k.val = 0 → ∀ b, W (k + 1) b → W (k + 2) b) :
    ∃ w : RliWords, RliWordsPin sevm pre s w ∧
      ∀ R, 66000 + 3 * U ≤ R →
        costImbalance s (rliEnvW sevm T.toNat) (argV3 sevm 0) + 5 * U ≤
          R + rliExactCost sevm pre P T w →
        (St pre [] Mem.empty (R + rliExactCost sevm pre P T w)).gasMeasure + 3000 < 2 ^ 256 →
        (∀ post (exc : Exec 0 sevm
            (St pre [] Mem.empty (R + rliExactCost sevm pre P T w)) (.ok post)),
          PoolCallsKeep ⟨0, sevm, St pre [] Mem.empty (R + rliExactCost sevm pre P T w), .ok post,
            exc⟩ ∧ ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4) →
        ∃ post, ∃ exc : Exec 0 sevm
            (St pre [] Mem.empty (R + rliExactCost sevm pre P T w)) (.ok post),
          post.gasLeft = R ∧
          RawEffect ⟨0, sevm, St pre [] Mem.empty (R + rliExactCost sevm pre P T w), .ok post, exc⟩
            post (rliEnvW sevm T.toNat) o ∧
          Checkpoint (post.getStor sevm.currentTarget) o.state ∧ W 4 post := by
  obtain ⟨hv0, hrl⟩ := rli_body hlen hsel hstep
  have hval : sevm.value = 0 := B256.toNat_inj _ _ (by rw [show sevm.value.toNat = 0 from hv0]; rfl)
  obtain ⟨amp, v0, v1, v2, xa, xb, xc, f0, f1, f2, s0, s1, s2, x0, x1, x2, hk, hA, hmf, hT0, hX0,
    hD0, hu0, hu1, hu2, hX1, hD1, h0, h1, h2, hX2, hD2, hD02, hmT, hbn, hb1, hslip, hTX, ho,
    -⟩ := rli_words hck.abs hrl
  refine ⟨⟨amp, v0, v1, v2, xa, xb, xc, f0, f1, f2, s0, s1, s2, x0, x1, x2⟩,
    ⟨hA, hX0, hD0, hX1, hD1, h0, h1, h2, hX2, hD2⟩, fun R hR hG hGm hkeep => ?_⟩
  have hG256 : R + rliExactCost sevm pre P T ⟨amp, v0, v1, v2, xa, xb, xc, f0, f1, f2, s0, s1, s2,
      x0, x1, x2⟩ + 3000 < 2 ^ 256 := by
    have e : (St pre [] Mem.empty (R + rliExactCost sevm pre P T ⟨amp, v0, v1, v2, xa, xb, xc, f0,
        f1, f2, s0, s1, s2, x0, x1, x2⟩)).gasMeasure =
      R + rliExactCost sevm pre P T ⟨amp, v0, v1, v2, xa, xb, xc, f0, f1, f2, s0, s1, s2, x0, x1,
        x2⟩ + pre.mach.stateGas.spilled + pre.mach.stateGas.committedSpill := rfl
    omega
  have hba : rliBurnAmt o = (rliBurnW (Nat.toB256 v0) (Nat.toB256 v2) T).toNat := by rw [ho]; rfl
  have hP' := hP
  rw [hba, toB256_toNat] at hP'
  have hkill : (pre.getStor sevm.currentTarget).get isKilledSlot = 0 := by
    rw [hck.abs.isKilled, hk]; rfl
  -- the exact run
  obtain ⟨r, hr, D, rfl, hDg⟩ := rx_rli_frame_exact (s := s) P
    ⟨amp, v0, v1, v2, xa, xb, xc, f0, f1, f2, s0, s1, s2, x0, x1, x2⟩ hfork hstatic hdepth hlen hcd
    hsel hid hWc hWb hck.abs hck.unlocked hval hkill hA hT0 hmf hX0 hD0 hu0 hu1 hu2 hX1 hD1 h0 h1 h2
    hX2 hD2 hD02 hmT hbn hb1 hslip hTX hP' (fun j hj => hskip ⟨j, hj⟩) hR hG256
  obtain ⟨exD⟩ := lift_exactM cert_checkM cert_jumpsOkM hcode hfork ⟨t_0000_c0, rfl, hr⟩
  -- the effect, at the same entry gas
  obtain ⟨post, exc, hraw, hckp, hW4⟩ := removeLiquidityImbalance_live
    (G := R + rliExactCost sevm pre P T ⟨amp, v0, v1, v2, xa, xb, xc, f0, f1, f2, s0, s1, s2, x0, x1,
      x2⟩) hcode hfork hstatic hdepth hlen hcd hsel hck hstep htok hcoin hpc hid hkeep hWc hWb
    (StaticWordExactAt.bounded ⟨_, _, hP.supply⟩) (MutCallExactAt.bounded ⟨_, _, hP.burn⟩)
    (fun k h => MutCallExactAt.bounded ⟨_, _, hP.push k.val k.isLt h⟩) hskip hG (by omega)
  have hpost : post = D := by
    have := Exec.result_unique exc exD
    injection this
  subst hpost
  exact ⟨post, exc, hDg, hraw, hckp, hW4⟩

end Blanc.Lift.Curve3Pool
