import Blanc.Lift.Curve3Pool.RemoveLiquidityLiveness
import Blanc.Lift.Curve3Pool.Walk.RemoveLiquidityExactWalk

/-!
# Exact-gas liveness of `remove_liquidity`

`removeLiquidity_live_exact`: at a `Checkpoint`, when the model's `remove_liquidity` succeeds in
`rlEnv sevm T` and the five calls are exact profiles with the data `P` (`RLExactPremises`), the
cost `c = rlExactCost sevm pre T P` is fixed, and for every residual gas `R ≥ 167000 + 5 U`
(headroom, not cost) the frame entered with `R + c` has an actual successful execution that ends
with exactly `R` gas, whose effect is the model's step: the same `RawEffect` and `Checkpoint` as
`removeLiquidity_live`.

The route: the exact byte walk `rx_rl_frame_exact` gives a run ending with `R`; `lift_exactM`
makes it an `Exec`. `removeLiquidity_live`, applied at the same entry gas with the exact profiles'
bounded projections, gives an `Exec` with the effect and the checkpoint; executions from one
entry have one result (`Exec.result_unique`), so that post is the exact walk's.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

/-- The exact walk's model-side checks, read off a successful model step at a checkpoint: no
value, a nonzero supply, and each coin's overflow, minimum and balance checks passing. -/
theorem removeLiquidity_walkChecks {sevm : Sevm} {pre : Devm} {s : State} {o : Out} {T : B256}
    (hlen : 4 ≤ sevm.data.length) (hsel : Sevm.selector sevm = selRemoveLiquidity)
    (hck : Checkpoint (pre.getStor sevm.currentTarget) s)
    (hstep : step s (rlEnv sevm T) (decodeCall sevm) = some o) :
    sevm.value = 0 ∧ T ≠ 0 ∧
      (∀ i, i < 3 → (B256.eqCheck (rlB sevm pre i * rlAmt sevm / rlB sevm pre i) (rlAmt sevm) |||
        B256.eqCheck (rlB sevm pre i) 0) ≠ 0) ∧
      (∀ i, i < 3 → B256.eqCheck (B256.ltCheck (rlV sevm pre T i) (rlMin sevm i)) 0 ≠ 0) ∧
      (∀ i, i < 3 → B256.eqCheck (B256.ltCheck (rlB sevm pre i) (rlV sevm pre T i)) 0 ≠ 0) ∧
      (rlAmt sevm).toNat ≤ T.toNat := by
  have hdec : decodeCall sevm = .removeLiquidity (arg sevm 0) (argV3 sevm 1) :=
    decodeCall_at (k := 7) rfl hsel hlen
  rw [hdec] at hstep
  have h' : (if (rlEnv sevm T).value = 0 then
      removeLiquidity s (rlEnv sevm T) (arg sevm 0) (argV3 sevm 1) else none) = some o := hstep
  split_ifs at h' with hv0
  have hval : sevm.value = 0 := B256.toNat_inj _ _ (by rw [show sevm.value.toNat = 0 from hv0]; rfl)
  obtain ⟨Tn, hTn, hT0n, hmul, hmin, hle, -, -, hTa⟩ := removeLiquidity_inv h'
  have hTn' : Tn = T.toNat := (Option.some.inj hTn).symm
  subst hTn'
  have hA : arg sevm 0 = (rlAmt sevm).toNat := by
    unfold arg Sevm.argWord
    rw [show (32 * (0 : B256) + 4 : B256) = Bytes.toB256 [4] by decide]
  have hM : ∀ i (hi : i < 3), (argV3 sevm 1).get ⟨i, hi⟩ = (rlMin sevm i).toNat := by
    intro i hi
    obtain rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    · show (Sevm.dataWord sevm (32 * 1 + 4)).toNat = _
      rw [show (32 * 1 + 4 : B256) = Bytes.toB256 [32] * Nat.toB256 0 + Bytes.toB256 [36] by decide]
    · show (Sevm.dataWord sevm (32 * (1 + 1) + 4)).toNat = _
      rw [show (32 * (1 + 1) + 4 : B256) = Bytes.toB256 [32] * Nat.toB256 1 + Bytes.toB256 [36]
        by decide]
    · show (Sevm.dataWord sevm (32 * (1 + 2) + 4)).toNat = _
      rw [show (32 * (1 + 2) + 4 : B256) = Bytes.toB256 [32] * Nat.toB256 2 + Bytes.toB256 [36]
        by decide]
  have hb : ∀ k : Fin 3, s.balances.get k = (balAt (pre.getStor sevm.currentTarget) k).toNat :=
    fun k => (hck.abs.balances k).symm
  have hT0 : T ≠ 0 := fun h => hT0n (by rw [h]; rfl)
  have hm : ∀ i, (hi : i < 3) → (balAt (pre.getStor sevm.currentTarget) i).toNat *
      (rlAmt sevm).toNat < 2 ^ 256 := by
    intro i hi; have := hmul ⟨i, hi⟩; rwa [hb, hA] at this
  have hv : ∀ i, (hi : i < 3) → (balAt (pre.getStor sevm.currentTarget) i * rlAmt sevm / T).toNat =
      (balAt (pre.getStor sevm.currentTarget) i).toNat * (rlAmt sevm).toNat / T.toNat :=
    fun i hi => rlOut_toNat (hm i hi) hT0
  refine ⟨hval, hT0, fun i hi => mulCheck_ne_zero (hm i hi), fun i hi => geCheck_ne_zero ?_,
    fun i hi => geCheck_ne_zero ?_, by rw [← hA]; exact hTa⟩
  · rw [hv i hi, ← hM i hi]; have := hmin ⟨i, hi⟩; rwa [hb, hA] at this
  · rw [hv i hi]; have := hle ⟨i, hi⟩; rwa [hb, hA] at this

/-- **Exact-gas liveness of `remove_liquidity`.** With the calls' data `P` and its exact
premises, the cost `rlExactCost sevm pre T P` is fixed before the residual gas. For every
`R ≥ 167000 + 5 U` (headroom only) at which the entry's gas measure is a word and every
execution's children keep the pool's storage and the code at `4` (`hkeep`, at that entry gas as
`removeLiquidity_live` takes it), the frame entered with `R + rlExactCost` has an actual
successful execution ending with exactly `R` gas, whose post state is the model's step: its
`RawEffect` in `rlEnv sevm T` with `o`, and `Checkpoint post o.state`. -/
theorem removeLiquidity_live_exact {sevm : Sevm} {pre : Devm} {s : State} {o : Out} {T : B256}
    {W : Nat → Devm → Prop} {U : Nat} (P : RLExactCalls)
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hstatic : sevm.isStatic = false) (hdepth : sevm.depth ≠ 0)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selRemoveLiquidity)
    (hck : Checkpoint (pre.getStor sevm.currentTarget) s)
    (hstep : step s (rlEnv sevm T) (decodeCall sevm) = some o)
    (htok : ¬ sevm.benvStat.rules.isPrecomp
      ((pre.getStor sevm.currentTarget).get tokenSlot).toAdr)
    (hcoin : ∀ k : Fin 3,
      ¬ sevm.benvStat.rules.isPrecomp ((pre.getStor sevm.currentTarget).get (coinSlot k)).toAdr)
    (hpc : pre.getCode sevm.currentTarget ≠ .empty) (hid : IdReady sevm pre)
    (hWc : ∀ k, k ≤ 3 → WClosed sevm (W k)) (hWb : W 0 pre)
    (hP : RLExactPremises sevm pre T W U P) :
    ∀ R, 167000 + 5 * U ≤ R →
      (St pre [] Mem.empty (R + rlExactCost sevm pre T P)).gasMeasure < 2 ^ 256 →
      (∀ post (exc : Exec 0 sevm (St pre [] Mem.empty (R + rlExactCost sevm pre T P)) (.ok post)),
        PoolCallsKeep ⟨0, sevm, St pre [] Mem.empty (R + rlExactCost sevm pre T P), .ok post, exc⟩ ∧
          ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4) →
      ∃ post, ∃ exc : Exec 0 sevm (St pre [] Mem.empty (R + rlExactCost sevm pre T P)) (.ok post),
        post.gasLeft = R ∧
        RawEffect ⟨0, sevm, St pre [] Mem.empty (R + rlExactCost sevm pre T P), .ok post, exc⟩
          post (rlEnv sevm T) o ∧
        Checkpoint (post.getStor sevm.currentTarget) o.state := by
  intro R hR hGm hkeep
  have hG256 : R + rlExactCost sevm pre T P < 2 ^ 256 := by
    have e : (St pre [] Mem.empty (R + rlExactCost sevm pre T P)).gasMeasure =
      R + rlExactCost sevm pre T P + pre.mach.stateGas.spilled +
        pre.mach.stateGas.committedSpill := rfl
    omega
  obtain ⟨hval, hT0, hmulw, hminw, hlew, hTa⟩ := removeLiquidity_walkChecks hlen hsel hck hstep
  have hP' := hP
  obtain ⟨hsup, hpush, hburn⟩ := hP'
  -- the exact run
  obtain ⟨r, hr, D, rfl, hDg, -⟩ := rx_rl_frame_exact P hfork hstatic hdepth hlen hcd hsel hid
    hck.unlocked hval hWc hWb hP hmulw hT0 hminw hlew hTa hR hG256
  obtain ⟨exD⟩ := lift_exactM cert_checkM cert_jumpsOkM hcode hfork ⟨t_0000_c0, rfl, hr⟩
  -- the effect, at the same entry gas
  obtain ⟨post, exc, hraw, hckp⟩ := removeLiquidity_live (G := R + rlExactCost sevm pre T P)
    hcode hfork hstatic hdepth hlen hcd hsel hck hstep htok hcoin hpc hid hkeep hWc hWb
    (StaticWordExactAt.bounded ⟨_, _, hsup⟩)
    (fun k => MutCallExactAt.bounded ⟨_, _, hpush k k.isLt⟩)
    (BurnOkAt.burnOkTo (MutCallExactAt.bounded ⟨_, _, hburn⟩))
    (by omega) hGm
  have hpost : post = D := by
    have := Exec.result_unique exc exD
    injection this
  subst hpost
  exact ⟨post, exc, hDg, hraw, hckp⟩

end Blanc.Lift.Curve3Pool
