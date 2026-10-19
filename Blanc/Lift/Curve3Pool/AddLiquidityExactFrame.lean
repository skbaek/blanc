import Blanc.Lift.Curve3Pool.AddLiquidityLive
import Blanc.Lift.Curve3Pool.Walk.AddLiquidityExactWalk

/-!
# Exact-gas liveness of `add_liquidity`

`addLiquidity_live_exact`: at a `Checkpoint`, when the model's `add_liquidity` succeeds in
`alEnvW sevm T B1 B2` and the calls are exact profiles with the data `P` (`ALExactPremises`:
`totalSupply()`, each nonzero amount's `transferFrom`, the fee coin's two `balanceOf(self)` reads
for a nonzero fee-coin amount, and the `mint` of the model's amount), there is one cost `c`,
fixed before the residual gas, such that for every `R` above the bounded walk's headroom
(`costAddLiquidity … + 7 U ≤ R`) at which the entry's gas measure is a word, the frame entered
with `R + c` has an actual successful execution that ends with exactly `R` gas, whose effect is
the model's step: the same conclusion as `addLiquidity_live`. The cost is the closed
`alExactCost1` (positive supply) or `alExactCost0` (first deposit) at the model's words; the
headroom and the no-wrap bound are stated separately from it.

The route is the one of `removeLiquidity_live_exact`: the exact byte walk
`rx_al_frame1_exact` / `rx_al_frame0_exact` gives a run ending with `R`; `lift_exactM` makes it an
`Exec`; `addLiquidity_live`, applied at the same entry gas with the exact profiles' bounded
projections, gives an `Exec` with the effect and the checkpoint; executions from one entry have
one result (`Exec.result_unique`), so that post is the exact walk's.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

/-- **Exact-gas liveness of `add_liquidity`** (see the module note). -/
theorem addLiquidity_live_exact {sevm : Sevm} {pre : Devm} {s : State} {o : Out} {T B1 B2 : B256}
    {W : Nat → Devm → Prop} {U : Nat} (P : ALExactCalls)
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hstatic : sevm.isStatic = false) (hdepth : sevm.depth ≠ 0)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selAddLiquidity)
    (hck : Checkpoint (pre.getStor sevm.currentTarget) s)
    (hstep : step s (alEnvW sevm T.toNat B1.toNat B2.toNat) (decodeCall sevm) = some o)
    (htok : ¬ sevm.benvStat.rules.isPrecomp
      ((pre.getStor sevm.currentTarget).get tokenSlot).toAdr)
    (hcoin : ∀ k : Fin 3,
      ¬ sevm.benvStat.rules.isPrecomp ((pre.getStor sevm.currentTarget).get (coinSlot k)).toAdr)
    (hpc : pre.getCode sevm.currentTarget ≠ .empty) (hid : IdReady sevm pre)
    (hWc : ∀ j, j ≤ 4 → WClosed sevm (W j)) (hWb : W 0 pre)
    (hskip : ∀ k : Fin 3, alAmt sevm k.val = 0 → ∀ b, W k b → W (k + 1) b)
    (hP : ALExactPremises sevm (pre.getStor sevm.currentTarget) T B1 B2
      (Nat.toB256 (alMintAmt o)) W U P) :
    ∃ c, ∀ R, costAddLiquidity s (alEnvW sevm T.toNat B1.toNat B2.toNat) (argV3 sevm 0) + 7 * U ≤ R →
      (St pre [] Mem.empty (R + c)).gasMeasure + 6000 < 2 ^ 256 →
      (∀ post (exc : Exec 0 sevm (St pre [] Mem.empty (R + c)) (.ok post)),
        PoolCallsKeep ⟨0, sevm, St pre [] Mem.empty (R + c), .ok post, exc⟩ ∧
          ∀ c' ∈ Exec.childFrames exc, c'.post.getCode 4 = c'.pre.getCode 4) →
      ∃ post, ∃ exc : Exec 0 sevm (St pre [] Mem.empty (R + c)) (.ok post), post.gasLeft = R ∧
        ∃ e : Env, e.supply = some T.toNat ∧ step s e (decodeCall sevm) = some o ∧
          RawEffect ⟨0, sevm, St pre [] Mem.empty (R + c), .ok post, exc⟩ post e o ∧
          Checkpoint (post.getStor sevm.currentTarget) o.state := by
  have hP' := hP
  obtain ⟨hsup, hpull, hbalB, hbalA, hmint⟩ := hP'
  -- the exact profiles' bounded projections, as `addLiquidity_live` takes them
  have bsup : SupplyOkAt sevm (W 0) (W 0) ((pre.getStor sevm.currentTarget).get tokenSlot) T U
      0x27c 0x2c0 := StaticWordExactAt.bounded ⟨_, _, hsup⟩
  have bpull : ∀ k : Fin 3, k ≠ feeIndex → alAmt sevm k.val ≠ 0 →
      CoinPullOkAt sevm (W k) (W (k + 1)) ((pre.getStor sevm.currentTarget).get (coinSlot k))
        (alAmt sevm k.val) U 0x760 0x820 :=
    fun k _ h => MutCallExactAt.bounded ⟨_, _, hpull k k.isLt h⟩
  have bfee : alAmt sevm 2 ≠ 0 →
      CoinBalOkAt sevm (W 2) (W 2) ((pre.getStor sevm.currentTarget).get (coinSlot 2)) B1 U
        0x53c 0x5a0 ∧
      CoinPullOkAt sevm (W 2) (W 3) ((pre.getStor sevm.currentTarget).get (coinSlot 2))
        (alAmt sevm 2) U 0x760 0x820 ∧
      CoinBalOkAt sevm (W 3) (W 3) ((pre.getStor sevm.currentTarget).get (coinSlot 2)) B2 U
        0x87c 0x8e0 := fun h =>
    ⟨StaticWordExactAt.bounded ⟨_, _, hbalB h⟩, MutCallExactAt.bounded ⟨_, _, hpull 2 (by decide) h⟩,
      StaticWordExactAt.bounded ⟨_, _, hbalA h⟩⟩
  have bmint : MintOkAt sevm (W 3) (W 4) ((pre.getStor sevm.currentTarget).get tokenSlot)
      (Nat.toB256 (alMintAmt o)) U 0xc7c 0xd00 := MutCallExactAt.bounded ⟨_, _, hmint⟩
  have hskip' : ∀ k, k < 3 → alAmt sevm k = 0 → ∀ b, W k b → W (k + 1) b :=
    fun k hk => hskip ⟨k, hk⟩
  -- the model's step, inverted, as words
  obtain ⟨hv0, hal⟩ := al_body hlen hsel hstep
  have hval : sevm.value = 0 := B256.toNat_inj _ _ (by rw [show sevm.value.toNat = 0 from hv0]; rfl)
  obtain ⟨amp, v1, xb, mint, T', hk, hamp, hfeeN, hnew, hmf, t0, sub, a0, a1, a2, hxb, hD1, hmin,
    hT', hbr⟩ := al_words_common hck.abs hal
  have hkill : (pre.getStor sevm.currentTarget).get isKilledSlot = 0 := by
    rw [hck.abs.isKilled, hk]; rfl
  have hbal : s.balances = ⟨(balAt (pre.getStor sevm.currentTarget) 0).toNat,
      (balAt (pre.getStor sevm.currentTarget) 1).toNat,
      (balAt (pre.getStor sevm.currentTarget) 2).toNat⟩ :=
    (V3.ext_get fun k => by rw [← ex_w3_nat]; exact ex_bal_nat hck.abs k).symm
  rcases hbr with ⟨rfl, hpos, rfl, ho⟩ | ⟨hT0, D0, fees, stored, after, D2, x, y, hD0, hlt, hfl, hD2,
    hx, hy, hm, ho⟩
  · -- the first deposit
    obtain ⟨hlt1, hslip, hadd, rfl, hv1e⟩ := al_words0 hD1 hpos hmin hT'
    have hcost := al_cost0 hamp hnew hxb
    have hma : alMintAmt o = mint := by rw [ho]; exact alMintAmt_eq
    rw [hma] at hP bmint
    refine ⟨alExactCost0 sevm pre P amp B1 B2 xb mint, fun R hR hGm hkeep => ?_⟩
    have hG256 : R + alExactCost0 sevm pre P amp B1 B2 xb mint + 6000 < 2 ^ 256 := by
      have e : (St pre [] Mem.empty (R + alExactCost0 sevm pre P amp B1 B2 xb mint)).gasMeasure =
        R + alExactCost0 sevm pre P amp B1 B2 xb mint + pre.mach.stateGas.spilled +
          pre.mach.stateGas.committedSpill := rfl
      omega
    obtain ⟨r, hr, -, D, rfl, hDg⟩ := rx_al_frame0_exact P hfork hstatic hdepth hlen hcd hsel hid
      hWc hWb hck.abs hck.unlocked hval hkill hamp hmf hP hskip' (t0 rfl) sub a0 a1 a2 hxb hD1 hlt1
      hslip hadd (by rw [hcost] at hR; omega) hG256
    obtain ⟨exD⟩ := lift_exactM cert_checkM cert_jumpsOkM hcode hfork ⟨t_0000_c0, rfl, hr⟩
    obtain ⟨post, exc, e, he, hstep', hraw, hckp⟩ := addLiquidity_live
      (G := R + alExactCost0 sevm pre P amp B1 B2 xb mint) hcode hfork hstatic hdepth hlen hcd hsel
      hck hstep htok hcoin hpc hid hkeep hWc hWb bsup bpull hskip bfee
      (by rw [hma]; exact bmint) (by omega) (by omega)
    have hpost : post = D := by
      have := Exec.result_unique exc exD
      injection this
    subst hpost
    exact ⟨post, exc, hDg, e, he, hstep', hraw, hckp⟩
  · -- a positive supply
    obtain ⟨xa, xc, v0, v2, f0, f1, f2, s0, s1, s2, x0, x1, x2, hxa, hD0', hlt', i0, i1, i2, hxc, hD2',
      hge, hmul, hD00, hslip, hadd, rfl, rfl, rfl, rfl, rfl, hxc0⟩ :=
      al_words1 hck.abs hD1 hD0 hlt hfl hD2 hx hy hm hmin hT'
    have hfl' := hfl
    rw [hck.abs.adminFee] at hfl'
    have hcost := al_cost1 hT0 hamp hfeeN hnew hxb (by rw [hbal]; exact hxa) hD0' hD1 hfl' hxc0
    have hma : Nat.toB256 (alMintAmt o) = alMintW T (Nat.toB256 D0) (Nat.toB256 v2) := by
      rw [ho, alMintAmt_eq]; exact toB256_toNat _
    have hP1 := hP
    rw [hma] at hP1
    have hnz : ¬ (alAmt sevm 0 = 0 ∧ alAmt sevm 1 = 0 ∧ alAmt sevm 2 = 0) := by
      rintro ⟨z0, z1, z2⟩
      have hsame : alNewW sevm (pre.getStor sevm.currentTarget) B1 B2 = s.balances := by
        obtain ⟨n0, n1, n2⟩ := al_liveNew_eq sevm (pre.getStor sevm.currentTarget) B1 B2
        have c0 : alCrK sevm B1 B2 0 = 0 := z0
        have c1 : alCrK sevm B1 B2 1 = 0 := z1
        have c2 : alCrK sevm B1 B2 2 = 0 := by
          show (if alAmt sevm 2 = 0 then alAmt sevm 2 else B2 - B1) = 0
          rw [ite_eq_left_of_eq_true _ _ (eq_true z2), z2]
        rw [hbal]
        show (⟨(alLiveNew sevm (alOld (pre.getStor sevm.currentTarget)) B1 B2 0).toNat,
          (alLiveNew sevm (alOld (pre.getStor sevm.currentTarget)) B1 B2 1).toNat,
          (alLiveNew sevm (alOld (pre.getStor sevm.currentTarget)) B1 B2 2).toNat⟩ : V3) = _
        rw [n0, n1, n2, c0, c1, c2, B256.add_zero, B256.add_zero, B256.add_zero]
      rw [hsame, hbal, hxa] at hxb
      obtain rfl := Option.some.inj hxb
      obtain rfl := Option.some.inj (hD0'.symm.trans hD1)
      exact Nat.lt_irrefl _ hlt
    refine ⟨alExactCost1 sevm pre P amp T B1 B2 xa xb xc D0 v1 v2 f0 f1 f2 s0 s1 s2 x0 x1 x2,
      fun R hR hGm hkeep => ?_⟩
    have hG256 : R + alExactCost1 sevm pre P amp T B1 B2 xa xb xc D0 v1 v2 f0 f1 f2 s0 s1 s2 x0 x1
        x2 + 6000 < 2 ^ 256 := by
      have e : (St pre [] Mem.empty (R + alExactCost1 sevm pre P amp T B1 B2 xa xb xc D0 v1 v2 f0
          f1 f2 s0 s1 s2 x0 x1 x2)).gasMeasure =
        R + alExactCost1 sevm pre P amp T B1 B2 xa xb xc D0 v1 v2 f0 f1 f2 s0 s1 s2 x0 x1 x2 +
          pre.mach.stateGas.spilled + pre.mach.stateGas.committedSpill := rfl
      omega
    obtain ⟨r, hr, -, D, rfl, hDg⟩ := rx_al_frame1_exact P hfork hstatic hdepth hlen hcd hsel hid
      hWc hWb hck.abs hck.unlocked hval hkill hamp hmf hP1 hskip' hT0 hnz sub a0 a1 a2 hxa hD0' hxb
      hD1 hlt' i0 i1 i2 hxc hD2' hge hmul hD00 hslip hadd (by rw [hcost] at hR; omega) hG256
    obtain ⟨exD⟩ := lift_exactM cert_checkM cert_jumpsOkM hcode hfork ⟨t_0000_c0, rfl, hr⟩
    obtain ⟨post, exc, e, he, hstep', hraw, hckp⟩ := addLiquidity_live
      (G := R + alExactCost1 sevm pre P amp T B1 B2 xa xb xc D0 v1 v2 f0 f1 f2 s0 s1 s2 x0 x1 x2)
      hcode hfork hstatic hdepth hlen hcd hsel hck hstep htok hcoin hpc hid hkeep hWc hWb bsup bpull
      hskip bfee bmint (by omega) (by omega)
    have hpost : post = D := by
      have := Exec.result_unique exc exD
      injection this
    subst hpost
    exact ⟨post, exc, hDg, e, he, hstep', hraw, hckp⟩

end Blanc.Lift.Curve3Pool
