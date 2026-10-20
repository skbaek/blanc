import Blanc.Lift.Curve3Pool.Model
import Blanc.Lift.Curve3Pool.Check
import Blanc.Lift.Curve3Pool.Refine
import Blanc.Lift.Curve3Pool.Walk.AddLiquidityChecks
import Blanc.Lift.Curve3Pool.Walk.AlLiveLink
import Blanc.Lift.Curve3Pool.Walk.AlLiveCut
import Blanc.Lift.Curve3Pool.Walk.LiveLink

/-!
# Liveness of `add_liquidity`

`addLiquidity_live`: at a `Checkpoint` (`s`), if the model's `add_liquidity` succeeds in the
environment `alEnvW sevm T B1 B2` (3Crv's `totalSupply()` answers `T`; every `transferFrom`
accepted; the fee coin's `balanceOf(self)` answers `B1` before and `B2` after its pull; `mint`
accepted) and the callees answer as `LivePremises` describes — `totalSupply()` (`SupplyOkAt`,
window `0x27c`/`0x2c0`), each nonzero amount's `transferFrom` (`CoinPullOkAt`, `0x760`/`0x820`),
for a nonzero fee-coin amount its two `balanceOf(self)` reads (`CoinBalOkAt`, `0x53c`/`0x5a0` and
`0x87c`/`0x8e0`), and `mint` of the model's amount (`MintOkAt`, `0xc7c`/`0xd00`), each within `U`
gas, along a world chain `W 0 → … → W 4` (the supply read in `W 0`; coin `k`'s pull from `W k` to
`W (k + 1)`, a coin with amount `0` skipped with `W k ⊆ W (k + 1)`; the fee coin's balance reads in
`W 2` and `W 3`; the mint from `W 3` to `W 4`: each state-changing call lands in a fresh
invariant, since one closed under a positive transfer or mint would admit no honest callee) — then every frame gas `G ≥ costAddLiquidity … + 7 U` yields an actual successful execution
of the pool's runtime whose effect is the model's step at the premised `o`: `RawEffect` in the
environment `e` the frame observed (`e.supply = T`; `step s e … = some o` too) and
`Checkpoint post o.state`. Both branches: the first deposit (`T = 0`) and the fee path.
`costAddLiquidity` is a closed sufficient-gas bound (the `get_D_mem` runs at their actual inputs
plus a constant), not the exact gas.

The route: the forward runs `rx_al_frame1` / `rx_al_frame0`, `lift_exactM`, the safety theorem on
that execution (`addLiquidity_rawE`); the supply its first child answered is `T` (the cut walk
`xa_cutAt_start` along `alSupplyPath`, which crosses `_A()`, and `xa_staticWordOkAt`); the fee
coin's observed answers are not pinned individually, but the produced execution stores the
forward run's balances and logs its fees, which pin the model's output (`al_out_unique`).

`addLiquidity_none_of_pull`: the U6 negative control — a refused `transferFrom` of a nonzero
deposit makes the model's step revert. (`pullIn_none_of_pull`: the pull itself fails, on either
the plain or the fee coin's balance-difference path.)
-/

namespace Blanc.Lift.Curve3Pool

/-- A refused `transferFrom` fails the model's pull, on either path. -/
theorem pullIn_none_of_pull {e : Env} {i : Fin 3} {amount : Nat}
    (hp : (e.coin i).pullOk = false) : pullIn e i amount = none := by
  unfold pullIn
  split_ifs
  · cases (e.coin i).balPre with
    | none => rfl
    | some w => simp only [Option.bind_eq_bind, Option.bind_some, req, hp, Bool.false_eq_true,
        ↓reduceIte, Option.bind_none]
  · simp only [Option.bind_eq_bind, req, hp, Bool.false_eq_true, ↓reduceIte, Option.bind_none]

/-- **The control**: a refused `transferFrom` of a nonzero deposit makes the model's
`add_liquidity` revert. -/
theorem addLiquidity_none_of_pull {s : State} {e : Env} {amounts : V3} {m : Nat} {k : Fin 3}
    (hk : amounts.get k ≠ 0) (hp : (e.coin k).pullOk = false) :
    addLiquidity s e amounts m = none := by
  have hpa : ∀ T old, pullAdd e T old amounts k = none := by
    intro T old
    have hpos : amounts.get k > 0 := Nat.pos_of_ne_zero hk
    unfold pullAdd
    rw [pullIn_none_of_pull hp]
    split_ifs <;> simp only [Option.bind_eq_bind, req, hpos, ↓reduceIte, Option.bind_some,
      Option.bind_none]
  have hof : ∀ T old, V3.ofFnM (pullAdd e T old amounts) = none := by
    intro T old
    unfold V3.ofFnM
    match k, hpa T old with
    | 0, h => simp only [Option.bind_eq_bind, h, Option.bind_none]
    | 1, h => cases pullAdd e T old amounts 0 <;>
        simp only [Option.bind_eq_bind, h, Option.bind_none, Option.bind_some]
    | 2, h => cases pullAdd e T old amounts 0 <;> cases pullAdd e T old amounts 1 <;>
        simp only [Option.bind_eq_bind, h, Option.bind_none, Option.bind_some]
  unfold addLiquidity
  simp only [Option.bind_eq_bind, hof, Option.bind_none, Option.bind_fun_none, ite_self]

open Jaune Blanc.Lift Blanc.StableSwapNewton in
/-- **The first child of a produced `add_liquidity` execution is the forward run's supply call**:
its reply is the premise's `T`. -/
theorem al_supplyChild {sevm : Sevm} {pre post : Devm} {s : State} {W : Devm → Prop}
    {G U amp : Nat} {T : B256}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hstatic : sevm.isStatic = false) (hlen : 4 ≤ sevm.data.length)
    (hcd : sevm.data.length < 2 ^ 256) (hsel : Sevm.selector sevm = selAddLiquidity)
    (hid : IdReady sevm pre) (hWc : WClosed sevm W) (hWb : W pre)
    (ha : Abstracts (pre.getStor sevm.currentTarget) s)
    (hlock : (pre.getStor sevm.currentTarget).get lockSlot = 0) (hval : sevm.value = 0)
    (hkill : (pre.getStor sevm.currentTarget).get isKilledSlot = 0)
    (hA : aChk s sevm.benvStat.time.toNat = some amp)
    (hmf : (pre.getStor sevm.currentTarget).get feeSlot * Bytes.toB256 [0x03] /
        (pre.getStor sevm.currentTarget).get feeSlot = Bytes.toB256 [0x03] ∨
      (pre.getStor sevm.currentTarget).get feeSlot = 0)
    (hsup : SupplyOkAt sevm W W ((pre.getStor sevm.currentTarget).get tokenSlot) T U 0x27c 0x2c0)
    (htok : ¬ sevm.benvStat.rules.isPrecomp
      ((pre.getStor sevm.currentTarget).get tokenSlot).toAdr)
    (hG : 70000 + U ≤ G) (hGm : (St pre [] Mem.empty G).gasMeasure < 2 ^ 256)
    (exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post)) :
    ∃ c L, Exec.childFrames exc = c :: L ∧ alWord c = T := by
  have hG256 : G < 2 ^ 256 := by
    have e : (St pre [] Mem.empty G).gasMeasure =
      G + pre.mach.stateGas.spilled + pre.mach.stateGas.committedSpill := rfl
    omega
  obtain ⟨r1, hr1, b1, S1, M1, g1, rfl, hW1, hU1, hg1, hin1, hS1⟩ := rx_al_toSupply (pre := pre)
    (U := U) (G := G) hfork hstatic hlen hcd hsel hid hWc hWb ha hlock hval hkill hA hmf hG hG256
  have hx : XAt sevm post 0 (St pre [] Mem.empty G) (Exec.childFrames exc) := XAt.of_exec exc hGm
  obtain ⟨m1, pc1, a1, μ1, hw1⟩ := xa_cutAt_start checkedM
    (Cert.jumpsOkM_of_jumpsOkM cert_jumpsOkM) hcode hfork a_execFreeSet a_noHaltSet rfl rfl rfl rfl
    rfl (SFunc.cutCall_of_cutPathOk _ _ alSupplyPath_ok) hr1 hx
  have hx1 := hw1.xat
  have hchk1 := hw1.check
  obtain ⟨X, hX⟩ : ∃ X, SFunc.subAt cert.prog alSupplyPath t_0000_c0 =
      .next (.exec .staticcall) X := ⟨_, rfl⟩
  rw [hX] at hchk1
  obtain ⟨c, L', hL, -, -, -, hcT⟩ := xa_staticWordOkAt hfork (checkNodeM_next_at hcode hchk1) hx1
    hsup hW1 hU1 hg1 hin1 htok hS1
  exact ⟨c, L', hL, hcT⟩

/-- The amount `add_liquidity` mints, read off the model's call list. -/
def alMintAmt (o : Out) : Nat :=
  match o.calls.getLast? with
  | some (.mint _ a) => a
  | _ => 0

theorem alMintAmt_eq {st : State} {r : Option Nat} {ev : List Event} {cs : List ExtCall}
    {c a : Nat} : alMintAmt ⟨st, r, ev, cs ++ [.mint c a]⟩ = a := by
  unfold alMintAmt
  rw [List.getLast?_concat]

open Jaune Blanc.Lift in
/-- The deposit loop's premises from the frame's: the windows at the stored coins, the words. -/
theorem al_loopOk {sevm : Sevm} {W : Nat → Devm → Prop} {σ : Stor} {T B1 B2 : B256} {U : Nat}
    (ht0 : T = 0 → alAmt sevm 0 ≠ 0 ∧ alAmt sevm 1 ≠ 0 ∧ alAmt sevm 2 ≠ 0)
    (hnz : ¬ (alAmt sevm 0 = 0 ∧ alAmt sevm 1 = 0 ∧ alAmt sevm 2 = 0))
    (hWc : ∀ j, j ≤ 4 → WClosed sevm (W j))
    (hpull : ∀ k : Fin 3, k ≠ feeIndex → alAmt sevm k.val ≠ 0 →
      CoinPullOkAt sevm (W k) (W (k + 1)) (σ.get (coinSlot k)) (alAmt sevm k.val) U 0x760 0x820)
    (hskip : ∀ k : Fin 3, alAmt sevm k.val = 0 → ∀ b, W k b → W (k + 1) b)
    (hfee : alAmt sevm 2 ≠ 0 →
      CoinBalOkAt sevm (W 2) (W 2) (σ.get (coinSlot 2)) B1 U 0x53c 0x5a0 ∧
      CoinPullOkAt sevm (W 2) (W 3) (σ.get (coinSlot 2)) (alAmt sevm 2) U 0x760 0x820 ∧
      CoinBalOkAt sevm (W 3) (W 3) (σ.get (coinSlot 2)) B2 U 0x87c 0x8e0)
    (hsub : alAmt sevm 2 ≠ 0 → ¬ B2 < B1)
    (ha0 : ¬ balAt σ 0 + alAmt sevm 0 < balAt σ 0) (ha1 : ¬ balAt σ 1 + alAmt sevm 1 < balAt σ 1)
    (ha2 : ¬ balAt σ 2 + alCr2 sevm B1 B2 < balAt σ 2) :
    AlLoopOk sevm W (alLocked1 σ) T B1 B2 (alOld σ) U := by
  have hc : ∀ k : Fin 3, coinAt (alLocked1 σ) k.val = σ.get (coinSlot k) := fun k =>
    Stor.get_set_ne _ (coin_ne_lock k.isLt) _
  have hc0 : coinAt (alLocked1 σ) 0 = σ.get (coinSlot 0) := hc 0
  have hc1 : coinAt (alLocked1 σ) 1 = σ.get (coinSlot 1) := hc 1
  have hc2 : coinAt (alLocked1 σ) 2 = σ.get (coinSlot 2) := hc 2
  refine ⟨ht0, hnz, fun j hj => hWc j (by omega), hskip 0, hskip 1, hskip 2, fun h => ?_,
    fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_, hsub, ha0, ha1, ha2⟩
  · rw [hc0]; exact hpull 0 (by decide) h
  · rw [hc1]; exact hpull 1 (by decide) h
  · rw [hc2]; exact (hfee h).1
  · rw [hc2]; exact (hfee h).2.1
  · rw [hc2]; exact (hfee h).2.2

open Jaune Blanc.Lift Blanc.StableSwapNewton in
/-- **`add_liquidity` is live** (see the module note). -/
theorem addLiquidity_live {sevm : Sevm} {pre : Devm} {s : State} {o : Out} {T B1 B2 : B256}
    {W : Nat → Devm → Prop} {U G : Nat}
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
    (hkeep : ∀ post (exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post)),
      PoolCallsKeep ⟨0, sevm, St pre [] Mem.empty G, .ok post, exc⟩ ∧
        ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4)
    (hWc : ∀ j, j ≤ 4 → WClosed sevm (W j)) (hWb : W 0 pre)
    (hsup : SupplyOkAt sevm (W 0) (W 0) ((pre.getStor sevm.currentTarget).get tokenSlot) T U
      0x27c 0x2c0)
    (hpull : ∀ k : Fin 3, k ≠ feeIndex → alAmt sevm k.val ≠ 0 →
      CoinPullOkAt sevm (W k) (W (k + 1)) ((pre.getStor sevm.currentTarget).get (coinSlot k))
        (alAmt sevm k.val) U 0x760 0x820)
    (hskip : ∀ k : Fin 3, alAmt sevm k.val = 0 → ∀ b, W k b → W (k + 1) b)
    (hfee : alAmt sevm 2 ≠ 0 →
      CoinBalOkAt sevm (W 2) (W 2) ((pre.getStor sevm.currentTarget).get (coinSlot 2)) B1 U
        0x53c 0x5a0 ∧
      CoinPullOkAt sevm (W 2) (W 3) ((pre.getStor sevm.currentTarget).get (coinSlot 2))
        (alAmt sevm 2) U 0x760 0x820 ∧
      CoinBalOkAt sevm (W 3) (W 3) ((pre.getStor sevm.currentTarget).get (coinSlot 2)) B2 U
        0x87c 0x8e0)
    (hmint : MintOkAt sevm (W 3) (W 4) ((pre.getStor sevm.currentTarget).get tokenSlot)
      (Nat.toB256 (alMintAmt o)) U 0xc7c 0xd00)
    (hG : costAddLiquidity s (alEnvW sevm T.toNat B1.toNat B2.toNat) (argV3 sevm 0) + 7 * U ≤ G)
    (hGm : (St pre [] Mem.empty G).gasMeasure + 3000 < 2 ^ 256) :
    ∃ post, ∃ exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post), ∃ e : Env,
      e.supply = some T.toNat ∧ step s e (decodeCall sevm) = some o ∧
      RawEffect ⟨0, sevm, St pre [] Mem.empty G, .ok post, exc⟩ post e o ∧
      Checkpoint (post.getStor sevm.currentTarget) o.state := by
  set σ := pre.getStor sevm.currentTarget with hσ
  have hG256 : G + 3000 < 2 ^ 256 := by
    have e : (St pre [] Mem.empty G).gasMeasure =
      G + pre.mach.stateGas.spilled + pre.mach.stateGas.committedSpill := rfl
    omega
  -- the model's step, inverted, as words
  obtain ⟨hv0, hal⟩ := al_body hlen hsel hstep
  have hval : sevm.value = 0 := B256.toNat_inj _ _ (by rw [show sevm.value.toNat = 0 from hv0]; rfl)
  obtain ⟨amp, v1, xb, mint, T', hk, hamp, hfeeN, hnew, hmf, t0, sub, a0, a1, a2, hxb, hD1, hmin,
    hT', hbr⟩ := al_words_common hck.abs hal
  have hkill : σ.get isKilledSlot = 0 := by rw [hck.abs.isKilled, hk]; rfl
  have hbal : s.balances = ⟨(balAt σ 0).toNat, (balAt σ 1).toNat, (balAt σ 2).toNat⟩ :=
    (V3.ext_get fun k => by rw [← ex_w3_nat]; exact ex_bal_nat hck.abs k).symm
  have hdec : decodeCall sevm = .addLiquidity (argV3 sevm 0) (arg sevm 3) :=
    decodeCall_at (k := 3) rfl hsel hlen
  rcases hbr with ⟨rfl, hpos, rfl, ho⟩ | ⟨hT0, D0, fees, stored, after, D2, x, y, hD0, hlt, hfl, hD2,
    hx, hy, hm, ho⟩
  · -- the first deposit
    obtain ⟨hlt1, hslip, hadd, rfl, hv1e⟩ := al_words0 hD1 hpos hmin hT'
    have hcost := al_cost0 hamp hnew hxb
    have hma : alMintAmt o = mint := by rw [ho]; exact alMintAmt_eq
    rw [hma] at hmint
    have hok := al_loopOk (σ := σ) (W := W) (T := 0) (U := U) t0
      (fun h => (t0 rfl).1 h.1) hWc hpull hskip hfee sub a0 a1 a2
    obtain ⟨r, hr, D, rfl, hDst, -⟩ := rx_al_frame0 (Wm := W 4) (G := G) hfork hstatic hdepth hlen
      hcd hsel hid (hWc 4 (by decide)) hWb hck.abs hck.unlocked hval hkill hamp hsup hmf hok hxb
      hD1 hlt1 hslip hadd hmint (by rw [hcost] at hG; omega) hG256
    obtain ⟨exc⟩ := lift_exactM cert_checkM cert_jumpsOkM hcode hfork ⟨t_0000_c0, rfl, hr⟩
    obtain ⟨c, L, hL, hcT⟩ := al_supplyChild hcode hfork hstatic hlen hcd hsel hid
      (hWc 0 (by decide)) hWb hck.abs
      hck.unlocked hval hkill hamp hmf hsup htok (by rw [hcost] at hG; omega) (by omega) exc
    obtain ⟨hkp, hidk⟩ := hkeep D exc
    obtain ⟨T₂, L0, L1, L2, o', hstep', hraw, c', L', hL', hc'⟩ := addLiquidity_rawE exc hcode
      hfork hlen hcd hsel rfl rfl (by omega) hck htok hcoin hpc
      (hid.of_rel ⟨fun _ => rfl, fun _ => rfl, rfl, rfl, rfl, rfl⟩) hkp hidk
    rw [hL] at hL'
    obtain ⟨rfl, -⟩ := List.cons.inj hL'
    obtain rfl : T₂ = 0 := hc'.symm.trans hcT
    obtain ⟨-, hal'⟩ := al_body hlen hsel hstep'
    have hoo : o' = o := by
      refine al_out_unique hal hal' rfl rfl rfl ?_ ?_
      · have hst := hraw.stor
        rw [hdec] at hst
        rw [al_bal_link hst, ho]
        obtain ⟨e0, e1, e2⟩ := al_end_bal σ (alLiveNew sevm (alOld σ) B1 B2 0)
          (alLiveNew sevm (alOld σ) B1 B2 1) (alLiveNew sevm (alOld σ) B1 B2 2)
        rw [hDst, hDst, hDst, e0, e1, e2]
      · obtain ⟨-, fee', amp', Tn, new', D1', mint', T'', -, -, hTn, -, -, -, -, -, hbr'⟩ :=
          addLiquidity_inv hal'
        obtain rfl : Tn = (0 : B256).toNat := (Option.some.inj hTn).symm
        rcases hbr' with ⟨-, -, -, ho'⟩ | ⟨h0, -⟩
        · rw [ho', ho]; rfl
        · exact absurd B256.toNat_zero h0
    subst hoo
    exact ⟨D, exc, _, rfl, hstep', hraw,
      (rawEffect_refines (D := ⟨0, sevm, St pre [] Mem.empty G, .ok D, exc⟩) hck hstep' hraw).1⟩
  · -- a positive supply
    obtain ⟨xa, xc, v0, v2, f0, f1, f2, s0, s1, s2, x0, x1, x2, hxa, hD0', hlt', i0, i1, i2, hxc, hD2',
      hge, hmul, hD00, hslip, hadd, rfl, rfl, rfl, rfl, rfl, hxc0⟩ :=
      al_words1 hck.abs hD1 hD0 hlt hfl hD2 hx hy hm hmin hT'
    have hfl' := hfl
    rw [hck.abs.adminFee] at hfl'
    have hcost := al_cost1 hT0 hamp hfeeN hnew hxb (by rw [hbal]; exact hxa) hD0' hD1 hfl' hxc0
    have hma : Nat.toB256 (alMintAmt o) = alMintW T (Nat.toB256 D0) (Nat.toB256 v2) := by
      rw [ho, alMintAmt_eq]; exact toB256_toNat _
    rw [hma] at hmint
    have hnz : ¬ (alAmt sevm 0 = 0 ∧ alAmt sevm 1 = 0 ∧ alAmt sevm 2 = 0) := by
      rintro ⟨z0, z1, z2⟩
      have hsame : alNewW sevm σ B1 B2 = s.balances := by
        obtain ⟨n0, n1, n2⟩ := al_liveNew_eq sevm σ B1 B2
        have c0 : alCrK sevm B1 B2 0 = 0 := z0
        have c1 : alCrK sevm B1 B2 1 = 0 := z1
        have c2 : alCrK sevm B1 B2 2 = 0 := by
          show (if alAmt sevm 2 = 0 then alAmt sevm 2 else B2 - B1) = 0
          rw [ite_eq_left_of_eq_true _ _ (eq_true z2), z2]
        rw [hbal]
        show (⟨(alLiveNew sevm (alOld σ) B1 B2 0).toNat, (alLiveNew sevm (alOld σ) B1 B2 1).toNat,
          (alLiveNew sevm (alOld σ) B1 B2 2).toNat⟩ : V3) = _
        rw [n0, n1, n2, c0, c1, c2, B256.add_zero, B256.add_zero, B256.add_zero]
      rw [hsame, hbal, hxa] at hxb
      obtain rfl := Option.some.inj hxb
      obtain rfl := Option.some.inj (hD0'.symm.trans hD1)
      exact Nat.lt_irrefl _ hlt
    have hok := al_loopOk (σ := σ) (W := W) (T := T) (U := U) t0 hnz hWc hpull hskip hfee sub a0
      a1 a2
    obtain ⟨r, hr, D, rfl, hDst, hDlog⟩ := rx_al_frame1 (Wm := W 4) (G := G) hfork hstatic hdepth
      hlen hcd hsel hid (hWc 4 (by decide)) hWb hck.abs hck.unlocked hval hkill hamp hsup hmf hT0
      hxa hD0' hok hxb hD1 hlt' i0 i1 i2 hxc hD2' hge hmul hD00 hslip hadd hmint
      (by rw [hcost] at hG; omega) hG256
    obtain ⟨exc⟩ := lift_exactM cert_checkM cert_jumpsOkM hcode hfork ⟨t_0000_c0, rfl, hr⟩
    obtain ⟨c, L, hL, hcT⟩ := al_supplyChild hcode hfork hstatic hlen hcd hsel hid
      (hWc 0 (by decide)) hWb hck.abs
      hck.unlocked hval hkill hamp hmf hsup htok (by rw [hcost] at hG; omega) (by omega) exc
    obtain ⟨hkp, hidk⟩ := hkeep D exc
    obtain ⟨T₂, L0, L1, L2, o', hstep', hraw, c', L', hL', hc'⟩ := addLiquidity_rawE exc hcode
      hfork hlen hcd hsel rfl rfl (by omega) hck htok hcoin hpc
      (hid.of_rel ⟨fun _ => rfl, fun _ => rfl, rfl, rfl, rfl, rfl⟩) hkp hidk
    rw [hL] at hL'
    obtain ⟨rfl, -⟩ := List.cons.inj hL'
    have hTT : T = T₂ := (hc'.symm.trans hcT).symm
    subst hTT
    obtain ⟨-, hal'⟩ := al_body hlen hsel hstep'
    have hoo : o' = o := by
      refine al_out_unique hal hal' rfl rfl rfl ?_ ?_
      · have hst := hraw.stor
        rw [hdec] at hst
        rw [al_bal_link hst, ho]
        obtain ⟨e0, e1, e2⟩ := al_end_bal σ s0 s1 s2
        rw [hDst, hDst, hDst, e0, e1, e2]
      · obtain ⟨-, fee', amp', Tn, new', D1', mint', T'', -, -, hTn, -, -, -, -, -, hbr'⟩ :=
          addLiquidity_inv hal'
        obtain rfl : Tn = T.toNat := (Option.some.inj hTn).symm
        rcases hbr' with ⟨h0, -⟩ | ⟨-, D0'', fees', stored', after', D2'', x', y', -, -, hfl'', -, -, -, -,
          ho'⟩
        · exact absurd h0 (toNat_ne_zero hT0)
        · obtain ⟨b0, b1, b2⟩ := al_feeLoop_lt hfl''
          obtain ⟨Lg, ts, data, hlogs, w0, w1, w2⟩ := hDlog
          have hlast := hraw.logs
          rw [ho', hlogs, List.map_cons, List.map_nil] at hlast
          have hev := congrArg List.getLast? hlast
          rw [List.getLast?_concat, List.getLast?_concat] at hev
          obtain ⟨g0, g1, g2⟩ := al_event_fees (Option.some.inj hev).symm
          rw [ho', ho]
          show fees' = _
          obtain ⟨u0, u1, u2⟩ := fees'
          have q0 : u0 = f0.toNat := by
            rw [w0.symm.trans g0]; exact (B256.toNat_toB256_of_lt b0).symm
          have q1 : u1 = f1.toNat := by
            rw [w1.symm.trans g1]; exact (B256.toNat_toB256_of_lt b1).symm
          have q2 : u2 = f2.toNat := by
            rw [w2.symm.trans g2]; exact (B256.toNat_toB256_of_lt b2).symm
          rw [q0, q1, q2]
          rfl
    subst hoo
    exact ⟨D, exc, _, rfl, hstep', hraw,
      (rawEffect_refines (D := ⟨0, sevm, St pre [] Mem.empty G, .ok D, exc⟩) hck hstep' hraw).1⟩

end Blanc.Lift.Curve3Pool
