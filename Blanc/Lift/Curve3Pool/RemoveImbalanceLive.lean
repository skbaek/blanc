import Blanc.Lift.Curve3Pool.Check
import Blanc.Lift.Curve3Pool.Refine
import Blanc.Lift.Curve3Pool.Walk.RemoveImbalanceRawChecks
import Blanc.Lift.Curve3Pool.Walk.RliLiveWords
import Blanc.Lift.Curve3Pool.Walk.RliLiveCut
import Blanc.Lift.Curve3Pool.Walk.LiveLink

/-!
# Liveness of `remove_liquidity_imbalance`

`removeLiquidityImbalance_live`: at a `Checkpoint` (`s`), if the model's
`remove_liquidity_imbalance` succeeds in the environment `rliEnvW sevm T` (3Crv's `totalSupply()`
answers `T`; the burn and each nonzero transfer accepted) and the callees answer as
`LivePremises` describes — `totalSupply()` (`SupplyOkAt`, window `0x17c`/`0x1c0`), `burnFrom` of
the model's burn amount (`BurnOkAt`, `0x85c`/`0x8e0`) and `transfer` of each nonzero amount
(`CoinPushOkAt`, `0xaa0`/`0xb40`), each within `U` gas, over world invariants `W` (before the burn)
and `W'` (after it) — then every frame gas `G ≥ costImbalance … + 5 U` yields an actual successful
execution of the pool's runtime whose effect is the model's step at `o`: its `RawEffect` in
`rliEnvW sevm T`, and `Checkpoint post o.state`. `costImbalance` is a closed sufficient-gas bound,
not the exact gas.

The supply reply the safety theorem observes is `T`: the produced execution's first direct child
is the `totalSupply()` call the forward run made (`rx_rli_toSupply`, the cut walk
`xa_cutAt_start`, `xa_staticWordOkAt`), whose reply the premise fixes.

`removeLiquidityImbalance_none_of_push`: the control — a refused `transfer` of a nonzero amount
makes the model's step revert.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

/-- The amount `remove_liquidity_imbalance` burns, read off the model's call list. -/
def rliBurnAmt (o : Out) : Nat :=
  match o.calls with
  | .burn _ a :: _ => a
  | _ => 0

/-- The model's `remove_liquidity_imbalance` from the step, at the frame's decoded arguments. -/
theorem rli_body {sevm : Sevm} {s : State} {e : Env} {o : Out} (hlen : 4 ≤ sevm.data.length)
    (hsel : Sevm.selector sevm = selRemoveLiquidityImbalance)
    (h : step s e (decodeCall sevm) = some o) :
    e.value = 0 ∧ removeLiquidityImbalance s e (argV3 sevm 0) (arg sevm 3) = some o := by
  rw [rli_decode hsel hlen] at h
  have h' : (if e.value = 0 then body s e (.removeLiquidityImbalance (argV3 sevm 0) (arg sevm 3))
      else none) = some o := h
  split_ifs at h' with hv
  exact ⟨hv, h'⟩

/-- **The control**: a refused `transfer` of a nonzero amount makes the model's
`remove_liquidity_imbalance` revert. -/
theorem removeLiquidityImbalance_none_of_push {s : State} {e : Env} {amounts : V3} {m : Nat}
    {k : Fin 3} (hk : amounts.get k ≠ 0) (hp : (e.coin k).pushOk = false) :
    removeLiquidityImbalance s e amounts m = none := by
  cases h : removeLiquidityImbalance s e amounts m with
  | none => rfl
  | some o =>
    obtain ⟨-, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, -, -, -, -, -, -, -, -, -, -, -, -, -,
      -, -, -, ⟨p0, p1, p2⟩, -, -⟩ := removeLiquidityImbalance_inv h
    match k with
    | 0 => rw [p0 hk] at hp; cases hp
    | 1 => rw [p1 hk] at hp; cases hp
    | 2 => rw [p2 hk] at hp; cases hp

/-- **`remove_liquidity_imbalance` is live** (see the module note). -/
theorem removeLiquidityImbalance_live {sevm : Sevm} {pre : Devm} {s : State} {o : Out} {T : B256}
    {W W' : Devm → Prop} {U G : Nat}
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
    (hkeep : ∀ post (exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post)),
      PoolCallsKeep ⟨0, sevm, St pre [] Mem.empty G, .ok post, exc⟩ ∧
        ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4)
    (hWc : WClosed sevm W) (hW'c : WClosed sevm W') (hWb : W pre)
    (hsup : SupplyOkAt sevm W W ((pre.getStor sevm.currentTarget).get tokenSlot) T U 0x17c 0x1c0)
    (hburn : BurnOkAt sevm W W' ((pre.getStor sevm.currentTarget).get tokenSlot)
      (Nat.toB256 (rliBurnAmt o)) U 0x85c 0x8e0)
    (hpush : ∀ k : Fin 3, rliAmt sevm k.val ≠ 0 → CoinPushOkAt sevm W' W'
      ((pre.getStor sevm.currentTarget).get (coinSlot k)) (rliAmt sevm k.val) U 0xaa0 0xb40)
    (hG : costImbalance s (rliEnvW sevm T.toNat) (argV3 sevm 0) + 5 * U ≤ G)
    (hGm : (St pre [] Mem.empty G).gasMeasure + 3000 < 2 ^ 256) :
    ∃ post, ∃ exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post),
      RawEffect ⟨0, sevm, St pre [] Mem.empty G, .ok post, exc⟩ post (rliEnvW sevm T.toNat) o ∧
      Checkpoint (post.getStor sevm.currentTarget) o.state := by
  have hG256 : G + 3000 < 2 ^ 256 := by
    have e : (St pre [] Mem.empty G).gasMeasure =
      G + pre.mach.stateGas.spilled + pre.mach.stateGas.committedSpill := rfl
    omega
  -- the model's step, inverted, as words
  obtain ⟨hv0, hrl⟩ := rli_body hlen hsel hstep
  have hval : sevm.value = 0 := B256.toNat_inj _ _ (by rw [show sevm.value.toNat = 0 from hv0]; rfl)
  obtain ⟨amp, v0, v1, v2, xa, xb, xc, f0, f1, f2, s0, s1, s2, x0, x1, x2, hk, hA, hmf, hT0, hX0,
    hD0, hu0, hu1, hu2, hX1, hD1, h0, h1, h2, hX2, hD2, hD02, hmT, hbn, hb1, hslip, hTX, ho,
    hcost⟩ := rli_words hck.abs hrl
  have hba : rliBurnAmt o = (rliBurnW (Nat.toB256 v0) (Nat.toB256 v2) T).toNat := by rw [ho]; rfl
  rw [hba, toB256_toNat] at hburn
  have hkill : (pre.getStor sevm.currentTarget).get isKilledSlot = 0 := by
    rw [hck.abs.isKilled, hk]; rfl
  -- the forward run
  obtain ⟨r, hr, D, rfl, -⟩ := rx_rli_frame (pre := pre) (s := s)
    (Q := fun r => ∃ D', r = .halted D' ∧ ExLive sevm W' D' _)
    hfork hstatic hdepth hlen hcd hsel hid hWc hW'c hWb hck.abs hck.unlocked hval
    hkill hA hsup hT0 hmf hX0 hD0 hu0 hu1 hu2 hX1 hD1 h0 h1 h2 hX2 hD2
    hD02 hmT hbn hb1 hslip hTX hburn (hpush 0) (hpush 1) (hpush 2)
    (by rw [hcost] at hG; omega) hG256 (fun D' h _ => ⟨D', rfl, h⟩)
  obtain ⟨exc⟩ := lift_exactM cert_checkM cert_jumpsOkM hcode hfork ⟨t_0000_c0, rfl, hr⟩
  -- the frame's first child is the supply call the forward run made: it answered `T`
  obtain ⟨r1, hr1, b1, S1, M1, g1, rfl, hW1, hU1, hg1, hin1, hS1⟩ := rx_rli_toSupply (pre := pre)
    (U := U) (G := G) hfork hstatic hlen hcd hsel hid hWc hWb hck.unlocked hval hkill
    (by rw [hcost] at hG; omega) (by omega)
  have hx : XAt sevm D 0 (St pre [] Mem.empty G) (Exec.childFrames exc) :=
    XAt.of_exec exc (by omega)
  obtain ⟨m1, pc1, a1, μ1, hw1⟩ := xa_cutAt_start checkedM
    (Cert.jumpsOkM_of_jumpsOkM cert_jumpsOkM) hcode hfork (E := []) rfl rfl rfl rfl rfl rfl rfl
    (SFunc.cutCall_of_cutPathOk _ _ rliSupplyPath_ok) hr1 hx
  have hx1 := hw1.xat
  have hchk1 := hw1.check
  obtain ⟨X, hX⟩ : ∃ X, SFunc.subAt cert.prog rliSupplyPath t_0000_c0 =
      .next (.exec .staticcall) X := ⟨_, rfl⟩
  rw [hX] at hchk1
  obtain ⟨c, L', hL, -, -, -, hcT⟩ := xa_staticWordOkAt hfork (checkNodeM_next_at hcode hchk1) hx1
    hsup hW1 hU1 hg1 hin1 htok hS1
  -- the safety result for that execution
  obtain ⟨hkp, hidk⟩ := hkeep D exc
  obtain ⟨T', o', hstep', hraw, c', L'', hL', hc'⟩ := removeLiquidityImbalance_rawE exc hcode hfork
    hlen hcd hsel rfl rfl (by omega) hck htok hcoin hpc
    (hid.of_rel ⟨fun _ => rfl, fun _ => rfl, rfl, rfl, rfl, rfl⟩) hkp hidk
  rw [hL] at hL'
  obtain ⟨rfl, -⟩ := List.cons.inj hL'
  have hTT : T' = T := hc'.symm.trans hcT
  subst hTT
  have hoo : o' = o := Option.some.inj (hstep'.symm.trans hstep)
  subst hoo
  refine ⟨D, exc, hraw, ?_⟩
  exact (rawEffect_refines (D := ⟨0, sevm, St pre [] Mem.empty G, .ok D, exc⟩) hck hstep' hraw).1

end Blanc.Lift.Curve3Pool
