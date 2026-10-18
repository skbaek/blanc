import Blanc.Lift.Curve3Pool.Check
import Blanc.Lift.Curve3Pool.Refine
import Blanc.Lift.Curve3Pool.Walk.OneCoinChecks
import Blanc.Lift.Curve3Pool.Walk.OneCoinLiveWords

/-!
# Liveness of `remove_liquidity_one_coin`

`removeLiquidityOneCoin_live`: at a `Checkpoint` (`s`), if the model's
`remove_liquidity_one_coin` succeeds in the environment `ocEnv sevm i T` (3Crv's `totalSupply()`
answers `T`, the burn and the push accepted) and the callees answer as `LivePremises` describes
— `totalSupply()` (`SupplyOkAt`, inside `_calc_withdraw_one_coin`), `burnFrom` (`BurnOkAt`) and
the output coin's `transfer` of the model's `dy` (`CoinPushOkAt`), each within `U` gas, over
world invariants `W` (before the burn) and `W'` (after it) — then every frame gas
`G ≥ costOneCoin … + 3 U` yields an actual successful execution of the pool's runtime whose
effect is the model's step: its `RawEffect` (in the environment the frame observed, which differs
from the premised one at most in the supply reply) and `Checkpoint post o.state`. `costOneCoin`
is a closed sufficient-gas bound, not the exact gas.

The route is `removeLiquidity_live`'s: the forward run `rx_oc_frame`, `lift_exactM`, the safety
result for that execution (`removeLiquidityOneCoin_rawE`), and the model step matched through the
event's `dy` and the stored balance of coin `i`.

`removeLiquidityOneCoin_none_of_push`: the control — a refused `transfer` makes the model's step
revert.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

/-- The amount `remove_liquidity_one_coin` pushes, read off the model's call list. -/
def ocPushAmt (o : Out) : Nat :=
  match o.calls with
  | [_, .push _ _ a] => a
  | _ => 0

theorem oc_decode {sevm : Sevm} (hlen : 4 ≤ sevm.data.length)
    (hsel : Sevm.selector sevm = selRemoveLiquidityOneCoin) :
    decodeCall sevm = .removeLiquidityOneCoin (ocAmt sevm).toNat (ocI sevm).toNat
      (ocMin sevm).toNat := by
  have hd := decodeCall_at (k := 10) rfl hsel hlen
  convert hd using 1; congr 1

/-- The model's `remove_liquidity_one_coin` from the step, at the frame's decoded arguments. -/
theorem oc_body {sevm : Sevm} {s : State} {e : Env} {o : Out} (hi3 : (ocI sevm).toNat < 3)
    (hlen : 4 ≤ sevm.data.length) (hsel : Sevm.selector sevm = selRemoveLiquidityOneCoin)
    (h : step s e (decodeCall sevm) = some o) :
    e.value = 0 ∧ removeLiquidityOneCoin s e (ocAmt sevm).toNat ⟨_, hi3⟩ (ocMin sevm).toNat =
      some o := by
  rw [oc_decode hlen hsel] at h
  have h' : (if e.value = 0 then body s e (.removeLiquidityOneCoin (ocAmt sevm).toNat
      (ocI sevm).toNat (ocMin sevm).toNat) else none) = some o := h
  split_ifs at h' with hv
  refine ⟨hv, ?_⟩
  simpa only [body, idx, hi3, ↓reduceDIte, Option.bind_eq_bind, Option.bind_some] using h'

/-- **The control**: a refused `transfer` of the output coin makes the model's
`remove_liquidity_one_coin` revert. -/
theorem removeLiquidityOneCoin_none_of_push {s : State} {e : Env} {amount : Nat} {i : Fin 3}
    {m : Nat} (hp : (e.coin i).pushOk = false) : removeLiquidityOneCoin s e amount i m = none := by
  cases h : removeLiquidityOneCoin s e amount i m with
  | none => rfl
  | some o =>
    obtain ⟨-, _, _, _, _, _, _, -, -, -, -, -, -, -, hq, -⟩ := removeLiquidityOneCoin_inv h
    rw [hq] at hp
    cases hp

/-- **`remove_liquidity_one_coin` is live** (see the module note). -/
theorem removeLiquidityOneCoin_live {sevm : Sevm} {pre : Devm} {s : State} {o : Out} {i : Fin 3}
    {T : B256} {W W' : Devm → Prop} {U G : Nat}
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
    (hkeep : ∀ post (exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post)),
      PoolCallsKeep ⟨0, sevm, St pre [] Mem.empty G, .ok post, exc⟩ ∧
        ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4)
    (hWc : WClosed sevm W) (hW'c : WClosed sevm W') (hWb : W pre)
    (hsup : SupplyOkAt sevm W W ((pre.getStor sevm.currentTarget).get tokenSlot) T U 0x2bc 0x300)
    (hburn : BurnOkAt sevm W W' ((pre.getStor sevm.currentTarget).get tokenSlot) (ocAmt sevm) U
      0x31c 0x3a0)
    (hpush : CoinPushOkAt sevm W' W' ((pre.getStor sevm.currentTarget).get (coinSlot i))
      (Nat.toB256 (ocPushAmt o)) U 0x540 0x5e0)
    (hG : costOneCoin s (ocEnv sevm i T.toNat) (ocAmt sevm).toNat i + 3 * U ≤ G)
    (hGm : (St pre [] Mem.empty G).gasMeasure + 2000 < 2 ^ 256) :
    ∃ post, ∃ exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post), ∃ T' : Nat,
      RawEffect ⟨0, sevm, St pre [] Mem.empty G, .ok post, exc⟩ post (ocEnv sevm i T') o ∧
        Checkpoint (post.getStor sevm.currentTarget) o.state := by
  have hG256 : G + 2000 < 2 ^ 256 := by
    have e : (St pre [] Mem.empty G).gasMeasure =
      G + pre.mach.stateGas.spilled + pre.mach.stateGas.committedSpill := rfl
    omega
  have hi3 : (ocI sevm).toNat < 3 := hi ▸ i.isLt
  obtain rfl : i = ⟨(ocI sevm).toNat, hi3⟩ := Fin.ext hi
  -- the model's step, inverted, as words
  obtain ⟨hv0, hrl⟩ := oc_body hi3 hlen hsel hstep
  have hval : sevm.value = 0 := B256.toNat_inj _ _ (by rw [show sevm.value.toNat = 0 from hv0]; rfl)
  obtain ⟨amp, x0, x1, x2, D0, y, r0, r1, r2, y2, hi3', hk, hA, hmf, hX, hD0, hm, hT0, hle, hy, hyl,
    h0, h1, h2, hy2, hs0, hs1, hs2, hmin, hma, hadd, hsub, ho, hcost⟩ := oc_words hck.abs rfl hrl
  have hci : coinSlot ⟨(ocI sevm).toNat, hi3⟩ = coinsBase + ocI sevm := by
    simp only [coinSlot, toB256_toNat]
  have hpa : ocPushAmt o = (cwDy (ocI sevm) r0 r1 r2 y2).toNat := by rw [ho]; rfl
  rw [hci, hpa, toB256_toNat] at hpush
  -- the forward run
  obtain ⟨r, hr, D, rfl, hL, L, ts, data, hlogs, hdata⟩ := rx_oc_frame (pre := pre) (s := s)
    (Q := fun r => ∃ D', r = .halted D' ∧ ExLive sevm W' D' _ ∧
      ∃ L ts data, D'.logs = L ++ [⟨sevm.currentTarget, ts, data⟩] ∧
        Bytes.toB256 (data.sliceD 0x20 32 0) = cwDy (ocI sevm) r0 r1 r2 y2)
    hfork hstatic hdepth hlen hcd hsel hid hWc hW'c hWb hck.abs hck.unlocked hval
    (by rw [hck.abs.isKilled, hk]; rfl) hi3 hA hsup hmf hX hD0 hm hT0 hle hy hyl h0 h1 h2 hy2 hs0
    hs1 hs2 hmin hma hadd hsub hburn hpush (by rw [hcost] at hG; omega) hG256
    (fun D' h hl => ⟨D', rfl, h, hl⟩)
  obtain ⟨exc⟩ := lift_exactM cert_checkM cert_jumpsOkM hcode hfork ⟨t_0000_c0, rfl, hr⟩
  -- the safety result for that execution
  obtain ⟨hkp, hidk⟩ := hkeep D exc
  obtain ⟨hi3'', T', o', hstep', hraw⟩ := removeLiquidityOneCoin_rawE exc hcode hfork hlen hcd hsel
    rfl rfl (by omega) hck htok hcoin hpc (hid.of_rel ⟨fun _ => rfl, fun _ => rfl, rfl, rfl, rfl, rfl⟩)
    hkp hidk
  obtain ⟨-, hrl'⟩ := oc_body hi3 hlen hsel hstep'
  obtain ⟨-, dy', fee', p', q', take', bi', -, -, -, -, htake', -, -, -, ho'⟩ :=
    removeLiquidityOneCoin_inv hrl'
  -- the event's `dy`
  have hlast := hraw.logs
  rw [hlogs, ho'] at hlast
  simp only [List.map_cons, List.map_nil] at hlast
  have hev := List.append_inj_right' hlast rfl
  simp only [List.cons.injEq, and_true] at hev
  have hdw := congrArg (fun l : Log => Bytes.toB256 (l.data.sliceD 0x20 32 0)) hev
  simp only [eventLog] at hdw
  have hsl : ∀ a b : Nat, (word a ++ word b).sliceD 32 32 0 = word b := fun a b => by
    have h1 : (word a).length = 32 := B256.length_toBytes _
    have h2 : (word b).length = 32 := B256.length_toBytes _
    have hg : (word a ++ word b).sliceD (word a).length (word b).length 0 = word b := by
      simp only [List.sliceD]
      rw [List.drop_left, List.takeD_eq_take _ (le_refl _), List.take_length]
    rwa [h1, h2] at hg
  rw [hdata, hsl, word, B256.toB256_toBytes] at hdw
  have hdy' : dy' < 2 ^ 256 := by
    have h1 := chkAdd_lt_of htake'
    rw [ex_chkAdd_eq htake'] at h1
    omega
  have hdyeq : dy' = (cwDy (ocI sevm) r0 r1 r2 y2).toNat := by
    rw [hdw, B256.toNat_toB256_of_lt hdy']
  -- the stored balance of coin `i`
  have hIw : ocI sevm = Nat.toB256 (ocI sevm).toNat := (toB256_toNat _).symm
  have hlk : Bytes.toB256 [0xff, 0xff, 0xff] ≠ balancesBase + ocI sevm := by
    rw [lockSlot_lit, hIw]; exact bal_ne_lock hi3
  have hla : Bytes.toB256 [0xff, 0xff, 0xff] ≠ adminFeeSlot := by decide
  have hbI : balanceSlot ⟨(ocI sevm).toNat, hi3⟩ = balancesBase + ocI sevm := by
    rw [balanceSlot]; exact congrArg _ (toB256_toNat _)
  have hw : ((D.getStor sevm.currentTarget).get (balancesBase + ocI sevm)).toNat =
      o'.state.balances.get ⟨(ocI sevm).toNat, hi3⟩ := by
    rw [← hbI]
    exact hraw.stor.written (.bal ⟨(ocI sevm).toNat, hi3⟩)
      (show Fld.bal _ ∈ footprint (decodeCall sevm) by rw [oc_decode hlen hsel]; exact bal_mem _)
  rw [hL.stor, Stor.get_set_ne _ hlk _, Stor.get_set_self, ho'] at hw
  simp only [ocBal] at hw
  rw [Stor.get_set_ne _ hlk _, Stor.get_set_ne _ hla _, V3.get_set_self] at hw
  have hoo : o' = o := by
    rw [ho', ho, hdyeq, ← hw]
    rfl
  subst hoo
  refine ⟨D, exc, T', hraw, ?_⟩
  exact (rawEffect_refines (D := ⟨0, sevm, St pre [] Mem.empty G, .ok D, exc⟩) hck hstep' hraw).1

end Blanc.Lift.Curve3Pool
