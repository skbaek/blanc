import Blanc.Lift.Curve3Pool.Check
import Blanc.Lift.Curve3Pool.Refine
import Blanc.Lift.Curve3Pool.Walk.ExchangeLiveFrame
import Blanc.Lift.Curve3Pool.Walk.ExchangeLiveWords

/-!
# Liveness of `exchange`

`exchange_live`: at a `Checkpoint` (`s`), if the model's `exchange` succeeds in the environment
`exEnv sevm i j (exBalOpt i B1) (exBalOpt i B2)` (the fee coin's `balanceOf(self)` answers `B1`,
`B2`; every call accepted) and the callees answer as `LivePremises` describes — the input coin's
`transferFrom` (`CoinPullOkAt`), for `i == FEE_INDEX` its two `balanceOf(self)` reads
(`CoinBalOkAt`), the output coin's `transfer` of the model's amount (`CoinPushOkAt`), each using
at most `U` gas, over world invariants `W` (before the pull), `W'` (after it) and `W''` (after the
push; the push is the last call, so `W''` need not support another push — a `W'` closed under a
transfer of a positive amount out of the pool would admit no honest token) — then every frame
gas `G ≥ costExchange … + 4 U` yields an actual successful execution of the pool's runtime whose
effect is the model's step: the `RawEffect` (in an environment differing from the premised one at
most in the fee coin's two individual answers, whose difference is the same) and `Checkpoint post
o.state`. `costExchange` is a closed sufficient-gas bound, not the exact gas: gas after a call
depends on the callee.

The route is `removeLiquidity_live`'s: the forward run `rx_ex_frame`, `lift_exactM`, the safety
theorem on that execution (`exchange_rawE`, `exchange_raw` with the observed environment exposed),
and the model step matched through the stored balance of coin `i`.

`exchange_none_of_push`: the control — a refused `transfer` makes the model's step revert.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

/-- `exchange` reads its environment only through the time, the caller, the credited amount and
the output coin's push. -/
theorem exchange_congr {s : State} {e e' : Env} {i j : Fin 3} {dx m : Nat}
    (ht : e.time = e'.time) (hc : e.caller = e'.caller) (hp : pullIn e i dx = pullIn e' i dx)
    (hq : (e.coin j).pushOk = (e'.coin j).pushOk) :
    exchange s e i j dx m = exchange s e' i j dx m := by
  unfold exchange
  rw [ht, hc, hp, hq]

/-- **The control**: a refused `transfer` of the output coin makes the model's `exchange`
revert. -/
theorem exchange_none_of_push {s : State} {e : Env} {i j : Fin 3} {dx m : Nat}
    (hj : (e.coin j).pushOk = false) : exchange s e i j dx m = none := by
  cases h : exchange s e i j dx m with
  | none => rfl
  | some o =>
    obtain ⟨-, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, -, -, -, -, -, -,
      -, -,
      -, -, -, -, -, -, -, -, -, -, -, -, -, -, hp, -⟩ := exchange_inv h
    rw [hp] at hj
    cases hj

theorem ex_decode {sevm : Sevm} (hlen : 4 ≤ sevm.data.length)
    (hsel : Sevm.selector sevm = selExchange) :
    decodeCall sevm =
      .exchange (exI sevm).toNat (exJ sevm).toNat (exDx sevm).toNat (exMinDy sevm).toNat := by
  have hd := decodeCall_at (k := 6) rfl hsel hlen
  convert hd using 1; congr 1

/-- The model's `exchange` from the step, at the frame's decoded arguments. -/
theorem ex_body {sevm : Sevm} {s : State} {e : Env} {o : Out} (hi3 : (exI sevm).toNat < 3)
    (hj3 : (exJ sevm).toNat < 3) (hlen : 4 ≤ sevm.data.length)
    (hsel : Sevm.selector sevm = selExchange)
    (h : step s e (decodeCall sevm) = some o) :
    e.value = 0 ∧
      exchange s e ⟨_, hi3⟩ ⟨_, hj3⟩ (exDx sevm).toNat (exMinDy sevm).toNat = some o := by
  rw [ex_decode hlen hsel] at h
  have h' : (if e.value = 0 then body s e (.exchange (exI sevm).toNat (exJ sevm).toNat
      (exDx sevm).toNat (exMinDy sevm).toNat) else none) = some o := h
  split_ifs at h' with hv
  refine ⟨hv, ?_⟩
  simpa only [body, idx, hi3, hj3, ↓reduceDIte, Option.bind_eq_bind, Option.bind_some] using h'

/-- **`exchange` is live** (see the module note). -/
theorem exchange_live {sevm : Sevm} {pre : Devm} {s : State} {o : Out} {i j : Fin 3} {B1 B2 : B256}
    {W W' W'' : Devm → Prop} {U G : Nat}
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hstatic : sevm.isStatic = false) (hdepth : sevm.depth ≠ 0)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selExchange)
    (hi : i.val = (exI sevm).toNat) (hj : j.val = (exJ sevm).toNat)
    (hck : Checkpoint (pre.getStor sevm.currentTarget) s)
    (hstep : step s (exEnv sevm i j (exBalOpt i B1) (exBalOpt i B2)) (decodeCall sevm) = some o)
    (hcoin : ∀ k : Fin 3,
      ¬ sevm.benvStat.rules.isPrecomp ((pre.getStor sevm.currentTarget).get (coinSlot k)).toAdr)
    (hpc : pre.getCode sevm.currentTarget ≠ .empty) (hid : IdReady sevm pre)
    (hkeep : ∀ post (exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post)),
      PoolCallsKeep ⟨0, sevm, St pre [] Mem.empty G, .ok post, exc⟩ ∧
        ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4)
    (hWc : WClosed sevm W) (hW'c : WClosed sevm W') (hWb : W pre)
    (hbal : i = feeIndex →
      CoinBalOkAt sevm W W ((pre.getStor sevm.currentTarget).get (coinSlot i)) B1 U 0x3dc 0x440 ∧
      CoinBalOkAt sevm W' W' ((pre.getStor sevm.currentTarget).get (coinSlot i)) B2 U 0x71c 0x780)
    (hpull : CoinPullOkAt sevm W W' ((pre.getStor sevm.currentTarget).get (coinSlot i))
      (exDx sevm) U 0x600 0x6c0)
    (hW''c : WClosed sevm W'')
    (hpush : CoinPushOkAt sevm W' W'' ((pre.getStor sevm.currentTarget).get (coinSlot j))
      (Nat.toB256 (exPushAmt o)) U 0xb60 0xc00)
    (hG : costExchange sevm pre s (exEnv sevm i j (exBalOpt i B1) (exBalOpt i B2)) i j
      (exDx sevm).toNat + 4 * U ≤ G)
    (hGm : (St pre [] Mem.empty G).gasMeasure < 2 ^ 256) :
    ∃ post, ∃ exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post), ∃ bp bq,
      pullIn (exEnv sevm i j bp bq) i (exDx sevm).toNat =
        pullIn (exEnv sevm i j (exBalOpt i B1) (exBalOpt i B2)) i (exDx sevm).toNat ∧
      RawEffect ⟨0, sevm, St pre [] Mem.empty G, .ok post, exc⟩ post (exEnv sevm i j bp bq) o ∧
        Checkpoint (post.getStor sevm.currentTarget) o.state := by
  have hG256 : G < 2 ^ 256 := by
    have e : (St pre [] Mem.empty G).gasMeasure =
      G + pre.mach.stateGas.spilled + pre.mach.stateGas.committedSpill := rfl
    omega
  have hi3 : (exI sevm).toNat < 3 := hi ▸ i.isLt
  have hj3 : (exJ sevm).toNat < 3 := hj ▸ j.isLt
  obtain rfl : i = ⟨(exI sevm).toNat, hi3⟩ := Fin.ext hi
  obtain rfl : j = ⟨(exJ sevm).toNat, hj3⟩ := Fin.ext hj
  -- the model's step, inverted, as words
  obtain ⟨hv0, hex⟩ := ex_body hi3 hj3 hlen hsel hstep
  have hval : sevm.value = 0 := B256.toNat_inj _ _ (by rw [show sevm.value.toNat = 0 from hv0]; rfl)
  obtain ⟨x0, x1, x2, amp, v, hi3', hj3', hk, hX, hsub, hmx, hax, hA, hres, hy1, hy2, hmf, hsf, hmo,
    hmin,
    hma, hmap, hbi, hbj1, hbj2, hpa, hij, hob, hpin, hcost⟩ := ex_words hck.abs rfl rfl hex
  have hne : (exI sevm).toNat ≠ (exJ sevm).toNat := fun h => hij (Fin.ext h)
  have hci : coinSlot ⟨(exI sevm).toNat, hi3⟩ = coinsBase + exI sevm := by
    simp only [coinSlot, toB256_toNat]
  have hcj : coinSlot ⟨(exJ sevm).toNat, hj3⟩ = coinsBase + exJ sevm := by
    simp only [coinSlot, toB256_toNat]
  rw [hci] at hpull hbal
  rw [hcj, hpa, toB256_toNat] at hpush
  have hcy := hcost pre
  -- the forward run
  obtain ⟨r, hr, D, rfl, hL⟩ := rx_ex_frame (pre := pre) (s0 := s) (B1 := B1) (B2 := B2)
    (Q := fun r => ∃ D', r = .halted D' ∧ ExLive sevm W'' D'
      (exFinal ((pre.getStor sevm.currentTarget).set lockSlot 1) sevm
        (exBal (pre.getStor sevm.currentTarget) ⟨(exI sevm).toNat, hi3⟩ + exCred sevm B1 B2) _))
    hfork hstatic hdepth hlen hcd hsel hid hWc hW'c hWb hck.abs hck.unlocked hval
    (by rw [hck.abs.isKilled, hk]; rfl) hi3 hj3 hX
    (fun h2 => ⟨(hbal (Fin.ext (show (exI sevm).toNat = 2 by rw [h2]; rfl))).1,
      (hbal (Fin.ext (show (exI sevm).toNat = 2 by rw [h2]; rfl))).2, hsub h2⟩)
    hpull hmx hax hA hres hy1 hy2 hmf hsf hmo hmin hma hmap hbi hbj1 hbj2 hW''c hpush (by omega) hG256
    (fun D' h => ⟨D', rfl, h⟩)
  obtain ⟨exc⟩ := lift_exactM cert_checkM cert_jumpsOkM hcode hfork ⟨t_0000_c0, rfl, hr⟩
  -- the safety theorem on that execution
  obtain ⟨hkp, hidk⟩ := hkeep D exc
  obtain ⟨hi3'', hj3'', bp, bq, o', hstep', hraw⟩ :=
    exchange_rawE exc hcode hfork hlen hcd hsel rfl rfl hGm
    hck hcoin hpc (hid.of_rel ⟨fun _ => rfl, fun _ => rfl, rfl, rfl, rfl, rfl⟩) hkp hidk
  obtain ⟨-, hex'⟩ := ex_body hi3 hj3 hlen hsel hstep'
  -- the stored balance of coin `i` pins the credited amount
  have hbI : balancesBase + exI sevm = balancesBase + Nat.toB256 (exI sevm).toNat := by
    rw [toB256_toNat]
  have hbJ : balancesBase + exJ sevm = balancesBase + Nat.toB256 (exJ sevm).toNat := by
    rw [toB256_toNat]
  have hsI : (D.getStor sevm.currentTarget).get (balancesBase + exI sevm) =
      exBal (pre.getStor sevm.currentTarget) ⟨(exI sevm).toNat, hi3⟩ + exCred sevm B1 B2 := by
    rw [hL.stor]
    exact (Stor.get_set_ne _ (by rw [hbI]; exact bal_ne_lock hi3) _).trans
      ((Stor.get_set_ne _ (by rw [hbI, hbJ]; exact bal_ne_bal hj3 hi3 (Ne.symm hne)) _).trans
        (Stor.get_set_self _ _ _))
  have hw : ((D.getStor sevm.currentTarget).get (balancesBase + exI sevm)).toNat =
      o'.state.balances.get ⟨(exI sevm).toNat, hi3⟩ := by
    rw [hbI]
    exact hraw.stor.written (.bal ⟨(exI sevm).toNat, hi3⟩)
      (show Fld.bal _ ∈ footprint (decodeCall sevm) by
        rw [ex_decode hlen hsel]; exact bal_mem _)
  rw [hsI, ← hob] at hw
  obtain ⟨-, _, Dm, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, bi, _, _,
    -, hDm, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hbim, -, -, -, ho⟩ :=
    exchange_inv hex
  obtain ⟨-, _, Dm', _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, bi', _, _,
    -, hDm', -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hbim', -, -, -, ho'⟩ :=
    exchange_inv hex'
  have hgi : ∀ (v : V3) (a b : Nat), ((v.set ⟨(exI sevm).toNat, hi3⟩ a).set
      ⟨(exJ sevm).toNat, hj3⟩ b).get ⟨(exI sevm).toNat, hi3⟩ = a := fun v a b =>
    (V3.get_set_ne _ hij _).trans (V3.get_set_self _ _ _)
  have h0 : o.state.balances.get ⟨(exI sevm).toNat, hi3⟩ = bi := by rw [ho]; exact hgi _ _ _
  have h1 : o'.state.balances.get ⟨(exI sevm).toNat, hi3⟩ = bi' := by rw [ho']; exact hgi _ _ _
  have hb0 := ex_chkAdd_eq hbim
  have hb1 := ex_chkAdd_eq hbim'
  clear ho ho'
  have hpeq : pullIn (exEnv sevm ⟨_, hi3⟩ ⟨_, hj3⟩ bp bq) ⟨_, hi3⟩ (exDx sevm).toNat =
      pullIn (exEnv sevm ⟨_, hi3⟩ ⟨_, hj3⟩ (exBalOpt ⟨_, hi3⟩ B1) (exBalOpt ⟨_, hi3⟩ B2))
        ⟨_, hi3⟩ (exDx sevm).toNat := by
    rw [hDm, hDm']; congr 1; omega
  rw [exchange_congr (e := exEnv sevm ⟨_, hi3⟩ ⟨_, hj3⟩ bp bq) 
    (e' := exEnv sevm ⟨_, hi3⟩ ⟨_, hj3⟩ (exBalOpt ⟨_, hi3⟩ B1)
    (exBalOpt ⟨_, hi3⟩ B2)) rfl rfl hpeq rfl, hex] at hex'
  cases Option.some.inj hex'
  refine ⟨D, exc, bp, bq, hpeq, hraw, ?_⟩
  exact (rawEffect_refines (D := ⟨0, sevm, St pre [] Mem.empty G, .ok D, exc⟩) hck hstep' hraw).1

end Blanc.Lift.Curve3Pool
