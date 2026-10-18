import Blanc.Lift.Curve3Pool.Check
import Blanc.Lift.Curve3Pool.Refine
import Blanc.Lift.Curve3Pool.Walk.RemoveImbalanceRawChecks
import Blanc.Lift.Curve3Pool.Walk.RliLiveWords

/-!
# Liveness of `remove_liquidity_imbalance`

`removeLiquidityImbalance_live`: at a `Checkpoint` (`s`), if the model's
`remove_liquidity_imbalance` succeeds in the environment `rliEnvW sevm T` (3Crv's `totalSupply()`
answers `T`; the burn and each nonzero transfer accepted) and the callees answer as
`LivePremises` describes — `totalSupply()` (`SupplyOkAt`, window `0x17c`/`0x1c0`), `burnFrom` of
the model's burn amount (`BurnOkAt`, `0x85c`/`0x8e0`) and `transfer` of each nonzero amount
(`CoinPushOkAt`, `0xaa0`/`0xb40`), each within `U` gas, over world invariants `W` (before the burn)
and `W'` (after it) — then every frame gas `G ≥ costImbalance … + 5 U` yields an actual successful
execution of the pool's runtime whose effect is the model's step: its `RawEffect` in the
environment the frame observed, at the model's output `o'` there, and `Checkpoint post o.state`.
`costImbalance` is a closed sufficient-gas bound, not the exact gas.

The observed environment can differ from the premised one only in the supply reply, and then
`o'` differs from `o` at most in the burned amount and the logged new supply: the stored
balances, the fees, the invariant and the transfers agree (`rli_det`), and the logged new supply
is the one the run logged. (The burned amount is not logged, and `T - ((D0 - D2) T / D0 + 1)` is
not injective in `T`, so the event does not pin the supply reply.)

`removeLiquidityImbalance_none_of_push`: the control — a refused `transfer` of a nonzero amount
makes the model's step revert.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

theorem rliEnvW_time (sevm : Sevm) (T : Nat) : (rliEnvW sevm T).time = sevm.benvStat.time.toNat :=
  rfl

theorem rliEnvW_caller (sevm : Sevm) (T : Nat) :
    (rliEnvW sevm T).caller = sevm.caller.toB256.toNat := rfl

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

/-- The last data word of an imbalance event: the new supply. -/
theorem rli_event_supply (a f : V3) (D t : Nat) :
    Bytes.toB256 ((wordsV3 a ++ wordsV3 f ++ word D ++ word t).sliceD 0xe0 32 0) = Nat.toB256 t := by
  have hl : (wordsV3 a ++ wordsV3 f ++ word D).length = 0xe0 := by
    simp only [wordsV3, word, List.length_append, B256.length_toBytes]
  have h2 : (word t).length = 32 := B256.length_toBytes _
  have hg : (wordsV3 a ++ wordsV3 f ++ word D ++ word t).sliceD
      (wordsV3 a ++ wordsV3 f ++ word D).length (word t).length 0 = word t := by
    simp only [List.sliceD]
    rw [List.drop_left, List.takeD_eq_take _ (le_refl _), List.take_length]
  rw [hl, h2] at hg
  rw [hg, word, B256.toB256_toBytes]

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
    ∃ post, ∃ exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post), ∃ (T' : B256) (o' : Out),
      step s (rliEnvW sevm T'.toNat) (decodeCall sevm) = some o' ∧
      RawEffect ⟨0, sevm, St pre [] Mem.empty G, .ok post, exc⟩ post (rliEnvW sevm T'.toNat) o' ∧
      o'.state = o.state ∧ o'.events = o.events ∧ o'.ret = o.ret ∧ o'.calls.tail = o.calls.tail ∧
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
  -- the forward run
  obtain ⟨r, hr, D, rfl, hL, L, ts, data, hlogs, -, -, -, -, hdata⟩ := rx_rli_frame (pre := pre)
    (s := s)
    (Q := fun r => ∃ D', r = .halted D' ∧ ExLive sevm W' D' _ ∧
      ∃ L ts data, D'.logs = L ++ [⟨sevm.currentTarget, ts, data⟩] ∧
        Bytes.toB256 (data.sliceD 0x60 32 0) = f0 ∧ Bytes.toB256 (data.sliceD 0x80 32 0) = f1 ∧
        Bytes.toB256 (data.sliceD 0xa0 32 0) = f2 ∧
        Bytes.toB256 (data.sliceD 0xc0 32 0) = Nat.toB256 v1 ∧
        Bytes.toB256 (data.sliceD 0xe0 32 0) = T - rliBurnW (Nat.toB256 v0) (Nat.toB256 v2) T)
    hfork hstatic hdepth hlen hcd hsel hid hWc hW'c hWb hck.abs hck.unlocked hval
    (by rw [hck.abs.isKilled, hk]; rfl) hA hsup hT0 hmf hX0 hD0 hu0 hu1 hu2 hX1 hD1 h0 h1 h2 hX2 hD2
    hD02 hmT hbn hb1 hslip hTX hburn (hpush 0) (hpush 1) (hpush 2)
    (by rw [hcost] at hG; omega) hG256 (fun D' h hl => ⟨D', rfl, h, hl⟩)
  obtain ⟨exc⟩ := lift_exactM cert_checkM cert_jumpsOkM hcode hfork ⟨t_0000_c0, rfl, hr⟩
  -- the safety result for that execution
  obtain ⟨hkp, hidk⟩ := hkeep D exc
  obtain ⟨T', o', hstep', hraw⟩ := removeLiquidityImbalance_rawE exc hcode hfork hlen hcd hsel
    rfl rfl (by omega) hck htok hcoin hpc (hid.of_rel ⟨fun _ => rfl, fun _ => rfl, rfl, rfl, rfl, rfl⟩)
    hkp hidk
  obtain ⟨-, hrl'⟩ := rli_body hlen hsel hstep'
  have hdet := rli_det (e := rliEnvW sevm T.toNat) (e' := rliEnvW sevm T'.toNat)
    (amounts := argV3 sevm 0) (mx := arg sevm 3) (o := o) (o' := o') (s := s)
    (by rw [rliEnvW_time, rliEnvW_time]) (by rw [rliEnvW_caller, rliEnvW_caller]) hrl hrl'
  obtain ⟨hst, hret, hcalls, fees, D1, T1, T2, he, he'⟩ := hdet
  -- the logged new supply
  have hlast := hraw.logs
  rw [hlogs, he'] at hlast
  simp only [List.map_cons, List.map_nil] at hlast
  have hev := List.append_inj_right' hlast rfl
  simp only [List.cons.injEq, and_true] at hev
  have hdw := congrArg (fun l : Log => Bytes.toB256 (l.data.sliceD 0xe0 32 0)) hev
  simp only [eventLog] at hdw
  rw [hdata, rli_event_supply] at hdw
  obtain ⟨-, Ts, _, _, _, _, _, _, _, _, _, _, _, _, b', Tx, hTs, -, -, -, -, -, -, -, -, -, -, -, -,
    -, -, -, -, hTx, ho'⟩ := removeLiquidityImbalance_inv hrl'
  have hTs' : Ts = T'.toNat := (Option.some.inj hTs).symm
  subst hTs'
  have hTxl : Tx < 2 ^ 256 := by
    have := chkSub_eq' hTx
    have := B256.toNat_lt T'
    omega
  have e2 := congrArg Out.events ho'
  rw [he'] at e2
  simp only [List.cons.injEq, and_true] at e2
  obtain ⟨-, -, -, -, hT2x⟩ := Event.removeLiquidityImbalance.inj e2
  have e1 : o.events = [.removeLiquidityImbalance sevm.caller.toB256.toNat (argV3 sevm 0) fees D1
      (T - rliBurnW (Nat.toB256 v0) (Nat.toB256 v2) T).toNat] := by
    rw [he]
    have e1' := congrArg Out.events ho
    rw [he] at e1'
    simp only [List.cons.injEq, and_true] at e1'
    obtain ⟨-, -, -, -, hT1⟩ := Event.removeLiquidityImbalance.inj e1'
    rw [hT1, rliEnvW_caller]
  have hT12 : (T - rliBurnW (Nat.toB256 v0) (Nat.toB256 v2) T).toNat = T2 := by
    rw [hdw, hT2x, B256.toNat_toB256_of_lt hTxl]
  refine ⟨D, exc, T', o', hstep', hraw, hst, ?_, hret, hcalls, ?_⟩
  · rw [he', e1, hT12, rliEnvW_caller]
  · rw [← hst]
    exact (rawEffect_refines (D := ⟨0, sevm, St pre [] Mem.empty G, .ok D, exc⟩) hck hstep' hraw).1


end Blanc.Lift.Curve3Pool
