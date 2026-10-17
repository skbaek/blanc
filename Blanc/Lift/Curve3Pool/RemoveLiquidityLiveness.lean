import Blanc.Lift.Curve3Pool.Check
import Blanc.Lift.Curve3Pool.Refine
import Blanc.Lift.Curve3Pool.Walk.RemoveLiquidityLive

/-!
# Liveness of `remove_liquidity`

`removeLiquidity_live`: at a `Checkpoint`, if the model's `remove_liquidity` succeeds in the
environment `rlEnv sevm T` (the supply `T` and every call accepted) and the callees answer as
`LivePremises` describes, then every frame gas `G ≥ 167000 + 5 U` yields an actual successful
execution of the pool's runtime whose effect is the model's step: the `RawEffect` (logs, output,
calls) and `Checkpoint post o.state`.

The route: the forward walk `rx_rl_frame` gives an exact run of the certificate's trees to
`STOP`; `lift_exactM` turns it into an `Exec`; the safety theorem `removeLiquidity_rawT` read on
that execution gives the model's step in the environment the frame observed, whose supply is `T`
because the frame's last log carries `T - _amount`.

`removeLiquidity_none_of_push`: the control — a coin whose `transfer` is refused makes the
model's step revert, so no premise set describing such a coin can satisfy `hstep`.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

/-! ## The model's `remove_liquidity`, inverted -/

/-- A successful model `remove_liquidity` passed every check. -/
theorem removeLiquidity_inv {s : State} {e : Env} {amt : Nat} {m : V3} {o : Out}
    (h : removeLiquidity s e amt m = some o) :
    ∃ T, e.supply = some T ∧ T ≠ 0 ∧ (∀ k : Fin 3, s.balances.get k * amt < 2 ^ 256) ∧
      (∀ k : Fin 3, m.get k ≤ s.balances.get k * amt / T) ∧
      (∀ k : Fin 3, s.balances.get k * amt / T ≤ s.balances.get k) ∧
      (∀ k : Fin 3, (e.coin k).pushOk = true) ∧ e.burnOk = true ∧ amt ≤ T := by
  cases hT : e.supply with
  | none => simp only [removeLiquidity, hT, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at h
  | some T =>
    refine ⟨T, rfl, ?_⟩
    simp only [removeLiquidity, hT, V3.ofFnM, V3.get, chkMul, chkDiv, chkSub, req, wordSize,
      Option.bind_eq_bind, Option.bind_some, Fin.isValue] at h
    simp only [Fin.isValue, Fin.val_zero, Fin.val_one, Fin.val_two, Nat.reduceEqDiff,
      ↓reduceIte] at h
    by_cases m0 : s.balances.v0 * amt < 2 ^ 256 <;> simp only [m0, ↓reduceIte, Option.bind_none, Option.bind_some, reduceCtorEq] at h
    by_cases hT0 : T = 0 <;> simp only [hT0, ↓reduceIte, Option.bind_none, Option.bind_some, reduceCtorEq] at h
    by_cases n0 : m.v0 ≤ s.balances.v0 * amt / T <;> simp only [n0, ↓reduceIte, Option.bind_none, Option.bind_some, reduceCtorEq] at h
    by_cases p0 : (e.coin 0).pushOk = true <;> simp only [p0, ↓reduceIte, Option.bind_none, Option.bind_some, reduceCtorEq] at h
    by_cases m1 : s.balances.v1 * amt < 2 ^ 256 <;> simp only [m1, ↓reduceIte, Option.bind_none, Option.bind_some, reduceCtorEq] at h
    by_cases n1 : m.v1 ≤ s.balances.v1 * amt / T <;> simp only [n1, ↓reduceIte, Option.bind_none, Option.bind_some, reduceCtorEq] at h
    by_cases p1 : (e.coin 1).pushOk = true <;> simp only [p1, ↓reduceIte, Option.bind_none, Option.bind_some, reduceCtorEq] at h
    by_cases m2 : s.balances.v2 * amt < 2 ^ 256 <;> simp only [m2, ↓reduceIte, Option.bind_none, Option.bind_some, reduceCtorEq] at h
    by_cases n2 : m.v2 ≤ s.balances.v2 * amt / T <;> simp only [n2, ↓reduceIte, Option.bind_none, Option.bind_some, reduceCtorEq] at h
    by_cases p2 : (e.coin 2).pushOk = true <;> simp only [p2, ↓reduceIte, Option.bind_none, Option.bind_some, reduceCtorEq] at h
    by_cases l0 : s.balances.v0 * amt / T ≤ s.balances.v0 <;> simp only [l0, ↓reduceIte, Option.bind_none, Option.bind_some, reduceCtorEq] at h
    by_cases l1 : s.balances.v1 * amt / T ≤ s.balances.v1 <;> simp only [l1, ↓reduceIte, Option.bind_none, Option.bind_some, reduceCtorEq] at h
    by_cases l2 : s.balances.v2 * amt / T ≤ s.balances.v2 <;> simp only [l2, ↓reduceIte, Option.bind_none, Option.bind_some, reduceCtorEq] at h
    by_cases hb : e.burnOk = true <;> simp only [hb, ↓reduceIte, Option.bind_none, Option.bind_some, reduceCtorEq] at h
    by_cases ha : amt ≤ T <;> simp only [ha, ↓reduceIte, Option.bind_none, Option.bind_some, reduceCtorEq] at h
    refine ⟨hT0, fun k => ?_, fun k => ?_, fun k => ?_, fun k => ?_, hb, ha⟩ <;>
      match k with
      | 0 => assumption
      | 1 => assumption
      | 2 => assumption

/-- **The control**: a coin whose `transfer` is refused makes the model's `remove_liquidity`
revert. -/
theorem removeLiquidity_none_of_push {s : State} {e : Env} {amt : Nat} {m : V3} (k : Fin 3)
    (hk : (e.coin k).pushOk = false) : removeLiquidity s e amt m = none := by
  cases h : removeLiquidity s e amt m with
  | none => rfl
  | some o =>
    obtain ⟨_, _, _, _, _, _, hp, _⟩ := removeLiquidity_inv h
    rw [hp k] at hk
    cases hk

/-! ## Words from the model's numbers -/

/-- The overflow guard of `B * A` passes when the product is a word. -/
theorem mulCheck_ne_zero {x y : B256} (h : x.toNat * y.toNat < 2 ^ 256) :
    (B256.eqCheck (x * y / x) y ||| B256.eqCheck x 0) ≠ 0 := by
  have key : x * y / x = y ∨ x = 0 := by
    by_cases hx : x = 0
    · exact .inr hx
    · left
      apply B256.toNat_inj
      rw [B256.toNat_div hx, B256.toNat_mul]
      unfold Nat.lo
      rw [Nat.mod_eq_of_lt h, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero (toNat_ne_zero hx))]
  unfold B256.eqCheck
  rcases key with h1 | h1 <;> simp only [h1, ↓reduceIte] <;> split_ifs <;> decide

/-- An `ISZERO (LT x y)` guard passes when `y ≤ x`. -/
theorem geCheck_ne_zero {x y : B256} (h : y.toNat ≤ x.toNat) :
    B256.eqCheck (B256.ltCheck x y) 0 ≠ 0 := by
  rw [ltCheck_eq_zero_of_le h]; decide

/-- `T - A` as a number, when `A ≤ T`. -/
theorem sub_word {T A : B256} (h : A.toNat ≤ T.toNat) : T - A = Nat.toB256 (T.toNat - A.toNat) := by
  rw [← B256.toNat_sub_eq_of_le T A (B256.le_iff_toNat_le_toNat.mpr h), toB256_toNat]

/-- The supply word a `RemoveLiquidity` log carries. -/
theorem rlEvent_supply (pool : Adr) (p : Nat) (a f : V3) (n : Nat) :
    Bytes.toB256 ((eventLog pool (.removeLiquidity p a f n)).data.sliceD 0xc0 32 0) = Nat.toB256 n := by
  have hr : Region (wordsV3 a ++ wordsV3 f ++ word n) 0 (wordsV3 a ++ wordsV3 f ++ word n) :=
    List.sliceD_zero_of_length rfl
  have hw := hr.right.word
  rw [show 0 + (wordsV3 a ++ wordsV3 f).length = 0xc0 by
    simp only [wordsV3, word, List.length_append, B256.length_toBytes]] at hw
  exact hw.read

/-! ## Liveness -/

/-- **Liveness of `remove_liquidity`.** At a `Checkpoint` (`s`), when the model's
`remove_liquidity` succeeds in the environment `rlEnv sevm T` (`hstep`), the frame premises of the
safety theorem hold, the frame is a non-static call at nonzero depth, and the callees answer for
a world invariant `W` with gas use at most `U` each (`SupplyOk` with `T`, `CoinPushOk` for each
coin with its amount `balances[k] * _amount / T`, `BurnOk`), then every frame gas
`G ≥ 167000 + 5 U` yields an actual successful execution whose post state is the model's step:
its `RawEffect` in `rlEnv sevm T` with `o`, and `Checkpoint post o.state`. -/
theorem removeLiquidity_live {sevm : Sevm} {pre : Devm} {s : State} {o : Out} {T : B256}
    {W : Devm → Prop} {U G : Nat}
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
    (hckeep : ∀ k : Fin 3, CallKeeps sevm ((pre.getStor sevm.currentTarget).get (coinSlot k)))
    (hsk : StaticKeeps sevm ((pre.getStor sevm.currentTarget).get tokenSlot))
    (htk : CallKeeps sevm ((pre.getStor sevm.currentTarget).get tokenSlot))
    (hWc : WClosed sevm W) (hWb : W pre)
    (hsup : SupplyOk sevm W ((pre.getStor sevm.currentTarget).get tokenSlot) T U)
    (hpush : ∀ k : Fin 3, CoinPushOk sevm W ((pre.getStor sevm.currentTarget).get (coinSlot k))
      (balAt (pre.getStor sevm.currentTarget) k * rlAmt sevm / T) U)
    (hburn : BurnOk sevm W ((pre.getStor sevm.currentTarget).get tokenSlot) (rlAmt sevm) U)
    (hG : 167000 + 5 * U ≤ G) (hGm : (St pre [] Mem.empty G).gasMeasure < 2 ^ 256) :
    ∃ post, ∃ exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post),
      RawEffect ⟨0, sevm, St pre [] Mem.empty G, .ok post, exc⟩ post (rlEnv sevm T) o ∧
        Checkpoint (post.getStor sevm.currentTarget) o.state := by
  have hG256 : G < 2 ^ 256 := by
    have e : (St pre [] Mem.empty G).gasMeasure =
      G + pre.mach.stateGas.spilled + pre.mach.stateGas.committedSpill := rfl
    omega
  -- the model's step, inverted
  have hdec : decodeCall sevm = .removeLiquidity (arg sevm 0) (argV3 sevm 1) :=
    decodeCall_at (k := 7) rfl hsel hlen
  have hbody : ∀ {T' : B256} {o' : Out}, step s (rlEnv sevm T') (decodeCall sevm) = some o' →
      sevm.value.toNat = 0 ∧ removeLiquidity s (rlEnv sevm T') (arg sevm 0) (argV3 sevm 1) = some o' := by
    intro T' o' h
    rw [hdec] at h
    have h' : (if (rlEnv sevm T').value = 0 then
        removeLiquidity s (rlEnv sevm T') (arg sevm 0) (argV3 sevm 1) else none) = some o' := h
    split_ifs at h' with hv
    · exact ⟨hv, h'⟩
  obtain ⟨hv0, hrl⟩ := hbody hstep
  have hval : sevm.value = 0 := B256.toNat_inj _ _ (by rw [hv0]; rfl)
  obtain ⟨Tn, hTn, hT0n, hmul, hmin, hle, -, -, hTa⟩ := removeLiquidity_inv hrl
  have hTn' : Tn = T.toNat := (Option.some.inj hTn).symm
  subst hTn'
  -- the model's numbers as words
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
  -- the forward run
  obtain ⟨r, hr, D, rfl, L, ts, data, hlogs, hdata⟩ := rx_rl_frame (b := pre)
    (σ := pre.getStor sevm.currentTarget)
    (Q := fun r => ∃ D, r = .halted D ∧ ∃ L ts data, D.logs = L ++ [⟨sevm.currentTarget, ts, data⟩] ∧
      Bytes.toB256 (data.sliceD 0xc0 32 0) = T - rlAmt sevm)
    hfork hstatic hdepth hlen hcd hsel hid rfl hck.unlocked hval hWc hWb hsup
    (fun i hi => hpush ⟨i, hi⟩) hburn (fun i hi => mulCheck_ne_zero (hm i hi)) hT0
    (fun i hi => geCheck_ne_zero (by
      rw [hv i hi, ← hM i hi]; have := hmin ⟨i, hi⟩; rwa [hb, hA] at this))
    (fun i hi => geCheck_ne_zero (by
      rw [hv i hi]; have := hle ⟨i, hi⟩; rwa [hb, hA] at this))
    (by rw [← hA]; exact hTa) hG hG256 (fun D h => ⟨D, rfl, h⟩)
  obtain ⟨exc⟩ := lift_exactM cert_checkM cert_jumpsOkM hcode hfork ⟨t_0000_c0, rfl, hr⟩
  -- the safety theorem on that execution
  obtain ⟨T', o', hstep', hraw⟩ := removeLiquidity_rawT exc hcode hfork hlen hcd hsel rfl rfl hGm
    hck htok hcoin hpc (hid.of_rel ⟨fun _ => rfl, fun _ => rfl, rfl, rfl, rfl, rfl⟩) hckeep hsk htk
  -- the observed supply is `T`
  obtain ⟨-, hrl'⟩ := hbody hstep'
  obtain ⟨Tn', hTn', hT0', hmul', hmin', hle', hp', hb', hTa'⟩ := removeLiquidity_inv hrl'
  have hTn'' : Tn' = T'.toNat := (Option.some.inj hTn').symm
  subst hTn''
  have ho' := removeLiquidity_eq (s := s) (e := rlEnv sevm T') rfl hT0' hmul' hmin' hle' hp' hb'
    hTa'
  rw [hrl'] at ho'
  cases Option.some.inj ho'
  have hlast := hraw.logs
  rw [hlogs] at hlast
  simp only [List.map_cons, List.map_nil] at hlast
  have hev := List.append_inj_right' hlast rfl
  simp only [List.cons.injEq, and_true] at hev
  have hsup' := congrArg (fun l : Log => Bytes.toB256 (l.data.sliceD 0xc0 32 0)) hev
  simp only at hsup'
  rw [hdata, rlEvent_supply, sub_word (by rw [← hA]; exact hTa)] at hsup'
  have hTT : T' = T := by
    have e := congrArg B256.toNat hsup'
    rw [B256.toNat_toB256_of_lt (by have := B256.toNat_lt T; omega),
      B256.toNat_toB256_of_lt (by have := B256.toNat_lt T'; omega)] at e
    rw [← hA] at e
    exact B256.toNat_inj _ _ (by omega)
  subst hTT
  refine ⟨D, exc, ?_, ?_⟩
  · rw [hstep] at hstep'
    cases Option.some.inj hstep'
    exact hraw
  · rw [hstep] at hstep'
    cases Option.some.inj hstep'
    exact (rawEffect_refines (D := ⟨0, sevm, St pre [] Mem.empty G, .ok D, exc⟩) hck hstep hraw).1

end Blanc.Lift.Curve3Pool
