import Blanc.Composition.Curve3Pool3CrvLiveEndEntry
import Blanc.Lift.Curve3Pool.RemoveLiquidityLiveness
import Blanc.Lift.Curve3Pool.Walk.RemoveLiquidityRawK

/-!
# `remove_liquidity` end to end at the concrete entry

* `removeLiquidity_liveK`: `removeLiquidity_live` with the per-child keep premise of the other
  entries (`PoolCallsKeep` and the children keeping the code at `4`, for every execution from the
  frame's entry) in place of the target-level `CallKeeps`/`StaticKeeps`; the route is the same,
  through `removeLiquidity_rawTK`.  (`CallKeeps sevm t` quantifies over every machine `X` issuing
  the `CALL`, including one whose pool account has no code, no nonce and exactly the `CALL`'s
  value as balance: the value transfer empties that account and `State.setAccount` clears its
  storage, so `CallKeeps` fails at every non-static frame of nonzero depth.)
* `rlw_step`: the model step at the concrete entry `cSevm rlwData` (calldata
  `remove_liquidity(600, [0, 0, 0])`), by kernel evaluation: `rlOut`, balances
  `[900, 1800, 2700]`, pushes `100, 200, 300` (each `balances[k] * 600 / 6000`), burn `600`.
* `rl_frame_live_of_keep`: the end-to-end instance — every premise of `removeLiquidity_liveK`
  discharged at the concrete entry except the per-child keep, which stays a hypothesis.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

theorem removeLiquidity_liveK {sevm : Sevm} {pre : Devm} {s : State} {o : Out} {T : B256}
    {W : Nat → Devm → Prop} {U G : Nat}
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
    (hkeep : ∀ post (exc : Exec 0 sevm (St pre [] Mem.empty G) (.ok post)),
      PoolCallsKeep ⟨0, sevm, St pre [] Mem.empty G, .ok post, exc⟩ ∧
        ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4)
    (hWc : ∀ k, k ≤ 3 → WClosed sevm (W k)) (hWb : W 0 pre)
    (hsup : SupplyOk sevm (W 0) ((pre.getStor sevm.currentTarget).get tokenSlot) T U)
    (hpush : ∀ k : Fin 3, CoinPushOkAt sevm (W k) (W (k + 1))
      ((pre.getStor sevm.currentTarget).get (coinSlot k))
      (balAt (pre.getStor sevm.currentTarget) k * rlAmt sevm / T) U 0x520 0x5c0)
    (hburn : BurnOkTo sevm (W 3) (W 4) ((pre.getStor sevm.currentTarget).get tokenSlot)
      (rlAmt sevm) U)
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
  obtain ⟨T', o', hstep', hraw⟩ := removeLiquidity_rawTK exc hcode hfork hlen hcd hsel rfl rfl hGm
    hck htok hcoin hpc (hid.of_rel ⟨fun _ => rfl, fun _ => rfl, rfl, rfl, rfl, rfl⟩)
    (hkeep D exc).1 (hkeep D exc).2
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

namespace Blanc.Composition.Curve3Pool3CrvInstance

open Jaune Blanc Blanc.Lift Blanc.Lift.Curve3Pool Blanc.Composition.Curve3PoolCalleeLive
open Blanc.Composition.Curve3Pool3CrvJoint

/-- The `remove_liquidity` calldata: burn `600`, minimum amounts `0, 0, 0`. -/
def rlwData : Bytes := abiSelectorBytes selRemoveLiquidity ++ (600 : B256).toBytes ++
  (0 : B256).toBytes ++ (0 : B256).toBytes ++ (0 : B256).toBytes

/-- **The model's output of `remove_liquidity(600, [0, 0, 0])`** at `poolState` with supply
`6000`. -/
def rlOut : Out :=
  ⟨{ poolState with balances := ⟨900, 1800, 2700⟩ }, none,
    [.removeLiquidity traderN ⟨100, 200, 300⟩ V3.zero 5400],
    [.push 0 traderN 100, .push 1 traderN 200, .push 2 traderN 300, .burn traderN 600]⟩

theorem rlw_len : 4 ≤ (cSevm rlwData).data.length ∧ (cSevm rlwData).data.length < 2 ^ 256 := by
  decide +kernel

theorem rlw_sel : Sevm.selector (cSevm rlwData) = selRemoveLiquidity := by
  decide +kernel

theorem rlw_amt : rlAmt (cSevm rlwData) = 600 := by
  decide +kernel

theorem rlw_decode : decodeCall (cSevm rlwData) = .removeLiquidity 600 ⟨0, 0, 0⟩ := by
  rw [decodeCall_at (k := 7) rfl rlw_sel rlw_len.1]
  decide +kernel

/-- **The model step at the concrete `remove_liquidity` entry** (kernel evaluation). -/
theorem rlw_step :
    step poolState (rlEnv (cSevm rlwData) 6000) (decodeCall (cSevm rlwData)) = some rlOut := by
  rw [rlw_decode]
  unfold rlEnv
  rw [cSevm_time, cSevm_caller, cSevm_value]
  decide +kernel

/-- **`remove_liquidity` end to end at the concrete entry**, given the per-child keep: an actual
successful execution of the pool's runtime from `wPre rlwData` at gas `878400`, whose effect is
the model's `remove_liquidity(600, [0, 0, 0])` (`rlOut`: pushes `100, 200, 300`, burn `600`),
with the pool's checkpoint at the post. -/
theorem rl_frame_live_of_keep
    (hkeep : ∀ post (exc : Exec 0 (cSevm rlwData) (St (wPre rlwData) [] Mem.empty 878400)
        (.ok post)),
      PoolCallsKeep ⟨0, cSevm rlwData, St (wPre rlwData) [] Mem.empty 878400, .ok post, exc⟩ ∧
        ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4) :
    ∃ post, ∃ exc : Exec 0 (cSevm rlwData) (St (wPre rlwData) [] Mem.empty 878400) (.ok post),
      RawEffect ⟨0, cSevm rlwData, St (wPre rlwData) [] Mem.empty 878400, .ok post, exc⟩ post
          (rlEnv (cSevm rlwData) 6000) rlOut ∧
        Checkpoint (post.getStor poolAddr) rlOut.state := by
  have hc3 := wPre_c3Entry rlwData
  have hcoins := wPre_coins rlwData
  obtain ⟨hWc, hWb, hsup, hpush, hburn⟩ := removeLiquidity_premises_satisfiable
    (sevm := cSevm rlwData) (pre := wPre rlwData) (T := 6000) (cSevm_fork _) rfl
    (by decide +kernel) hc3 hcoins (by unfold BurnFits; decide +kernel)
    (by unfold T20MoveFits; decide +kernel)
  exact removeLiquidity_liveK (pre := wPre rlwData) (G := 878400) (U := 80000) rfl (cSevm_fork _)
    rfl (by decide +kernel) rlw_len.1 rlw_len.2 rlw_sel (wPre_checkpoint _) rlw_step hc3.prec
    hcoins.prec (wPre_poolCode _) (wPre_id _) hkeep hWc hWb hsup hpush hburn (by decide)
    (Nat.lt_of_le_of_lt (Nat.le_add_right _ 2000) (wPre_gas rlwData 878400 (by decide +kernel)))

end Blanc.Composition.Curve3Pool3CrvInstance
