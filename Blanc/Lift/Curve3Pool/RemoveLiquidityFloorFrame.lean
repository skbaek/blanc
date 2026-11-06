import Blanc.Lift.Curve3Pool.RemoveLiquidityExactFrame
import Blanc.Lift.Curve3Pool.Walk.RemoveLiquidityFloorWalk
import Blanc.Lift.StaticGasMessage

/-!
# `remove_liquidity` live at the true gas minimum

`removeLiquidity_live_floor` is `removeLiquidity_live_exact` for every `R ≥ 2201`, and `removeLiquidity_msg_floor` its
message form. Its run comes from `rx_rl_frame_floor`. Its effect does not come through `removeLiquidity_live`, whose
walk needs `167000 + 5 U`: `removeLiquidity_effect` reads the safety theorem on any execution whose last log carries
`T - _amount`, at any gas.
-/

namespace Blanc.Lift.Curve3Pool

open Jaune Blanc.Lift Blanc.StableSwapNewton

/-- **What any execution ending in the supply's log has done**: the model's step, whatever gas it had. -/
theorem removeLiquidity_effect {sevm : Sevm} {pre post : Devm} {s : State} {o : Out} {T : B256}
    (exc : Exec 0 sevm pre (.ok post))
    (hcode : sevm.code = code) (hfork : CoveredFork sevm.benvStat.fork)
    (hlen : 4 ≤ sevm.data.length) (hcd : sevm.data.length < 2 ^ 256)
    (hsel : Sevm.selector sevm = selRemoveLiquidity)
    (hs : pre.stack = []) (hm : pre.memory = Mem.empty) (hGm : pre.gasMeasure < 2 ^ 256)
    (hck : Checkpoint (pre.getStor sevm.currentTarget) s)
    (hstep : step s (rlEnv sevm T) (decodeCall sevm) = some o)
    (htok : ¬ sevm.benvStat.rules.isPrecomp
      ((pre.getStor sevm.currentTarget).get tokenSlot).toAdr)
    (hcoin : ∀ k : Fin 3,
      ¬ sevm.benvStat.rules.isPrecomp ((pre.getStor sevm.currentTarget).get (coinSlot k)).toAdr)
    (hpc : pre.getCode sevm.currentTarget ≠ .empty) (hid : IdReadyH sevm pre)
    (hkeep : PoolCallsKeep ⟨0, sevm, pre, .ok post, exc⟩ ∧
      ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4)
    (hlogs : ∃ L ts data, post.logs = L ++ [⟨sevm.currentTarget, ts, data⟩] ∧
      Bytes.toB256 (data.sliceD 0xc0 32 0) = T - rlAmt sevm) :
    RawEffect ⟨0, sevm, pre, .ok post, exc⟩ post (rlEnv sevm T) o ∧
      Checkpoint (post.getStor sevm.currentTarget) o.state := by
  obtain ⟨L, ts, data, hlogs, hdata⟩ := hlogs
  obtain ⟨-, hT0, -, -, -, hTa⟩ := removeLiquidity_walkChecks hlen hsel hck hstep
  have hdec : decodeCall sevm = .removeLiquidity (arg sevm 0) (argV3 sevm 1) :=
    decodeCall_at (k := 7) rfl hsel hlen
  have hA : arg sevm 0 = (rlAmt sevm).toNat := by
    unfold arg Sevm.argWord
    rw [show (32 * (0 : B256) + 4 : B256) = Bytes.toB256 [4] by decide]
  obtain ⟨T', o', hstep', hraw⟩ := removeLiquidity_rawTK exc hcode hfork.histFork hlen hcd hsel hs hm hGm
    hck htok hcoin hpc hid hkeep.1 hkeep.2
  have hbody : removeLiquidity s (rlEnv sevm T') (arg sevm 0) (argV3 sevm 1) = some o' := by
    rw [hdec] at hstep'
    have h' : (if (rlEnv sevm T').value = 0 then
        removeLiquidity s (rlEnv sevm T') (arg sevm 0) (argV3 sevm 1) else none) = some o' := hstep'
    split_ifs at h'
    exact h'
  obtain ⟨Tn', hTn', hT0', hmul', hmin', hle', hp', hb', hTa'⟩ := removeLiquidity_inv hbody
  have hTn'' : Tn' = T'.toNat := (Option.some.inj hTn').symm
  subst hTn''
  have ho' := removeLiquidity_eq (s := s) (e := rlEnv sevm T') rfl hT0' hmul' hmin' hle' hp' hb' hTa'
  rw [hbody] at ho'
  cases Option.some.inj ho'
  have hlast := hraw.logs
  rw [hlogs] at hlast
  simp only [List.map_cons, List.map_nil] at hlast
  have hev := List.append_inj_right' hlast rfl
  simp only [List.cons.injEq, and_true] at hev
  have hsup' := congrArg (fun l : Log => Bytes.toB256 (l.data.sliceD 0xc0 32 0)) hev
  simp only at hsup'
  rw [hdata, rlEvent_supply, sub_word hTa] at hsup'
  have hTT : T' = T := by
    have e := congrArg B256.toNat hsup'
    rw [B256.toNat_toB256_of_lt (by have := B256.toNat_lt T; omega),
      B256.toNat_toB256_of_lt (by have := B256.toNat_lt T'; omega)] at e
    rw [← hA] at e hTa
    exact B256.toNat_inj _ _ (by omega)
  subst hTT
  rw [hstep] at hstep'
  cases Option.some.inj hstep'
  exact ⟨hraw, (rawEffect_refines (D := ⟨0, sevm, pre, .ok post, exc⟩) hck hstep hraw).1⟩

/-- **`remove_liquidity` at the true minimum.** As `removeLiquidity_live_exact`, with the calls at their floors and
every `R ≥ 2201`. -/
theorem removeLiquidity_live_floor {sevm : Sevm} {pre : Devm} {s : State} {o : Out} {T : B256}
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
    (hP : RLFloorPremises sevm pre T W U P) :
    ∀ R, 2201 ≤ R →
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
  obtain ⟨r, hr, D, rfl, hDg, hlogs⟩ := rx_rl_frame_floor P hfork hstatic hdepth hlen hcd hsel hid
    hck.unlocked hval hWc hWb hP hmulw hT0 hminw hlew hTa hR hG256
  obtain ⟨exD⟩ := lift_exactM cert_checkM cert_jumpsOkM hcode hfork ⟨t_0000_c0, rfl, hr⟩
  obtain ⟨hraw, hckp⟩ := removeLiquidity_effect exD hcode hfork hlen hcd hsel rfl rfl hGm hck hstep htok
    hcoin hpc (hid.toH.of_rel ⟨fun _ => rfl, fun _ => rfl, rfl, rfl, rfl, rfl⟩) (hkeep D exD) hlogs
  exact ⟨D, exD, hDg, hraw, hckp⟩

/-- **`remove_liquidity` at the true minimum, at message entry.** -/
theorem removeLiquidity_msg_floor {msg : Msg} {s : State} {o : Out} {T : B256}
    {W : Nat → Devm → Prop} {U : Nat} (P : RLExactCalls)
    (hcode : (initSevm msg).code = code) (hfork : CoveredFork (initSevm msg).benvStat.fork)
    (hstatic : (initSevm msg).isStatic = false) (hdepth : (initSevm msg).depth ≠ 0)
    (hlen : 4 ≤ (initSevm msg).data.length) (hcd : (initSevm msg).data.length < 2 ^ 256)
    (hsel : Sevm.selector (initSevm msg) = selRemoveLiquidity)
    (hck : Checkpoint ((initDevm msg).getStor msg.currentTarget) s)
    (hstep : step s (rlEnv (initSevm msg) T) (decodeCall (initSevm msg)) = some o)
    (htok : ¬ (initSevm msg).benvStat.rules.isPrecomp
      (((initDevm msg).getStor msg.currentTarget).get tokenSlot).toAdr)
    (hcoin : ∀ k : Fin 3, ¬ (initSevm msg).benvStat.rules.isPrecomp
      (((initDevm msg).getStor msg.currentTarget).get (coinSlot k)).toAdr)
    (hpc : (initDevm msg).getCode msg.currentTarget ≠ .empty)
    (hid : IdReady (initSevm msg) (initDevm msg))
    (hWc : ∀ k, k ≤ 3 → WClosed (initSevm msg) (W k)) (hWb : W 0 (initDevm msg))
    (hP : RLFloorPremises (initSevm msg) (initDevm msg) T W U P) :
    ∀ R, 2201 ≤ R →
      R + rlExactCost (initSevm msg) (initDevm msg) T P < 2 ^ 256 →
      (∀ post (exc : Exec 0 (initSevm (msg.withGas (R + rlExactCost (initSevm msg) (initDevm msg) T P)))
          (initDevm (msg.withGas (R + rlExactCost (initSevm msg) (initDevm msg) T P))) (.ok post)),
        PoolCallsKeep ⟨0, _, _, .ok post, exc⟩ ∧
          ∀ c ∈ Exec.childFrames exc, c.post.getCode 4 = c.pre.getCode 4) →
      ∃ post, ∃ exc : Exec 0 (initSevm (msg.withGas (R + rlExactCost (initSevm msg) (initDevm msg) T P)))
          (initDevm (msg.withGas (R + rlExactCost (initSevm msg) (initDevm msg) T P))) (.ok post),
        exec (initEvm (msg.withGas (R + rlExactCost (initSevm msg) (initDevm msg) T P))) =
          .ok post ∧
        post.gasLeft = R ∧
        RawEffect ⟨0, _, _, .ok post, exc⟩ post (rlEnv (initSevm msg) T) o ∧
        Checkpoint (post.getStor msg.currentTarget) o.state := by
  intro R hR hGm hkeep
  obtain ⟨F, hF⟩ : ∃ F, F = R + rlExactCost (initSevm msg) (initDevm msg) T P := ⟨_, rfl⟩
  have h := removeLiquidity_live_floor (sevm := {initSevm msg with gas := F})
    (pre := initDevm msg) P hcode hfork hstatic hdepth hlen hcd hsel hck hstep htok hcoin hpc
    (hid.withStaticGas F) (fun k hk => (hWc k hk).withStaticGas F) hWb (hP.withStaticGas F)
  rw [rlExactCost_withStaticGas (initSevm msg) F] at h
  have h' := h R
  rw [← hF] at h' hGm hkeep ⊢
  obtain ⟨post, exc, hg, hraw, hckp⟩ := h' hR hGm hkeep
  exact ⟨post, exc, exec_withGas_of_frame exc, hg, hraw, hckp⟩

end Blanc.Lift.Curve3Pool
