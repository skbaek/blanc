import Blanc.Lift.LidoCircuitBreakerDeployed.PauseSteps

/-!
# The deployed Lido `pause` wrapper, walked

Ladder unit lido-writers-v1, the `pause` field of `LidoWriterSpecsM`.  Route:
selector wrapper 49 → decoder 7 → body 13:

* `t_05ac`/`t_05e8`: the `nonReentrant` lock (`TLOAD`, revert if held, `TSTORE`),
  the `getPauser(t) == msg.sender` check;
* `t_0673`: the liveness check;
* `t_06ba`: `setPauser(t, 0)` (entry 32, return tag `0x6ce`), discharged by
  `entry32Spec 0x6ce`;
* `t_06ce`/`t_0733`: `extcodesize`, then the one external `CALL` (`pauseFor`),
  discharged by `ContractSpecSem.post_of_call_self_with (Q := InRoots R)` and the
  admitted deeper-frame hypothesis, as `Weth9.withdraw_post_in` does;
* `t_0745`/`t_0792`: the `isPaused` `STATICCALL` (storage unchanged) and its
  bool decoding (entry 33);
* `t_07ec`: the event, then `_setHeartbeatExpiry(msg.sender, …)` (entry 22) under
  the frame's own `LocalApart` (never the entry witness: the registry may have
  been changed by a reentrant frame during the `CALL`);
* `t_0864`: the lock release.

**Entry 32 discharge.** Entry 32's branch walks `setPauser_*_inv` generalize
the caller's return tag to an arbitrary variable `ra`, proved by `entry32Spec`
in `PauseSteps.lean`. The call in `pause` at tag `0x6ce` is discharged by
`entry32Spec 0x6ce`.
-/

namespace Blanc.Lift.LidoCircuitBreakerDeployed

open Jaune
open Blanc
open Blanc.Lift
open Blanc.LidoCircuitBreaker

/-- Forget a walk state's base and memory, keeping the base's storage. -/
theorem ric_forget {fs : List SFunc} {sevm : Sevm} {C : List Nat} {b : Devm} {S : List B256}
    {M : Mem} {G : Nat} {f : SFunc} {r : Seg}
    (run : SFunc.RunCut fs sevm C (St b S M G) f r) :
    ∃ b' M', Devm.getStor b' = Devm.getStor b ∧ SFunc.RunCut fs sevm C (St b' S M' G) f r :=
  ⟨b, M, rfl, run⟩

theorem getStor_St_code (b : Devm) (S : List B256) (M : Mem) (G : Nat) (a : Adr) :
    (St b S M G).getCode a = b.getCode a := rfl

theorem canonicalAddress_adr (a : Adr) : canonicalAddress a.toB256 := by
  rw [← toAdr_toB256 a]
  exact canonical_toAdr_toB256 _

/-! ## After the `CALL` -/

/-- `t_0864_c13`: release the lock and return; storage is untouched. -/
theorem t0864_ret {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat} {t dur t2 ra : B256}
    {xs : List B256} {D : Devm} (hfork : CoveredFork sevm.benvStat.fork)
    (run : SFunc.RunCut prog sevm [] (St b (t :: dur :: t2 :: ra :: xs) M G) t_0864_c13
      (.done (.returned D))) :
    Devm.getStor D sevm.currentTarget = Devm.getStor b sevm.currentTarget := by
  unfold t_0864_c13 at run
  obtain ⟨G1, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G2, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G3, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G4, rfl⟩ := ri_swap (n := 0) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G5, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G6, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G7, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G8, rfl⟩ := ri_tload s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G9, rfl⟩ := ri_and s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G10, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G11, rfl⟩ := ri_tstore hfork s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G12, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G13, rfl⟩ := ri_pop s1
  obtain ⟨G14, hr⟩ := ric_ret run
  injection hr with hr
  injection hr with hr
  rw [hr]
  rfl

theorem regInv_afterSload_addLog {sevm : Sevm} {b : Devm} {L : Log} {k : B256}
    (h : RegInv (Devm.getStor b sevm.currentTarget)) :
    RegInv (Devm.getStor (afterSload sevm (b.addLog L) k) sevm.currentTarget) := by
  rw [afterSload_getStor]; exact h

/-- `t_07ec_c13`: the `PauseTriggered` event, then `_setHeartbeatExpiry(msg.sender,
…)` (entry 22, directly or after the checked addition, entry 23), then the lock
release.  Keeps `RegInv` given the caller's `heartbeatExpiry` slot is off the
Registry. -/
theorem t07ec_regInv {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat} {t dur t2 ra : B256}
    {xs : List B256} {D : Devm} (hfork : CoveredFork sevm.benvStat.fork)
    (hfa : ForeignApart (2 ^ 160) (mapSlot sevm.caller.toB256 2))
    (hinv : RegInv (Devm.getStor b sevm.currentTarget))
    (run : SFunc.RunCut prog sevm [] (St b (t :: dur :: t2 :: ra :: xs) M G) t_07ec_c13
      (.done (.returned D))) :
    RegInv (Devm.getStor D sevm.currentTarget) := by
  have hΦ : ∀ {s : Stor} {w v : B256}, ForeignApart (2 ^ 160) w → RegInv s → RegInv (s.set w v) :=
    fun hfa h => RegInv.set_foreign hfa h
  have hc := canonicalAddress_adr sevm.caller
  unfold t_07ec_c13 at run
  obtain ⟨G1, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G2, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G3, rfl⟩ := ri_mload s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G4, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G5, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G6, rfl⟩ := ri_mstore s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G7, rfl⟩ := ri_caller s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G8, rfl⟩ := ri_swap (n := 0) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G9, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G10, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G11, rfl⟩ := ri_and s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G12, rfl⟩ := ri_swap (n := 0) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G13, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G14, rfl⟩ := ri_swap (n := 0) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G15, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G16, rfl⟩ := ri_add s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G17, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G18, rfl⟩ := ri_mload s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G19, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G20, rfl⟩ := ri_swap (n := 1) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G21, rfl⟩ := ri_sub s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G22, rfl⟩ := ri_swap (n := 0) rfl s1
  try dsimp only [List.set] at run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G23, rfl⟩ := ri_log3 s1
  obtain ⟨b1, M1, hb1, run⟩ := ric_forget run
  have hinvb1 : RegInv (Devm.getStor b1 sevm.currentTarget) := by rw [hb1]; exact hinv
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G24, rfl⟩ := ri_caller s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G25, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G26, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G27, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G28, rfl⟩ := ri_mstore s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G29, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G30, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G31, rfl⟩ := ri_mstore s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G32, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G33, rfl⟩ := ri_swap (n := 0) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G34, rfl⟩ := ri_keccak s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G35, rfl⟩ := ri_sload hfork s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G36, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G37, rfl⟩ := ri_swap (n := 1) rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G38, rfl⟩ := ri_swap (n := 0) rfl s1
  try dsimp only [List.set] at run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G39, rfl⟩ := ri_push s1
  rcases ric_branch run with ⟨-, G40, run⟩ | ⟨-, G40, run⟩
  · -- no pausables left: `_setHeartbeatExpiry(msg.sender, 0)`
    unfold t_0852_c13 at run
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G41, rfl⟩ := ri_push s1
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G42, rfl⟩ := ri_push s1
    obtain ⟨b', M', G', hinv', run⟩ := call22_foreign (Φ := RegInv) hΦ hfork hc hfa
      (by rw [afterSload_getStor]; exact hinvb1) run (fun _ h => by cases h)
    exact (t0864_ret hfork run) ▸ hinv'
  · -- `_setHeartbeatExpiry(msg.sender, now + heartbeatInterval)`
    unfold t_0857_c13 at run
    obtain ⟨G41, run⟩ := ric_dest run
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G42, rfl⟩ := ri_push s1
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G43, rfl⟩ := ri_sload hfork s1
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G44, rfl⟩ := ri_push s1
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G45, rfl⟩ := ri_swap (n := 0) rfl s1
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G46, rfl⟩ := ri_timestamp s1
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G47, rfl⟩ := ri_push s1
    obtain ⟨G48, hcall⟩ := ric_call (g := t_10a8_c23) rfl run
    rcases hcall with ⟨D23, r23, run⟩ | ⟨D23, -, hh⟩
    swap
    · cases hh
    obtain ⟨w, hw⟩ := entry23_ret (xs := sevm.caller.toB256 :: Bytes.toB256 [0x08, 0x64] ::
      t :: dur :: t2 :: ra :: xs) (St_pref _ _ _ _) r23
    obtain ⟨tl, hw⟩ := stack_of_pref hw
    have hst : D23.state = _ := silent_entry_state (k := 23) (by decide) rfl r23
    have hinv23 : RegInv (Devm.getStor D23 sevm.currentTarget) := by
      rw [getStor_eq_of_state_eq hst, getStor_St, afterSload_getStor, afterSload_getStor]
      exact hinvb1
    rw [St.self (d := D23) hw rfl] at run
    unfold t_0446_c13 at run
    obtain ⟨G49, run⟩ := ric_dest run
    obtain ⟨d1, s1, run⟩ := ric_next run
    obtain ⟨G50, rfl⟩ := ri_push s1
    obtain ⟨b', M', G', hinv', run⟩ := call22_foreign (Φ := RegInv) hΦ hfork hc hfa hinv23 run
      (fun _ h => by cases h)
    exact (t0864_ret hfork run) ▸ hinv'

/-- `t_0745_c13` onward: the `isPaused` `STATICCALL` (every storage map kept),
its bool decoding (entry 33), then `t_07ec_c13`.  Keeps `RegInv`. -/
theorem t0745_regInv {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat}
    {z e F u t dur t2 ra : B256} {xs : List B256} {D : Devm}
    (hfork : CoveredFork sevm.benvStat.fork)
    (hfa : ForeignApart (2 ^ 160) (mapSlot sevm.caller.toB256 2))
    (hinv : RegInv (Devm.getStor b sevm.currentTarget))
    (run : SFunc.RunCut prog sevm []
      (St b (z :: e :: F :: u :: t :: dur :: t2 :: ra :: xs) M G) t_0745_c13
      (.done (.returned D))) :
    RegInv (Devm.getStor D sevm.currentTarget) := by
  unfold t_0745_c13 at run
  obtain ⟨G1, run⟩ := ric_dest run
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G2, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G3, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G4, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G5, rfl⟩ := ri_pop s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G6, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G7, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G8, rfl⟩ := ri_and s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G9, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G10, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G11, rfl⟩ := ri_mload s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G12, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G13, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G14, rfl⟩ := ri_and s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G15, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G16, rfl⟩ := ri_shl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G17, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G18, rfl⟩ := ri_mstore s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G19, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G20, rfl⟩ := ri_add s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G21, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G22, rfl⟩ := ri_push s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G23, rfl⟩ := ri_mload s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G24, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G25, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G26, rfl⟩ := ri_sub s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G27, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨G28, rfl⟩ := ri_dup rfl s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨gw, G29, rfl⟩ := ri_gas s1
  obtain ⟨d1, s1, run⟩ := ric_next run
  obtain ⟨flag, out, hsp, -⟩ := ri_staticcall hfork s1
  have hinv1 : RegInv (Devm.getStor d1 sevm.currentTarget) := by
    rw [show Devm.getStor d1 sevm.currentTarget = _ from hsp.stor _]; exact hinv
  rw [hsp.eq_St] at run
  obtain ⟨d2, s2, run⟩ := ric_next run
  obtain ⟨G30, rfl⟩ := ri_iszero s2
  obtain ⟨d2, s2, run⟩ := ric_next run
  obtain ⟨G31, rfl⟩ := ri_dup rfl s2
  obtain ⟨d2, s2, run⟩ := ric_next run
  obtain ⟨G32, rfl⟩ := ri_iszero s2
  obtain ⟨d2, s2, run⟩ := ric_next run
  obtain ⟨G33, rfl⟩ := ri_push s2
  rcases ric_branch run with ⟨-, G34, run⟩ | ⟨-, G34, run⟩
  · exact (SFunc.RunCutP.false_of_noOk run (by decide)).elim
  unfold t_0792_c13 at run
  obtain ⟨G35, run⟩ := ric_dest run
  obtain ⟨d2, s2, run⟩ := ric_next run
  obtain ⟨G36, rfl⟩ := ri_pop s2
  obtain ⟨d2, s2, run⟩ := ric_next run
  obtain ⟨G37, rfl⟩ := ri_pop s2
  obtain ⟨d2, s2, run⟩ := ric_next run
  obtain ⟨G38, rfl⟩ := ri_pop s2
  obtain ⟨d2, s2, run⟩ := ric_next run
  obtain ⟨G39, rfl⟩ := ri_pop s2
  obtain ⟨d2, s2, run⟩ := ric_next run
  obtain ⟨G40, rfl⟩ := ri_push s2
  obtain ⟨d2, s2, run⟩ := ric_next run
  obtain ⟨G41, rfl⟩ := ri_mload s2
  obtain ⟨d2, s2, run⟩ := ric_next run
  obtain ⟨G42, rfl⟩ := ri_returndatasize s2
  obtain ⟨d2, s2, run⟩ := ric_next run
  obtain ⟨G43, rfl⟩ := ri_push s2
  obtain ⟨d2, s2, run⟩ := ric_next run
  obtain ⟨G44, rfl⟩ := ri_not s2
  obtain ⟨d2, s2, run⟩ := ric_next run
  obtain ⟨G45, rfl⟩ := ri_push s2
  obtain ⟨d2, s2, run⟩ := ric_next run
  obtain ⟨G46, rfl⟩ := ri_dup rfl s2
  obtain ⟨d2, s2, run⟩ := ric_next run
  obtain ⟨G47, rfl⟩ := ri_add s2
  obtain ⟨d2, s2, run⟩ := ric_next run
  obtain ⟨G48, rfl⟩ := ri_and s2
  obtain ⟨d2, s2, run⟩ := ric_next run
  obtain ⟨G49, rfl⟩ := ri_dup rfl s2
  obtain ⟨d2, s2, run⟩ := ric_next run
  obtain ⟨G50, rfl⟩ := ri_add s2
  obtain ⟨d2, s2, run⟩ := ric_next run
  obtain ⟨G51, rfl⟩ := ri_dup rfl s2
  obtain ⟨d2, s2, run⟩ := ric_next run
  obtain ⟨G52, rfl⟩ := ri_push s2
  obtain ⟨d2, s2, run⟩ := ric_next run
  obtain ⟨G53, rfl⟩ := ri_mstore s2
  obtain ⟨d2, s2, run⟩ := ric_next run
  obtain ⟨G54, rfl⟩ := ri_pop s2
  obtain ⟨d2, s2, run⟩ := ric_next run
  obtain ⟨G55, rfl⟩ := ri_dup rfl s2
  obtain ⟨d2, s2, run⟩ := ric_next run
  obtain ⟨G56, rfl⟩ := ri_add s2
  obtain ⟨d2, s2, run⟩ := ric_next run
  obtain ⟨G57, rfl⟩ := ri_swap (n := 0) rfl s2
  obtain ⟨d2, s2, run⟩ := ric_next run
  obtain ⟨G58, rfl⟩ := ri_push s2
  obtain ⟨d2, s2, run⟩ := ric_next run
  obtain ⟨G59, rfl⟩ := ri_swap (n := 1) rfl s2
  obtain ⟨d2, s2, run⟩ := ric_next run
  obtain ⟨G60, rfl⟩ := ri_swap (n := 0) rfl s2
  try dsimp only [List.set] at run
  obtain ⟨d2, s2, run⟩ := ric_next run
  obtain ⟨G61, rfl⟩ := ri_push s2
  obtain ⟨G62, hcall⟩ := ric_call (g := t_10bb_c33) rfl run
  rcases hcall with ⟨D33, r33, run⟩ | ⟨D33, -, hh⟩
  swap
  · cases hh
  obtain ⟨v, M33, G63, rfl⟩ := entry33_ret r33
  unfold t_07b6_c13 at run
  obtain ⟨G64, run⟩ := ric_dest run
  obtain ⟨d2, s2, run⟩ := ric_next run
  obtain ⟨G65, rfl⟩ := ri_push s2
  rcases ric_branch run with ⟨-, G66, run⟩ | ⟨-, G66, run⟩
  · exact (SFunc.RunCutP.false_of_noOk run (by decide)).elim
  exact t07ec_regInv hfork hfa hinv1 run

/-! ## Before the `CALL`, and the `CALL` itself -/

theorem zero_le_B256 (x : B256) : (0 : B256) ≤ x := by
  rw [B256.le_iff_toNat_le_toNat, show (0 : B256).toNat = 0 from rfl]
  exact Nat.zero_le _

/-- **The `pause(t)` body (entry 13)**, inside a root derivation `R`: from the
frame-entry witness, the frame's code, well-formed memory, the `setPauser(t, 0)`
branch keys and the caller's `heartbeatExpiry` slot off the Registry, a
successful run keeps `RegInv`.  Entry 32 (return tag `0x6ce`) is discharged by
`entry32Spec 0x6ce`; the `CALL` child is discharged from `R`'s frame admission
and the admitted deeper-frame hypothesis. -/
theorem entry13_regInv {A : List Entry → Sevm → Prop}
    {R : Exec.Deriv} {sevm : Sevm} {b : Devm} {M : Mem} {G : Nat} {t ra : B256}
    {xs : List B256} {D : Devm} {entries : List Entry}
    (hfork : CoveredFork sevm.benvStat.fork)
    (hadm : Exec.FrameAdmitted sevm.currentTarget (lidoFrameEntry A) R.exc)
    (ih : LidoDeeper (lidoFrameEntry A) sevm)
    (hmem : MemOK M)
    (hw : RegistryWitness (solRegistryStorage (Devm.getStor b sevm.currentTarget)) entries)
    (hcode : some (b.getCode sevm.currentTarget).toList = lidoSpec.sem.image)
    (ht : canonicalAddress t)
    (hkeys : t ≠ 0 → RegistryKeysFaithful (2 ^ 160) (setPauserKeys entries t 0))
    (hfa : ForeignApart (2 ^ 160) (mapSlot sevm.caller.toB256 2))
    (run : SFunc.RunP (StepIn R) prog sevm (St b (t :: ra :: xs) M G) t_05ac_c13
      (.returned D)) :
    RegInv (Devm.getStor D sevm.currentTarget) := by
  unfold t_05ac_c13 at run
  obtain ⟨G1, run⟩ := rp_dest run
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_tload (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_and (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_iszero (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun s1)
  rcases rp_branch run with ⟨-, G2, run⟩ | ⟨-, G2, run⟩
  · exact (SFunc.RunCutP.false_of_noOk (SFunc.runP_iff_runCutP_nil.mp run) (by decide)).elim
  unfold t_05e8_c13 at run
  obtain ⟨G3, run⟩ := rp_dest run
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_tload (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_and (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_or (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_tstore hfork (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_pop (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_and (StepIn.toRun s1)
  rw [ff20_and_canonical ht] at run
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_mstore (StepIn.toRun s1)
  try dsimp only [List.set] at run
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_mstore (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_keccak (StepIn.toRun s1)
  simp only [show (Bytes.toB256 [] : B256) = 0 from rfl,
    show (Bytes.toB256 [32] : B256) = 32 from rfl,
    show (Bytes.toB256 [64] : B256) = 64 from rfl,
    show (Bytes.toB256 [3] : B256) = 3 from rfl,
    show (0 : B256).toNat = 0 from rfl,
    show (32 : B256).toNat = 32 from rfl,
    show (64 : B256).toNat = 64 from rfl] at run
  have hscr := scratch_mapSlot hmem.1 hmem.2 t 3
  rw [hscr.1, hscr.2.1] at run
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_sload hfork (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_and (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_caller (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_eq (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun s1)
  rcases rp_branch run with ⟨-, G4, run⟩ | ⟨-, G4, run⟩
  · exact (SFunc.RunCutP.false_of_noOk (SFunc.runP_iff_runCutP_nil.mp run) (by decide)).elim
  unfold t_0673_c13 at run
  obtain ⟨G5, run⟩ := rp_dest run
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_caller (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_mstore (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_mstore (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_keccak (StepIn.toRun s1)
  simp only [show (Bytes.toB256 [] : B256) = 0 from rfl,
    show (Bytes.toB256 [32] : B256) = 32 from rfl,
    show (Bytes.toB256 [64] : B256) = 64 from rfl,
    show (Bytes.toB256 [2] : B256) = 2 from rfl,
    show (0 : B256).toNat = 0 from rfl,
    show (32 : B256).toNat = 32 from rfl,
    show (64 : B256).toNat = 64 from rfl] at run
  have hscr2 := scratch_mapSlot hscr.2.2.1 hscr.2.2.2 sevm.caller.toB256 2
  rw [hscr2.1, hscr2.2.1] at run
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_sload hfork (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_timestamp (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_lt (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun s1)
  rcases rp_branch run with ⟨-, G6, run⟩ | ⟨-, G6, run⟩
  · exact (SFunc.RunCutP.false_of_noOk (SFunc.runP_iff_runCutP_nil.mp run) (by decide)).elim
  unfold t_06ba_c13 at run
  obtain ⟨G7, run⟩ := rp_dest run
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_sload hfork (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (StepIn.toRun s1)
  try dsimp only [List.set] at run
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun s1)
  obtain ⟨G8, hcall⟩ := rp_call (g := t_0934_c32) rfl run
  rcases hcall with ⟨D32, r32, run⟩ | ⟨D32, -, hh⟩
  swap
  · cases hh
  rw [show (Bytes.toB256 [] : B256) = 0 from rfl, show (Bytes.toB256 [3] : B256) = 3 from rfl,
    show (Bytes.toB256 [0x06, 0xce] : B256) = 0x6ce from rfl] at r32
  obtain ⟨hinv2, hcode2, b2, M2, G9, rfl⟩ :=
    (entry32Spec 0x6ce) hfork ⟨hscr2.2.2.1, hscr2.2.2.2⟩
      (by simp only [afterSload_getStor, getStor_setTransVal]; exact hw) ht hkeys
      (r32.mono StepIn.toRun)
  unfold t_06ce_c13 at run
  obtain ⟨G10, run⟩ := rp_dest run
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_mload (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_mstore (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_add (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_mstore (StepIn.toRun s1)
  try dsimp only [List.set] at run
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_and (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_swap (n := 0) rfl (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_add (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_mload (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_sub (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨⟨v, hv⟩, hst⟩ := extcodesize_step hfork (StepIn.toRun s1)
  rw [St.self (d := d1) hv rfl] at run
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_iszero (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_dup rfl (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_iszero (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun s1)
  rcases rp_branch run with ⟨-, G11, run⟩ | ⟨-, G11, run⟩
  · exact (SFunc.RunCutP.false_of_noOk (SFunc.runP_iff_runCutP_nil.mp run) (by decide)).elim
  unfold t_0733_c13 at run
  obtain ⟨G12, run⟩ := rp_dest run
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_pop (StepIn.toRun s1)
  obtain ⟨d1', s1, run⟩ := rp_next run
  obtain ⟨gw, _, rfl⟩ := ri_gas (StepIn.toRun s1)
  obtain ⟨sf, hcall, run⟩ := rp_next run
  -- the `CALL`: the child is admitted, the caller's state satisfies `Pre`'s pieces
  have hpost : lidoSpec.Post sevm.currentTarget sevm sf := by
    refine ContractSpecSem.post_of_call_self_with (c := lidoSpec) (Q := InRoots R)
      (run := hcall) hfork rfl
      (fun pc' sevm' pre' post' child hq hd hat hf hpw =>
        ih pc' sevm' pre' post' child hd hat hf (hadm.mono hq) hpw)
      (St_pref _ _ _ _) ?_ trivial (zero_le_B256 _) ?_
    · have hc := congrFun hcode2 sevm.currentTarget
      rw [getStor_St_code] at hc
      rw [getStor_St_code, getCode_eq_of_state_eq hst, hc]
      simpa [getStor_St_code, afterSload_getCode, getCode_setTransVal] using hcode
    · show RegInv (Devm.getStor d1 sevm.currentTarget)
      rw [getStor_eq_of_state_eq hst]
      exact hinv2
  have hinvF : RegInv (Devm.getStor sf sevm.currentTarget) := hpost.2
  obtain ⟨flag, hsf⟩ := call_stack hfork (StepIn.toRun hcall)
  rw [St.self (d := sf) hsf rfl] at run
  have run := SFunc.Run.cut (run.mono StepIn.toRun)
  obtain ⟨d2, s2, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_iszero s2
  obtain ⟨d2, s2, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_dup rfl s2
  obtain ⟨d2, s2, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_iszero s2
  obtain ⟨d2, s2, run⟩ := ric_next run
  obtain ⟨_, rfl⟩ := ri_push s2
  rcases ric_branch run with ⟨-, G13, run⟩ | ⟨-, G13, run⟩
  · exact (SFunc.RunCutP.false_of_noOk run (by decide)).elim
  exact t0745_regInv hfork hfa hinvF run

/-! ## The `pause` selector wrapper (entry 49) -/

private instance : Inhabited SFunc := ⟨.undefined⟩

/-- **`pause(address)` (wrapper 49) establishes the frame postcondition** inside
a root derivation: the `pause` field of `LidoWriterSpecsM lidoA`. -/
theorem pause_wrapper_post {R : Exec.Deriv} {sevm : Sevm} {d : Devm}
    {o : Outcome} {w : SFunc}
    (hfork : CoveredFork sevm.benvStat.fork) (_hcode : sevm.code = code)
    (hadm : Exec.FrameAdmitted sevm.currentTarget (lidoFrameEntry lidoA) R.exc)
    (ih : LidoDeeper (lidoFrameEntry lidoA) sevm)
    (hw : prog[49]? = some w) (hloc : LocalApart sevm) (hA : EntryAt lidoA sevm d)
    (hmem : MemOK d.memory) (hpre : lidoSpec.Pre sevm.currentTarget sevm d)
    (run : SFunc.RunP (StepIn R) prog sevm d w o) :
    lidoSpec.Post sevm.currentTarget sevm (Outcome.devm o) := by
  rw [show prog[49]? = some t_0208_c49 from rfl] at hw
  cases hw
  obtain ⟨entries, hwit⟩ : RegInv (Devm.getStor d sevm.currentTarget) := hpre.inv.left rfl
  have hAe := hA entries hwit
  rw [St.self (d := d) rfl rfl] at run
  unfold t_0208_c49 at run
  obtain ⟨G1, run⟩ := rp_dest run
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_calldatasize (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun s1)
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun s1)
  obtain ⟨G2, hcall⟩ := rp_call (g := t_0fec_c7) rfl run
  rcases hcall with ⟨D7, r7, run⟩ | ⟨D7, r7, -⟩
  swap
  · exact (SFunc.RunP.not_halted_entry writerNoHalt_set (k := 7) (by decide) rfl r7 rfl).elim
  have r7 := r7.mono StepIn.toRun
  rw [show (Bytes.toB256 [0x04] : B256) = 4 from rfl] at r7
  obtain ⟨ht, G3, rfl⟩ := entry7_ret r7
  unfold t_0216_c49 at run
  obtain ⟨G4, run⟩ := rp_dest run
  obtain ⟨d1, s1, run⟩ := rp_next run
  obtain ⟨_, rfl⟩ := ri_push (StepIn.toRun s1)
  obtain ⟨G5, hcall⟩ := rp_call (g := t_05ac_c13) rfl run
  rcases hcall with ⟨D13, r13, run⟩ | ⟨D13, r13, -⟩
  swap
  · exact (SFunc.RunP.not_halted_entry writerNoHalt_set (k := 13) (by decide) rfl r13 rfl).elim
  have hinv := entry13_regInv hfork hadm ih hmem hwit hpre.code ht
    (fun ht0 => hAe.2 ⟨ht0, ht⟩) hloc.1 r13
  have hst := SFunc.RunP.state_of_silent StepIn.toRun (S := []) rfl (by decide) (by decide) run
  have h : RegInv (Devm.getStor (Outcome.devm o) sevm.currentTarget) := by
    rw [getStor_eq_of_state_eq hst]; exact hinv
  exact ⟨trivial, h⟩

end Blanc.Lift.LidoCircuitBreakerDeployed
