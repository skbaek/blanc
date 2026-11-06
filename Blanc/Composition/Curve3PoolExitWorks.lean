import Blanc.Composition.Curve3PoolExitFits
import Blanc.Composition.Curve3PoolExitTx
import Blanc.Composition.Curve3PoolExitMoment
import Blanc.Composition.Curve3Pool3CrvCoinExactFloor

/-!
# `lp_exit`, from a moment of mainnet, under marked hypotheses

`exit_run`: at a `ColdEntry`, the frame commits with exactly the requested residual gas, ending at the canonical
final state. **Marked, not proved here:** `ExitMarked` (coverage, USDC at the moment, the hash class of the new `E`, the
fee's bound, the minter and address 4 at the cut) and `ExitCold` (the canonical chain's cost, refund and effect).
`lp_exit_of_marked` is the theorem those give.
-/

namespace Blanc.Composition.Curve3PoolPublic

open Jaune Blanc Blanc.Lift Blanc.ExecutionTrace
open Blanc.Lift.Curve3Pool (rlExactCost rlBurnBase rlBurnMem rlHeadMem3 rlAmt rlEnv Checkpoint RLExactCalls WClosed)
open Blanc.Composition.Curve3Pool3CrvLiteralWitness (RealCoins exitPushD exitPushN exit_pushesF rlFloorPremises_c3crv
  pinsFrom pinsFrom_entry pinsFrom_blind pinsFrom_wClosed pinsFrom_stable)
open Blanc.Composition.Curve3Pool3CrvExactAssembly (rlC3Calls rlC3W)
open Blanc.Composition.Curve3Pool3CrvHeadlines (c3With_wClosed)
open Blanc.Composition.Curve3Pool3CrvInstance (coinOf tokOf)

/-! ## The frame's run, ending at its canonical final state -/

/-- `remove_liquidity`'s calls with the real coins. -/
noncomputable abbrev exitCalls (msg : Msg) : RLExactCalls :=
  rlC3Calls (initSevm msg) (initDevm msg) (exitPushD (initSevm msg) ((initDevm msg).getStor msg.currentTarget))
    (exitPushN (initSevm msg) ((initDevm msg).getStor msg.currentTarget))

/-- The state after the burn, canonically. -/
noncomputable abbrev exitAfterBurn (msg : Msg) (T : B256) : Devm :=
  (exitCalls msg).burnNext (rlBurnBase (initSevm msg) (initDevm msg) T (exitCalls msg)) []
    (rlBurnMem (initSevm msg) (rlHeadMem3 (initSevm msg) (initDevm msg) T (exitCalls msg)))

/-- The frame's last state from the state after the burn: its event, then the lock's release. -/
noncomputable abbrev exitLast (msg : Msg) (d : Devm) (l : Log) : Devm :=
  afterSstore (initSevm msg) (d.addLog l) (Bytes.toB256 [255, 255, 255]) (Bytes.toB256 [0])

/-- The canonical schedule ignores the frame's static initial gas. -/
theorem rlBurn_withStaticGas (sevm : Sevm) (F : Nat) (pre : Devm) (T : B256) (P : RLExactCalls) :
    rlBurnBase {sevm with gas := F} pre T P = rlBurnBase sevm pre T P ∧
      rlHeadMem3 {sevm with gas := F} pre T P = rlHeadMem3 sevm pre T P := by
  simp only [rlBurnBase, Curve3Pool.rlHead3, Curve3Pool.rlHead2, Curve3Pool.rlHead1, Curve3Pool.rlHead0,
    rlHeadMem3, Curve3Pool.rlHeadMem2, Curve3Pool.rlHeadMem1, Curve3Pool.rlHeadMem0, Curve3Pool.rlIterBase,
    Curve3Pool.rlIterMem, Curve3Pool.rlSupplyBase, Curve3Pool.rlSupplyMem, Curve3Pool.rlLoopMem0, Curve3Pool.rlPushNext,
    Curve3Pool.rlPushBase, Curve3Pool.rlPushMem, Curve3Pool.rlReplyLen, Curve3Pool.rlS2Base, Curve3Pool.rlS2MemOf,
    Curve3Pool.rlS1Base, Curve3Pool.rlS2Next, Curve3Pool.rlS2Mem, Curve3Pool.rlS2Mem2, Curve3Pool.rlS2Base1,
    Curve3Pool.rlV, Curve3Pool.rlB, rlAmt, afterSload_withStaticGas, afterSstore_withStaticGas,
    dataWord_withStaticGas, identityCallNext_withStaticGas, rawTailBaseNext_withStaticGas, and_self]

/-- The canonical schedule's memories ignore the frame's static initial gas. -/
theorem RLWindows.ofStaticGas {sevm : Sevm} {F : Nat} {pre : Devm} {T : B256} {P : RLExactCalls}
    (h : Curve3Pool.RLWindows {sevm with gas := F} pre T P) : Curve3Pool.RLWindows sevm pre T P := by
  have hb : ∀ M, rlBurnMem {sevm with gas := F} M = rlBurnMem sevm M := fun M => by
    simp only [rlBurnMem, dataWord_withStaticGas]
  have hh : ∀ i (m : Mem), Curve3Pool.rlPushMem {sevm with gas := F} pre T i m = Curve3Pool.rlPushMem sevm pre T i m := fun i m => by
    simp only [Curve3Pool.rlPushMem, Curve3Pool.rlS2MemOf, Curve3Pool.rlS2Mem, Curve3Pool.rlS2Mem2, Curve3Pool.rlV,
      Curve3Pool.rlB, rlAmt, dataWord_withStaticGas]
  have e0 := rlBurn_withStaticGas sevm F pre T P
  have hm0 : Curve3Pool.rlHeadMem0 {sevm with gas := F} pre T P = Curve3Pool.rlHeadMem0 sevm pre T P ∧
      Curve3Pool.rlHeadMem1 {sevm with gas := F} pre T P = Curve3Pool.rlHeadMem1 sevm pre T P ∧
      Curve3Pool.rlHeadMem2 {sevm with gas := F} pre T P = Curve3Pool.rlHeadMem2 sevm pre T P := by
    simp only [Curve3Pool.rlHeadMem0, Curve3Pool.rlHeadMem1, Curve3Pool.rlHeadMem2, Curve3Pool.rlHead0, Curve3Pool.rlHead1,
      Curve3Pool.rlHead2, Curve3Pool.rlIterBase, Curve3Pool.rlIterMem, Curve3Pool.rlSupplyBase, Curve3Pool.rlSupplyMem,
      Curve3Pool.rlLoopMem0, Curve3Pool.rlPushNext, Curve3Pool.rlPushBase, Curve3Pool.rlPushMem, Curve3Pool.rlReplyLen,
      Curve3Pool.rlS2Base, Curve3Pool.rlS2MemOf, Curve3Pool.rlS1Base, Curve3Pool.rlS2Next, Curve3Pool.rlS2Mem,
      Curve3Pool.rlS2Mem2, Curve3Pool.rlS2Base1, Curve3Pool.rlV, Curve3Pool.rlB, rlAmt, afterSload_withStaticGas,
      afterSstore_withStaticGas, dataWord_withStaticGas, identityCallNext_withStaticGas, rawTailBaseNext_withStaticGas,
      and_self]
  obtain ⟨⟨r0, s0⟩, ⟨r1, s1⟩, ⟨r2, s2⟩, ⟨r3, s3⟩⟩ := h
  rw [hm0.1, hh] at r0 s0
  rw [hm0.2.1, hh] at r1 s1
  rw [hm0.2.2, hh] at r2 s2
  rw [e0.2, hb] at r3 s3
  exact ⟨⟨r0, s0⟩, ⟨r1, s1⟩, ⟨r2, s2⟩, ⟨by simpa only [rlAmt, dataWord_withStaticGas] using r3, s3⟩⟩

/-- `rx_rl_frame_floor` at message entry, keeping the frame's end. -/
theorem rl_msg_end {msg : Msg} {s : Curve3Pool.State} {o : Curve3Pool.Out} {T : B256} {W : Nat → Devm → Prop} {U : Nat}
    (P : RLExactCalls) (hcode : (initSevm msg).code = Curve3Pool.code)
    (hfork : CoveredFork (initSevm msg).benvStat.fork) (hstatic : (initSevm msg).isStatic = false)
    (hdepth : (initSevm msg).depth ≠ 0) (hlen : 4 ≤ (initSevm msg).data.length)
    (hcd : (initSevm msg).data.length < 2 ^ 256)
    (hsel : Sevm.selector (initSevm msg) = Curve3Pool.selRemoveLiquidity)
    (hck : Checkpoint ((initDevm msg).getStor msg.currentTarget) s)
    (hstep : Curve3Pool.step s (rlEnv (initSevm msg) T) (Curve3Pool.decodeCall (initSevm msg)) = some o)
    (hid : IdReady (initSevm msg) (initDevm msg))
    (hWc : ∀ k, k ≤ 3 → WClosed (initSevm msg) (W k)) (hWb : W 0 (initDevm msg))
    (hP : Curve3Pool.RLFloorPremises (initSevm msg) (initDevm msg) T W U P)
    {R : Nat} (hR : 2201 ≤ R) (hG : R + rlExactCost (initSevm msg) (initDevm msg) T P < 2 ^ 256) :
    ∃ post, exec (initEvm (msg.withGas (R + rlExactCost (initSevm msg) (initDevm msg) T P))) = .ok post ∧
      post.gasLeft = R ∧ ∃ d l, Devm.EqModGas d (P.burnNext (rlBurnBase (initSevm msg) (initDevm msg) T P) []
          (rlBurnMem (initSevm msg) (rlHeadMem3 (initSevm msg) (initDevm msg) T P))) ∧
        (∃ S M G, post = St (afterSstore (initSevm msg) (d.addLog l) (Bytes.toB256 [255, 255, 255])
          (Bytes.toB256 [0])) S M G) ∧ Curve3Pool.RLWindows (initSevm msg) (initDevm msg) T P := by
  obtain ⟨hval, hT0, hmulw, hminw, hlew, hTa⟩ := Curve3Pool.removeLiquidity_walkChecks hlen hsel hck hstep
  obtain ⟨F, hF⟩ : ∃ F, F = R + rlExactCost (initSevm msg) (initDevm msg) T P := ⟨_, rfl⟩
  have hcost := Curve3Pool.rlExactCost_withStaticGas (initSevm msg) F (initDevm msg) T P
  obtain ⟨r, hr, D, rfl, hDg, ⟨d, l, hd, S, M, G, hD⟩, -, hwin⟩ := Curve3Pool.rx_rl_frame_floor
    (sevm := {initSevm msg with gas := F}) (pre := initDevm msg) (T := T) P hfork hstatic hdepth hlen hcd hsel
    (hid.withStaticGas F) hck.unlocked hval (fun k hk => (hWc k hk).withStaticGas F) hWb (hP.withStaticGas F)
    hmulw hT0 hminw hlew hTa hR (by rw [hcost]; omega)
  rw [hcost, ← hF] at hr
  obtain ⟨exD⟩ := Lift.lift_exactM (sevm := {initSevm msg with gas := F}) Curve3Pool.cert_checkM
    Curve3Pool.cert_jumpsOkM hcode hfork ⟨Curve3Pool.t_0000_c0, rfl, hr⟩
  rw [← hF]
  obtain ⟨e1, e2⟩ := rlBurn_withStaticGas (initSevm msg) F (initDevm msg) T P
  have hb : rlBurnMem {initSevm msg with gas := F} (rlHeadMem3 (initSevm msg) (initDevm msg) T P) =
      rlBurnMem (initSevm msg) (rlHeadMem3 (initSevm msg) (initDevm msg) T P) := by
    simp only [rlBurnMem, rlAmt, dataWord_withStaticGas]
  rw [e1, e2, hb] at hd
  exact ⟨D, Lift.exec_withGas_of_frame exD, hDg, d, l, hd, ⟨S, M, G, hD⟩, RLWindows.ofStaticGas hwin⟩

/-- **The frame's run at any residual `R ≥ 2201`, ending at its canonical final state.** -/
theorem exit_run {msg : Msg} {s : Curve3Pool.State} {o : Curve3Pool.Out} {T : B256}
    (hcode : (initSevm msg).code = Curve3Pool.code) (hfork : CoveredFork (initSevm msg).benvStat.fork)
    (hstatic : (initSevm msg).isStatic = false) (hdepth : 2 ≤ (initSevm msg).depth)
    (hlen : 4 ≤ (initSevm msg).data.length) (hcd : (initSevm msg).data.length < 2 ^ 256)
    (hsel : Sevm.selector (initSevm msg) = Curve3Pool.selRemoveLiquidity)
    (hck : Checkpoint ((initDevm msg).getStor msg.currentTarget) s)
    (hstep : Curve3Pool.step s (rlEnv (initSevm msg) T) (Curve3Pool.decodeCall (initSevm msg)) = some o)
    (hid : IdReady (initSevm msg) (initDevm msg))
    (hc3 : Blanc.Composition.Curve3Pool3CrvInstance.C3Entry (initSevm msg) (initDevm msg) T)
    (hC : RealCoins (initSevm msg) (initDevm msg))
    (hburn : Blanc.Composition.Curve3PoolCalleeLive.BurnFits
      (Devm.getStor (initDevm msg) (tokOf (initSevm msg) (initDevm msg))) (initSevm msg).currentTarget
      (initSevm msg).caller.toB256 (rlAmt (initSevm msg)))
    (hf0 : Lift.Dai.MoveFits ((initDevm msg).getStor (coinOf (initSevm msg) (initDevm msg) 0))
      (initSevm msg).currentTarget (initSevm msg).caller
      (Curve3Pool.balAt ((initDevm msg).getStor (initSevm msg).currentTarget) 0 * rlAmt (initSevm msg) / T))
    (hf1 : Blanc.Composition.UsdcLive.MoveFits ((initDevm msg).getStor (coinOf (initSevm msg) (initDevm msg) 1))
      (initSevm msg).currentTarget (initSevm msg).caller
      (Curve3Pool.balAt ((initDevm msg).getStor (initSevm msg).currentTarget) 1 * rlAmt (initSevm msg) / T))
    (hf2 : Lift.Usdt.XferFits ((initDevm msg).getStor (coinOf (initSevm msg) (initDevm msg) 2))
      (initSevm msg).currentTarget (initSevm msg).caller
      (Curve3Pool.balAt ((initDevm msg).getStor (initSevm msg).currentTarget) 2 * rlAmt (initSevm msg) / T))
    {R : Nat} (hR : 2201 ≤ R) (hG : R + rlExactCost (initSevm msg) (initDevm msg) T (exitCalls msg) < 2 ^ 256) :
    ∃ post, exec (initEvm (msg.withGas (R + rlExactCost (initSevm msg) (initDevm msg) T (exitCalls msg)))) = .ok post ∧
      post.gasLeft = R ∧ ∃ d l, Devm.EqModGas d (exitAfterBurn msg T) ∧
        (∃ S M G, post = St (exitLast msg d l) S M G) ∧ Curve3Pool.RLWindows (initSevm msg) (initDevm msg) T (exitCalls msg) := by
  have hne : (initSevm msg).currentTarget ≠ tokOf (initSevm msg) (initDevm msg) := Ne.symm hc3.pool
  have hdep0 : (initSevm msg).depth ≠ 0 := by omega
  have hpush := exit_pushesF (c3 := tokOf (initSevm msg) (initDevm msg))
    (σ := Devm.getStor (initDevm msg) (tokOf (initSevm msg) (initDevm msg))) (T := T)
    hfork hstatic hdepth hC hC.tok hf0 hf1 hf2
  have hP := rlFloorPremises_c3crv rfl hne hfork hstatic hdep0 hc3.prec hc3.supply hburn (pinsFrom_blind hC.tok)
    (fun k _ => pinsFrom_stable k) hpush
  have hWc : ∀ k, k ≤ 3 → WClosed (initSevm msg) (rlC3W (tokOf (initSevm msg) (initDevm msg))
      (Devm.getStor (initDevm msg) (tokOf (initSevm msg) (initDevm msg)))
      (Blanc.Composition.Curve3PoolCalleeLive.burnStor (Devm.getStor (initDevm msg)
        (tokOf (initSevm msg) (initDevm msg))) (initSevm msg).caller.toB256 (rlAmt (initSevm msg)))
      (pinsFrom (initSevm msg) (initDevm msg)) k) := fun k hk => by
    have hk' : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases hk' with rfl | rfl | rfl | rfl
    all_goals exact c3With_wClosed hne (pinsFrom_wClosed hC _)
  exact rl_msg_end (exitCalls msg) hcode hfork hstatic hdep0 hlen hcd hsel hck hstep hid hWc
    ⟨⟨hc3.code, rfl⟩, pinsFrom_entry 0⟩ hP hR hG

/-! ## The message, from the moment's facts -/

/-- **Marked: what the proof takes and this module does not prove.** -/
structure ExitMarked (w : State) : Prop where
  /-- MARKED, the Mac's `Moment.backed`: the pool's books are covered at the moment. -/
  covered : PoolBacked w
  /-- MARKED, the Mac's read at the cut: USDC's proxy, and V2_2 at its word. -/
  usdcCode : w.getCode usdc = Usdc.Proxy.code ∧ w.getCode (usdcImplOf w) = Usdc.Impl.code
  /-- MARKED, provable: 3Crv's minter at the cut (`supply_walk` over the window). -/
  minter : (w.getStor c3).get Curve3Crv.vyMinterSlot = pool.toB256
  /-- MARKED, provable: address 4's code at the cut (`codeAt_empty` over the window). -/
  id4 : w.getCode 4 = ByteArray.empty

/-- A message as a transaction's entry prepares it. -/
abbrev ColdEntry (msg : Msg) (w : State) (E : Adr) (data : Bytes) : Prop := Asked msg w E data

theorem parties_not_precomp {f : Fork} (h : HistFork f) :
    ¬ (Fork.ruleSet f).isPrecomp pool ∧ ¬ (Fork.ruleSet f).isPrecomp Usdc.usdcImpl ∧ (Fork.ruleSet f).isPrecomp 4 ∧
      c3 ∉ (Fork.ruleSet f).precompiles ∧ dai ∉ (Fork.ruleSet f).precompiles ∧ usdc ∉ (Fork.ruleSet f).precompiles ∧
      usdt ∉ (Fork.ruleSet f).precompiles ∧ Usdc.usdcImpl ∉ (Fork.ruleSet f).precompiles := by
  revert h
  cases f <;> decide +kernel

/-- **The cost, refund and effect of the canonical chain at a cold entry.** MARKED: the evaluation still to prove. -/
structure ExitCold (msg : Msg) (w : State) (E : Adr) (a : Nat) (T : B256) : Prop where
  cost : rlExactCost (initSevm msg) (initDevm msg) T (exitCalls msg) = exitFrameGas w E a
  last : ∀ d l S M G, Devm.EqModGas d (exitAfterBurn msg T) →
    (St (exitLast msg d l) S M G).error = none ∧
      (St (exitLast msg d l) S M G).refundCounter = (exitRefund w E a : Int) ∧
      (St (exitLast msg d l) S M G).accountsToDelete.toList = [] ∧
      ExitPaid w (St (exitLast msg d l) S M G).state E a

end Blanc.Composition.Curve3PoolPublic
